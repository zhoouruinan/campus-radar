#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""云端校园通知雷达（GitHub Actions 版）

与本地 skill 的分工：
    本地（电脑开着）  —— AI 整理摘要、判断相关性，质量高，主力通道
    云端（电脑关机）  —— 纯规则整理，只做兜底，保证不漏

抓取与解析逻辑同步自本地 skill 的 scripts/run.py，两边的条目哈希算法一致
（sha1(url)[:16]），因此 seen.json 可以互通，不会重复推送。

无 AI，所以整理是规则化的：
    - 关键词加权判断重不重要
    - 只从标题里抽截止日期（云端不打开原文，拿不到正文里的截止日）
    - 抽不到截止日期就只显示发布日期，不编造

用法（GitHub Actions 里自动运行，本地调试也可）：
    python radar.py             正式跑一轮
    python radar.py --dry-run   只打印将要发送的内容，不发信、不写 seen
"""
import hashlib
import json
import os
import re
import smtplib
import ssl
import sys
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CONFIG = ROOT / "config.json"
SEEN_FILE = ROOT / "seen.json"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

NAV_WORDS = {
    "首页", "上一页", "下一页", "尾页", "末页", "更多", "返回", "跳转",
    "English", "english", "EN", "繁體", "简体", "旧版", "新版", "登录",
    "注册", "联系我们", "站点地图", "版权所有", "详情", "查看", "点击",
    "下载", "附件", "打印", "关闭", "分享", "收藏", "顶部", "回到顶部",
}

A_RE = re.compile(r'<a\b[^>]*?href\s*=\s*["\']([^"\']+)["\'][^>]*?>(.*?)</a>', re.I | re.S)
TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")
YMD_RE = re.compile(r"(20\d{2})\s*[-/年.]\s*(\d{1,2})\s*[-/月.]\s*(\d{1,2})")
MD_RE = re.compile(r"(?<!\d)(\d{1,2})\s*[-/月.]\s*(\d{1,2})(?!\d)")
URL_DATE_RE = re.compile(r"/a/(\d{4})(\d{2})(\d{2})")
SCRIPT_RE = re.compile(r"<(script|style)\b[^>]*>.*?</\1>", re.I | re.S)
COMMENT_RE = re.compile(r"<!--.*?-->", re.S)

# 命中说明与「报名/申请/截止」这类硬时间点相关，必须提醒
IMPORTANT_WORDS = [
    "推免", "保研", "免试", "推荐免试", "研究生", "招生", "报名", "申请",
    "截止", "遴选", "公示", "拟录取", "复试", "调剂", "预报名", "夏令营",
    "奖学金", "助学金", "助学贷款", "认定", "评选", "申报", "材料",
]
# 命中说明大概率是噪音，降级处理
NOISE_WORDS = [
    "喜报", "表彰", "祝贺", "荣获", "获奖", "夺冠", "夺冠", "通报表扬",
    "讲座", "报告会", "学术报告", "论坛", "沙龙", "预告",
]


def log(msg):
    print(msg, file=sys.stderr)


def decode_bytes(raw):
    m = re.search(rb'charset=["\']?\s*([\w-]+)', raw[:4096], re.I)
    enc = m.group(1).decode("ascii", "ignore").lower() if m else None
    for e in [enc, "utf-8", "gb18030", "gbk", "big5"]:
        if not e:
            continue
        try:
            return raw.decode(e)
        except (UnicodeDecodeError, LookupError):
            continue
    return raw.decode("utf-8", "ignore")


def http_get(url, timeout=25):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "zh-CN,zh;q=0.9",
    })
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return decode_bytes(resp.read()), resp.geturl()


def clean_text(html_frag):
    txt = TAG_RE.sub(" ", html_frag)
    for a, b in (("&nbsp;", " "), ("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">")):
        txt = txt.replace(a, b)
    return WS_RE.sub(" ", txt).strip()


def norm_date(text, today):
    if not text:
        return None
    m = YMD_RE.search(text)
    if m:
        y, mo, d = (int(x) for x in m.groups())
        try:
            return date(y, mo, d).isoformat()
        except ValueError:
            pass
    m = MD_RE.search(text)
    if m:
        mo, d = int(m.group(1)), int(m.group(2))
        if not (1 <= mo <= 12 and 1 <= d <= 31):
            return None
        try:
            cand = date(today.year, mo, d)
        except ValueError:
            return None
        delta = (cand - today).days
        if delta < -180:
            cand = date(today.year + 1, mo, d)
        elif delta > 180:
            cand = date(today.year - 1, mo, d)
        return cand.isoformat()
    return None


def block_context(html, start, end, pad=200):
    for tag in ("li", "tr", "p", "div"):
        open_at = html.rfind(f"<{tag}", 0, start)
        if open_at == -1:
            continue
        close_at = html.find(f"</{tag}>", end)
        if close_at == -1:
            continue
        seg = html[open_at:close_at]
        if seg.count(f"<{tag}") > 1:
            continue
        return seg
    return html[max(0, start - pad): end + pad]


def parse_list(html, base_url, min_len, today):
    items, seen = [], set()
    html = COMMENT_RE.sub(" ", SCRIPT_RE.sub(" ", html))
    for m in A_RE.finditer(html):
        href, inner = m.group(1), m.group(2)
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        title = clean_text(inner)
        if len(title) < min_len or title in NAV_WORDS:
            continue
        url = urllib.parse.urljoin(base_url, href)
        m_url = URL_DATE_RE.search(url)
        url_date = f"{m_url.group(1)}-{m_url.group(2)}-{m_url.group(3)}" if m_url else None
        context = clean_text(block_context(html, m.start(), m.end()))
        pub = norm_date(context, today) or url_date
        if pub is None:
            up = urllib.parse.urlparse(url)
            if len(title) < 12 or up.path in ("", "/", "/index.html", "/index.htm"):
                continue
        key = (title, url)
        if key in seen:
            continue
        seen.add(key)
        items.append({"title": title, "url": url, "date": pub, "source": ""})
    return items


def item_hash(item):
    return hashlib.sha1((item["url"] or item["title"]).encode("utf-8")).hexdigest()[:16]


def score(item):
    """规则化打分：越大越重要。返回 (分数, 是否噪音)。"""
    t = item["title"]
    s = 0
    for w in IMPORTANT_WORDS:
        if w in t:
            s += 3
    for w in NOISE_WORDS:
        if w in t:
            s -= 4
    if "截止" in t or "报名" in t or "申请" in t:
        s += 2
    return s, s < 0


def extract_deadline(title, today):
    """从标题里抽截止日期。抽不到返回 None —— 云端不打开原文，不猜。"""
    m = re.search(r"(?:截止|截至|于|before)?\s*"
                  r"(20\d{2})\s*[-/年.]\s*(\d{1,2})\s*[-/月.]\s*(\d{1,2})", title)
    if m:
        y, mo, d = (int(x) for x in m.groups())
        try:
            return date(y, mo, d)
        except ValueError:
            pass
    m = re.search(r"(\d{1,2})\s*月\s*(\d{1,2})\s*[日号]", title)
    if m:
        mo, d = int(m.group(1)), int(m.group(2))
        try:
            cand = date(today.year, mo, d)
        except ValueError:
            return None
        if (cand - today).days < -180:
            cand = date(today.year + 1, mo, d)
        return cand
    return None


def build_html(items, today, source_errors):
    """生成邮件正文。紧急度按剩余天数着色。"""
    rows = []
    for idx, it in enumerate(items, 1):
        dl = extract_deadline(it["title"], today)
        if dl:
            left = (dl - today).days
            if left < 0:
                color, tag = "#888780", f"已过期 {abs(left)} 天"
            elif left <= 3:
                color, tag = "#e34d59", f"还剩 {left} 天"
            elif left <= 10:
                color, tag = "#fa8c16", f"还剩 {left} 天"
            else:
                color, tag = "#2ba471", f"还剩 {left} 天"
            date_line = f'截止 {dl.strftime("%m-%d")} · {tag}'
        else:
            color = "#2ba471"
            date_line = f'发布 {it.get("date") or "日期未知"}'
        rows.append(f'''
  <div style="border-left:4px solid {color};background:#f7f8fa;padding:12px 16px;border-radius:6px;margin:0 0 12px">
    <p style="margin:0 0 6px"><strong>{idx}. {it["title"]}</strong></p>
    <p style="margin:0 0 6px;color:{color};font-weight:bold">{date_line} ｜ {it["source"]}</p>
    <p style="margin:8px 0 0"><a href="{it["url"]}" style="color:#185fa5">查看原文</a></p>
  </div>''')

    err_html = ""
    if source_errors:
        err_html = ('<p style="color:#a32d2d;font-size:13px;margin:12px 0 0">'
                    '以下数据源本次抓取失败：' + "、".join(source_errors) + "</p>")

    return f'''<div style="font-family:-apple-system,Segoe UI,Helvetica,Arial,sans-serif;max-width:640px;margin:0 auto;color:#1f2329">
  <h2 style="margin:0 0 8px;color:#2b6cb0">校园通知雷达 · 云端兜底</h2>
  <p style="color:#555;margin:0 0 16px">{len(items)} 条新通知（你的电脑处于离线状态，由云端接管）</p>
  {''.join(rows)}
  <p style="color:#888;font-size:12px;margin:16px 0 0">
    本邮件由 GitHub Actions 自动生成，云端无 AI，摘要与截止日期均从标题提取，未经人工核对。
    电脑开机后本地通道会接管，届时通知会有完整摘要。
  </p>
  {err_html}
</div>'''


def send_mail(subject, html, to_addr, sender, auth_code):
    import email.utils
    from email.mime.multipart import MIMEMultipart
    from email.mime.text import MIMEText

    text = re.sub(r"<[^>]+>", " ", html)
    text = WS_RE.sub(" ", text).strip()

    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = to_addr
    msg["Date"] = email.utils.formatdate(localtime=True)
    msg.attach(MIMEText(text, "plain", "utf-8"))
    msg.attach(MIMEText(html, "html", "utf-8"))

    ctx = ssl.create_default_context()
    with smtplib.SMTP_SSL("smtp.qq.com", 465, context=ctx, timeout=30) as s:
        s.login(sender, auth_code)
        s.send_message(msg, from_addr=sender, to_addrs=[to_addr])


def main():
    dry = "--dry-run" in sys.argv

    # 若本地 48 小时内有心跳，说明电脑开着，云端跳过，避免和本地重复推送/发失败邮件
    HEARTBEAT = ROOT / "last_local_run.txt"
    if HEARTBEAT.exists():
        try:
            last = HEARTBEAT.read_text(encoding="utf-8").strip()
            last_dt = datetime.fromisoformat(last)
            if datetime.now(timezone.utc) - last_dt < timedelta(hours=48):
                print("LOCAL_ACTIVE_SKIP")
                return 0
        except ValueError:
            pass

    today = date.today()

    cfg = json.loads(CONFIG.read_text(encoding="utf-8"))
    sources = [s for s in cfg.get("sources", []) if s.get("enabled", True)]
    window = int(cfg.get("days_window", 45))
    min_len = int(cfg.get("min_title_len", 6))
    cutoff = (today - timedelta(days=window)).isoformat()

    seen = json.loads(SEEN_FILE.read_text(encoding="utf-8"))["hashes"] if SEEN_FILE.exists() else {}

    collected, errors = [], []
    for src in sources:
        name, url = src.get("name", "未命名"), src.get("url", "")
        if not url:
            errors.append(f"{name}(缺 url)")
            continue
        try:
            body, final_url = http_get(url)
        except Exception as exc:
            errors.append(f"{name}({type(exc).__name__})")
            continue
        items = parse_list(body, final_url, min_len, today)
        for it in items:
            it["source"] = name
        items = [it for it in items if not it.get("date") or it["date"] >= cutoff]
        collected.extend(items[: int(cfg.get("limit_per_source", 40))])
        log(f"[ok] {name}: {len(items)} 条")

    uniq, seen_urls = [], set()
    for it in collected:
        if it["url"] in seen_urls:
            continue
        seen_urls.add(it["url"])
        uniq.append(it)
    for it in uniq:
        it["hash"] = item_hash(it)

    pending = [it for it in uniq if it["hash"] not in seen]
    if not pending:
        print("NO_NEW")
        return 0

    # 噪音条目不单独推送，但仍记进 seen，避免下次重复判断
    pending.sort(key=lambda x: (score(x)[0], x.get("date") or ""), reverse=True)
    worth = [it for it in pending if not score(it)[1]]

    if not worth:
        log("[info] 本轮新条目全是低价值内容，静默跳过，仅记录已读")
        for it in pending:
            seen[it["hash"]] = {"title": it["title"], "date": it.get("date"),
                                "at": datetime.now().isoformat(timespec="seconds")}
        if not dry:
            SEEN_FILE.write_text(json.dumps({"hashes": seen}, ensure_ascii=False, indent=2),
                                 encoding="utf-8")
        print("NO_NEW")
        return 0

    subject = (f"【校园通知雷达】{today.strftime('%m-%d')} 有 {len(worth)} 条新通知"
               if len(worth) > 1 else f"【校园通知雷达】{worth[0]['title'][:30]}")
    html = build_html(worth, today, errors)

    if dry:
        print(f"[dry-run] 主题: {subject}")
        print(f"[dry-run] 收件人: {os.environ.get('MAIL_TO', '(未设置)')}")
        print(re.sub(r"<[^>]+>", " ", html))
        return 0

    auth = os.environ.get("SMTP_AUTH_CODE", "")
    to_addr = os.environ.get("MAIL_TO", "")
    sender = os.environ.get("MAIL_FROM", "")
    if not (auth and to_addr and sender):
        log("[失败] 缺少环境变量：需要 SMTP_AUTH_CODE / MAIL_TO / MAIL_FROM")
        return 2

    try:
        send_mail(subject, html, to_addr, sender, auth)
    except Exception as exc:
        log(f"[失败] 邮件发送失败: {type(exc).__name__}: {exc}")
        log("[重要] seen.json 未更新，下一轮会自动重试")
        return 3

    # 只有发送成功才标记已读
    for it in pending:
        seen[it["hash"]] = {"title": it["title"], "date": it.get("date"),
                            "at": datetime.now().isoformat(timespec="seconds")}
    SEEN_FILE.write_text(json.dumps({"hashes": seen}, ensure_ascii=False, indent=2),
                         encoding="utf-8")
    print(f"SENT {len(worth)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
