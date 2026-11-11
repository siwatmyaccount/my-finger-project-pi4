"""Web export for practice reports.

Each press of the export button writes one self-contained HTML snapshot to
``web_reports/``. A small read-only HTTP server shares that folder on the
local network so a phone on the same Wi-Fi can open it by scanning a QR code.

The server never touches application state: pages are rendered on the Tk
thread and the server only reads finished files, so no locking is needed.
"""

import html
import logging
import os
import re
import socket
import threading
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

FONT_NAME = re.compile(r"^PromptTH-(Light|Regular|SemiBold|Bold)\.ttf$")
FONT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fonts")
REPORT_NAME = re.compile(r"^report_\d{4}-\d{2}-\d{2}_\d{2}-\d{2}-\d{2}\.html$")
DEFAULT_PORT = int(os.environ.get("REPORT_PORT", "8080"))

STYLE = """
@font-face{font-family:"Prompt";font-weight:300;font-display:swap;src:url("/fonts/PromptTH-Light.ttf") format("truetype")}
@font-face{font-family:"Prompt";font-weight:400;font-display:swap;src:url("/fonts/PromptTH-Regular.ttf") format("truetype")}
@font-face{font-family:"Prompt";font-weight:600;font-display:swap;src:url("/fonts/PromptTH-SemiBold.ttf") format("truetype")}
@font-face{font-family:"Prompt";font-weight:700;font-display:swap;src:url("/fonts/PromptTH-Bold.ttf") format("truetype")}
:root{--ink:#2C3E50;--muted:#52667A;--line:#DCE4EC;--bg:#F4F7F6;--card:#FFFFFF;
--purple:#4A235A;--green:#137A4B;--amber:#A56A00;--red:#B83228;--blue:#244B72}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);
font-family:"Prompt","Sarabun","Noto Sans Thai","Leelawadee UI",Tahoma,sans-serif;font-size:17px;line-height:1.55}
header{background:var(--purple);color:#fff;padding:20px 16px}
header h1{margin:0;font-size:1.5rem;font-weight:700}
h2,h3{font-weight:600}
.pain{border-left:6px solid var(--c);margin-bottom:16px}
.pain b{display:block;color:var(--c);font-size:1.3rem;font-weight:600}
.pain p{margin:6px 0 0}
header p{margin:4px 0 0;opacity:.85}
main{max-width:860px;margin:0 auto;padding:16px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px;margin-bottom:16px}
.card{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:14px 16px}
.stat b{display:block;font-size:1.6rem;font-weight:700}
.stat b.long{font-size:1.1rem}
.stat span{color:var(--muted);font-size:.95rem;font-weight:300}
h2{font-size:1.2rem;margin:22px 0 10px}
.set{margin-bottom:12px;border-left:6px solid var(--c)}
.set h3{margin:0 0 4px;font-size:1.1rem}
.badge{display:inline-block;padding:2px 10px;border-radius:999px;background:var(--c);color:#fff;font-weight:600;font-size:.9rem}
.set dl{display:grid;grid-template-columns:max-content 1fr;gap:2px 12px;margin:10px 0}
.set dt{color:var(--muted)}
.set dd{margin:0;font-weight:500}
.tip{background:#F5EFF8;border-radius:10px;padding:8px 12px;margin-top:6px}
.bars{display:flex;align-items:flex-end;gap:10px;height:150px;padding-top:8px}
.bar{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:flex-end;height:100%}
.bar i{display:block;width:100%;max-width:56px;background:var(--blue);border-radius:6px 6px 0 0;min-height:2px}
.bar small{color:var(--muted);margin-top:4px;font-size:.8rem}
.bar em{font-style:normal;font-weight:700;font-size:.9rem}
ul.list{list-style:none;padding:0;margin:0}
ul.list li{border-bottom:1px solid var(--line)}
ul.list a{display:block;padding:12px 4px;color:var(--purple);font-weight:700;text-decoration:none}
footer{color:var(--muted);font-size:.85rem;text-align:center;padding:20px 16px 32px}
"""


def _page(lang, title, body, extra_style=""):
    return (f'<!doctype html><html lang="{lang}"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{html.escape(title)}</title><style>{STYLE}{extra_style}</style></head>'
            f'<body>{body}</body></html>')


SIMPLE_STYLE = """
body{font-size:22px;line-height:1.5;background:#F3F1F6;color:#1F2A37}
.top{background:#4A235A;color:#fff;padding:20px 18px}
.top h1{margin:0 auto;max-width:640px;font-size:28px;font-weight:700}
.top p{margin:4px auto 0;max-width:640px;font-size:20px}
.wrap{max-width:640px;margin:0 auto;padding:16px}
.box{background:#fff;border-radius:22px;padding:20px;margin-bottom:16px;box-shadow:0 2px 10px rgba(0,0,0,.06)}
.box h2{margin:0 0 12px;font-size:26px;font-weight:700;color:#4A235A}
.hero{text-align:center;border:4px solid var(--c)}
.hero .ic{width:76px;height:76px;border-radius:50%;background:var(--c);color:#fff;font-size:48px;font-weight:700;
 line-height:76px;margin:0 auto 6px}
.hero b{display:block;font-size:36px;color:var(--c);line-height:1.25}
.hero p{margin:6px 0 0;font-size:24px}
.nums{display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-bottom:16px}
.num{background:#fff;border-radius:22px;padding:16px;text-align:center;box-shadow:0 2px 10px rgba(0,0,0,.06)}
.num b{display:block;font-size:52px;font-weight:700;color:#4A235A;line-height:1.1}
.num span{font-size:22px}
.pain{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:8px;text-align:center}
.pv{border-radius:18px;padding:12px 6px;background:var(--bg)}
.pv small{display:block;font-size:22px}
.pv b{display:block;font-size:48px;line-height:1.1;color:var(--c)}
.pv span{font-size:20px;color:var(--c);font-weight:600}
.arrow{font-size:40px;color:#7A8A99}
.res{margin-top:12px;padding:12px;border-radius:16px;background:var(--bg);color:var(--c);font-size:24px;font-weight:700;text-align:center}
ul.steps{list-style:none;margin:0;padding:0}
ul.steps li{display:flex;gap:12px;align-items:flex-start;padding:10px 0;border-bottom:2px solid #F0EDF3;font-size:24px}
ul.steps li:last-child{border:0}
ul.steps i{flex:none;width:40px;height:40px;border-radius:50%;background:var(--c);color:#fff;font-style:normal;
 font-weight:700;text-align:center;line-height:40px;font-size:24px}
ul.steps b{color:#B83228}
.days{display:flex;gap:8px;justify-content:space-between}
.d{flex:1;text-align:center;font-size:20px}
.d i{display:block;width:44px;height:44px;border-radius:50%;margin:6px auto;background:#DDD8E2}
.d.on i{background:#1E8E4F}
details{background:#fff;border-radius:22px;padding:8px 20px;margin-bottom:16px;box-shadow:0 2px 10px rgba(0,0,0,.06)}
summary{cursor:pointer;font-weight:600;color:#4A235A;padding:12px 0;font-size:22px;text-align:center}
details .set{box-shadow:none;border:1px solid #E5E1EA;margin:0 0 12px;font-size:19px}
.links{text-align:center;margin:4px 0 8px}
.links a{display:inline-block;padding:14px 26px;border-radius:16px;background:#4A235A;color:#fff;text-decoration:none;
 font-weight:600;font-size:22px}
footer{font-size:18px}
"""


def render_report(data):
    """Render one export snapshot in the approved large-print design."""
    e = html.escape
    t = data["text"]
    simple = data["simple"]
    summary = data["summary"]
    icon = {"ok": "✓", "warn": "!", "info": "i"}.get(summary.get("icon"), "✓")
    boxes = []
    for box in simple["pain_boxes"]:
        value = "–" if box["value"] is None else str(box["value"])
        boxes.append(f'<div class="pv" style="--c:{e(box["color"])};--bg:{e(box["bg"])}">'
                     f'<small>{e(box["label"])}</small><b>{e(value)}</b><span>{e(box["word"])}</span></div>')
    result = simple["pain_result"]
    todo = "".join(f"<li><i>{n}</i><span>{e(tip)}</span></li>" for n, tip in enumerate(simple["todo"], 1))
    doctor = "".join(f"<li><i>!</i><span>{e(sign)}<br><b>{e(action)}</b></span></li>"
                     for sign, action in simple["doctor"])
    days = "".join(f'<div class="d{" on" if on else ""}">{e(name)}<i></i></div>' for name, on in simple["day_dots"])
    sets = []
    for item in data["sets"]:
        rows = "".join(f"<dt>{e(k)}</dt><dd>{e(v)}</dd>" for k, v in item["rows"])
        sets.append(f'<article class="card set" style="--c:{e(item["color"])}"><h3>{e(item["heading"])}</h3>'
                    f'<span class="badge">{e(item["result"])}</span><dl>{rows}</dl></article>')
    body = (f'<header class="top"><h1>{e(t["title"])}</h1><p>{e(simple["date"])} · {e(data["hand"])}</p></header>'
            f'<main class="wrap">'
            f'<section class="box hero" style="--c:{e(summary["color"])}"><div class="ic">{icon}</div>'
            f'<b>{e(summary["headline"])}</b><p>{e(summary["detail"])}</p></section>'
            f'<div class="nums"><div class="num"><b>{simple["poses"]}</b><span>{e(t["n_poses"])}</span></div>'
            f'<div class="num"><b>{simple["sets"]}</b><span>{e(t["n_sets"])}</span></div></div>'
            f'<section class="box"><h2>{e(t["pain"])}</h2><div class="pain">{boxes[0]}<div class="arrow">→</div>{boxes[1]}</div>'
            f'<div class="res" style="--c:{e(result["color"])};--bg:{e(result["bg"])}">{e(result["text"])}</div></section>'
            f'<section class="box" style="--c:#1E8E4F"><h2>{e(t["todo"])}</h2><ul class="steps">{todo}</ul></section>'
            f'<section class="box" style="--c:#B83228"><h2>{e(t["doctor"])}</h2><ul class="steps">{doctor}</ul></section>'
            f'<section class="box"><h2>{e(t["days"])}</h2><div class="days">{days}</div></section>'
            f'<details><summary>{e(t["details"])}</summary>{"".join(sets)}</details>'
            f'<p class="links"><a href="/">{e(t["all"])}</a></p></main>'
            f'<footer>{e(t["disclaimer"])}</footer>')
    return _page(data["lang"], t["title"], body, SIMPLE_STYLE)


def save_report(directory, data, stamp):
    os.makedirs(directory, exist_ok=True)
    name = f"report_{stamp}.html"
    path = os.path.join(directory, name)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as output:
        output.write(render_report(data))
    os.replace(temporary, path)
    return name


def _index_page(directory, lang):
    try:
        names = sorted((n for n in os.listdir(directory) if REPORT_NAME.match(n)), reverse=True)
    except OSError:
        names = []
    th = lang == "th"
    items = []
    for name in names:
        when = datetime.strptime(name[7:26], "%Y-%m-%d_%H-%M-%S")
        label = when.strftime("%d/%m/") + str(when.year + 543 if th else when.year) + when.strftime(" %H:%M:%S")
        items.append(f'<li><a href="/{name}">{html.escape(label)}</a></li>')
    title = "รายงานผลการฝึกทั้งหมด" if th else "All practice reports"
    empty = "ยังไม่มีรายงาน" if th else "No reports yet"
    body = (f'<header><h1>{title}</h1></header><main><div class="card">'
            f'{"<ul class=list>" + "".join(items) + "</ul>" if items else empty}</div></main>')
    return _page(lang, title, body)


class _Handler(BaseHTTPRequestHandler):
    directory = "."
    lang = "th"

    def do_GET(self):
        path = self.path.split("?", 1)[0].lstrip("/")
        if path == "":
            self._send(200, _index_page(self.directory, self.lang).encode("utf-8"))
            return
        if path == "latest":
            names = sorted(n for n in os.listdir(self.directory) if REPORT_NAME.match(n)) \
                if os.path.isdir(self.directory) else []
            if names:
                self.send_response(302)
                self.send_header("Location", "/" + names[-1])
                self.end_headers()
                return
        if path.startswith("fonts/") and FONT_NAME.match(path[6:]):
            try:
                with open(os.path.join(FONT_DIR, path[6:]), "rb") as source:
                    self._send(200, source.read(), "font/ttf", cache=True)
                return
            except OSError:
                pass
        if REPORT_NAME.match(path):  # whitelist: no traversal possible
            try:
                with open(os.path.join(self.directory, path), "rb") as source:
                    self._send(200, source.read())
                return
            except OSError:
                pass
        self._send(404, b"Not found", "text/plain; charset=utf-8")

    def _send(self, code, payload, kind="text/html; charset=utf-8", cache=False):
        self.send_response(code)
        self.send_header("Content-Type", kind)
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "max-age=86400" if cache else "no-store")
        self.end_headers()
        self.wfile.write(payload)

    def log_message(self, fmt, *args):
        logging.debug("web report: " + fmt, *args)


def local_ip():
    """Address other devices on the LAN can reach. UDP connect sends no packets."""
    probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        probe.connect(("10.255.255.255", 1))
        return probe.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        probe.close()


class ReportServer:
    def __init__(self, directory, port=DEFAULT_PORT):
        self.directory = directory
        self.port = port
        self._server = None
        self._thread = None

    def set_language(self, lang):
        if self._server is not None:
            self._server.RequestHandlerClass.lang = lang

    def start(self, lang="th"):
        if self._server is not None:
            self.set_language(lang)
            return self.port
        handler = type("ReportHandler", (_Handler,), {"directory": self.directory, "lang": lang})
        last_error = None
        for port in range(self.port, self.port + 10):
            try:
                self._server = ThreadingHTTPServer(("0.0.0.0", port), handler)
                break
            except OSError as exc:
                last_error = exc
        else:
            raise last_error
        self._server.daemon_threads = True
        self.port = self._server.server_address[1]
        self._thread = threading.Thread(target=self._server.serve_forever, name="WebReport", daemon=True)
        self._thread.start()
        logging.info("Web report server on port %s", self.port)
        return self.port

    def url(self, name=""):
        return f"http://{local_ip()}:{self.port}/{name}"

    def stop(self):
        if self._server is not None:
            self._server.shutdown()
            self._server.server_close()
            self._server = None


def qr_image(text, box_size=10):
    """Return a PIL image of a QR code, or None if the qrcode package is missing."""
    try:
        import qrcode
    except ImportError:
        logging.warning("qrcode package not installed; showing the link only")
        return None
    code = qrcode.QRCode(border=2, box_size=box_size)
    code.add_data(text)
    code.make(fit=True)
    return code.make_image(fill_color="black", back_color="white").convert("RGB")
