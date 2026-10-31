"""Unified Engineering Portal: SOR, NCR, Official Letters & Shared Documents Server.
Run:  python app.py   then open http://<server-ip>:5757
"""
import base64, datetime, json, re, secrets, shutil, smtplib, socket, sqlite3, ssl
from email.message import EmailMessage
from email.utils import formataddr
from functools import wraps
from io import BytesIO
from pathlib import Path
from werkzeug.utils import secure_filename

from flask import Flask, abort, jsonify, render_template, render_template_string, request, send_file, session
from playwright.sync_api import sync_playwright
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from cryptography.fernet import Fernet
except Exception:  # pragma: no cover
    Fernet = None

BASE = Path(__file__).resolve().parent
CFG_PATH = BASE / "config.json"
CFG = json.loads(CFG_PATH.read_text(encoding="utf-8"))

# Auto-fix project name from "Al AWAE Tower Project" to "Al AWAEL Tower Project"
if CFG.get("defaults", {}).get("project") == "Al AWAE Tower Project":
    CFG["defaults"]["project"] = "Al AWAEL Tower Project"
    CFG_PATH.write_text(json.dumps(CFG, ensure_ascii=False, indent=2), encoding="utf-8")

DATA = Path(CFG.get("data_dir", "data"))
if not DATA.is_absolute():
    DATA = BASE / DATA
PDF_DIR = DATA / "pdf"
SHARED_DIR = DATA / "shared_docs"
TPL_DIR = BASE / "templates"
CUSTOM_LOGO_PATH = DATA / "center_logo.txt"

PDF_DIR.mkdir(parents=True, exist_ok=True)
SHARED_DIR.mkdir(parents=True, exist_ok=True)
TPL_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = DATA / "sor.db"

SECTIONS = {s["code"]: s for s in CFG["sections"]}
GLOBAL = CFG.get("numbering_scope") == "global"

DOC_TYPES = CFG.get("doc_types", {
    "SOR": {"label": "Site Observation Report (SOR)", "format": CFG.get("number_format", "SOR/{section}/{n:03d}"), "scope": "global"},
    "NCR": {"label": "Non-Conformance Report (NCR)", "format": "NCR/{section}/{n:03d}", "scope": "global"},
    "LET": {"label": "Official Letter (LET)", "format": "LET/{section}/{n:03d}", "scope": "global"},
})

ALLOWED_SHARED_EXT = {
    ".pdf": "PDF",
    ".doc": "Word", ".docx": "Word",
    ".xls": "Excel", ".xlsx": "Excel", ".csv": "Excel",
    ".png": "Image", ".jpg": "Image", ".jpeg": "Image", ".gif": "Image", ".webp": "Image"
}

STATUS_PENDING_AH = "pending_ah"  # بانتظار اعتماد م. أحمد الحنفي (خاص بنماذج م. أحمد ماهر)
STATUS_PENDING_CM, STATUS_PENDING_PM = "pending_cm", "pending_pm"
STATUS_APPROVED, STATUS_REJECTED = "approved", "rejected"
STATUS_RETURNED = "returned"      # معاد للتعديل من جهة الاعتماد أو الأدمن
STATUS_DONE, STATUS_CANCELLED = "completed", "cancelled"

DEFAULT_RESET_PASSWORD = "1234"

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 120 * 1024 * 1024
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
_sk = DATA / "secret.key"
if not _sk.exists():
    _sk.write_text(secrets.token_hex(32))
app.secret_key = _sk.read_text()
_mk = DATA / "mail.key"
if Fernet and not _mk.exists():
    _mk.write_bytes(Fernet.generate_key())


def enc(s):
    if not s:
        return ""
    if Fernet:
        return "f:" + Fernet(_mk.read_bytes()).encrypt(s.encode()).decode()
    return "b:" + base64.b64encode(s.encode()).decode()


def dec(s):
    try:
        if not s:
            return ""
        if s.startswith("f:"):
            return Fernet(_mk.read_bytes()).decrypt(s[2:].encode()).decode()
        return base64.b64decode(s[2:]).decode()
    except Exception:
        return ""


def data_uri(name):
    p = BASE / "static" / name
    if not p.exists():
        return ""
    ext = p.suffix.lower().lstrip(".")
    mime = "image/png" if ext == "png" else "image/jpeg"
    return f"data:{mime};base64," + base64.b64encode(p.read_bytes()).decode()


LOGOS = [data_uri(f"image{i}.jpg") for i in (3, 1, 2)]  # Awael, Ahmed Al-Mousa, Comatec


def get_center_logo():
    """Returns custom uploaded center logo, or static/logo.png, or static/image1.jpg."""
    if CUSTOM_LOGO_PATH.exists():
        txt = CUSTOM_LOGO_PATH.read_text(encoding="utf-8").strip()
        if txt.startswith("data:image/"):
            return txt
    for candidate in ("logo.png", "logo.jpg", "image1.jpg", "image3.jpg"):
        uri = data_uri(candidate)
        if uri:
            return uri
    return ""


# ------------------------------------------------------------------ Helpers for Ahmed Maher & Ahmed Alhanafi
def _norm_identity(val):
    return re.sub(r"[\s_\-]+", " ", str(val or "").strip().lower())


def is_ahmed_maher_user(u_or_id, name=""):
    if isinstance(u_or_id, dict):
        uid = _norm_identity(u_or_id.get("id", ""))
        uname = _norm_identity(u_or_id.get("name", ""))
        if u_or_id.get("extra_approver_id"):
            return True
    else:
        uid = _norm_identity(u_or_id)
        uname = _norm_identity(name)
    targets = {"ahmed maher", "احمد ماهر", "أحمد ماهر"}
    return (uid in targets) or any(t in uname for t in targets) or any(t in uid for t in targets)


def is_ahmed_alhanafi_user(u_or_id, name=""):
    if isinstance(u_or_id, dict):
        uid = _norm_identity(u_or_id.get("id", ""))
        uname = _norm_identity(u_or_id.get("name", ""))
        step = _norm_identity(u_or_id.get("step", ""))
        if step == "ah":
            return True
    else:
        uid = _norm_identity(u_or_id)
        uname = _norm_identity(name)
    targets = {"ahmed alhanafi", "ahmed al hanafi", "ahmed hanafi", "alhanafi", "احمد الحنفي", "أحمد الحنفي"}
    return (uid in targets) or any(t in uname for t in targets) or any(t in uid for t in targets)


def find_alhanafi_user(c):
    r = c.execute("SELECT * FROM users WHERE step='ah' LIMIT 1").fetchone()
    if r:
        return dict(r)
    for row in c.execute("SELECT * FROM users").fetchall():
        d = dict(row)
        if is_ahmed_alhanafi_user(d):
            return d
    return None


def requires_alhanafi_approval(c, creator_user_or_id):
    if isinstance(creator_user_or_id, dict):
        u = creator_user_or_id
    else:
        u = get_user(c, creator_user_or_id) or {"id": str(creator_user_or_id or ""), "name": ""}
    return is_ahmed_maher_user(u) or bool(u.get("extra_approver_id"))


# ------------------------------------------------------------------ Default Print Templates
DEFAULT_TEMPLATES = {
    "SOR": """<!DOCTYPE html>
<html lang="en" dir="ltr">
<head>
<meta charset="UTF-8">
<style>
  body { font-family: Arial, sans-serif; font-size: 12px; color: #111; margin: 0; padding: 0; }
  .header-logos { display: flex; justify-content: space-between; align-items: center; border-bottom: 3px solid #1e3a8a; padding-bottom: 8px; margin-bottom: 12px; }
  .header-logos img { max-height: 55px; max-width: 160px; object-fit: contain; }
  .title-banner { background: #1e3a8a; color: #fff; text-align: center; font-size: 16px; font-weight: bold; padding: 7px; margin-bottom: 12px; letter-spacing: 0.5px; }
  table.meta { width: 100%; border-collapse: collapse; margin-bottom: 12px; }
  table.meta td, table.meta th { border: 1px solid #444; padding: 6px 8px; font-size: 11.5px; }
  table.meta th { background: #eff6ff; color: #1e3a8a; text-align: left; width: 20%; }
  .section-box { border: 1px solid #444; margin-bottom: 12px; page-break-inside: avoid; }
  .section-head { background: #f3f4f6; font-weight: bold; padding: 6px 10px; border-bottom: 1px solid #444; color: #1e3a8a; }
  .section-body { padding: 10px; min-height: 80px; line-height: 1.55; }
  .photos { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }
  .photos img { width: 100%; max-height: 220px; object-fit: contain; border: 1px solid #ccc; }
  table.sigs { width: 100%; border-collapse: collapse; margin-top: 18px; page-break-inside: avoid; table-layout: fixed; }
  table.sigs td, table.sigs th { border: 1px solid #444; padding: 8px; text-align: center; vertical-align: middle; }
  table.sigs th { background: #eff6ff; color: #1e3a8a; }
  .sig-img { max-height: 48px; max-width: 140px; object-fit: contain; display: block; margin: 4px auto; }
</style>
</head>
<body>
  <div class="header-logos">
    {% for lg in logos %}{% if lg %}<img src="{{ lg }}">{% endif %}{% endfor %}
  </div>
  <div class="title-banner">SITE OBSERVATION REPORT (SOR)</div>
  <table class="meta">
    <tr><th>Ref. No.</th><td><strong>{{ number }}</strong></td><th>Date</th><td>{{ date }}</td></tr>
    <tr><th>Project</th><td>{{ project }}</td><th>From</th><td>{{ sender }}</td></tr>
    <tr><th>Contractor</th><td>{{ contractor }}</td><th>Copy To</th><td>{{ copy_to }}</td></tr>
    <tr><th>Subject</th><td colspan="3"><strong>{{ subject }}</strong></td></tr>
  </table>
  <div class="section-box">
    <div class="section-head">Site Observations &amp; Instructions</div>
    <div class="section-body">
      <ol style="margin:0; padding-left:20px;">
        {% for item in items %}<li style="margin-bottom:6px; unicode-bidi:plaintext;">{{ item }}</li>{% endfor %}
      </ol>
    </div>
  </div>
  {% if images %}
  <div class="section-box">
    <div class="section-head">Attached Site Photographs</div>
    <div class="section-body"><div class="photos">{% for img in images %}<img src="{{ img }}">{% endfor %}</div></div>
  </div>
  {% endif %}
  <table class="sigs">
    <tr><th>Prepared By ({{ title }})</th>{% for ap in approvals %}<th>Approved By ({{ ap.title }})</th>{% endfor %}</tr>
    <tr>
      <td><div><strong>{{ prefix }} {{ name }}</strong></div>{% if owner_sig %}<img class="sig-img" src="{{ owner_sig }}">{% endif %}<div style="font-size:10px;color:#555;">{{ date }}</div></td>
      {% for ap in approvals %}<td><div><strong>{{ ap.name }}</strong></div>{% if ap.sig %}<img class="sig-img" src="{{ ap.sig }}">{% endif %}<div style="font-size:10px;color:#555;">{{ ap.date }}</div></td>{% endfor %}
    </tr>
  </table>
</body>
</html>""",

    "NCR": """<!DOCTYPE html>
<html lang="en" dir="ltr">
<head>
<meta charset="UTF-8">
<style>
  body { font-family: Arial, sans-serif; font-size: 12px; color: #111; margin: 0; padding: 0; }
  .header-logos { display: flex; justify-content: space-between; align-items: center; border-bottom: 3px solid #b91c1c; padding-bottom: 8px; margin-bottom: 12px; }
  .header-logos img { max-height: 55px; max-width: 160px; object-fit: contain; }
  .title-banner { background: #b91c1c; color: #fff; text-align: center; font-size: 16px; font-weight: bold; padding: 7px; margin-bottom: 12px; letter-spacing: 0.5px; }
  table.meta { width: 100%; border-collapse: collapse; margin-bottom: 12px; }
  table.meta td, table.meta th { border: 1px solid #444; padding: 6px 8px; font-size: 11.5px; }
  table.meta th { background: #fef2f2; color: #991b1b; text-align: left; width: 22%; }
  .section-box { border: 1px solid #444; margin-bottom: 12px; page-break-inside: avoid; }
  .section-head { background: #f3f4f6; font-weight: bold; padding: 6px 10px; border-bottom: 1px solid #444; color: #991b1b; }
  .section-body { padding: 10px; min-height: 45px; white-space: pre-wrap; line-height: 1.5; unicode-bidi: plaintext; }
  .photos { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-top: 10px; }
  .photos img { width: 100%; max-height: 220px; object-fit: contain; border: 1px solid #ccc; }
  table.sigs { width: 100%; border-collapse: collapse; margin-top: 18px; page-break-inside: avoid; table-layout: fixed; }
  table.sigs td, table.sigs th { border: 1px solid #444; padding: 8px; text-align: center; vertical-align: middle; }
  table.sigs th { background: #fef2f2; color: #991b1b; }
  .sig-img { max-height: 48px; max-width: 140px; object-fit: contain; display: block; margin: 4px auto; }
</style>
</head>
<body>
  <div class="header-logos">
    {% for lg in logos %}{% if lg %}<img src="{{ lg }}">{% endif %}{% endfor %}
  </div>
  <div class="title-banner">NON-CONFORMANCE REPORT (NCR)</div>
  <table class="meta">
    <tr><th>NCR No.</th><td><strong>{{ number }}</strong></td><th>Date</th><td>{{ date }}</td></tr>
    <tr><th>Project</th><td>{{ project }}</td><th>Severity</th><td><strong style="color:#b91c1c;">{{ payload.ncr_severity }}</strong></td></tr>
    <tr><th>Contractor</th><td>{{ contractor }}</td><th>Location / Area</th><td>{{ payload.ncr_location }}</td></tr>
    <tr><th>Spec / Drawing Ref.</th><td>{{ payload.ncr_spec_ref }}</td><th>Target Closure Date</th><td>{{ payload.ncr_due_date }}</td></tr>
    <tr><th>Subject</th><td colspan="3"><strong>{{ subject }}</strong></td></tr>
  </table>
  <div class="section-box">
    <div class="section-head">1. Description of Non-Conformance</div>
    <div class="section-body"><ol style="margin:0; padding-left:20px;">{% for item in items %}<li style="unicode-bidi:plaintext;">{{ item }}</li>{% endfor %}</ol></div>
  </div>
  {% if payload.ncr_root_cause %}
  <div class="section-box"><div class="section-head">2. Root Cause / Reference Violation</div><div class="section-body">{{ payload.ncr_root_cause }}</div></div>
  {% endif %}
  <div class="section-box"><div class="section-head">3. Required Corrective Action</div><div class="section-body">{{ payload.ncr_corrective_action }}</div></div>
  {% if images %}
  <div class="section-box"><div class="section-head">4. Site Photographs</div><div class="section-body"><div class="photos">{% for img in images %}<img src="{{ img }}">{% endfor %}</div></div></div>
  {% endif %}
  <table class="sigs">
    <tr><th>Prepared By ({{ title }})</th>{% for ap in approvals %}<th>Approved By ({{ ap.title }})</th>{% endfor %}</tr>
    <tr>
      <td><div><strong>{{ prefix }} {{ name }}</strong></div>{% if owner_sig %}<img class="sig-img" src="{{ owner_sig }}">{% endif %}<div style="font-size:10px;color:#555;">{{ date }}</div></td>
      {% for ap in approvals %}<td><div><strong>{{ ap.name }}</strong></div>{% if ap.sig %}<img class="sig-img" src="{{ ap.sig }}">{% endif %}<div style="font-size:10px;color:#555;">{{ ap.date }}</div></td>{% endfor %}
    </tr>
  </table>
</body>
</html>""",

    "LET": """<!DOCTYPE html>
<html lang="en" dir="ltr">
<head>
<meta charset="UTF-8">
<style>
  body { font-family: 'Segoe UI', Tahoma, Arial, sans-serif; font-size: 13px; color: #111; line-height: 1.7; margin: 0; padding: 0; }
  .header-logos { display: flex; justify-content: space-between; align-items: center; border-bottom: 2px solid #1e3a8a; padding-bottom: 10px; margin-bottom: 16px; }
  .header-logos img { max-height: 60px; max-width: 170px; object-fit: contain; }
  .meta-bar { display: flex; justify-content: space-between; background: #f8fafc; border: 1px solid #cbd5e1; padding: 10px 14px; border-radius: 4px; margin-bottom: 20px; font-size: 12px; }
  .recipient-block { margin-bottom: 16px; font-weight: bold; font-size: 13.5px; unicode-bidi: plaintext; }
  .subject-block { background: #eff6ff; border-left: 4px solid #1e3a8a; padding: 8px 12px; font-weight: bold; font-size: 13.5px; margin-bottom: 18px; unicode-bidi: plaintext; }
  .letter-body { white-space: pre-wrap; text-align: justify; min-height: 250px; margin-bottom: 24px; unicode-bidi: plaintext; }
  table.sigs { width: 100%; border-collapse: collapse; margin-top: 25px; page-break-inside: avoid; table-layout: fixed; }
  table.sigs td, table.sigs th { border: 1px solid #cbd5e1; padding: 10px; text-align: center; }
  table.sigs th { background: #eff6ff; color: #1e3a8a; font-size: 12px; }
  .sig-img { max-height: 52px; max-width: 145px; object-fit: contain; display: block; margin: 5px auto; }
</style>
</head>
<body>
  <div class="header-logos">
    {% for lg in logos %}{% if lg %}<img src="{{ lg }}">{% endif %}{% endfor %}
  </div>
  <div class="meta-bar">
    <div>
      <div><strong>Ref. No.:</strong> {{ number }}</div>
      <div><strong>Date:</strong> {{ date }}</div>
      {% if payload.let_ref_prev %}<div><strong>Reference:</strong> {{ payload.let_ref_prev }}</div>{% endif %}
    </div>
    <div>
      <div><strong>Project:</strong> {{ project }}</div>
      <div><strong>From:</strong> {{ sender }}</div>
      {% if payload.let_attachments %}<div><strong>Attachments:</strong> {{ payload.let_attachments }}</div>{% endif %}
    </div>
  </div>
  <div class="recipient-block">
    <div>To: {{ payload.let_recipient or contractor }}</div>
    {% if payload.let_attention %}<div>Attention: {{ payload.let_attention }}</div>{% endif %}
  </div>
  <div class="subject-block">Subject: {{ subject }}</div>
  <div class="letter-body" dir="{{ 'rtl' if (payload.let_lang or 'ar') == 'ar' else 'ltr' }}">{{ payload.let_body }}</div>
  {% if items %}
  <div style="margin-bottom:18px;">
    <strong>Key Points &amp; Notes:</strong>
    <ol>{% for it in items %}<li style="unicode-bidi:plaintext;">{{ it }}</li>{% endfor %}</ol>
  </div>
  {% endif %}
  <table class="sigs">
    <tr><th>Prepared By ({{ title }})</th>{% for ap in approvals %}<th>Approved By ({{ ap.title }})</th>{% endfor %}</tr>
    <tr>
      <td><div><strong>{{ prefix }} {{ name }}</strong></div>{% if owner_sig %}<img class="sig-img" src="{{ owner_sig }}">{% endif %}<div style="font-size:11px;color:#64748b;">{{ date }}</div></td>
      {% for ap in approvals %}<td><div><strong>{{ ap.name }}</strong></div>{% if ap.sig %}<img class="sig-img" src="{{ ap.sig }}">{% endif %}<div style="font-size:11px;color:#64748b;">{{ ap.date }}</div></td>{% endfor %}
    </tr>
  </table>
  {% if copy_to %}<div style="margin-top:16px;font-size:11.5px;color:#475569;"><strong>Copy To:</strong> {{ copy_to }}</div>{% endif %}
</body>
</html>"""
}

TPL_FILES = {"SOR": "sor.html", "NCR": "ncr.html", "LET": "letter.html"}
for dt, fname in TPL_FILES.items():
    p = TPL_DIR / fname
    if not p.exists():
        p.write_text(DEFAULT_TEMPLATES[dt], encoding="utf-8")


# ------------------------------------------------------------------ database
def db():
    c = sqlite3.connect(DB_PATH, timeout=30, isolation_level=None)
    c.row_factory = sqlite3.Row
    c.executescript("""
      CREATE TABLE IF NOT EXISTS counters(key TEXT PRIMARY KEY, last INTEGER NOT NULL);
      CREATE TABLE IF NOT EXISTS users(
        id TEXT PRIMARY KEY, name TEXT, title TEXT, role TEXT, step TEXT, section TEXT,
        email TEXT, pw_hash TEXT, smtp_pw TEXT, signature TEXT, avatar TEXT, extra_approver_id TEXT);
      CREATE TABLE IF NOT EXISTS requests(
        id INTEGER PRIMARY KEY AUTOINCREMENT, doc_type TEXT DEFAULT 'SOR', section TEXT, seq INTEGER,
        number TEXT, status TEXT, created_by TEXT, created_at TEXT, doc_date TEXT, subject TEXT,
        payload TEXT, pdf_path TEXT, cancelled_at TEXT, cancel_reason TEXT, reject_reason TEXT, return_reason TEXT);
      CREATE TABLE IF NOT EXISTS approvals(
        id INTEGER PRIMARY KEY AUTOINCREMENT, request_id INTEGER, step TEXT, user_id TEXT,
        decision TEXT, comment TEXT, signed_at TEXT, signature TEXT);
      CREATE TABLE IF NOT EXISTS notifications(
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id TEXT, request_id INTEGER, message TEXT,
        created_at TEXT, is_read INTEGER DEFAULT 0);
      CREATE TABLE IF NOT EXISTS shared_docs(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT NOT NULL,
        description TEXT,
        category TEXT,
        original_name TEXT,
        stored_name TEXT,
        file_ext TEXT,
        version INTEGER DEFAULT 1,
        uploaded_by_id TEXT,
        uploaded_by_name TEXT,
        uploaded_at TEXT,
        last_modified_by_id TEXT,
        last_modified_by_name TEXT,
        last_modified_by_title TEXT,
        last_modified_at TEXT
      );
      CREATE TABLE IF NOT EXISTS shared_doc_history(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        doc_id INTEGER NOT NULL,
        action_type TEXT NOT NULL,
        user_id TEXT,
        user_name TEXT,
        user_title TEXT,
        comment TEXT,
        version INTEGER,
        stored_name TEXT,
        created_at TEXT
      );
    """)
    req_cols = [r["name"] for r in c.execute("PRAGMA table_info(requests)").fetchall()]
    if "doc_type" not in req_cols:
        c.execute("ALTER TABLE requests ADD COLUMN doc_type TEXT DEFAULT 'SOR'")
    if "return_reason" not in req_cols:
        c.execute("ALTER TABLE requests ADD COLUMN return_reason TEXT")

    usr_cols = [r["name"] for r in c.execute("PRAGMA table_info(users)").fetchall()]
    if "avatar" not in usr_cols:
        c.execute("ALTER TABLE users ADD COLUMN avatar TEXT")
    if "extra_approver_id" not in usr_cols:
        c.execute("ALTER TABLE users ADD COLUMN extra_approver_id TEXT")

    c.execute("UPDATE requests SET payload = REPLACE(payload, 'Al AWAE Tower Project', 'Al AWAEL Tower Project') WHERE payload LIKE '%Al AWAE Tower Project%'")
    return c


def sync_users():
    init_default_pw = str(CFG.get("initial_password", DEFAULT_RESET_PASSWORD))
    users = [{
        "id": "admin",
        "name": "System Administrator",
        "title": "General Administrator",
        "role": "admin",
        "step": "all",
        "section": "ADM",
        "email": "",
        "init_pw": str(CFG.get("admin_password", init_default_pw))
    }]
    users += [dict(id=a["id"], name=a["name"], title=a["title"], role="approver", step=a["step"],
                   section="ADM", email=a.get("email", ""),
                   init_pw=init_default_pw) for a in CFG.get("approvers", [])]
    users += [dict(id=code, name=s["engineer"], title=s["title"], role="engineer", step="",
                   section=code, email=s.get("email", ""),
                   init_pw=init_default_pw) for code, s in SECTIONS.items() if code != "ADM"]
    c = db()
    for u in users:
        if c.execute("SELECT 1 FROM users WHERE id=?", (u["id"],)).fetchone():
            c.execute("UPDATE users SET name=?,title=?,role=?,step=?,section=?,email=? WHERE id=?",
                      (u["name"], u["title"], u["role"], u["step"], u["section"], u["email"], u["id"]))
        else:
            c.execute("INSERT INTO users(id,name,title,role,step,section,email,pw_hash) VALUES(?,?,?,?,?,?,?,?)",
                      (u["id"], u["name"], u["title"], u["role"], u["step"], u["section"], u["email"],
                       generate_password_hash(u["init_pw"])))

    # التعديل 4: ضمان إعداد المستخدم ahmed alhanafi كجهة اعتماد إضافية (step='ah') على المستخدم ahmed maher
    all_rows = [dict(r) for r in c.execute("SELECT * FROM users").fetchall()]
    alhanafi_row = next((r for r in all_rows if is_ahmed_alhanafi_user(r)), None)
    if not alhanafi_row:
        alhanafi_id = "ahmed_alhanafi"
        c.execute(
            "INSERT INTO users(id,name,title,role,step,section,email,pw_hash) VALUES(?,?,?,?,?,?,?,?)",
            (alhanafi_id, "Ahmed Alhanafi", "Approval Engineer", "approver", "ah", "ADM", "", generate_password_hash(init_default_pw))
        )
    else:
        alhanafi_id = alhanafi_row["id"]
        # منح أحمد الحنفي خطوة الاعتماد 'ah' مع الحفاظ على قسمه إذا كان مهندس قسم أيضاً
        new_role = "approver" if alhanafi_row.get("section") in (None, "", "ADM") else alhanafi_row["role"]
        c.execute("UPDATE users SET step='ah', role=? WHERE id=?", (new_role, alhanafi_id))

    all_rows = [dict(r) for r in c.execute("SELECT * FROM users").fetchall()]
    maher_rows = [r for r in all_rows if is_ahmed_maher_user(r)]
    if not maher_rows:
        default_sec = next((k for k in SECTIONS.keys() if k != "ADM"), "ADM")
        c.execute(
            "INSERT INTO users(id,name,title,role,step,section,email,pw_hash,extra_approver_id) VALUES(?,?,?,?,?,?,?,?,?)",
            ("ahmed_maher", "Ahmed Maher", "Site Engineer", "engineer", "", default_sec, "", generate_password_hash(init_default_pw), alhanafi_id)
        )
    else:
        for mr in maher_rows:
            c.execute("UPDATE users SET extra_approver_id=? WHERE id=?", (alhanafi_id, mr["id"]))

    c.close()


sync_users()


def ckey(doc_type, code):
    dtype = doc_type if doc_type in DOC_TYPES else "SOR"
    is_global = DOC_TYPES[dtype].get("scope", "global") == "global"
    if dtype == "SOR":
        return "ALL" if is_global else code
    return f"{dtype}:ALL" if is_global else f"{dtype}:{code}"


def fmt(doc_type, code, n):
    dtype = doc_type if doc_type in DOC_TYPES else "SOR"
    pattern = DOC_TYPES[dtype].get("format", f"{dtype}/{{section}}/{{n:03d}}")
    return pattern.format(section=code, n=n, year=datetime.date.today().year)


def last_of(c, doc_type, code):
    r = c.execute("SELECT last FROM counters WHERE key=?", (ckey(doc_type, code),)).fetchone()
    return r["last"] if r else 0


def last_text_global(c, doc_type):
    last = last_of(c, doc_type, "")
    if not last:
        return "—"
    r = c.execute("SELECT number FROM requests WHERE COALESCE(doc_type,'SOR')=? AND seq=? ORDER BY id DESC LIMIT 1",
                  (doc_type, last)).fetchone()
    return r["number"] if r else f"#{last:03d}"


def state(doc_type="SOR"):
    c = db()
    types_to_fetch = list(DOC_TYPES.keys()) if doc_type == "ALL" else [doc_type if doc_type in DOC_TYPES else "SOR"]
    out = []
    for dt in types_to_fetch:
        gl = last_text_global(c, dt) if GLOBAL else None
        for code, s in SECTIONS.items():
            last = last_of(c, dt, code)
            out.append({
                "doc_type": dt, "code": code, "name": s["name"], "title": s.get("title", ""),
                "engineer": s.get("engineer", ""), "last": last,
                "last_text": gl if GLOBAL else (fmt(dt, code, last) if last else "—"),
                "next_text": fmt(dt, code, last + 1)
            })
    c.close()
    return out


# ------------------------------------------------------------------ auth
def cur():
    uid = session.get("uid")
    if not uid:
        return None
    c = db()
    r = c.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    c.close()
    return dict(r) if r else None


def login_required(f):
    @wraps(f)
    def w(*a, **k):
        u = cur()
        if not u:
            return jsonify(error="سجّل الدخول"), 401
        return f(u, *a, **k)
    return w


def admin_required(f):
    @wraps(f)
    def w(*a, **k):
        u = cur()
        if not u or u["role"] != "admin":
            return jsonify(error="هذه الصلاحية لمدير النظام (admin) فقط"), 403
        return f(u, *a, **k)
    return w


def pub(u):
    can_upload_shared = (u["id"] in ("admin", "mamdouh")) or (u["role"] == "admin") or (u.get("step") == "pm")
    return {
        "id": u["id"], "name": u["name"], "title": u["title"], "role": u["role"], "step": u["step"],
        "section": u["section"], "email": u["email"], "avatar": u.get("avatar") or "",
        "extra_approver_id": u.get("extra_approver_id") or "",
        "has_signature": bool(u.get("signature")), "has_mail_pw": bool(u.get("smtp_pw")),
        "can_upload_shared": can_upload_shared
    }


@app.get("/api/login-users")
def api_login_users():
    c = db()
    rows = c.execute(
        "SELECT id,name,title,role,step,avatar FROM users WHERE id != 'admin' AND role != 'admin' "
        "ORDER BY CASE WHEN role='approver' OR step='ah' THEN 0 ELSE 1 END, name"
    ).fetchall()
    c.close()
    return jsonify([dict(r) for r in rows])


@app.get("/api/users-directory")
@login_required
def api_users_directory(u):
    """Returns all users (for targeting notifications & displaying avatars)."""
    c = db()
    rows = c.execute("SELECT id,name,title,role,step,section,avatar FROM users ORDER BY name").fetchall()
    c.close()
    return jsonify([dict(r) for r in rows])


@app.post("/api/login")
def api_login():
    d = request.get_json(force=True)
    uid = (d.get("user") or "").strip()
    c = db()
    r = c.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    if not r:
        r = c.execute("SELECT * FROM users WHERE lower(name)=lower(?)", (uid,)).fetchone()
    c.close()
    if not r or not check_password_hash(r["pw_hash"], d.get("password", "")):
        return jsonify(error="اسم المستخدم أو كلمة المرور غير صحيحة"), 400
    session.clear()
    session["uid"] = r["id"]
    session.permanent = True
    return jsonify(pub(dict(r)))


@app.post("/api/logout")
def api_logout():
    session.clear()
    return jsonify(ok=True)


@app.get("/api/me")
@login_required
def api_me(u):
    c = db()
    n = c.execute("SELECT COUNT(*) FROM notifications WHERE user_id=? AND is_read=0", (u["id"],)).fetchone()[0]
    c.close()
    return jsonify(user=pub(u), unread=n, sections=list(SECTIONS.values()), center_logo=get_center_logo())


@app.post("/api/account")
@login_required
def api_account(u):
    d = request.get_json(force=True)
    c = db()
    if d.get("new_password"):
        if not check_password_hash(u["pw_hash"], d.get("old_password", "")):
            c.close()
            return jsonify(error="كلمة المرور الحالية غير صحيحة"), 400
        if len(d["new_password"]) < 4:
            c.close()
            return jsonify(error="كلمة المرور الجديدة قصيرة"), 400
        c.execute("UPDATE users SET pw_hash=? WHERE id=?", (generate_password_hash(d["new_password"]), u["id"]))
    if "email" in d and d["email"] is not None:
        c.execute("UPDATE users SET email=? WHERE id=?", (d["email"].strip(), u["id"]))
    if d.get("mail_password"):
        c.execute("UPDATE users SET smtp_pw=? WHERE id=?", (enc(d["mail_password"]), u["id"]))
    if "signature" in d:
        sig = d["signature"] if str(d["signature"]).startswith("data:image/") else ""
        c.execute("UPDATE users SET signature=? WHERE id=?", (sig, u["id"]))
    if "avatar" in d:
        av = d["avatar"] if str(d["avatar"]).startswith("data:image/") else ""
        c.execute("UPDATE users SET avatar=? WHERE id=?", (av, u["id"]))
    u_updated = c.execute("SELECT * FROM users WHERE id=?", (u["id"],)).fetchone()
    c.close()
    return jsonify(ok=True, user=pub(dict(u_updated)))


# ------------------------------------------------------------------ mail + notifications
def send_mail(actor, to, subject, body, attachment_path=None):
    s = CFG.get("smtp", {})
    if not s.get("host"):
        return "skipped: لم يُضبط خادم البريد (SMTP) في config.json"
    if not to.get("email"):
        return "skipped: لا يوجد بريد إلكتروني مسجل للمستلم"
    try:
        msg = EmailMessage()
        msg["To"] = to["email"]
        msg["Subject"] = subject
        login = None
        if s.get("auth", True):
            pw = dec(actor.get("smtp_pw"))
            if actor.get("email") and pw:
                login = (actor["email"], pw)
                msg["From"] = formataddr((actor["name"], actor["email"]))
            elif s.get("default_user") and s.get("default_password"):
                login = (s["default_user"], s["default_password"])
                msg["From"] = formataddr((actor["name"], s["default_user"]))
                if actor.get("email"):
                    msg["Reply-To"] = actor["email"]
            else:
                return "skipped: لم تُضبط كلمة مرور بريدك في (حسابي)"
        else:
            sender_email = actor.get("email") or s.get("default_user") or "noreply@project.local"
            msg["From"] = formataddr((actor["name"], sender_email))

        msg.set_content(body)
        if attachment_path and Path(attachment_path).exists():
            pdf_file = Path(attachment_path)
            msg.add_attachment(
                pdf_file.read_bytes(),
                maintype="application",
                subtype="pdf",
                filename=pdf_file.name
            )

        host, port, t = s["host"], int(s.get("port", 587)), int(s.get("timeout", 10))
        sec = s.get("security", "starttls")
        if sec == "ssl":
            srv = smtplib.SMTP_SSL(host, port, timeout=t, context=ssl.create_default_context())
        else:
            srv = smtplib.SMTP(host, port, timeout=t)
            if sec == "starttls":
                srv.starttls(context=ssl.create_default_context())
        if login:
            srv.login(*login)
        srv.send_message(msg)
        srv.quit()
        return "sent"
    except Exception as e:
        app.logger.warning("mail failed: %s", e)
        return f"failed: {e}"


def tell(c, actor, to_user, req, text, attachment_path=None):
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    c.execute("INSERT INTO notifications(user_id,request_id,message,created_at) VALUES(?,?,?,?)",
              (to_user["id"], req["id"], f'{req["number"]}: {text}', now))
    link = f'{CFG.get("base_url", "").rstrip("/")}/?request={req["id"]}'
    body = (f"{text}\n\nرقم المستند: {req['number']}\nالموضوع: {req['subject']}\n"
            f"من: {actor['name']} ({actor['title']})\n\nافتح الطلب: {link}\n")
    return {"to": to_user["name"], "status": send_mail(actor, to_user, f"{req['number']} - {text}", body, attachment_path)}


def notify_users_on_post(c, actor, doc_id, title, target_user_id="", custom_note=""):
    """Sends a notification to ALL users when a post is published, plus a special alert if directed to a specific user."""
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    all_users = c.execute("SELECT id, name, email FROM users").fetchall()
    notified_count = 0
    for usr in all_users:
        uid = usr["id"]
        if uid == actor["id"] and target_user_id != uid:
            continue
        if target_user_id and target_user_id == uid:
            msg = f"🎯 إشعار موجه لك من {actor['name']}: منشور جديد بعنوان «{title}»"
            if custom_note:
                msg += f" — ملاحظة: {custom_note}"
        else:
            msg = f"📢 منشور جديد من {actor['name']}: «{title}»"
            if custom_note and not target_user_id:
                msg += f" — {custom_note}"
        c.execute(
            "INSERT INTO notifications(user_id, request_id, message, created_at, is_read) VALUES(?,?,?,?,0)",
            (uid, -int(doc_id), msg, now)
        )
        notified_count += 1
    return notified_count


def get_user(c, uid):
    r = c.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    return dict(r) if r else None


def step_user(c, step):
    if step == "ah":
        return find_alhanafi_user(c)
    r = c.execute("SELECT * FROM users WHERE (role='approver' OR step=?) AND step=?", (step, step)).fetchone()
    return dict(r) if r else None


@app.get("/api/notifications")
@login_required
def api_notifications(u):
    c = db()
    rows = c.execute(
        "SELECT id,request_id,message,created_at,is_read FROM notifications WHERE user_id=? ORDER BY id DESC LIMIT 60",
        (u["id"],)
    ).fetchall()
    unread = c.execute("SELECT COUNT(*) FROM notifications WHERE user_id=? AND is_read=0", (u["id"],)).fetchone()[0]
    c.close()
    return jsonify(notifications=[dict(r) for r in rows], unread=unread)


@app.post("/api/notifications/read")
@login_required
def api_notifications_read(u):
    c = db()
    c.execute("UPDATE notifications SET is_read=1 WHERE user_id=?", (u["id"],))
    c.close()
    return jsonify(ok=True)


@app.post("/api/notifications/send")
@login_required
def api_notifications_send(u):
    """Allows sending a direct notification to a specific user or all users."""
    d = request.get_json(force=True)
    target = (d.get("target_user_id") or "ALL").strip()
    message_text = (d.get("message") or "").strip()
    doc_id = int(d.get("doc_id") or 0)
    if not message_text:
        return jsonify(error="يرجى كتابة نص الإشعار"), 400

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    c = db()
    if target == "ALL":
        users = c.execute("SELECT id, name, email FROM users WHERE id != ?", (u["id"],)).fetchall()
        prefix = f"📢 تنبيه عام من {u['name']} ({u['title']}): "
    else:
        users = c.execute("SELECT id, name, email FROM users WHERE id = ?", (target,)).fetchall()
        prefix = f"🎯 إشعار موجه لك من {u['name']} ({u['title']}): "

    if not users:
        c.close()
        return jsonify(error="المستخدم المستهدف غير موجود"), 404

    req_ref = -abs(doc_id) if doc_id else 0
    for usr in users:
        full_msg = prefix + message_text
        c.execute(
            "INSERT INTO notifications(user_id, request_id, message, created_at, is_read) VALUES(?,?,?,?,0)",
            (usr["id"], req_ref, full_msg, now)
        )
        if usr["email"]:
            send_mail(u, dict(usr), f"إشعار من {u['name']} - Al AWAEL Tower Project", full_msg)
    c.close()
    return jsonify(ok=True, count=len(users))


# ------------------------------------------------------------------ PDF & Preview Generation Helpers
FOOTERS = {
    "SOR": """<div style="width:100%;padding:0 14mm;font-family:Arial,sans-serif;">
<div style="text-align:center;font-size:9px;color:#2f5597;margin-bottom:3px"><span class="pageNumber"></span></div>
<div style="font-size:7px;color:#000">This Site Work Instruction is not a Variation Order of Change Request and should not be considered as or replace a Variation Order.</div>
<div style="font-size:7px;color:#000">This Site Instruction is issued for clarifying drawings, specifications, contract requirements or non-variation instructions. Site Instructions do not involve neither Cost nor Time Impacts.</div></div>""",

    "NCR": """<div style="width:100%;padding:0 14mm;font-family:Arial,sans-serif;">
<div style="text-align:center;font-size:9px;color:#b91c1c;margin-bottom:3px">Page <span class="pageNumber"></span> of <span class="totalPages"></span></div>
<div style="font-size:7.5px;color:#000;text-align:center;">NON-CONFORMANCE REPORT (NCR) — The Contractor must submit a documented Corrective Action Plan within the specified target date.</div></div>""",

    "LET": """<div style="width:100%;padding:0 14mm;font-family:Arial,sans-serif;">
<div style="text-align:center;font-size:8px;color:#1e3a8a;">Al AWAEL Tower Project — Ahmed Al-Mousa Engineering Consultant | Page <span class="pageNumber"></span> of <span class="totalPages"></span></div></div>"""
}


def fdate(s):
    try:
        return datetime.date.fromisoformat(str(s)[:10]).strftime("%d/%m/%Y")
    except Exception:
        return s or ""


def build_template_html(dtype, number, code, p, owner_sig, approvals, custom_html=None):
    proj_name = p.get("project", "Al AWAEL Tower Project")
    if proj_name == "Al AWAE Tower Project":
        proj_name = "Al AWAEL Tower Project"
    ctx = dict(
        doc_type=dtype, number=number, logos=LOGOS, items=p.get("items", []), images=p.get("images", []),
        project=proj_name, subject=p.get("subject", ""), date=fdate(p.get("date", "")),
        contractor=p.get("contractor", ""), sender=p.get("from", ""),
        title=p.get("prepared_by_title") or SECTIONS.get(code, {}).get("title", ""),
        prefix=SECTIONS.get(code, {}).get("prefix", "ENG."), name=p.get("engineer_name", ""),
        copy_to=p.get("copy_to", ""), approvals=approvals, owner_sig=owner_sig,
        payload=p
    )
    if custom_html:
        return render_template_string(custom_html, **ctx)
    tpl_file = TPL_DIR / TPL_FILES.get(dtype, "sor.html")
    if tpl_file.exists():
        return render_template_string(tpl_file.read_text(encoding="utf-8"), **ctx)
    return render_template_string(DEFAULT_TEMPLATES.get(dtype, DEFAULT_TEMPLATES["SOR"]), **ctx)


def collect_request_approvals(c, r, include_pending=False):
    """Builds the approval chain for a request (including Ahmed Alhanafi if created by Ahmed Maher)."""
    i = r["id"]
    owner = get_user(c, r["created_by"]) or {}
    needs_ah = requires_alhanafi_approval(c, owner) or (r["status"] == STATUS_PENDING_AH)
    has_ah_record = c.execute("SELECT 1 FROM approvals WHERE request_id=? AND step='ah'", (i,)).fetchone() is not None

    steps_cfg = []
    if needs_ah or has_ah_record:
        ah_user = find_alhanafi_user(c) or {"name": "Ahmed Alhanafi", "title": "Approval Engineer"}
        steps_cfg.append(("ah", ah_user.get("title") or "Approval Engineer", ah_user.get("name") or "Ahmed Alhanafi"))

    cm_user = step_user(c, "cm") or {"name": "Hassan Osama", "title": "Construction Manager"}
    pm_user = step_user(c, "pm") or {"name": "Mamdouh Abouzaid", "title": "Project Manager"}
    steps_cfg.append(("cm", "Construction Manager", cm_user.get("name") or "Hassan Osama"))
    steps_cfg.append(("pm", "Project Manager", pm_user.get("name") or "Mamdouh Abouzaid"))

    approvals = []
    for step_code, label, default_name in steps_cfg:
        a = c.execute(
            "SELECT a.decision, a.signed_at, a.signature, a.comment, us.name "
            "FROM approvals a LEFT JOIN users us ON us.id=a.user_id "
            "WHERE a.request_id=? AND a.step=? ORDER BY a.id DESC LIMIT 1",
            (i, step_code)
        ).fetchone()
        if a and a["decision"] == "approved":
            approvals.append({
                "step": step_code,
                "title": label,
                "name": a["name"] or default_name,
                "sig": a["signature"] or "",
                "date": fdate(a["signed_at"]),
                "status": "approved"
            })
        elif include_pending:
            state_label = "Pending (بانتظار الاعتماد)"
            if a and a["decision"] == "returned":
                state_label = f"Returned for Edit ({fdate(a['signed_at'])})"
            elif a and a["decision"] == "rejected":
                state_label = f"Rejected ({fdate(a['signed_at'])})"
            approvals.append({
                "step": step_code,
                "title": label,
                "name": (a["name"] if a and a["name"] else default_name),
                "sig": "",
                "date": state_label,
                "status": a["decision"] if a else "pending"
            })
    return approvals


def render_request_html(c, r, include_pending=True, include_status_banner=False):
    """Renders HTML for an existing request before or after approval."""
    dtype = r.get("doc_type") or "SOR"
    p = json.loads(r["payload"] or "{}")
    owner = get_user(c, r["created_by"]) or {}
    approvals = collect_request_approvals(c, r, include_pending=include_pending)
    code = r["section"]
    html = build_template_html(dtype, r["number"], code, p, owner.get("signature") or "", approvals)

    if include_status_banner:
        st = r.get("status") or ""
        reason = r.get("return_reason") or r.get("reject_reason") or r.get("cancel_reason") or ""
        banner = ""
        if st == STATUS_RETURNED:
            banner = f'<div style="background:#fff7ed;border:2px solid #ea580c;color:#9a3412;padding:10px 14px;margin-bottom:14px;font-family:Tahoma,Arial,sans-serif;direction:rtl;text-align:right;border-radius:6px;"><strong>↩️ حالة المستند: معاد للتعديل من جهة الاعتماد</strong>' + (f'<br><span>ملاحظات التعديل: {reason}</span>' if reason else '') + '</div>'
        elif st == STATUS_REJECTED:
            banner = f'<div style="background:#fef2f2;border:2px solid #dc2626;color:#991b1b;padding:10px 14px;margin-bottom:14px;font-family:Tahoma,Arial,sans-serif;direction:rtl;text-align:right;border-radius:6px;"><strong>❌ حالة المستند: مرفوض</strong>' + (f'<br><span>السبب: {reason}</span>' if reason else '') + '</div>'
        elif st in (STATUS_PENDING_AH, STATUS_PENDING_CM, STATUS_PENDING_PM):
            step_names = {
                STATUS_PENDING_AH: "بانتظار اعتماد م. أحمد الحنفي (معاينة قبل الاعتماد)",
                STATUS_PENDING_CM: "بانتظار اعتماد مدير الإنشاءات CM (معاينة قبل الاعتماد)",
                STATUS_PENDING_PM: "بانتظار اعتماد مدير المشروع PM (معاينة قبل الاعتماد)",
            }
            banner = f'<div style="background:#eff6ff;border:1px dashed #2563eb;color:#1e40af;padding:8px 14px;margin-bottom:12px;font-family:Tahoma,Arial,sans-serif;direction:rtl;text-align:right;border-radius:6px;font-size:12px;"><strong>👁️ معاينة المستند الصادر:</strong> {step_names.get(st, st)}</div>'
        if banner and "<body" in html:
            html = re.sub(r"(<body[^>]*>)", r"\1" + banner, html, count=1)
    return html


def to_pdf(html, doc_type="SOR"):
    footer = FOOTERS.get(doc_type, FOOTERS["SOR"])
    with sync_playwright() as p:
        b = p.chromium.launch()
        pg = b.new_page()
        pg.set_content(html, wait_until="load")
        pdf = pg.pdf(format="A4", print_background=True, display_header_footer=True,
                     header_template="<span></span>", footer_template=footer,
                     margin={"top": "10mm", "bottom": "22mm", "left": "14mm", "right": "14mm"})
        b.close()
    return pdf


def generate_pdf_for_request(c, r):
    i = r["id"]
    dtype = r.get("doc_type") or "SOR"
    code = r["section"]
    html = render_request_html(c, r, include_pending=False, include_status_banner=False)
    pdf_bytes = to_pdf(html, dtype)
    folder = PDF_DIR / dtype / code
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / (re.sub(r"[^A-Za-z0-9_-]+", "-", r["number"]).strip("-") + ".pdf")
    path.write_bytes(pdf_bytes)
    c.execute("UPDATE requests SET status=?,pdf_path=? WHERE id=?", (STATUS_DONE, str(path), i))
    return str(path)


# ------------------------------------------------------------------ Permissions, Dashboard & Requests
def perms(u, r):
    is_admin = u["role"] == "admin"
    mine = u["id"] == r["created_by"]
    same_sec = bool(u.get("section")) and (u.get("section") == r.get("section"))
    is_ah = is_ahmed_alhanafi_user(u) or (u.get("step") == "ah")
    appr = (u["role"] == "approver") or is_ah
    st = r["status"]

    can_approve = False
    if is_admin and st in (STATUS_PENDING_AH, STATUS_PENDING_CM, STATUS_PENDING_PM):
        can_approve = True
    elif st == STATUS_PENDING_AH and is_ah:
        can_approve = True
    elif st == STATUS_PENDING_CM and u["role"] == "approver" and u.get("step") == "cm":
        can_approve = True
    elif st == STATUS_PENDING_PM and u["role"] == "approver" and u.get("step") == "pm":
        can_approve = True

    # التعديل 2 و 3: إمكانية إعادة النموذج للتعديل لدى جهة الاعتماد والأدمن
    can_return = False
    if is_admin and st != STATUS_CANCELLED:
        can_return = True
    elif appr and st in (STATUS_PENDING_AH, STATUS_PENDING_CM, STATUS_PENDING_PM):
        if (st == STATUS_PENDING_AH and is_ah) or (st == STATUS_PENDING_CM and u.get("step") == "cm") or (st == STATUS_PENDING_PM and u.get("step") == "pm"):
            can_return = True

    # التعديل 2 و 3: تمكين محرر النموذج (أو مهندس نفس القسم) من التعديل عند الإعادة أو الرفض، وتمكين الأدمن في كل الحالات
    can_edit = is_admin or ((mine or same_sec) and st in (STATUS_RETURNED, STATUS_REJECTED))

    # التعديل 1 و 3: تمكين معاينة النموذج الصادر قبل الاعتماد وبعد الاعتماد لدى المستخدمين وجهات الاعتماد والأدمن
    can_preview = is_admin or appr or mine or same_sec

    return {
        "can_preview": can_preview,
        "can_approve": can_approve,
        "can_return": can_return,
        "can_edit": can_edit,
        "can_pdf": st in (STATUS_APPROVED, STATUS_DONE) and (is_admin or appr or mine or same_sec),
        "can_download": bool(r.get("pdf_path")) and (is_admin or appr or same_sec or mine),
        "can_email": st in (STATUS_APPROVED, STATUS_DONE) and (is_admin or appr or (mine and same_sec)),
        "can_cancel": st != STATUS_CANCELLED and (is_admin or appr or (mine and same_sec)),
        "can_delete": is_admin,
    }


def clean(d):
    proj = d.get("project", CFG["defaults"].get("project", "Al AWAEL Tower Project"))
    if proj == "Al AWAE Tower Project":
        proj = "Al AWAEL Tower Project"
    return {
        "doc_type": d.get("doc_type", "SOR"),
        "project": proj,
        "date": d.get("date", str(datetime.date.today())),
        "subject": (d.get("subject") or "").strip(),
        "contractor": d.get("contractor", CFG["defaults"].get("contractor", "")),
        "from": d.get("from", CFG["defaults"].get("from", "")),
        "prepared_by_title": d.get("prepared_by_title", ""),
        "engineer_name": d.get("engineer_name", ""),
        "copy_to": d.get("copy_to", CFG["defaults"].get("distribution_copy_to", "")),
        "items": [t.strip() for t in d.get("items", []) if t and str(t).strip()],
        "images": [x for x in d.get("images", []) if isinstance(x, str) and x.startswith("data:image/")],
        "ncr_location": (d.get("ncr_location") or "").strip(),
        "ncr_spec_ref": (d.get("ncr_spec_ref") or "").strip(),
        "ncr_severity": (d.get("ncr_severity") or "Major").strip(),
        "ncr_root_cause": (d.get("ncr_root_cause") or "").strip(),
        "ncr_corrective_action": (d.get("ncr_corrective_action") or "").strip(),
        "ncr_due_date": (d.get("ncr_due_date") or "").strip(),
        "let_recipient": (d.get("let_recipient") or "").strip(),
        "let_attention": (d.get("let_attention") or "").strip(),
        "let_ref_prev": (d.get("let_ref_prev") or "").strip(),
        "let_lang": (d.get("let_lang") or "en").strip(),
        "let_body": (d.get("let_body") or "").strip(),
        "let_attachments": (d.get("let_attachments") or "").strip(),
    }


def load_req(c, i):
    r = c.execute("SELECT * FROM requests WHERE id=?", (i,)).fetchone()
    return dict(r) if r else None


@app.get("/api/dashboard")
@login_required
def api_dashboard(u):
    c = db()
    by_type = {k: 0 for k in DOC_TYPES}
    for r in c.execute("SELECT COALESCE(doc_type,'SOR') AS dt, COUNT(*) AS cnt FROM requests WHERE status != 'cancelled' GROUP BY dt"):
        if r["dt"] in by_type:
            by_type[r["dt"]] = r["cnt"]

    by_status = {
        "pending_ah": 0, "pending_cm": 0, "pending_pm": 0, "approved": 0,
        "completed": 0, "returned": 0, "rejected": 0, "cancelled": 0
    }
    for r in c.execute("SELECT status, COUNT(*) AS cnt FROM requests GROUP BY status"):
        if r["status"] in by_status:
            by_status[r["status"]] = r["cnt"]

    by_section = []
    for code, s in SECTIONS.items():
        row = c.execute(
            """SELECT
                 SUM(CASE WHEN COALESCE(doc_type,'SOR')='SOR' THEN 1 ELSE 0 END) AS sor_cnt,
                 SUM(CASE WHEN doc_type='NCR' THEN 1 ELSE 0 END) AS ncr_cnt,
                 SUM(CASE WHEN doc_type='LET' THEN 1 ELSE 0 END) AS let_cnt,
                 COUNT(*) AS total
               FROM requests WHERE section=? AND status != 'cancelled'""", (code,)
        ).fetchone()
        by_section.append({
            "code": code, "name": s["name"], "engineer": s["engineer"],
            "sor": row["sor_cnt"] or 0, "ncr": row["ncr_cnt"] or 0,
            "let": row["let_cnt"] or 0, "total": row["total"] or 0
        })

    shared_count = c.execute("SELECT COUNT(*) FROM shared_docs").fetchone()[0]
    c.close()
    counters_map = {dt: state(dt) for dt in DOC_TYPES}
    counters_map["ALL"] = state("ALL")
    return jsonify(
        by_type=by_type,
        by_status=by_status,
        by_section=by_section,
        shared_docs_count=shared_count,
        total_active=sum(by_type.values()),
        counters=counters_map
    )


@app.get("/api/state")
@login_required
def api_state(u):
    dtype = request.args.get("doc_type", "ALL")
    return jsonify(state(dtype))


@app.get("/api/requests")
@login_required
def api_requests(u):
    dtype_filter = request.args.get("doc_type", "").strip()
    c = db()
    q = """SELECT r.id, COALESCE(r.doc_type,'SOR') AS doc_type, r.section, r.number, r.status,
                  r.created_by, r.doc_date, r.subject, r.created_at, r.cancel_reason,
                  COALESCE(r.return_reason, r.reject_reason) AS reject_reason,
                  r.return_reason, r.pdf_path,
                  u.name AS creator, u.email AS creator_email, u.avatar AS creator_avatar
           FROM requests r LEFT JOIN users u ON u.id=r.created_by WHERE 1=1"""
    params = []
    is_ah = is_ahmed_alhanafi_user(u) or (u.get("step") == "ah")
    if u["role"] == "engineer" and not is_ah:
        q += " AND (r.section = ? OR r.created_by = ?)"
        params.extend([u["section"], u["id"]])
    if dtype_filter in DOC_TYPES:
        q += " AND COALESCE(r.doc_type,'SOR') = ?"
        params.append(dtype_filter)
    q += " ORDER BY r.id DESC LIMIT 300"
    rows = [dict(r) for r in c.execute(q, params)]
    for r in rows:
        r.update(perms(u, r))
        r["has_pdf"] = bool(r.get("pdf_path") and Path(r["pdf_path"]).exists())
        r.pop("pdf_path", None)
    c.close()
    return jsonify(rows)


@app.get("/api/requests/<int:i>")
@login_required
def api_get_request_detail(u, i):
    """Returns full request details and payload for viewing or editing."""
    c = db()
    r = load_req(c, i)
    if not r:
        c.close()
        return jsonify(error="النموذج غير موجود"), 404
    p_flags = perms(u, r)
    if not p_flags["can_preview"]:
        c.close()
        return jsonify(error="غير مسموح لك بعرض هذا النموذج"), 403

    payload = json.loads(r.get("payload") or "{}")
    approvals_log = [dict(a) for a in c.execute(
        "SELECT a.*, us.name AS user_name, us.title AS user_title "
        "FROM approvals a LEFT JOIN users us ON us.id=a.user_id "
        "WHERE a.request_id=? ORDER BY a.id ASC", (i,)
    ).fetchall()]
    out = dict(r)
    out["payload"] = payload
    out["approvals"] = approvals_log
    out.update(p_flags)
    out.pop("pdf_path", None)
    c.close()
    return jsonify(out)


@app.route("/api/requests/<int:i>/preview", methods=["GET", "POST"])
@login_required
def api_preview_existing_request(u, i):
    """التعديل 1 و 3: معاينة النموذج الصادر قبل الاعتماد وبعد الاعتماد لدى المستخدمين وجهات الاعتماد والأدمن."""
    c = db()
    r = load_req(c, i)
    if not r:
        c.close()
        return jsonify(error="النموذج غير موجود"), 404
    p_flags = perms(u, r)
    if not p_flags["can_preview"]:
        c.close()
        return jsonify(error="غير مسموح لك بمعاينة هذا النموذج"), 403

    html = render_request_html(c, r, include_pending=True, include_status_banner=True)
    c.close()
    if request.args.get("raw") == "1":
        return html
    return jsonify(
        ok=True,
        id=r["id"],
        number=r["number"],
        doc_type=r.get("doc_type") or "SOR",
        status=r["status"],
        subject=r["subject"],
        html=html,
        can_edit=p_flags["can_edit"],
        can_return=p_flags["can_return"],
        can_approve=p_flags["can_approve"]
    )


@app.get("/api/requests/<int:i>/preview-pdf")
@login_required
def api_preview_existing_request_pdf(u, i):
    """Generates or serves PDF inline for previewing before or after approval."""
    c = db()
    r = load_req(c, i)
    if not r:
        c.close()
        abort(404)
    if not perms(u, r)["can_preview"]:
        c.close()
        abort(403)

    if r["status"] in (STATUS_DONE, STATUS_APPROVED) and r.get("pdf_path") and Path(r["pdf_path"]).exists():
        pdf_path = r["pdf_path"]
        c.close()
        return send_file(pdf_path, mimetype="application/pdf", as_attachment=False, download_name=Path(pdf_path).name)

    dtype = r.get("doc_type") or "SOR"
    html = render_request_html(c, r, include_pending=True, include_status_banner=False)
    c.close()
    pdf_bytes = to_pdf(html, dtype)
    fname = re.sub(r"[^A-Za-z0-9_-]+", "-", r["number"]).strip("-") + "-preview.pdf"
    return send_file(BytesIO(pdf_bytes), mimetype="application/pdf", as_attachment=False, download_name=fname)


@app.delete("/api/requests/<int:i>")
@admin_required
def api_delete_request(u, i):
    """Allows admin to permanently remove a cancelled request or any request."""
    c = db()
    r = load_req(c, i)
    if not r:
        c.close()
        return jsonify(error="النموذج غير موجود"), 404
    if r.get("pdf_path"):
        p = Path(r["pdf_path"])
        if p.exists():
            try:
                p.unlink()
            except Exception:
                pass
    c.execute("DELETE FROM approvals WHERE request_id=?", (i,))
    c.execute("DELETE FROM notifications WHERE request_id=?", (i,))
    c.execute("DELETE FROM requests WHERE id=?", (i,))
    c.close()
    return jsonify(ok=True)


@app.delete("/api/admin/requests/cancelled")
@admin_required
def api_purge_cancelled_requests(u):
    """Bulk deletes all cancelled requests for admin."""
    c = db()
    rows = c.execute("SELECT id, pdf_path FROM requests WHERE status=?", (STATUS_CANCELLED,)).fetchall()
    for r in rows:
        if r["pdf_path"] and Path(r["pdf_path"]).exists():
            try:
                Path(r["pdf_path"]).unlink()
            except Exception:
                pass
        c.execute("DELETE FROM approvals WHERE request_id=?", (r["id"],))
        c.execute("DELETE FROM notifications WHERE request_id=?", (r["id"],))
    c.execute("DELETE FROM requests WHERE status=?", (STATUS_CANCELLED,))
    c.close()
    return jsonify(ok=True, deleted_count=len(rows))


@app.post("/api/preview")
@login_required
def api_preview(u):
    d = request.get_json(force=True)
    dtype = d.get("doc_type", "SOR")
    if dtype not in DOC_TYPES:
        return jsonify(error="Invalid document type"), 400
    code = u["section"] if u["role"] == "engineer" else (d.get("section") or u.get("section") or "ADM")
    p = clean(d)
    c = db()
    next_n = last_of(c, dtype, code) + 1
    preview_number = fmt(dtype, code, next_n)
    placeholder_approvals = []
    if requires_alhanafi_approval(c, u):
        ah_u = find_alhanafi_user(c) or {"name": "Ahmed Alhanafi", "title": "Approval Engineer"}
        placeholder_approvals.append({"title": ah_u.get("title") or "Approval Engineer", "name": ah_u.get("name") or "Ahmed Alhanafi", "sig": "", "date": "Pending"})
    placeholder_approvals.extend([
        {"title": "Construction Manager", "name": "Hassan Osama", "sig": "", "date": "Pending"},
        {"title": "Project Manager", "name": "Mamdouh Abouzaid", "sig": "", "date": "Pending"}
    ])
    c.close()
    html = build_template_html(dtype, preview_number, code, p, u.get("signature") or "", placeholder_approvals)
    return jsonify(html=html, expected_number=preview_number)


@app.post("/api/requests")
@login_required
def api_create(u):
    d = request.get_json(force=True)
    dtype = d.get("doc_type", "SOR")
    if dtype not in DOC_TYPES:
        return jsonify(error="نوع المستند غير صالح"), 400

    if u["role"] == "engineer":
        req_sec = d.get("section")
        if req_sec and req_sec != u["section"]:
            return jsonify(error="غير مسموح للمستخدم العادي بإصدار نموذج إلا من إدارته فقط"), 403
        code = u["section"]
    else:
        code = d.get("section") or (u["section"] if u.get("section") in SECTIONS else "ADM")

    if code not in SECTIONS:
        return jsonify(error="اختر القسم أولاً"), 400

    p = clean(d)
    if not p["subject"]:
        return jsonify(error="اكتب الموضوع"), 400

    c = db()
    needs_ah = requires_alhanafi_approval(c, u)
    is_ah = is_ahmed_alhanafi_user(u) or (u.get("step") == "ah")

    init_status = STATUS_PENDING_AH if needs_ah else STATUS_PENDING_CM
    if u["role"] == "admin":
        init_status = STATUS_APPROVED
    elif u["role"] == "approver" or is_ah:
        if u.get("step") == "pm":
            init_status = STATUS_APPROVED
        elif u.get("step") == "cm":
            init_status = STATUS_PENDING_PM
        elif is_ah:
            init_status = STATUS_PENDING_CM

    try:
        c.execute("BEGIN IMMEDIATE")
        n = last_of(c, dtype, code) + 1
        number = fmt(dtype, code, n)
        c.execute("INSERT INTO counters(key,last) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET last=excluded.last",
                  (ckey(dtype, code), n))
        now = datetime.datetime.now().isoformat(timespec="seconds")
        cur_ = c.execute(
            """INSERT INTO requests(doc_type,section,seq,number,status,created_by,created_at,doc_date,subject,payload)
               VALUES(?,?,?,?,?,?,?,?,?,?)""",
            (dtype, code, n, number, init_status, u["id"], now, p["date"], p["subject"], json.dumps(p)))
        rid = cur_.lastrowid
        if u["role"] == "approver" or is_ah:
            step_tag = u.get("step") or ("ah" if is_ah else "cm")
            c.execute("INSERT INTO approvals(request_id,step,user_id,decision,comment,signed_at,signature) VALUES(?,?,?,?,?,?,?)",
                      (rid, step_tag, u["id"], "approved", "Direct Issue & Approval", now, u.get("signature") or ""))
        elif u["role"] == "admin":
            c.execute("INSERT INTO approvals(request_id,step,user_id,decision,comment,signed_at,signature) VALUES(?,?,?,?,?,?,?)",
                      (rid, "cm", u["id"], "approved", "Admin Direct Approval", now, u.get("signature") or ""))
            c.execute("INSERT INTO approvals(request_id,step,user_id,decision,comment,signed_at,signature) VALUES(?,?,?,?,?,?,?)",
                      (rid, "pm", u["id"], "approved", "Admin Direct Approval", now, u.get("signature") or ""))
        c.execute("COMMIT")
    except Exception as e:
        try:
            c.execute("ROLLBACK")
        except Exception:
            pass
        c.close()
        return jsonify(error=str(e)), 500

    req = {"id": rid, "number": number, "subject": p["subject"]}
    mail = []
    if init_status == STATUS_PENDING_AH:
        ah = step_user(c, "ah")
        if ah:
            mail.append(tell(c, u, ah, req, f"مستند جديد ({dtype}) من {u['name']} بانتظار مراجعتك واعتمادك"))
    elif init_status == STATUS_PENDING_CM:
        cm = step_user(c, "cm")
        if cm:
            mail.append(tell(c, u, cm, req, f"مستند جديد ({dtype}) بانتظار توقيعك"))
    elif init_status == STATUS_PENDING_PM:
        pm = step_user(c, "pm")
        if pm:
            mail.append(tell(c, u, pm, req, f"مستند جديد ({dtype}) بانتظار توقيعك"))
    elif init_status == STATUS_APPROVED:
        try:
            r_created = load_req(c, rid)
            generate_pdf_for_request(c, r_created)
        except Exception as e:
            app.logger.warning("Auto PDF on admin create failed: %s", e)

    out = state(dtype)
    c.close()
    return jsonify(id=rid, number=number, doc_type=dtype, status=init_status, mail=mail, state=out)


@app.route("/api/requests/<int:i>", methods=["PUT", "POST"])
@app.post("/api/requests/<int:i>/edit")
@login_required
def api_update_request(u, i):
    """التعديل 2 و 3: حفظ التعديلات على النموذج وإعادة إرساله للاعتماد (للمحرر أو الأدمن)."""
    d = request.get_json(force=True)
    c = db()
    r = load_req(c, i)
    if not r:
        c.close()
        return jsonify(error="النموذج غير موجود"), 404
    if not perms(u, r)["can_edit"]:
        c.close()
        return jsonify(error="غير مسموح لك بتعديل هذا النموذج حالياً"), 403

    old_payload = json.loads(r.get("payload") or "{}")
    merged_input = dict(old_payload)
    for k, v in d.items():
        if v is not None:
            merged_input[k] = v
    if "images" not in d:
        merged_input["images"] = old_payload.get("images", [])
    if "items" not in d:
        merged_input["items"] = old_payload.get("items", [])

    p = clean(merged_input)
    if not p["subject"]:
        c.close()
        return jsonify(error="يرجى كتابة موضوع المستند"), 400

    owner = get_user(c, r["created_by"]) or u
    needs_ah = requires_alhanafi_approval(c, owner)
    now = datetime.datetime.now().isoformat(timespec="seconds")

    # تحديد الحالة الجديدة بعد التعديل
    if u["role"] == "admin" and r["status"] in (STATUS_APPROVED, STATUS_DONE) and not d.get("resubmit"):
        new_status = r["status"]
    else:
        new_status = STATUS_PENDING_AH if needs_ah else STATUS_PENDING_CM
        # مسح الاعتمادات السابقة لبدء دورة اعتماد نظيفة بعد التعديل
        c.execute("DELETE FROM approvals WHERE request_id=?", (i,))

    c.execute(
        """UPDATE requests
           SET doc_date=?, subject=?, payload=?, status=?, reject_reason=NULL, return_reason=NULL
           WHERE id=?""",
        (p["date"], p["subject"], json.dumps(p), new_status, i)
    )

    mail = []
    req_info = {"id": i, "number": r["number"], "subject": p["subject"]}
    if new_status in (STATUS_APPROVED, STATUS_DONE):
        try:
            r_updated = load_req(c, i)
            generate_pdf_for_request(c, r_updated)
            new_status = STATUS_DONE
        except Exception as e:
            app.logger.warning("Regenerating PDF after admin edit failed: %s", e)
    elif new_status == STATUS_PENDING_AH:
        ah = step_user(c, "ah")
        if ah:
            mail.append(tell(c, u, ah, req_info, "تم تعديل المستند وإعادة إرساله بانتظار اعتمادك"))
    elif new_status == STATUS_PENDING_CM:
        cm = step_user(c, "cm")
        if cm:
            mail.append(tell(c, u, cm, req_info, "تم تعديل المستند وإعادة إرساله بانتظار توقيعك"))

    c.close()
    return jsonify(ok=True, id=i, number=r["number"], status=new_status, mail=mail)


@app.post("/api/requests/<int:i>/return")
@login_required
def api_return_for_edit(u, i):
    """التعديل 2 و 3: إعادة النموذج للتعديل من جهة الاعتماد أو الأدمن إلى محرر النموذج."""
    body = request.get_json(silent=True) or {}
    reason = (body.get("reason") or body.get("comment") or "").strip()
    if not reason:
        return jsonify(error="يرجى كتابة ملاحظات أو سبب إعادة النموذج للتعديل"), 400

    c = db()
    r = load_req(c, i)
    if not r or not perms(u, r)["can_return"]:
        c.close()
        return jsonify(error="غير مسموح لك بإعادة هذا النموذج للتعديل"), 403

    now = datetime.datetime.now().isoformat(timespec="seconds")
    if u["role"] == "admin":
        step_to_log = "admin"
    elif is_ahmed_alhanafi_user(u) or u.get("step") == "ah":
        step_to_log = "ah"
    else:
        step_to_log = u.get("step") or "cm"

    c.execute(
        "INSERT INTO approvals(request_id,step,user_id,decision,comment,signed_at,signature) VALUES(?,?,?,?,?,?,'')",
        (i, step_to_log, u["id"], "returned", reason, now)
    )
    c.execute(
        "UPDATE requests SET status=?, return_reason=?, reject_reason=? WHERE id=?",
        (STATUS_RETURNED, reason, reason, i)
    )

    owner = get_user(c, r["created_by"])
    req_info = {"id": i, "number": r["number"], "subject": r["subject"]}
    mail = [tell(c, u, owner, req_info, f"تمت إعادة النموذج للتعديل: {reason}")] if owner else []
    c.close()
    return jsonify(ok=True, status=STATUS_RETURNED, mail=mail)


@app.post("/api/requests/<int:i>/approve")
@login_required
def api_approve(u, i):
    comment = ((request.get_json(silent=True) or {}).get("comment") or "").strip()
    c = db()
    try:
        c.execute("BEGIN IMMEDIATE")
        r = load_req(c, i)
        if not r or not perms(u, r)["can_approve"]:
            c.execute("ROLLBACK")
            c.close()
            return jsonify(error="غير مسموح أو تم البت في الطلب"), 403
        now = datetime.datetime.now().isoformat(timespec="seconds")
        st = r["status"]

        if u["role"] == "admin":
            if st == STATUS_PENDING_AH:
                step_to_sign, nxt = "ah", STATUS_PENDING_CM
            elif st == STATUS_PENDING_CM:
                step_to_sign, nxt = "cm", STATUS_PENDING_PM
            else:
                step_to_sign, nxt = "pm", STATUS_APPROVED
        else:
            is_ah = is_ahmed_alhanafi_user(u) or (u.get("step") == "ah")
            if st == STATUS_PENDING_AH and is_ah:
                step_to_sign, nxt = "ah", STATUS_PENDING_CM
            elif st == STATUS_PENDING_CM and u.get("step") == "cm":
                step_to_sign, nxt = "cm", STATUS_PENDING_PM
            else:
                step_to_sign, nxt = "pm", STATUS_APPROVED

        c.execute("INSERT INTO approvals(request_id,step,user_id,decision,comment,signed_at,signature) VALUES(?,?,?,?,?,?,?)",
                  (i, step_to_sign, u["id"], "approved", comment, now, u.get("signature") or ""))
        c.execute("UPDATE requests SET status=? WHERE id=?", (nxt, i))
        c.execute("COMMIT")
    except Exception as e:
        try:
            c.execute("ROLLBACK")
        except Exception:
            pass
        c.close()
        return jsonify(error=str(e)), 500

    req = {"id": i, "number": r["number"], "subject": r["subject"]}
    mail = []
    if nxt == STATUS_PENDING_CM:
        cm = step_user(c, "cm")
        if cm:
            mail.append(tell(c, u, cm, req, f"اعتمده {u['name']} - بانتظار توقيعك (مدير الإنشاءات)"))
    elif nxt == STATUS_PENDING_PM:
        pm = step_user(c, "pm")
        if pm:
            mail.append(tell(c, u, pm, req, "اعتمدها مدير الإنشاءات - بانتظار توقيعك"))
    else:
        pdf_path = None
        try:
            r_updated = load_req(c, i)
            pdf_path = generate_pdf_for_request(c, r_updated)
            nxt = STATUS_DONE
        except Exception as e:
            app.logger.warning("Auto PDF on approval failed: %s", e)

        owner = get_user(c, r["created_by"])
        if owner:
            mail.append(tell(c, u, owner, req, "اكتمل اعتماد مستندك وتم إرفاق نسخة PDF الرسمية", attachment_path=pdf_path))
    c.close()
    return jsonify(ok=True, status=nxt, mail=mail)


@app.post("/api/requests/<int:i>/reject")
@login_required
def api_reject(u, i):
    reason = ((request.get_json(silent=True) or {}).get("reason") or "").strip()
    if not reason:
        return jsonify(error="اكتب سبب الرفض"), 400
    c = db()
    r = load_req(c, i)
    if not r or not perms(u, r)["can_approve"]:
        c.close()
        return jsonify(error="غير مسموح"), 403
    now = datetime.datetime.now().isoformat(timespec="seconds")
    if u["role"] == "admin":
        step_to_sign = "ah" if r["status"] == STATUS_PENDING_AH else ("cm" if r["status"] == STATUS_PENDING_CM else "pm")
    else:
        step_to_sign = "ah" if (is_ahmed_alhanafi_user(u) or u.get("step") == "ah") else u["step"]
    c.execute("INSERT INTO approvals(request_id,step,user_id,decision,comment,signed_at,signature) VALUES(?,?,?,?,?,?,'')",
              (i, step_to_sign, u["id"], "rejected", reason, now))
    c.execute("UPDATE requests SET status=?,reject_reason=? WHERE id=?", (STATUS_REJECTED, reason, i))
    owner = get_user(c, r["created_by"])
    req = {"id": i, "number": r["number"], "subject": r["subject"]}
    mail = [tell(c, u, owner, req, f"تم رفض الطلب (يمكنك تعديله وإعادة إرساله): {reason}")] if owner else []
    c.close()
    return jsonify(ok=True, mail=mail)


@app.post("/api/requests/<int:i>/pdf")
@login_required
def api_pdf_make(u, i):
    c = db()
    try:
        r = load_req(c, i)
        if not r or not perms(u, r)["can_pdf"]:
            c.close()
            return jsonify(error="الطلب غير جاهز أو غير مسموح لإدارتك"), 403
        generate_pdf_for_request(c, r)
        c.close()
        return jsonify(ok=True)
    except Exception as e:
        c.close()
        return jsonify(error=f"فشل إنشاء الملف: {e}"), 500


@app.post("/api/requests/<int:i>/email")
@login_required
def api_email_document(u, i):
    d = request.get_json(silent=True) or {}
    target_email = (d.get("email") or "").strip()
    c = db()
    r = load_req(c, i)
    if not r or not perms(u, r)["can_email"]:
        c.close()
        return jsonify(error="المستند غير معتمد بعد أو غير مسموح"), 403

    pdf_path = r.get("pdf_path")
    if not pdf_path or not Path(pdf_path).exists():
        try:
            pdf_path = generate_pdf_for_request(c, r)
        except Exception as e:
            c.close()
            return jsonify(error=f"تعذر توليد ملف PDF للإرسال: {e}"), 500

    owner = get_user(c, r["created_by"]) or {"id": r["created_by"], "name": r["created_by"], "email": ""}
    recipient_user = dict(owner)
    if target_email:
        recipient_user["email"] = target_email

    if not recipient_user.get("email"):
        c.close()
        return jsonify(error="يرجى إدخال البريد الإلكتروني للمستلم"), 400

    body = (
        f"مرفق لكم النسخة الرسمية المعتمدة من المستند:\n\n"
        f"المشروع: Al AWAEL Tower Project\n"
        f"رقم المستند: {r['number']}\n"
        f"النوع: {r.get('doc_type', 'SOR')}\n"
        f"الموضوع: {r['subject']}\n"
        f"التاريخ: {r['doc_date']}\n"
        f"مرسل بواسطة: {u['name']} ({u['title']})\n"
    )
    status = send_mail(u, recipient_user, f"مستند معتمد: {r['number']} - {r['subject']}", body, attachment_path=pdf_path)
    c.close()
    if status.startswith("failed") or status.startswith("skipped"):
        return jsonify(error=status), 400
    return jsonify(ok=True, status=status, sent_to=recipient_user["email"])


@app.get("/api/pdf/<int:i>")
@login_required
def api_pdf(u, i):
    c = db()
    r = load_req(c, i)
    if not r or not perms(u, r)["can_preview"]:
        c.close()
        abort(404)
    inline = request.args.get("inline") == "1"
    if r.get("pdf_path") and Path(r["pdf_path"]).exists():
        p_path = r["pdf_path"]
        c.close()
        return send_file(p_path, mimetype="application/pdf", as_attachment=not inline,
                         download_name=Path(p_path).name)
    # إذا لم يكن ملف PDF قد أُنشئ بعد، يتم توليد نسخة معاينة فورية
    dtype = r.get("doc_type") or "SOR"
    html = render_request_html(c, r, include_pending=True, include_status_banner=False)
    c.close()
    pdf_bytes = to_pdf(html, dtype)
    fname = re.sub(r"[^A-Za-z0-9_-]+", "-", r["number"]).strip("-") + ".pdf"
    return send_file(BytesIO(pdf_bytes), mimetype="application/pdf", as_attachment=not inline, download_name=fname)


@app.post("/api/requests/<int:i>/cancel")
@login_required
def api_cancel(u, i):
    reason = ((request.get_json(silent=True) or {}).get("reason") or "").strip()
    c = db()
    r = load_req(c, i)
    if not r or not perms(u, r)["can_cancel"]:
        c.close()
        return jsonify(error="غير مسموح"), 403
    dst = r["pdf_path"]
    if r["pdf_path"]:
        src = Path(r["pdf_path"])
        d2 = PDF_DIR / "_cancelled" / src.name
        d2.parent.mkdir(parents=True, exist_ok=True)
        if src.exists():
            shutil.move(str(src), str(d2))
        dst = str(d2)
    c.execute("UPDATE requests SET status=?,cancelled_at=?,cancel_reason=?,pdf_path=? WHERE id=?",
              (STATUS_CANCELLED, datetime.datetime.now().isoformat(timespec="seconds"), reason, dst, i))
    c.close()
    return jsonify(ok=True)


# ------------------------------------------------------------------ Shared Documents Hub (بند مستندات)
def can_upload_initial_shared_doc(u):
    return (u["id"] in ("admin", "mamdouh")) or (u["role"] == "admin") or (u.get("step") == "pm")


@app.get("/api/shared-docs")
@login_required
def api_shared_docs_list(u):
    c = db()
    docs = [dict(r) for r in c.execute("""
        SELECT s.*,
               u1.avatar AS uploader_avatar,
               u2.avatar AS modifier_avatar
        FROM shared_docs s
        LEFT JOIN users u1 ON u1.id = s.uploaded_by_id
        LEFT JOIN users u2 ON u2.id = s.last_modified_by_id
        ORDER BY s.id DESC
    """).fetchall()]
    for d in docs:
        d["comments_count"] = c.execute("SELECT COUNT(*) FROM shared_doc_history WHERE doc_id=?", (d["id"],)).fetchone()[0]
        d["can_delete"] = (u["role"] == "admin") or (u["id"] == d["uploaded_by_id"])
    c.close()
    return jsonify(docs)


@app.post("/api/shared-docs")
@login_required
def api_shared_docs_upload(u):
    if not can_upload_initial_shared_doc(u):
        return jsonify(error="رفع المستندات الجديدة متاح فقط لمدير المشروع (Mamdouh Abouzaid) ومدير النظام (admin)"), 403

    title = (request.form.get("title") or "").strip()
    description = (request.form.get("description") or "").strip()
    target_user_id = (request.form.get("target_user_id") or "").strip()
    f = request.files.get("file")
    if not f or not f.filename:
        return jsonify(error="يرجى اختيار ملف للرفع"), 400

    ext = Path(f.filename).suffix.lower()
    if ext not in ALLOWED_SHARED_EXT:
        return jsonify(error="نوع الملف غير مدعوم. المسموح: الصور، PDF، Word، Excel"), 400

    if not title:
        title = Path(f.filename).stem

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_orig = secure_filename(f.filename) or f"file{ext}"
    stored_name = f"doc_{stamp}_v1_{safe_orig}"
    f.save(SHARED_DIR / stored_name)

    category = ALLOWED_SHARED_EXT[ext]
    c = db()
    cur_ = c.execute(
        """INSERT INTO shared_docs(
             title, description, category, original_name, stored_name, file_ext, version,
             uploaded_by_id, uploaded_by_name, uploaded_at,
             last_modified_by_id, last_modified_by_name, last_modified_by_title, last_modified_at
           ) VALUES(?,?,?,?,?,?,1,?,?,?,?,?,?,?)""",
        (title, description, category, f.filename, stored_name, ext,
         u["id"], u["name"], now, u["id"], u["name"], u["title"], now)
    )
    doc_id = cur_.lastrowid
    c.execute(
        """INSERT INTO shared_doc_history(doc_id, action_type, user_id, user_name, user_title, comment, version, stored_name, created_at)
           VALUES(?,?,?,?,?,?,?,?,?)""",
        (doc_id, "upload", u["id"], u["name"], u["title"], description or "تم رفع النسخة الأساسية للمستند", 1, stored_name, now)
    )
    notified = notify_users_on_post(c, u, doc_id, title, target_user_id=target_user_id, custom_note=description)
    c.close()
    return jsonify(ok=True, id=doc_id, notified=notified)


@app.delete("/api/shared-docs/<int:doc_id>")
@login_required
def api_shared_docs_delete(u, doc_id):
    c = db()
    doc = c.execute("SELECT * FROM shared_docs WHERE id=?", (doc_id,)).fetchone()
    if not doc:
        c.close()
        return jsonify(error="المنشور غير موجود"), 404
    if u["role"] != "admin" and u["id"] != doc["uploaded_by_id"]:
        c.close()
        return jsonify(error="غير مسموح: فقط ناشر المنشور أو مدير النظام (admin) يمكنه إزالته"), 403

    hist_files = c.execute("SELECT stored_name FROM shared_doc_history WHERE doc_id=?", (doc_id,)).fetchall()
    for hf in hist_files:
        if hf["stored_name"]:
            p = SHARED_DIR / hf["stored_name"]
            if p.exists():
                try:
                    p.unlink()
                except Exception:
                    pass
    if doc["stored_name"]:
        p = SHARED_DIR / doc["stored_name"]
        if p.exists():
            try:
                p.unlink()
            except Exception:
                pass

    c.execute("DELETE FROM shared_doc_history WHERE doc_id=?", (doc_id,))
    c.execute("DELETE FROM notifications WHERE request_id=?", (-int(doc_id),))
    c.execute("DELETE FROM shared_docs WHERE id=?", (doc_id,))
    c.close()
    return jsonify(ok=True)


@app.post("/api/shared-docs/<int:doc_id>/modify")
@login_required
def api_shared_docs_modify(u, doc_id):
    comment = (request.form.get("comment") or "").strip()
    target_user_id = (request.form.get("target_user_id") or "").strip()
    f = request.files.get("file")

    c = db()
    doc = c.execute("SELECT * FROM shared_docs WHERE id=?", (doc_id,)).fetchone()
    if not doc:
        c.close()
        return jsonify(error="المستند غير موجود"), 404

    if not f and not comment:
        c.close()
        return jsonify(error="يرجى إرفاق الملف المعدل أو كتابة تعليق"), 400

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    new_ver = doc["version"]
    stored_name = doc["stored_name"]
    orig_name = doc["original_name"]
    ext = doc["file_ext"]
    category = doc["category"]
    action_type = "comment"

    if f and f.filename:
        ext = Path(f.filename).suffix.lower()
        if ext not in ALLOWED_SHARED_EXT:
            c.close()
            return jsonify(error="امتداد الملف المعدل غير مدعوم"), 400
        new_ver = doc["version"] + 1
        stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_orig = secure_filename(f.filename) or f"file{ext}"
        stored_name = f"doc_{doc_id}_{stamp}_v{new_ver}_{safe_orig}"
        f.save(SHARED_DIR / stored_name)
        orig_name = f.filename
        category = ALLOWED_SHARED_EXT[ext]
        action_type = "modify"
        c.execute(
            """UPDATE shared_docs
               SET original_name=?, stored_name=?, file_ext=?, category=?, version=?,
                   last_modified_by_id=?, last_modified_by_name=?, last_modified_by_title=?, last_modified_at=?
               WHERE id=?""",
            (orig_name, stored_name, ext, category, new_ver, u["id"], u["name"], u["title"], now, doc_id)
        )
    else:
        c.execute(
            """UPDATE shared_docs
               SET last_modified_by_id=?, last_modified_by_name=?, last_modified_by_title=?, last_modified_at=?
               WHERE id=?""",
            (u["id"], u["name"], u["title"], now, doc_id)
        )

    log_comment = comment or f"قام برفع نسخة معدلة من الملف (الإصدار v{new_ver})"
    c.execute(
        """INSERT INTO shared_doc_history(doc_id, action_type, user_id, user_name, user_title, comment, version, stored_name, created_at)
           VALUES(?,?,?,?,?,?,?,?,?)""",
        (doc_id, action_type, u["id"], u["name"], u["title"], log_comment, new_ver, stored_name, now)
    )

    if target_user_id:
        msg = f"🎯 إشعار موجه لك من {u['name']} على منشور «{doc['title']}»: {log_comment}"
        c.execute("INSERT INTO notifications(user_id,request_id,message,created_at,is_read) VALUES(?,?,?,?,0)",
                  (target_user_id, -int(doc_id), msg, now))
    elif doc["uploaded_by_id"] and doc["uploaded_by_id"] != u["id"]:
        msg = f"💬 تحديث على منشورك «{doc['title']}» بواسطة {u['name']}: {log_comment}"
        c.execute("INSERT INTO notifications(user_id,request_id,message,created_at,is_read) VALUES(?,?,?,?,0)",
                  (doc["uploaded_by_id"], -int(doc_id), msg, now))

    c.close()
    return jsonify(ok=True, version=new_ver)


@app.get("/api/shared-docs/<int:doc_id>/history")
@login_required
def api_shared_docs_history(u, doc_id):
    c = db()
    doc = c.execute("SELECT * FROM shared_docs WHERE id=?", (doc_id,)).fetchone()
    if not doc:
        c.close()
        abort(404)
    rows = [dict(r) for r in c.execute("""
        SELECT h.*, u.avatar AS user_avatar
        FROM shared_doc_history h
        LEFT JOIN users u ON u.id = h.user_id
        WHERE h.doc_id=? ORDER BY h.id DESC
    """, (doc_id,)).fetchall()]
    c.close()
    return jsonify(doc=dict(doc), history=rows)


@app.get("/api/shared-docs/file/<filename>")
@login_required
def api_shared_docs_file(u, filename):
    safe = Path(filename).name
    p = SHARED_DIR / safe
    if not p.exists():
        abort(404)
    inline = request.args.get("inline") == "1"
    return send_file(p, as_attachment=not inline, download_name=safe)


# ------------------------------------------------------------------ Admin Control Panel APIs
@app.post("/api/admin/center-logo")
@admin_required
def api_admin_center_logo(u):
    """Allows admin to set or update the top-center dashboard logo."""
    d = request.get_json(force=True)
    logo_data = d.get("logo") or ""
    if logo_data.startswith("data:image/"):
        CUSTOM_LOGO_PATH.write_text(logo_data, encoding="utf-8")
    elif d.get("reset"):
        if CUSTOM_LOGO_PATH.exists():
            CUSTOM_LOGO_PATH.unlink()
    return jsonify(ok=True, center_logo=get_center_logo())


@app.post("/api/admin/counters")
@admin_required
def api_admin_counters(u):
    d = request.get_json(force=True)
    dtype = d.get("doc_type", "ALL")
    sec = d.get("section", "ALL")
    val = max(0, int(d.get("value", 0)))

    types_list = list(DOC_TYPES.keys()) if dtype == "ALL" else [dtype]
    secs_list = list(SECTIONS.keys()) if sec == "ALL" else [sec]

    c = db()
    for dt in types_list:
        if dt not in DOC_TYPES:
            continue
        c.execute("INSERT INTO counters(key,last) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET last=excluded.last",
                  (ckey(dt, ""), val))
        for sc in secs_list:
            c.execute("INSERT INTO counters(key,last) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET last=excluded.last",
                      (ckey(dt, sc), val))
            c.execute("INSERT INTO counters(key,last) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET last=excluded.last",
                      (f"{dt}:{sc}", val))
    c.close()
    return jsonify(ok=True, counters=state("ALL"))


@app.get("/api/admin/templates/<dtype>")
@admin_required
def api_admin_get_template(u, dtype):
    if dtype not in TPL_FILES:
        abort(400)
    p = TPL_DIR / TPL_FILES[dtype]
    html = p.read_text(encoding="utf-8") if p.exists() else DEFAULT_TEMPLATES[dtype]
    return jsonify(doc_type=dtype, html=html)


@app.post("/api/admin/templates/<dtype>")
@admin_required
def api_admin_save_template(u, dtype):
    if dtype not in TPL_FILES:
        abort(400)
    d = request.get_json(force=True)
    if d.get("reset_default"):
        html = DEFAULT_TEMPLATES[dtype]
    else:
        html = d.get("html") or ""
        if not html.strip():
            return jsonify(error="كود القالب فارغ"), 400
    p = TPL_DIR / TPL_FILES[dtype]
    p.write_text(html, encoding="utf-8")
    return jsonify(ok=True, html=html)


@app.get("/api/admin/users")
@admin_required
def api_admin_list_users(u):
    c = db()
    rows = [dict(r) for r in c.execute(
        "SELECT id,name,title,role,step,section,email,avatar,extra_approver_id FROM users ORDER BY role, id"
    ).fetchall()]
    c.close()
    return jsonify(users=rows, sections=list(SECTIONS.values()))


@app.post("/api/admin/users")
@admin_required
def api_admin_add_user(u):
    d = request.get_json(force=True)
    uid = (d.get("id") or "").strip()
    name = (d.get("name") or "").strip()
    title = (d.get("title") or "").strip()
    role = (d.get("role") or "engineer").strip()
    step = (d.get("step") or "").strip()
    sec_code = (d.get("section") or "ADM").strip().upper()
    sec_name = (d.get("section_name") or title or sec_code).strip()
    prefix = (d.get("prefix") or "ENG.").strip()
    email = (d.get("email") or "").strip()
    pw = (d.get("password") or "").strip()
    if d.get("reset_password"):
        pw = DEFAULT_RESET_PASSWORD
    avatar = d.get("avatar") or ""
    extra_approver_id = (d.get("extra_approver_id") or "").strip()

    if not uid or not name or not title:
        return jsonify(error="يرجى إدخال معرف المستخدم، الاسم، والمسمى الوظيفي"), 400

    if sec_code not in SECTIONS:
        new_sec = {
            "code": sec_code,
            "name": sec_name,
            "title": title,
            "engineer": name,
            "prefix": prefix,
            "email": email
        }
        SECTIONS[sec_code] = new_sec
        CFG.setdefault("sections", []).append(new_sec)
        CFG_PATH.write_text(json.dumps(CFG, ensure_ascii=False, indent=2), encoding="utf-8")

    c = db()
    if is_ahmed_maher_user(uid, name) and not extra_approver_id:
        ah_u = find_alhanafi_user(c)
        if ah_u:
            extra_approver_id = ah_u["id"]
    if is_ahmed_alhanafi_user(uid, name) and not step:
        step = "ah"

    exists = c.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    if exists:
        new_pw_hash = generate_password_hash(pw) if pw else exists["pw_hash"]
        new_avatar = avatar if avatar.startswith("data:image/") else (exists["avatar"] or "")
        ext_app = extra_approver_id if "extra_approver_id" in d or extra_approver_id else (exists["extra_approver_id"] or "")
        c.execute(
            "UPDATE users SET name=?,title=?,role=?,step=?,section=?,email=?,pw_hash=?,avatar=?,extra_approver_id=? WHERE id=?",
            (name, title, role, step, sec_code, email, new_pw_hash, new_avatar, ext_app, uid)
        )
    else:
        init_pw = pw or DEFAULT_RESET_PASSWORD
        new_avatar = avatar if avatar.startswith("data:image/") else ""
        c.execute(
            "INSERT INTO users(id,name,title,role,step,section,email,pw_hash,avatar,extra_approver_id) VALUES(?,?,?,?,?,?,?,?,?,?)",
            (uid, name, title, role, step, sec_code, email, generate_password_hash(init_pw), new_avatar, extra_approver_id)
        )
    c.close()
    return jsonify(ok=True)


@app.post("/api/admin/users/<uid>/reset-password")
@admin_required
def api_admin_reset_user_password(u, uid):
    """التعديل 5: إعادة كلمة السر الخاصة بمستخدم محدد إلى الوضع الافتراضي 1234."""
    c = db()
    target = c.execute("SELECT id, name FROM users WHERE id=?", (uid,)).fetchone()
    if not target:
        c.close()
        return jsonify(error="المستخدم غير موجود"), 404
    c.execute("UPDATE users SET pw_hash=? WHERE id=?", (generate_password_hash(DEFAULT_RESET_PASSWORD), uid))
    c.close()
    return jsonify(ok=True, user_id=uid, default_password=DEFAULT_RESET_PASSWORD,
                   message=f"تمت إعادة كلمة مرور ({target['name']}) إلى الوضع الافتراضي {DEFAULT_RESET_PASSWORD}")


@app.post("/api/admin/users/reset-all-passwords")
@admin_required
def api_admin_reset_all_passwords(u):
    """التعديل 5: إعادة كلمات السر لجميع المستخدمين إلى الوضع الافتراضي 1234."""
    d = request.get_json(silent=True) or {}
    include_admin = bool(d.get("include_admin", False))
    c = db()
    pw_hash = generate_password_hash(DEFAULT_RESET_PASSWORD)
    if include_admin:
        cur_ = c.execute("UPDATE users SET pw_hash=?", (pw_hash,))
    else:
        cur_ = c.execute("UPDATE users SET pw_hash=? WHERE id != 'admin'", (pw_hash,))
    count = cur_.rowcount
    c.close()
    return jsonify(ok=True, reset_count=count, default_password=DEFAULT_RESET_PASSWORD,
                   message=f"تمت إعادة كلمات المرور لـ ({count}) مستخدم إلى الوضع الافتراضي {DEFAULT_RESET_PASSWORD}")


@app.delete("/api/admin/users/<uid>")
@admin_required
def api_admin_delete_user(u, uid):
    if uid == "admin":
        return jsonify(error="لا يمكن حذف حساب مدير النظام الرئيسي"), 400
    c = db()
    c.execute("DELETE FROM users WHERE id=?", (uid,))
    c.close()
    return jsonify(ok=True)


# ------------------------------------------------------------------ Auto-Injected Frontend Enhancements
FRONTEND_ENHANCEMENTS_SNIPPET = r"""
<style>
  .sor-ext-btn {
    display: inline-flex; align-items: center; gap: 4px;
    padding: 4px 9px; margin: 2px; border-radius: 6px; border: 1px solid transparent;
    font-size: 11.5px; font-weight: 600; cursor: pointer; transition: 0.15s;
    font-family: inherit;
  }
  .sor-ext-preview { background: #eff6ff; color: #1d4ed8; border-color: #bfdbfe; }
  .sor-ext-preview:hover { background: #dbeafe; }
  .sor-ext-return { background: #fff7ed; color: #c2410c; border-color: #fed7aa; }
  .sor-ext-return:hover { background: #ffedd5; }
  .sor-ext-edit { background: #f0fdf4; color: #15803d; border-color: #bbf7d0; }
  .sor-ext-edit:hover { background: #dcfce7; }
  .sor-ext-resetpw { background: #fef3c7; color: #92400e; border-color: #fde68a; }
  .sor-ext-resetpw:hover { background: #fde68a; }
  .sor-ext-modal-backdrop {
    position: fixed; inset: 0; background: rgba(15, 23, 42, 0.65);
    display: flex; align-items: center; justify-content: center;
    z-index: 99999; padding: 16px; direction: rtl;
  }
  .sor-ext-modal {
    background: #fff; color: #0f172a; border-radius: 12px; width: 100%; max-width: 960px;
    max-height: 92vh; display: flex; flex-direction: column;
    box-shadow: 0 20px 45px rgba(0,0,0,0.3); overflow: hidden;
  }
  .sor-ext-modal-head {
    padding: 12px 18px; background: #1e3a8a; color: #fff;
    display: flex; justify-content: space-between; align-items: center; font-weight: bold;
  }
  .sor-ext-modal-body { padding: 16px; overflow-y: auto; flex: 1; }
  .sor-ext-modal-foot {
    padding: 10px 18px; background: #f8fafc; border-top: 1px solid #e2e8f0;
    display: flex; justify-content: flex-end; gap: 8px; flex-wrap: wrap;
  }
  .sor-ext-field { margin-bottom: 12px; }
  .sor-ext-field label { display: block; font-weight: 600; font-size: 12.5px; margin-bottom: 4px; color: #334155; }
  .sor-ext-field input, .sor-ext-field textarea, .sor-ext-field select {
    width: 100%; padding: 8px 10px; border: 1px solid #cbd5e1; border-radius: 6px;
    font-family: inherit; font-size: 13px; box-sizing: border-box;
  }
</style>
<script>
(function(){
  window.__sorReqsMap = {};
  window.__sorCurrentUser = null;
  window.__sorUsersList = [];

  const origFetch = window.fetch;
  window.fetch = async function(...args) {
    const res = await origFetch.apply(this, args);
    try {
      const url = typeof args[0] === 'string' ? args[0] : (args[0] && args[0].url) || '';
      if (url.includes('/api/me')) {
        res.clone().json().then(d => {
          if (d && d.user) {
            window.__sorCurrentUser = d.user;
            setTimeout(injectAdminFloatingResetBtn, 400);
          }
        }).catch(()=>{});
      } else if (url.includes('/api/requests') && !url.match(/\/api\/requests\/\d+/)) {
        res.clone().json().then(list => {
          if (Array.isArray(list)) {
            list.forEach(r => { window.__sorReqsMap[r.id] = r; });
            setTimeout(enhanceRequestRows, 250);
          }
        }).catch(()=>{});
      } else if (url.includes('/api/admin/users')) {
        res.clone().json().then(d => {
          if (d && Array.isArray(d.users)) {
            window.__sorUsersList = d.users;
            setTimeout(enhanceAdminUsersTable, 250);
          }
        }).catch(()=>{});
      }
    } catch(e) {}
    return res;
  };

  function closeExtModal() {
    const el = document.getElementById('sor-ext-modal-root');
    if (el) el.remove();
  }

  // 1. معاينة النموذج الصادر قبل وبعد الاعتماد
  window.sorPreviewRequest = async function(reqId) {
    try {
      const r = await fetch(`/api/requests/${reqId}/preview`);
      const d = await r.json();
      if (!r.ok || d.error) return alert(d.error || 'تعذر فتح المعاينة');
      closeExtModal();
      const wrap = document.createElement('div');
      wrap.id = 'sor-ext-modal-root';
      wrap.className = 'sor-ext-modal-backdrop';
      wrap.innerHTML = `
        <div class="sor-ext-modal">
          <div class="sor-ext-modal-head">
            <span>👁️ معاينة المستند: ${d.number} — ${d.subject || ''}</span>
            <button onclick="document.getElementById('sor-ext-modal-root').remove()" style="background:transparent;border:none;color:#fff;font-size:18px;cursor:pointer;">✕</button>
          </div>
          <div class="sor-ext-modal-body" style="background:#f1f5f9;padding:12px;">
            <iframe id="sor-ext-preview-frame" style="width:100%;height:70vh;border:1px solid #cbd5e1;background:#fff;border-radius:8px;"></iframe>
          </div>
          <div class="sor-ext-modal-foot">
            ${d.can_edit ? `<button class="sor-ext-btn sor-ext-edit" onclick="window.sorEditRequest(${reqId})">✏️ تعديل النموذج</button>` : ''}
            ${d.can_return ? `<button class="sor-ext-btn sor-ext-return" onclick="window.sorReturnRequest(${reqId})">↩️ إعادة للتعديل</button>` : ''}
            <button class="sor-ext-btn sor-ext-preview" onclick="window.open('/api/requests/${reqId}/preview-pdf', '_blank')">📄 فتح كملف PDF / طباعة</button>
            <button class="sor-ext-btn" style="background:#e2e8f0;color:#1e293b;" onclick="document.getElementById('sor-ext-modal-root').remove()">إغلاق</button>
          </div>
        </div>`;
      document.body.appendChild(wrap);
      const iframe = document.getElementById('sor-ext-preview-frame');
      iframe.contentWindow.document.open();
      iframe.contentWindow.document.write(d.html);
      iframe.contentWindow.document.close();
    } catch (e) {
      alert('حدث خطأ أثناء تحميل المعاينة');
    }
  };

  // 2. إعادة النموذج للتعديل من جهة الاعتماد أو الأدمن
  window.sorReturnRequest = async function(reqId) {
    const reason = prompt('اكتب ملاحظات التعديل لإعادة النموذج إلى المحرر:');
    if (reason === null) return;
    if (!reason.trim()) return alert('يرجى كتابة سبب/ملاحظات التعديل');
    try {
      const r = await fetch(`/api/requests/${reqId}/return`, {
        method: 'POST',
        headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({reason: reason.trim()})
      });
      const d = await r.json();
      if (!r.ok || d.error) return alert(d.error || 'تعذر إعادة النموذج');
      closeExtModal();
      alert('تمت إعادة النموذج للتعديل وإشعار محرر النموذج بنجاح');
      location.reload();
    } catch (e) {
      alert('فشل الاتصال بالخادم');
    }
  };

  // 3. نافذة تعديل النموذج وإعادة إرساله (للمحرر والأدمن)
  window.sorEditRequest = async function(reqId) {
    try {
      const r = await fetch(`/api/requests/${reqId}`);
      const d = await r.json();
      if (!r.ok || d.error) return alert(d.error || 'تعذر تحميل بيانات النموذج');
      closeExtModal();
      const p = d.payload || {};
      const dt = d.doc_type || 'SOR';
      const itemsText = (p.items || []).join('\n');
      const wrap = document.createElement('div');
      wrap.id = 'sor-ext-modal-root';
      wrap.className = 'sor-ext-modal-backdrop';
      wrap.innerHTML = `
        <div class="sor-ext-modal" style="max-width:720px;">
          <div class="sor-ext-modal-head">
            <span>✏️ تعديل النموذج: ${d.number} (${dt})</span>
            <button onclick="document.getElementById('sor-ext-modal-root').remove()" style="background:transparent;border:none;color:#fff;font-size:18px;cursor:pointer;">✕</button>
          </div>
          <div class="sor-ext-modal-body">
            ${d.reject_reason ? `<div style="background:#fff7ed;border:1px solid #fdba74;color:#9a3412;padding:10px;border-radius:6px;margin-bottom:12px;font-size:12.5px;"><strong>📌 ملاحظات جهة الاعتماد للتعديل:</strong> ${d.reject_reason}</div>` : ''}
            <div class="sor-ext-field">
              <label>الموضوع (Subject):</label>
              <input type="text" id="sor-edit-subject" value="${(d.subject || '').replace(/"/g, '&quot;')}">
            </div>
            <div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;">
              <div class="sor-ext-field">
                <label>التاريخ (Date):</label>
                <input type="date" id="sor-edit-date" value="${(d.doc_date || p.date || '').slice(0,10)}">
              </div>
              <div class="sor-ext-field">
                <label>المقاول / الجهة (Contractor):</label>
                <input type="text" id="sor-edit-contractor" value="${(p.contractor || '').replace(/"/g, '&quot;')}">
              </div>
            </div>
            <div class="sor-ext-field">
              <label>نسخة إلى (Copy To):</label>
              <input type="text" id="sor-edit-copyto" value="${(p.copy_to || '').replace(/"/g, '&quot;')}">
            </div>
            ${dt === 'NCR' ? `
              <div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;">
                <div class="sor-ext-field"><label>الموقع (Location):</label><input type="text" id="sor-edit-ncr-loc" value="${(p.ncr_location || '').replace(/"/g, '&quot;')}"></div>
                <div class="sor-ext-field"><label>المرجع (Spec Ref):</label><input type="text" id="sor-edit-ncr-spec" value="${(p.ncr_spec_ref || '').replace(/"/g, '&quot;')}"></div>
              </div>
              <div class="sor-ext-field"><label>السبب الجذري (Root Cause):</label><textarea id="sor-edit-ncr-root" rows="2">${p.ncr_root_cause || ''}</textarea></div>
              <div class="sor-ext-field"><label>الإجراء التصحيحي المطلوب (Corrective Action):</label><textarea id="sor-edit-ncr-corr" rows="2">${p.ncr_corrective_action || ''}</textarea></div>
            ` : ''}
            ${dt === 'LET' ? `
              <div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;">
                <div class="sor-ext-field"><label>المرسل إليه (To):</label><input type="text" id="sor-edit-let-rec" value="${(p.let_recipient || '').replace(/"/g, '&quot;')}"></div>
                <div class="sor-ext-field"><label>عناية (Attention):</label><input type="text" id="sor-edit-let-att" value="${(p.let_attention || '').replace(/"/g, '&quot;')}"></div>
              </div>
              <div class="sor-ext-field"><label>نص الخطاب (Letter Body):</label><textarea id="sor-edit-let-body" rows="5">${p.let_body || ''}</textarea></div>
            ` : ''}
            <div class="sor-ext-field">
              <label>البنود / الملاحظات (كل سطر يمثل بنداً مستقلاً):</label>
              <textarea id="sor-edit-items" rows="5">${itemsText}</textarea>
            </div>
          </div>
          <div class="sor-ext-modal-foot">
            <button class="sor-ext-btn sor-ext-edit" onclick="window.sorSubmitEditedRequest(${reqId}, '${dt}')">💾 حفظ التعديلات وإعادة الإرسال للاعتماد</button>
            <button class="sor-ext-btn" style="background:#e2e8f0;color:#1e293b;" onclick="document.getElementById('sor-ext-modal-root').remove()">إلغاء</button>
          </div>
        </div>`;
      document.body.appendChild(wrap);
    } catch (e) {
      alert('تعذر فتح نافذة التعديل');
    }
  };

  window.sorSubmitEditedRequest = async function(reqId, dt) {
    const itemsRaw = (document.getElementById('sor-edit-items')?.value || '').split('\n').map(s => s.trim()).filter(Boolean);
    const payload = {
      doc_type: dt,
      subject: document.getElementById('sor-edit-subject')?.value || '',
      date: document.getElementById('sor-edit-date')?.value || '',
      contractor: document.getElementById('sor-edit-contractor')?.value || '',
      copy_to: document.getElementById('sor-edit-copyto')?.value || '',
      items: itemsRaw
    };
    if (dt === 'NCR') {
      payload.ncr_location = document.getElementById('sor-edit-ncr-loc')?.value || '';
      payload.ncr_spec_ref = document.getElementById('sor-edit-ncr-spec')?.value || '';
      payload.ncr_root_cause = document.getElementById('sor-edit-ncr-root')?.value || '';
      payload.ncr_corrective_action = document.getElementById('sor-edit-ncr-corr')?.value || '';
    }
    if (dt === 'LET') {
      payload.let_recipient = document.getElementById('sor-edit-let-rec')?.value || '';
      payload.let_attention = document.getElementById('sor-edit-let-att')?.value || '';
      payload.let_body = document.getElementById('sor-edit-let-body')?.value || '';
    }
    try {
      const r = await fetch(`/api/requests/${reqId}`, {
        method: 'PUT',
        headers: {'Content-Type': 'application/json'},
        body: JSON.stringify(payload)
      });
      const d = await r.json();
      if (!r.ok || d.error) return alert(d.error || 'فشل حفظ التعديلات');
      closeExtModal();
      alert('تم حفظ التعديلات وإرسال النموذج بنجاح');
      location.reload();
    } catch (e) {
      alert('حدث خطأ أثناء حفظ التعديلات');
    }
  };

  // 4. إعادة ضبط كلمة المرور للمستخدمين إلى 1234 (خاص بالأدمن)
  window.sorResetUserPw = async function(uid, uname) {
    if (!confirm(`هل تريد إعادة كلمة السر للمستخدم (${uname || uid}) إلى الوضع الافتراضي 1234؟`)) return;
    try {
      const r = await fetch(`/api/admin/users/${encodeURIComponent(uid)}/reset-password`, {method: 'POST'});
      const d = await r.json();
      if (!r.ok || d.error) return alert(d.error || 'فشل إعادة كلمة السر');
      alert(d.message || 'تمت إعادة كلمة السر إلى 1234 بنجاح');
    } catch (e) {
      alert('تعذر الاتصال بالخادم');
    }
  };

  window.sorOpenAdminPwModal = async function() {
    try {
      const r = await fetch('/api/admin/users');
      const d = await r.json();
      if (!r.ok || !d.users) return alert(d.error || 'غير مسموح');
      closeExtModal();
      const rowsHtml = d.users.map(u => `
        <tr>
          <td style="padding:8px;border-bottom:1px solid #e2e8f0;"><strong>${u.name}</strong><br><small style="color:#64748b;">@${u.id}</small></td>
          <td style="padding:8px;border-bottom:1px solid #e2e8f0;">${u.title || ''} (${u.section || ''})</td>
          <td style="padding:8px;border-bottom:1px solid #e2e8f0;text-align:left;">
            <button class="sor-ext-btn sor-ext-resetpw" onclick="window.sorResetUserPw('${u.id}', '${(u.name||'').replace(/'/g, '')}')">🔑 استعادة إلى 1234</button>
          </td>
        </tr>
      `).join('');
      const wrap = document.createElement('div');
      wrap.id = 'sor-ext-modal-root';
      wrap.className = 'sor-ext-modal-backdrop';
      wrap.innerHTML = `
        <div class="sor-ext-modal" style="max-width:650px;">
          <div class="sor-ext-modal-head">
            <span>🔑 إدارة وإعادة كلمات المرور للوضع الافتراضي (1234)</span>
            <button onclick="document.getElementById('sor-ext-modal-root').remove()" style="background:transparent;border:none;color:#fff;font-size:18px;cursor:pointer;">✕</button>
          </div>
          <div class="sor-ext-modal-body">
            <div style="margin-bottom:12px;display:flex;justify-content:space-between;align-items:center;">
              <span>اختر مستخدماً لإعادة كلمة مروره إلى <strong>1234</strong>:</span>
              <button class="sor-ext-btn sor-ext-return" onclick="window.sorResetAllPws()">🔄 تصفير جميع المستخدمين إلى 1234</button>
            </div>
            <table style="width:100%;border-collapse:collapse;font-size:13px;">
              <thead><tr style="background:#f1f5f9;"><th style="padding:8px;text-align:right;">المستخدم</th><th style="padding:8px;text-align:right;">المسمى / القسم</th><th style="padding:8px;text-align:left;">إجراء</th></tr></thead>
              <tbody>${rowsHtml}</tbody>
            </table>
          </div>
        </div>`;
      document.body.appendChild(wrap);
    } catch (e) {
      alert('تعذر تحميل قائمة المستخدمين');
    }
  };

  window.sorResetAllPws = async function() {
    if (!confirm('هل أنت متأكد من إعادة كلمات المرور لجميع المستخدمين إلى الوضع الافتراضي 1234؟')) return;
    const r = await fetch('/api/admin/users/reset-all-passwords', {method: 'POST', headers: {'Content-Type':'application/json'}, body: '{}'});
    const d = await r.json();
    alert(d.message || 'تمت العملية بنجاح');
  };

  function injectAdminFloatingResetBtn() {
    if (!window.__sorCurrentUser || window.__sorCurrentUser.role !== 'admin') return;
    if (document.getElementById('sor-admin-pw-quickbtn')) return;
    const btn = document.createElement('button');
    btn.id = 'sor-admin-pw-quickbtn';
    btn.className = 'sor-ext-btn sor-ext-resetpw';
    btn.style.cssText = 'position:fixed;bottom:18px;left:18px;z-index:9990;padding:8px 14px;box-shadow:0 4px 12px rgba(0,0,0,0.18);font-size:12.5px;';
    btn.innerHTML = '🔑 إعادة كلمات السر (1234)';
    btn.onclick = window.sorOpenAdminPwModal;
    document.body.appendChild(btn);
  }

  function enhanceRequestRows() {
    document.querySelectorAll('tr, .request-card, .req-row').forEach(row => {
      const txt = row.innerText || '';
      if (txt.includes('pending_ah')) {
        row.innerHTML = row.innerHTML.replace(/pending_ah/g, '<span style="background:#fef3c7;color:#92400e;padding:2px 7px;border-radius:4px;font-weight:bold;">بانتظار اعتماد م. أحمد الحنفي</span>');
      }
      if (txt.includes('returned')) {
        row.innerHTML = row.innerHTML.replace(/returned/g, '<span style="background:#ffedd5;color:#c2410c;padding:2px 7px;border-radius:4px;font-weight:bold;">معاد للتعديل</span>');
      }
      if (row.dataset.sorEnhanced) return;
      for (const [idStr, reqObj] of Object.entries(window.__sorReqsMap)) {
        if (reqObj.number && txt.includes(reqObj.number)) {
          row.dataset.sorEnhanced = '1';
          const targetCell = row.querySelector('td:last-child') || row;
          const holder = document.createElement('span');
          holder.style.display = 'inline-flex';
          holder.style.flexWrap = 'wrap';
          holder.style.gap = '4px';

          if (reqObj.can_preview) {
            const bPrev = document.createElement('button');
            bPrev.className = 'sor-ext-btn sor-ext-preview';
            bPrev.innerHTML = '👁️ معاينة';
            bPrev.onclick = (e) => { e.stopPropagation(); window.sorPreviewRequest(reqObj.id); };
            holder.appendChild(bPrev);
          }
          if (reqObj.can_return) {
            const bRet = document.createElement('button');
            bRet.className = 'sor-ext-btn sor-ext-return';
            bRet.innerHTML = '↩️ إعادة للتعديل';
            bRet.onclick = (e) => { e.stopPropagation(); window.sorReturnRequest(reqObj.id); };
            holder.appendChild(bRet);
          }
          if (reqObj.can_edit) {
            const bEd = document.createElement('button');
            bEd.className = 'sor-ext-btn sor-ext-edit';
            bEd.innerHTML = '✏️ تعديل';
            bEd.onclick = (e) => { e.stopPropagation(); window.sorEditRequest(reqObj.id); };
            holder.appendChild(bEd);
          }
          targetCell.appendChild(holder);
          break;
        }
      }
    });
  }

  function enhanceAdminUsersTable() {
    if (!window.__sorUsersList || !window.__sorUsersList.length) return;
    document.querySelectorAll('tr').forEach(row => {
      if (row.dataset.sorUserPwEnhanced) return;
      const txt = row.innerText || '';
      for (const u of window.__sorUsersList) {
        if (u.id && txt.includes(u.id) && txt.includes(u.name)) {
          row.dataset.sorUserPwEnhanced = '1';
          const lastTd = row.querySelector('td:last-child');
          if (lastTd) {
            const b = document.createElement('button');
            b.className = 'sor-ext-btn sor-ext-resetpw';
            b.innerHTML = '🔑 1234';
            b.title = 'إعادة كلمة السر للوضع الافتراضي 1234';
            b.onclick = (e) => { e.stopPropagation(); window.sorResetUserPw(u.id, u.name); };
            lastTd.appendChild(b);
          }
          break;
        }
      }
    });
  }

  setInterval(() => {
    enhanceRequestRows();
    enhanceAdminUsersTable();
    injectAdminFloatingResetBtn();
  }, 1200);
})();
</script>
"""


@app.get("/")
def index():
    html = render_template("index.html", cfg=CFG, doc_types=DOC_TYPES, center_logo=get_center_logo())
    if "</body>" in html:
        html = html.replace("</body>", FRONTEND_ENHANCEMENTS_SNIPPET + "\n</body>")
    else:
        html += FRONTEND_ENHANCEMENTS_SNIPPET
    return html


if __name__ == "__main__":
    port = int(CFG.get("port", 5757))
    try:
        ip = socket.gethostbyname(socket.gethostname())
    except Exception:
        ip = "localhost"
    print(f"\n  Al AWAEL Tower Project Portal running:  http://{ip}:{port}   (local: http://localhost:{port})\n  Data folder: {DATA}\n")
    try:
        from waitress import serve
        serve(app, host="0.0.0.0", port=port, threads=8)
    except ImportError:
        app.run(host="0.0.0.0", port=port, threaded=True)