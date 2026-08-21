
from http.server import BaseHTTPRequestHandler, HTTPServer
from socketserver import ThreadingMixIn
from pathlib import Path
from urllib.parse import urlparse, parse_qs
import sqlite3, json
import psycopg
from psycopg.rows import dict_row
from datetime import date, datetime, timedelta
from decimal import Decimal
import os, time, logging
import base64, binascii, hashlib, hmac, secrets, csv, io, re, math
from threading import Lock

try:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A3, A4, landscape
    from reportlab.lib.units import mm
    from reportlab.pdfbase.pdfmetrics import stringWidth
    from reportlab.pdfgen import canvas as pdf_canvas
    from reportlab.platypus import Table, TableStyle
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

class ThreadingHTTPServer(ThreadingMixIn, HTTPServer):
    daemon_threads = True
    allow_reuse_address = True

try:
    from openai import OpenAI
except ImportError:
    OpenAI = None

BASE = Path(__file__).resolve().parent

NUT = BASE / "banco_nutrientes.db"
DIA = BASE / "diario_alimentar.db"

HOST = "0.0.0.0"
PORT = int(os.environ.get("PORT", 5000))
SESSION_COOKIE = "diario_session"
CSRF_COOKIE = "diario_csrf"
SESSION_DAYS = 30
ENVIRONMENT = os.environ.get("ENVIRONMENT", "").strip().lower()
IS_PRODUCTION = ENVIRONMENT == "production" or bool(os.environ.get("RENDER"))
SESSION_SECRET = os.environ.get("SESSION_SECRET", "")
if IS_PRODUCTION and len(SESSION_SECRET) < 32:
    raise RuntimeError("SESSION_SECRET forte é obrigatório em produção. Configure ao menos 32 caracteres aleatórios no Render.")
if not SESSION_SECRET:
    SESSION_SECRET = secrets.token_urlsafe(48)
VISION_MODEL = os.environ.get("VISION_MODEL", "gpt-4o-mini")
APP_VERSION = "V55 · Bebidas em ml + Segurança P0"
MAX_JSON_BODY = 1 * 1024 * 1024
MAX_IMAGE_BODY = 8 * 1024 * 1024
MAX_IMAGE_DECODED = 5 * 1024 * 1024
RATE_LOCK = Lock()
RATE_BUCKETS = {}
LOG = logging.getLogger("diario_alimentar")
logging.basicConfig(level=os.environ.get("LOG_LEVEL", "INFO"))

MEALS = ["Café da manhã", "Almoço", "Lanche", "Jantar", "Ceia"]
DEFAULT_GOALS = {"calorias_kcal":2300.0,"proteina_g":180.0,"carboidratos_g":220.0,"gorduras_g":70.0,"fibras_g":30.0,"sodio_mg":2000.0,"agua_ml":4000.0,"manual_override":False}

def goal_dict(row):
    data = DEFAULT_GOALS.copy()
    if row:
        data.update(dict(row))
    return data

def json_default(value):
    if isinstance(value, Decimal):
        return float(value)
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    raise TypeError(f"Tipo não serializável: {type(value).__name__}")

def validate_image_data(image_data):
    if not isinstance(image_data, str) or not image_data.startswith("data:image/"):
        raise ValueError("Imagem inválida.")
    try:
        header, encoded = image_data.split(",", 1)
        mime = header.split(";", 1)[0].lower()
        if mime not in {"data:image/jpeg", "data:image/png", "data:image/webp"}:
            raise ValueError("Use imagem JPEG, PNG ou WEBP.")
        raw = base64.b64decode(encoded, validate=True)
    except (ValueError, UnicodeError, binascii.Error):
        raise ValueError("Imagem inválida.")
    if not raw or len(raw) > MAX_IMAGE_DECODED:
        raise ValueError("A imagem deve ter no máximo 5 MB.")
    valid_magic = raw.startswith(b"\xff\xd8\xff") or raw.startswith(b"\x89PNG\r\n\x1a\n") or raw[:4] == b"RIFF" and raw[8:12] == b"WEBP"
    if not valid_magic:
        raise ValueError("O arquivo de imagem não é válido.")

def allow_request(bucket, limit, window_seconds):
    now = time.monotonic()
    with RATE_LOCK:
        entries = [stamp for stamp in RATE_BUCKETS.get(bucket, []) if now - stamp < window_seconds]
        if len(entries) >= limit:
            RATE_BUCKETS[bucket] = entries
            return False
        entries.append(now)
        RATE_BUCKETS[bucket] = entries
        return True

def public_error_message(message):
    text = str(message or "")
    safe_prefixes = (
        "Autenticação necessária", "E-mail ou senha inválidos", "Informe ", "Idade ", "Peso ",
        "Altura ", "Ritmo ", "Nome ", "Quantidade ", "As metas ", "Selecione ", "Data ",
        "Datas ", "Nutriente ", "Alimento ", "Refeição ", "Nenhum campo ", "Imagem ",
        "Use imagem ", "O arquivo ", "JSON ", "Origem ", "Sessão ", "Muitas tentativas",
        "Não foi possível", "A análise de prato requer", "A leitura por foto ainda não está configurada"
    )
    if text.startswith(safe_prefixes):
        return text
    LOG.warning("internal_error_redacted detail=%s", text)
    return "Não foi possível concluir a solicitação. Tente novamente."

def calculate_profile_goals(idade, sexo, peso_kg, altura_cm, atividade, objetivo, ritmo_kg_semana):
    if not all([idade, sexo, peso_kg, altura_cm, atividade, objetivo]):
        return None
    multipliers = {"sedentario":1.20, "leve":1.375, "moderado":1.55, "alto":1.725, "atleta":1.90}
    if sexo not in ("M", "F") or atividade not in multipliers or objetivo not in ("perder", "ganhar", "manter"):
        return None
    rate = float(ritmo_kg_semana or 0)
    if objetivo in ("perder", "ganhar") and rate <= 0:
        return None
    bmr = 10 * float(peso_kg) + 6.25 * float(altura_cm) - 5 * int(idade) + (5 if sexo == "M" else -161)
    kcal = bmr * multipliers[atividade]
    if objetivo == "perder":
        kcal -= rate * 7700 / 7
    elif objetivo == "ganhar":
        kcal += rate * 7700 / 7
    kcal = max(1200, round(kcal))
    protein = round(float(peso_kg) * (2.0 if objetivo == "ganhar" else 1.8))
    fat = max(45, round(float(peso_kg) * 0.8))
    carbs = round((kcal - protein * 4 - fat * 9) / 4)
    if carbs < 0:
        fat = max(45, int((kcal - protein * 4) // 9))
        carbs = max(0, round((kcal - protein * 4 - fat * 9) / 4))
    return {
        "calorias_kcal": float(kcal), "proteina_g": float(protein), "carboidratos_g": float(carbs),
        "gorduras_g": float(fat), "fibras_g": float(max(25, round(kcal * 14 / 1000))),
        "sodio_mg": 2000.0, "agua_ml": float(round(float(peso_kg) * 35)), "manual_override": False,
    }

NUTS = [
    ("energia_kcal", "Calorias", "kcal"),
    ("proteina_g", "Proteína", "g"),
    ("carboidrato_g", "Carboidratos", "g"),
    ("lipidios_g", "Gorduras", "g"),
    ("fibra_g", "Fibras", "g"),
    ("calcio_mg", "Cálcio", "mg"),
    ("magnesio_mg", "Magnésio", "mg"),
    ("manganes_mg", "Manganês", "mg"),
    ("fosforo_mg", "Fósforo", "mg"),
    ("ferro_mg", "Ferro", "mg"),
    ("sodio_mg", "Sódio", "mg"),
    ("potassio_mg", "Potássio", "mg"),
    ("cobre_mg", "Cobre", "mg"),
    ("zinco_mg", "Zinco", "mg"),
    ("vitamina_c_mg", "Vitamina C", "mg"),
    ("tiamina_mg", "B1", "mg"),
    ("riboflavina_mg", "B2", "mg"),
    ("niacina_mg", "B3", "mg"),
    ("piridoxina_mg", "B6", "mg"),
    ("colesterol_mg", "Colesterol", "mg")
]

def ndb():
    c=sqlite3.connect(NUT);c.row_factory=sqlite3.Row;return c
def _open_db_connection():
    database_url = os.environ.get("DATABASE_URL")

    if not database_url:
        raise RuntimeError("DATABASE_URL não configurada no ambiente.")

    class DB:
        def __init__(self):
            self.conn = psycopg.connect(
                database_url,
                row_factory=dict_row
            )

        def execute(self, sql, params=None):
            # Mantém compatibilidade com o código antigo que usa ?
            sql = sql.replace("?", "%s")
            return self.conn.execute(sql, params)

        def commit(self):
            self.conn.commit()

        def rollback(self):
            self.conn.rollback()

        def close(self):
            self.conn.close()

    return DB()

def ddb():
    """Abre uma conexão PostgreSQL limpa para uso exclusivo da requisição atual."""
    return _open_db_connection()

def init_db():
    """Aplica a estrutura legada uma vez por processo, antes de atender requisições."""
    c = _open_db_connection()
    c.execute("SELECT pg_advisory_xact_lock(?)", (46124046,))
    c.execute("""
        CREATE TABLE IF NOT EXISTS consumo(
            id BIGSERIAL PRIMARY KEY,
            data TEXT NOT NULL,
            refeicao TEXT NOT NULL,
            alimento_id INTEGER,
            alimento_nome TEXT NOT NULL,
            quantidade_g REAL NOT NULL,
            unidade TEXT NOT NULL DEFAULT 'g'
        )
    """)

    c.execute("""
        CREATE TABLE IF NOT EXISTS hidratacao(
            id BIGSERIAL PRIMARY KEY,
            data TEXT NOT NULL,
            hora TEXT NOT NULL,
            quantidade_ml REAL NOT NULL
        )
    """)

    c.execute("""
        CREATE TABLE IF NOT EXISTS metas(
            id INTEGER PRIMARY KEY CHECK(id=1),
            calorias_kcal REAL,
            proteina_g REAL,
            carboidratos_g REAL,
            gorduras_g REAL,
            fibras_g REAL,
            sodio_mg REAL,
            agua_ml REAL,
            manual_override BOOLEAN NOT NULL DEFAULT FALSE
        )
    """)

    c.execute("""
        CREATE TABLE IF NOT EXISTS perfil(
            id INTEGER PRIMARY KEY CHECK(id=1),
            nome TEXT NOT NULL DEFAULT '',
            idade INTEGER,
            sexo TEXT,
            peso_kg REAL,
            altura_cm REAL,
            atividade TEXT,
            objetivo TEXT,
            peso_meta_kg REAL,
            ritmo_kg_semana REAL
        )
    """)

    c.execute("""
        CREATE TABLE IF NOT EXISTS usuarios(
            id BIGSERIAL PRIMARY KEY,
            email TEXT NOT NULL UNIQUE,
            senha_hash TEXT NOT NULL,
            criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW()
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS sessoes(
            id BIGSERIAL PRIMARY KEY,
            usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
            token_hash TEXT NOT NULL UNIQUE,
            criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            expira_em TIMESTAMPTZ NOT NULL
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS perfis(
            usuario_id BIGINT PRIMARY KEY REFERENCES usuarios(id) ON DELETE CASCADE,
            nome TEXT NOT NULL DEFAULT '', idade INTEGER, sexo TEXT, peso_kg REAL,
            altura_cm REAL, atividade TEXT, objetivo TEXT, peso_meta_kg REAL,
            ritmo_kg_semana REAL
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS metas_usuario(
            usuario_id BIGINT PRIMARY KEY REFERENCES usuarios(id) ON DELETE CASCADE,
            calorias_kcal REAL NOT NULL DEFAULT 2300,
            proteina_g REAL NOT NULL DEFAULT 180,
            carboidratos_g REAL NOT NULL DEFAULT 220,
            gorduras_g REAL NOT NULL DEFAULT 70,
            fibras_g REAL NOT NULL DEFAULT 30,
            sodio_mg REAL NOT NULL DEFAULT 2000,
            agua_ml REAL NOT NULL DEFAULT 4000,
            manual_override BOOLEAN NOT NULL DEFAULT FALSE,
            atualizado_em TIMESTAMPTZ NOT NULL DEFAULT NOW()
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS favoritos(
            id BIGSERIAL PRIMARY KEY,
            usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
            alimento_id INTEGER NOT NULL, alimento_nome TEXT NOT NULL,
            criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            UNIQUE(usuario_id, alimento_id)
        )
    """)
    c.execute("""
        CREATE TABLE IF NOT EXISTS porcoes(
            id BIGSERIAL PRIMARY KEY,
            usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
            alimento_id INTEGER NOT NULL, alimento_nome TEXT NOT NULL,
            nome TEXT NOT NULL, quantidade_g REAL NOT NULL,
            unidade TEXT NOT NULL DEFAULT 'g',
            criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            UNIQUE(usuario_id, alimento_id, nome)
        )
    """)
    for table in ("consumo", "hidratacao"):
        exists = c.execute("""
            SELECT 1 FROM information_schema.columns
            WHERE table_name=? AND column_name='usuario_id'
        """, (table,)).fetchone()
        if not exists:
            c.execute(f"ALTER TABLE {table} ADD COLUMN usuario_id BIGINT")
    c.execute("CREATE INDEX IF NOT EXISTS idx_consumo_usuario_data ON consumo(usuario_id, data)")
    c.execute("CREATE INDEX IF NOT EXISTS idx_hidratacao_usuario_data ON hidratacao(usuario_id, data)")
    c.execute("ALTER TABLE consumo ADD COLUMN IF NOT EXISTS unidade TEXT NOT NULL DEFAULT 'g'")
    c.execute("ALTER TABLE porcoes ADD COLUMN IF NOT EXISTS unidade TEXT NOT NULL DEFAULT 'g'")
    c.execute("""
        CREATE TABLE IF NOT EXISTS alimentos_usuario(
            id BIGSERIAL PRIMARY KEY,
            usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
            nome TEXT NOT NULL,
            energia_kcal REAL, proteina_g REAL, carboidrato_g REAL,
            lipidios_g REAL, fibra_g REAL, colesterol_mg REAL,
            calcio_mg REAL, magnesio_mg REAL, fosforo_mg REAL, ferro_mg REAL,
            sodio_mg REAL, potassio_mg REAL, zinco_mg REAL, vitamina_c_mg REAL,
            porcao_valor REAL, porcao_unidade TEXT, base_calculo TEXT DEFAULT '100g',
            criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(), atualizado_em TIMESTAMPTZ NOT NULL DEFAULT NOW()
        )
    """)
    c.execute("CREATE INDEX IF NOT EXISTS idx_alimentos_usuario_nome ON alimentos_usuario(usuario_id, nome)")
    c.execute("ALTER TABLE alimentos_usuario ADD COLUMN IF NOT EXISTS origem TEXT")
    c.execute("ALTER TABLE alimentos_usuario ADD COLUMN IF NOT EXISTS confianca_ia REAL")

    prow = c.execute(
        "SELECT id FROM perfil WHERE id=1"
    ).fetchone()

    if not prow:
        c.execute(
            "INSERT INTO perfil(id,nome) VALUES(1,'')"
        )

    # Migração segura para bancos já existentes.
    pcols = [
        r["column_name"]
        for r in c.execute("""
            SELECT column_name
            FROM information_schema.columns
            WHERE table_name='perfil'
        """).fetchall()
    ]

    for col, typ in [
        ("idade", "INTEGER"),
        ("sexo", "TEXT"),
        ("peso_kg", "REAL"),
        ("altura_cm", "REAL"),
        ("atividade", "TEXT"),
        ("objetivo", "TEXT"),
        ("peso_meta_kg", "REAL"),
        ("ritmo_kg_semana", "REAL")
    ]:
        if col not in pcols:
            c.execute(
                f"ALTER TABLE perfil ADD COLUMN {col} {typ}"
            )

    # Migração para registrar quando as metas foram alteradas manualmente.
    mcols = [
        r["column_name"]
        for r in c.execute("""
            SELECT column_name
            FROM information_schema.columns
            WHERE table_name='metas'
        """).fetchall()
    ]
    if "manual_override" not in mcols:
        c.execute("ALTER TABLE metas ADD COLUMN manual_override BOOLEAN NOT NULL DEFAULT FALSE")

    row = c.execute(
        "SELECT id FROM metas WHERE id=1"
    ).fetchone()

    if not row:
        c.execute("""
            INSERT INTO metas(
                id,
                calorias_kcal,
                proteina_g,
                carboidratos_g,
                gorduras_g,
                fibras_g,
                sodio_mg,
                agua_ml
            )
            VALUES(1,2300,180,220,70,30,2000,4000)
        """)

    c.commit()
    c.close()
def _hash_password(password):
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(password.encode('utf-8'), salt=salt, n=2**14, r=8, p=1)
    return base64.urlsafe_b64encode(salt + digest).decode('ascii')

def _verify_password(password, encoded):
    try:
        raw = base64.urlsafe_b64decode(encoded.encode('ascii'))
        salt, expected = raw[:16], raw[16:]
        actual = hashlib.scrypt(password.encode('utf-8'), salt=salt, n=2**14, r=8, p=1)
        return hmac.compare_digest(actual, expected)
    except Exception:
        return False

def _token_hash(token):
    return hmac.new(SESSION_SECRET.encode('utf-8'), token.encode('utf-8'), hashlib.sha256).hexdigest()

def _csrf_for_token(token):
    return hmac.new(SESSION_SECRET.encode("utf-8"), f"csrf:{token}".encode("utf-8"), hashlib.sha256).hexdigest()

def _cookie_value(handler, name):
    raw = handler.headers.get('Cookie', '')
    for piece in raw.split(';'):
        key, _, value = piece.strip().partition('=')
        if key == name:
            return value
    return ''

def _ensure_user_records(c, user_id, migrate_legacy=False):
    legacy_profile = c.execute('SELECT * FROM perfil WHERE id=1').fetchone() if migrate_legacy else None
    legacy_goals = c.execute('SELECT * FROM metas WHERE id=1').fetchone() if migrate_legacy else None
    if migrate_legacy:
        c.execute('UPDATE consumo SET usuario_id=? WHERE usuario_id IS NULL', (user_id,))
        c.execute('UPDATE hidratacao SET usuario_id=? WHERE usuario_id IS NULL', (user_id,))
    p = legacy_profile or {}
    c.execute('''INSERT INTO perfis(usuario_id,nome,idade,sexo,peso_kg,altura_cm,atividade,objetivo,peso_meta_kg,ritmo_kg_semana)
                 VALUES(?,?,?,?,?,?,?,?,?,?) ON CONFLICT(usuario_id) DO NOTHING''',
              (user_id, p.get('nome',''), p.get('idade'), p.get('sexo'), p.get('peso_kg'),
               p.get('altura_cm'), p.get('atividade'), p.get('objetivo'), p.get('peso_meta_kg'),
               p.get('ritmo_kg_semana')))
    g = legacy_goals or {}
    c.execute('''INSERT INTO metas_usuario(usuario_id,calorias_kcal,proteina_g,carboidratos_g,gorduras_g,fibras_g,sodio_mg,agua_ml,manual_override)
                 VALUES(?,?,?,?,?,?,?,?,FALSE) ON CONFLICT(usuario_id) DO NOTHING''',
              (user_id, g.get('calorias_kcal',2300), g.get('proteina_g',180), g.get('carboidratos_g',220),
               g.get('gorduras_g',70), g.get('fibras_g',30), g.get('sodio_mg',2000), g.get('agua_ml',4000)))

def _current_user(handler):
    token = _cookie_value(handler, SESSION_COOKIE)
    if not token:
        return None
    c = ddb()
    try:
        row = c.execute('''SELECT u.id, u.email FROM sessoes s JOIN usuarios u ON u.id=s.usuario_id
                           WHERE s.token_hash=? AND s.expira_em>NOW()''', (_token_hash(token),)).fetchone()
        if not row:
            return None
        user = dict(row)
        _ensure_user_records(c, user['id'])
        c.commit()
        return user
    finally:
        c.close()

def _session_cookie(token, max_age=SESSION_DAYS*86400):
    secure = '; Secure' if IS_PRODUCTION else ''
    return f'{SESSION_COOKIE}={token}; Path=/; HttpOnly; SameSite=Lax; Max-Age={max_age}{secure}'

def calc(rows,user_id=None):
    t={x[0]:0.0 for x in NUTS};nc=ndb();pc=None
    try:
        if user_id is not None: pc=ddb()
        for r in rows:
            aid=int(r["alimento_id"])
            if aid<0 and pc:
                f=pc.execute("SELECT * FROM alimentos_usuario WHERE id=? AND usuario_id=?",(-aid,user_id)).fetchone()
            else:
                f=nc.execute("SELECT * FROM alimentos WHERE id=?",(aid,)).fetchone()
            if not f:continue
            z=float(r["quantidade_g"])/100
            for k,_,_ in NUTS:
                if k in f.keys() and f[k] is not None:t[k]+=float(f[k])*z
    finally:
        nc.close()
        if pc:pc.close()
    return t

REPORT_METRICS = (
    ("energia_kcal", "calorias_kcal", "Calorias", "kcal", "#ef4444"),
    ("proteina_g", "proteina_g", "Proteína", "g", "#8b5cf6"),
    ("carboidrato_g", "carboidratos_g", "Carboidratos", "g", "#f59e0b"),
    ("lipidios_g", "gorduras_g", "Gorduras", "g", "#ec4899"),
    ("fibra_g", "fibras_g", "Fibras", "g", "#22c55e"),
    ("sodio_mg", "sodio_mg", "Sódio", "mg", "#14b8a6"),
    ("agua_ml", "agua_ml", "Água", "L", "#0284c7"),
)

def _report_value(value, unit):
    value = float(value or 0)
    if unit == "L":
        return f"{value / 1000:.2f} L"
    if unit == "mg":
        return f"{value:,.0f} mg".replace(",", ".")
    if unit == "kcal":
        return f"{value:,.0f} kcal".replace(",", ".")
    return f"{value:.1f} g"

def report_period_data(user_id, start, end):
    try:
        d1, d2 = date.fromisoformat(start), date.fromisoformat(end)
    except Exception:
        raise ValueError("Datas inválidas para o relatório.")
    if d1 > d2:
        raise ValueError("A data inicial deve ser anterior à data final.")
    if (d2 - d1).days > 89:
        raise ValueError("O relatório permite no máximo 90 dias por vez.")
    c = ddb()
    try:
        consumed = c.execute("SELECT * FROM consumo WHERE usuario_id=? AND data>=? AND data<=? ORDER BY data,id", (user_id, start, end)).fetchall()
        water_rows = c.execute("SELECT data,COALESCE(SUM(quantidade_ml),0) AS water FROM hidratacao WHERE usuario_id=? AND data>=? AND data<=? GROUP BY data", (user_id, start, end)).fetchall()
        goals_row = c.execute("SELECT * FROM metas_usuario WHERE usuario_id=?", (user_id,)).fetchone()
        profile = c.execute("SELECT nome FROM perfis WHERE usuario_id=?", (user_id,)).fetchone()
    finally:
        c.close()
    by_day = {}
    for row in consumed:
        by_day.setdefault(str(row["data"]), []).append(row)
    water_by_day = {str(row["data"]): float(row["water"] or 0) for row in water_rows}
    goals = goal_dict(goals_row)
    rows, cursor = [], d1
    while cursor <= d2:
        day_key = cursor.isoformat()
        nutrients = calc(by_day.get(day_key, []), user_id)
        nutrients["agua_ml"] = water_by_day.get(day_key, 0.0)
        rows.append({"data": day_key, "label": cursor.strftime("%d/%m"), "values": nutrients})
        cursor += timedelta(days=1)
    return {
        "start": d1, "end": d2, "days": rows, "goals": goals,
        "name": (profile["nome"] if profile and profile["nome"] else "Pessoa usuária"),
    }

def _pdf_header(pdf, title, subtitle):
    width, height = landscape(A4)
    pdf.setFillColor(colors.HexColor("#0b1728"))
    pdf.rect(0, height - 38 * mm, width, 38 * mm, stroke=0, fill=1)
    pdf.setFillColor(colors.white)
    pdf.setFont("Helvetica-Bold", 20)
    pdf.drawString(18 * mm, height - 18 * mm, title)
    pdf.setFillColor(colors.HexColor("#b9c9d8"))
    pdf.setFont("Helvetica", 9)
    pdf.drawString(18 * mm, height - 26 * mm, subtitle)
    return width, height

def _pdf_footer(pdf, page_no):
    width, _ = landscape(A4)
    pdf.setStrokeColor(colors.HexColor("#d7e1ea"))
    pdf.line(14 * mm, 11 * mm, width - 14 * mm, 11 * mm)
    pdf.setFillColor(colors.HexColor("#64748b"))
    pdf.setFont("Helvetica", 7)
    pdf.drawString(14 * mm, 6 * mm, "Diário Alimentar · Relatório gerado a partir dos registros do período selecionado")
    pdf.drawRightString(width - 14 * mm, 6 * mm, f"Página {page_no}")

def _pdf_table(pdf, dataset, page_no):
    width, height = landscape(A4)
    header = ["Dia"] + [m[2] for m in REPORT_METRICS] + ["Atingimento"]
    daily_rows = []
    for item in dataset["days"]:
        cells = [item["label"]]
        percent_values = []
        for key, goal_key, _, unit, _ in REPORT_METRICS:
            actual, goal = item["values"].get(key, 0), dataset["goals"].get(goal_key, 0)
            cells.append(f"{_report_value(actual, unit)}\n{_report_value(goal, unit)}")
            if float(goal or 0) > 0:
                percent_values.append(float(actual or 0) / float(goal) * 100)
        cells.append(f"{sum(percent_values)/len(percent_values):.0f}%" if percent_values else "—")
        daily_rows.append(cells)
    total_cells = ["TOTAL"]
    period_days = max(1, len(dataset["days"]))
    for key, goal_key, _, unit, _ in REPORT_METRICS:
        actual = sum(float(item["values"].get(key, 0) or 0) for item in dataset["days"])
        goal = float(dataset["goals"].get(goal_key, 0) or 0) * period_days
        pct = actual / goal * 100 if goal > 0 else 0
        total_cells.append(f"{_report_value(actual, unit)}\n{_report_value(goal, unit)} · {pct:.0f}%")
    all_pct = []
    for key, goal_key, _, _, _ in REPORT_METRICS:
        goal = float(dataset["goals"].get(goal_key, 0) or 0) * period_days
        actual = sum(float(item["values"].get(key, 0) or 0) for item in dataset["days"])
        if goal > 0: all_pct.append(actual / goal * 100)
    total_cells.append(f"{sum(all_pct)/len(all_pct):.0f}%" if all_pct else "—")
    data = [header] + daily_rows + [total_cells]
    usable = width - 28 * mm
    col_widths = [15 * mm] + [((usable - 15 * mm - 19 * mm) / 7)] * 7 + [19 * mm]
    table = Table(data, colWidths=col_widths, repeatRows=1)
    table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#10243a")), ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"), ("FONTSIZE", (0, 0), (-1, 0), 7),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"), ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("FONTSIZE", (0, 1), (-1, -2), 6), ("GRID", (0, 0), (-1, -1), .25, colors.HexColor("#cbd5e1")),
        ("ROWBACKGROUNDS", (0, 1), (-1, -2), [colors.white, colors.HexColor("#f6f9fc")]),
        ("BACKGROUND", (0, -1), (-1, -1), colors.HexColor("#dbeafe")), ("FONTNAME", (0, -1), (-1, -1), "Helvetica-Bold"),
        ("FONTSIZE", (0, -1), (-1, -1), 6), ("TOPPADDING", (0, 0), (-1, -1), 4), ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
    ]))
    fragments = table.split(usable, height - 66 * mm) or [table]
    for fragment_index, fragment in enumerate(fragments):
        _pdf_header(pdf, "RESUMO DE ALIMENTAÇÃO", f"{dataset['name']} · {dataset['start'].strftime('%d/%m/%Y')} a {dataset['end'].strftime('%d/%m/%Y')}")
        pdf.setFillColor(colors.HexColor("#10243a")); pdf.setFont("Helvetica-Bold", 11)
        suffix = f" · continuação {fragment_index + 1}" if fragment_index else ""
        pdf.drawString(14 * mm, height - 46 * mm, "Consumo diário / meta diária" + suffix)
        _, table_h = fragment.wrap(usable, height - 66 * mm)
        fragment.drawOn(pdf, 14 * mm, height - 52 * mm - table_h)
        _pdf_footer(pdf, page_no)
        if fragment_index < len(fragments) - 1:
            pdf.showPage(); page_no += 1
    return page_no

def _pdf_line_chart(pdf, dataset, metric, page_no, chart_days):
    key, goal_key, label, unit, color = metric
    chart_start, chart_end = chart_days[0]["label"], chart_days[-1]["label"]
    width, height = _pdf_header(pdf, "RESUMO DE ALIMENTAÇÃO", f"Evolução diária · {label} · realizado e meta · {chart_start} a {chart_end}")
    left, right, bottom, top = 20 * mm, width - 18 * mm, 34 * mm, height - 58 * mm
    values = [float(row["values"].get(key, 0) or 0) for row in chart_days]
    goal = float(dataset["goals"].get(goal_key, 0) or 0)
    maximum = max([goal] + values + [1]) * 1.14
    pdf.setFillColor(colors.HexColor("#10243a")); pdf.setFont("Helvetica-Bold", 13); pdf.drawString(left, height - 48 * mm, label)
    pdf.setFont("Helvetica", 8); pdf.setFillColor(colors.HexColor("#64748b")); pdf.drawString(left, height - 53 * mm, "Linha contínua: realizado · Linha tracejada: meta diária")
    pdf.setStrokeColor(colors.HexColor("#cbd5e1")); pdf.setLineWidth(.5)
    for step in range(5):
        y = bottom + (top - bottom) * step / 4
        pdf.line(left, y, right, y)
        pdf.setFillColor(colors.HexColor("#64748b")); pdf.setFont("Helvetica", 6); pdf.drawRightString(left - 3 * mm, y - 2, _report_value(maximum * step / 4, unit))
    count = max(1, len(values)); span = (right - left) / max(1, count - 1)
    coords = []
    for index, value in enumerate(values):
        x = left + (index * span if count > 1 else (right - left) / 2)
        y = bottom + (value / maximum) * (top - bottom)
        coords.append((x, y))
    goal_y = bottom + (goal / maximum) * (top - bottom)
    pdf.setStrokeColor(colors.HexColor(color)); pdf.setLineWidth(2.2); pdf.setDash(5, 3); pdf.line(left, goal_y, right, goal_y); pdf.setDash()
    pdf.setStrokeColor(colors.HexColor(color)); pdf.setLineWidth(3.2)
    for first, second in zip(coords, coords[1:]): pdf.line(first[0], first[1], second[0], second[1])
    for index, (x, y) in enumerate(coords):
        pdf.setFillColor(colors.HexColor(color)); pdf.circle(x, y, 2.7, stroke=0, fill=1)
        pdf.setFont("Helvetica-Bold", 6.3); pdf.drawCentredString(x, min(top + 8, y + 7), _report_value(values[index], unit))
        pdf.setFillColor(colors.HexColor("#475569")); pdf.setFont("Helvetica", 6.0); pdf.drawCentredString(x, max(bottom - 11, goal_y - 9), f"M {_report_value(goal, unit)}")
        pdf.setFont("Helvetica", 6); pdf.drawCentredString(x, bottom - 20, chart_days[index]["label"])
    _pdf_footer(pdf, page_no)

def _pdf_accumulated_bars(pdf, dataset, page_no):
    width, height = _pdf_header(pdf, "RESUMO DE ALIMENTAÇÃO", "Acumulado do período · realizado em azul e meta em verde")
    left, right, bottom, top = 18 * mm, width - 18 * mm, 39 * mm, height - 58 * mm
    days = max(1, len(dataset["days"])); groups = len(REPORT_METRICS); group_w = (right - left) / groups
    pdf.setFillColor(colors.HexColor("#10243a")); pdf.setFont("Helvetica-Bold", 12); pdf.drawString(left, height - 48 * mm, "Acumulados do período")
    pdf.setFillColor(colors.HexColor("#64748b")); pdf.setFont("Helvetica", 8); pdf.drawString(left, height - 53 * mm, "Azul: consumo acumulado · Verde: meta acumulada · escala proporcional por objetivo")
    pdf.setStrokeColor(colors.HexColor("#cbd5e1")); pdf.line(left, bottom, right, bottom)
    for index, (key, goal_key, label, unit, _) in enumerate(REPORT_METRICS):
        actual = sum(float(row["values"].get(key, 0) or 0) for row in dataset["days"])
        goal = float(dataset["goals"].get(goal_key, 0) or 0) * days
        ratio = actual / goal * 100 if goal > 0 else 0
        scale = max(200.0, ratio, 100.0)
        x = left + index * group_w + group_w * .20; bar_w = group_w * .22
        actual_h = (top - bottom) * min(ratio, scale) / scale
        goal_h = (top - bottom) * 100 / scale
        pdf.setFillColor(colors.HexColor("#0284c7")); pdf.rect(x, bottom, bar_w, actual_h, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor("#16a34a")); pdf.rect(x + bar_w + 3, bottom, bar_w, goal_h, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor("#0f172a")); pdf.setFont("Helvetica-Bold", 6); pdf.drawCentredString(x + bar_w, bottom - 10, label)
        pdf.setFont("Helvetica", 5.6); pdf.drawCentredString(x + bar_w, bottom - 18, f"{_report_value(actual, unit)} / {_report_value(goal, unit)}")
        pdf.drawCentredString(x + bar_w, bottom - 26, f"{ratio:.0f}%")
    _pdf_footer(pdf, page_no)

def _compact_number(value, unit):
    value = float(value or 0)
    if unit == "L":
        return f"{value / 1000:.1f}"
    if value >= 1000:
        return f"{value:,.0f}".replace(",", ".")
    return f"{value:.0f}"

def _pdf_compact_chart(pdf, metric, chart_days, goals, x, y, width, height):
    key, goal_key, label, unit, color = metric
    values = [float(day["values"].get(key, 0) or 0) for day in chart_days]
    goal = float(goals.get(goal_key, 0) or 0)
    maximum = max([goal] + values + [1]) * 1.08
    pdf.setFillColor(colors.HexColor("#f8fafc")); pdf.roundRect(x, y, width, height, 3, stroke=0, fill=1)
    pdf.setStrokeColor(colors.HexColor("#dbeafe")); pdf.roundRect(x, y, width, height, 3, stroke=1, fill=0)
    pdf.setFillColor(colors.HexColor("#0f172a")); pdf.setFont("Helvetica-Bold", 5.8); pdf.drawString(x + 4, y + height - 8, label)
    pdf.setFillColor(colors.HexColor("#64748b")); pdf.setFont("Helvetica", 4.4); pdf.drawRightString(x + width - 4, y + height - 8, f"Meta {_compact_number(goal, unit)} {unit}")
    left, right, bottom, top = x + 8, x + width - 5, y + 13, y + height - 15
    pdf.setStrokeColor(colors.HexColor("#cbd5e1")); pdf.setLineWidth(.35)
    pdf.line(left, bottom, right, bottom); pdf.line(left, (top + bottom) / 2, right, (top + bottom) / 2); pdf.line(left, top, right, top)
    goal_y = bottom + (goal / maximum) * (top - bottom)
    pdf.setStrokeColor(colors.HexColor("#16a34a")); pdf.setLineWidth(1.0); pdf.setDash(2, 1); pdf.line(left, goal_y, right, goal_y); pdf.setDash()
    count = len(values); step = (right - left) / max(1, count - 1); points = []
    for index, value in enumerate(values):
        px = left + (index * step if count > 1 else (right - left) / 2); py = bottom + (value / maximum) * (top - bottom); points.append((px, py))
    pdf.setStrokeColor(colors.HexColor(color)); pdf.setLineWidth(1.65)
    for first, second in zip(points, points[1:]): pdf.line(first[0], first[1], second[0], second[1])
    show_every = 1 if count <= 10 else 2 if count <= 15 else 3
    for index, (px, py) in enumerate(points):
        pdf.setFillColor(colors.HexColor(color)); pdf.circle(px, py, 1.25, stroke=0, fill=1)
        if index % show_every == 0 or index == count - 1:
            pdf.setFont("Helvetica-Bold", 3.6); pdf.drawCentredString(px, min(top + 3, py + 3), _compact_number(values[index], unit))
            pdf.setFillColor(colors.HexColor("#64748b")); pdf.setFont("Helvetica", 3.5); pdf.drawCentredString(px, bottom - 6, chart_days[index]["label"])

def _pdf_one_page_report(pdf, dataset):
    width, height = landscape(A3)
    pdf.setFillColor(colors.HexColor("#0b1728")); pdf.rect(0, height - 25 * mm, width, 25 * mm, stroke=0, fill=1)
    pdf.setFillColor(colors.white); pdf.setFont("Helvetica-Bold", 15); pdf.drawString(12 * mm, height - 12 * mm, "RESUMO DE ALIMENTAÇÃO")
    pdf.setFillColor(colors.HexColor("#bfdbfe")); pdf.setFont("Helvetica", 6.4)
    pdf.drawString(12 * mm, height - 18 * mm, f"{dataset['name']} · {dataset['start'].strftime('%d/%m/%Y')} a {dataset['end'].strftime('%d/%m/%Y')} · consumo diário, metas e acumulados")
    header = ["Dia"] + [f"{metric[2]}\n{metric[3]}" for metric in REPORT_METRICS] + ["Média\nmeta"]
    table_rows = []
    for day in dataset["days"]:
        cells, percents = [day["label"]], []
        for key, goal_key, _, unit, _ in REPORT_METRICS:
            actual, goal = float(day["values"].get(key, 0) or 0), float(dataset["goals"].get(goal_key, 0) or 0)
            cells.append(f"{_compact_number(actual, unit)}/{_compact_number(goal, unit)}")
            if goal > 0: percents.append(actual / goal * 100)
        cells.append(f"{sum(percents)/len(percents):.0f}%" if percents else "—")
        table_rows.append(cells)
    total = ["TOTAL"]
    all_pcts, count_days = [], max(1, len(dataset["days"]))
    for key, goal_key, _, unit, _ in REPORT_METRICS:
        actual = sum(float(day["values"].get(key, 0) or 0) for day in dataset["days"])
        goal = float(dataset["goals"].get(goal_key, 0) or 0) * count_days
        pct = actual / goal * 100 if goal else 0
        total.append(f"{_compact_number(actual, unit)}/{_compact_number(goal, unit)} · {pct:.0f}%")
        if goal: all_pcts.append(pct)
    total.append(f"{sum(all_pcts)/len(all_pcts):.0f}%" if all_pcts else "—")
    usable = width - 24 * mm; column_widths = [12 * mm] + [((usable - 12 * mm - 16 * mm) / 7)] * 7 + [16 * mm]
    table = Table([header] + table_rows + [total], colWidths=column_widths)
    table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#10243a")), ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"), ("FONTSIZE", (0, 0), (-1, 0), 4.2), ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"), ("FONTSIZE", (0, 1), (-1, -2), 3.7), ("GRID", (0, 0), (-1, -1), .16, colors.HexColor("#cbd5e1")),
        ("ROWBACKGROUNDS", (0, 1), (-1, -2), [colors.white, colors.HexColor("#f8fafc")]), ("BACKGROUND", (0, -1), (-1, -1), colors.HexColor("#dbeafe")),
        ("FONTNAME", (0, -1), (-1, -1), "Helvetica-Bold"), ("FONTSIZE", (0, -1), (-1, -1), 3.8),
        ("TOPPADDING", (0, 0), (-1, -1), 1), ("BOTTOMPADDING", (0, 0), (-1, -1), 1),
    ]))
    _, table_height = table.wrap(usable, 230)
    table_y = height - 29 * mm - table_height
    table.drawOn(pdf, 12 * mm, table_y)
    chart_top = table_y - 10; chart_height = 100; chart_width = (usable - 3 * 7) / 4
    for index, metric in enumerate(REPORT_METRICS):
        row, col = divmod(index, 4)
        x = 12 * mm + col * (chart_width + 7); y = chart_top - (row + 1) * chart_height - row * 7
        _pdf_compact_chart(pdf, metric, dataset["days"], dataset["goals"], x, y, chart_width, chart_height)
    bars_top = chart_top - 2 * chart_height - 18
    bar_height = 72; pdf.setFillColor(colors.HexColor("#f8fafc")); pdf.roundRect(12 * mm, bars_top - bar_height, usable, bar_height, 3, stroke=0, fill=1)
    pdf.setStrokeColor(colors.HexColor("#dbeafe")); pdf.roundRect(12 * mm, bars_top - bar_height, usable, bar_height, 3, stroke=1, fill=0)
    pdf.setFillColor(colors.HexColor("#0f172a")); pdf.setFont("Helvetica-Bold", 5.8); pdf.drawString(12 * mm + 5, bars_top - 8, "ACUMULADOS DO PERÍODO")
    pdf.setFillColor(colors.HexColor("#0284c7")); pdf.rect(12 * mm + 88, bars_top - 10, 8, 3, stroke=0, fill=1); pdf.setFillColor(colors.HexColor("#475569")); pdf.setFont("Helvetica", 4.6); pdf.drawString(12 * mm + 99, bars_top - 9, "Realizado")
    pdf.setFillColor(colors.HexColor("#16a34a")); pdf.rect(12 * mm + 133, bars_top - 10, 8, 3, stroke=0, fill=1); pdf.setFillColor(colors.HexColor("#475569")); pdf.drawString(12 * mm + 144, bars_top - 9, "Meta")
    group_width = usable / 7
    for index, (key, goal_key, label, unit, _) in enumerate(REPORT_METRICS):
        actual = sum(float(day["values"].get(key, 0) or 0) for day in dataset["days"]); goal = float(dataset["goals"].get(goal_key, 0) or 0) * count_days
        ratio = actual / goal * 100 if goal else 0; scale = max(130, ratio, 100); base = bars_top - bar_height + 16; max_h = 38
        x = 12 * mm + index * group_width + group_width * .30; bar_w = group_width * .15
        pdf.setFillColor(colors.HexColor("#0284c7")); pdf.rect(x, base, bar_w, max_h * min(ratio, scale) / scale, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor("#16a34a")); pdf.rect(x + bar_w + 2, base, bar_w, max_h * 100 / scale, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor("#0f172a")); pdf.setFont("Helvetica-Bold", 5.4); pdf.drawCentredString(x + bar_w, base - 7, label)
        pdf.setFont("Helvetica", 4.7); pdf.drawCentredString(x + bar_w, base - 14, f"{_compact_number(actual, unit)}/{_compact_number(goal, unit)} · {ratio:.0f}%")
    pdf.setStrokeColor(colors.HexColor("#d7e1ea")); pdf.line(12 * mm, 8 * mm, width - 12 * mm, 8 * mm)
    pdf.setFillColor(colors.HexColor("#64748b")); pdf.setFont("Helvetica", 4.3); pdf.drawString(12 * mm, 4.3 * mm, "Linhas: realizado na cor do nutriente · meta tracejada verde · dados detalhados na tabela diária")


def build_food_report_pdf(user_id, start, end):
    if not REPORTLAB_AVAILABLE:
        raise RuntimeError("A geração de PDF não está disponível. Atualize as dependências do serviço.")
    dataset = report_period_data(user_id, start, end)
    output = io.BytesIO(); pdf = pdf_canvas.Canvas(output, pagesize=landscape(A3), pageCompression=1)
    _pdf_one_page_report(pdf, dataset)
    pdf.save()
    return output.getvalue()

def has_usable_energy(record):
    try:
        calories = float(record.get("energia_kcal") if isinstance(record, dict) else record["energia_kcal"])
        macros = sum(float((record.get(field) if isinstance(record, dict) else record[field]) or 0) for field in ("proteina_g", "carboidrato_g", "lipidios_g"))
        return math.isfinite(calories) and calories > 0 and math.isfinite(macros) and macros > 0
    except Exception:
        return False

def find_plate_food(name, user_id):
    query = re.sub(r"\s+", " ", str(name or "").strip())
    if not query:
        return None
    pc = ddb()
    try:
        rows = pc.execute("SELECT id,nome,energia_kcal,proteina_g,carboidrato_g,lipidios_g FROM alimentos_usuario WHERE usuario_id=? AND LOWER(nome)=LOWER(?)", (user_id, query)).fetchall()
        for row in rows:
            if has_usable_energy(row):
                return {"id": -int(row["id"]), "nome": row["nome"]}
        rows = pc.execute("SELECT id,nome,energia_kcal,proteina_g,carboidrato_g,lipidios_g FROM alimentos_usuario WHERE usuario_id=? AND LOWER(nome) LIKE LOWER(?) ORDER BY LENGTH(nome) LIMIT 8", (user_id, "%" + query + "%")).fetchall()
        for row in rows:
            if has_usable_energy(row):
                return {"id": -int(row["id"]), "nome": row["nome"]}
    finally:
        pc.close()
    nc = ndb()
    try:
        rows = nc.execute("SELECT id,nome,energia_kcal,proteina_g,carboidrato_g,lipidios_g FROM alimentos WHERE LOWER(nome)=LOWER(?)", (query,)).fetchall()
        if not rows:
            rows = nc.execute("SELECT id,nome,energia_kcal,proteina_g,carboidrato_g,lipidios_g FROM alimentos WHERE LOWER(nome) LIKE LOWER(?) ORDER BY LENGTH(nome) LIMIT 8", ("%" + query + "%",)).fetchall()
        for row in rows:
            if has_usable_energy(row):
                return {"id": int(row["id"]), "nome": row["nome"]}
        return None
    finally:
        nc.close()

ESTIMATED_NUTRIENT_FIELDS = [
    "energia_kcal", "proteina_g", "carboidrato_g", "lipidios_g", "fibra_g",
    "colesterol_mg", "calcio_mg", "magnesio_mg", "fosforo_mg", "ferro_mg",
    "sodio_mg", "potassio_mg", "zinco_mg", "vitamina_c_mg"
]

def normalize_estimated_nutrients(raw):
    if not isinstance(raw, dict):
        return None
    values = {}
    for field in ESTIMATED_NUTRIENT_FIELDS:
        try:
            value = float(raw.get(field, 0) or 0)
        except Exception:
            value = 0.0
        if not math.isfinite(value) or value < 0:
            value = 0.0
        values[field] = round(min(value, 100000), 4)
    if values["energia_kcal"] <= 0 or (values["proteina_g"] + values["carboidrato_g"] + values["lipidios_g"]) <= 0:
        return None
    return values

HTML=r"""
<!doctype html><html lang="pt-BR"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>V43 - Diário Alimentar · Base pessoal confirmada</title>
<style>
*{box-sizing:border-box}body{margin:0;color:#f8fafc;font-family:Arial,sans-serif;background:#0b1220 url("data:image/jpeg;base64,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") center/cover fixed no-repeat;}body:before{content:"";position:fixed;inset:0;background:rgba(3,10,20,.38);backdrop-filter:blur(1px);z-index:-1}
header{background:rgba(8,15,28,.78);backdrop-filter:none;color:white;padding:16px;position:sticky;top:0;z-index:5;border-bottom:1px solid #ffffff20}
header h1{margin:0;font-size:23px}header p{margin:5px 0 0;font-size:12px;opacity:.8}header .headrow{display:flex;justify-content:space-between;align-items:center;gap:10px}header .profileBtn{border:1px solid #ffffff30;background:#ffffff12;color:white;border-radius:10px;padding:9px 12px;font-weight:bold}
main{max-width:900px;margin:auto;padding:12px}.card{background:rgba(9,18,31,.78);backdrop-filter:none;color:#f8fafc;border:1px solid #ffffff18;border-radius:16px;padding:14px;margin-bottom:12px;box-shadow:0 8px 30px #0004}
h2{font-size:16px;margin:0 0 12px}.date{display:flex;gap:8px}.date input{flex:1;padding:11px;border:1px solid #ffffff30;border-radius:10px;font-size:16px;background:#ffffff10;color:white}.date button,.add button{background:#111827;color:white;border:0;border-radius:10px;padding:12px;font-weight:bold}
.meals{display:grid;grid-template-columns:1fr 1fr;gap:8px}.meals button{border:0;border-radius:12px;padding:14px 4px;background:#e5e7eb;font-weight:bold}.meals .on{background:#111827;color:white}
.search{width:100%;padding:13px;border:1px solid #ffffff30;border-radius:10px;font-size:16px;background:#ffffff10;color:white}.foods{max-height:200px;overflow:auto}.food{padding:11px;border-bottom:1px solid #ffffff15;cursor:pointer}
.add{display:flex;gap:8px;margin-top:10px}.add input{width:105px;padding:12px;border:1px solid #ffffff30;border-radius:10px;font-size:16px;background:#ffffff10;color:white}.add button{flex:1}
.sel{font-size:13px;color:#cbd5e1;margin-top:8px}.item{display:flex;justify-content:space-between;gap:8px;padding:11px 0;border-bottom:1px solid #ffffff15}.name{font-weight:bold}.info{font-size:12px;color:#cbd5e1;margin-top:3px}.act{display:flex;gap:4px}.act button{border:0;border-radius:8px;padding:7px;background:#eee}
.metrics{display:grid;grid-template-columns:1fr 1fr;gap:8px}.metric{background:rgba(255,255,255,.07);border:1px solid #ffffff12;border-radius:12px;padding:10px}.metric small{color:#cbd5e1}.metric b{display:block;font-size:18px;margin:3px 0}.empty{text-align:center;color:#cbd5e1;padding:14px}
@media(min-width:650px){.meals{grid-template-columns:repeat(5,1fr)}}@media(max-width:520px){.metrics{grid-template-columns:1fr}.card{border-radius:14px}.meals button{font-size:12px}}

/* V11 CONTRASTE DOS MODAIS */
#summaryModal input,#summaryModal select,#summaryModal textarea,
#periodModal input,#periodModal select,#periodModal textarea,
#foodModal input,#foodModal select,#foodModal textarea,
#newFoodModal input,#newFoodModal select,#newFoodModal textarea {
  background:#0b1220 !important;
  color:#f8fafc !important;
  border:1px solid #475569 !important;
  color-scheme:dark;
}
#summaryModal label,#periodModal label,#foodModal label,#newFoodModal label,
#summaryModal small,#periodModal small,#foodModal small,#newFoodModal small {
  color:#cbd5e1 !important;
}
#summaryModal .metric,#periodModal .metric,#foodModal .metric,#newFoodModal .metric {
  background:#172033 !important;
  color:#f8fafc !important;
}
#summaryModal h2,#periodModal h2,#foodModal h2,#newFoodModal h2,
#summaryModal h3,#periodModal h3,#foodModal h3,#newFoodModal h3 {
  color:#ffffff !important;
}

.card{background:rgba(15,23,42,.88)!important;border:1px solid rgba(148,163,184,.18)!important}

/* V11 visual dashboard */
body{background-attachment:fixed;background-position:center;background-size:cover}
body:before{content:"";position:fixed;inset:0;background:linear-gradient(180deg,rgba(3,8,20,.46),rgba(3,8,20,.78));pointer-events:none;z-index:-1}
main{max-width:1120px;margin:0 auto;padding:12px 18px 40px}
header{position:sticky;top:0;z-index:20;background:rgba(5,12,24,.68)!important;backdrop-filter:none;border-bottom:1px solid rgba(255,255,255,.08)}
header .headrow{max-width:1120px;margin:auto;padding:10px 18px}
header h1{display:none} header p{display:block}
.hero{background:linear-gradient(135deg,rgba(7,18,35,.91),rgba(16,31,55,.78));border:1px solid rgba(255,255,255,.13);border-radius:24px;padding:22px;margin-bottom:14px;box-shadow:0 18px 55px rgba(0,0,0,.28);backdrop-filter:blur(12px)}
.heroTop{display:flex;justify-content:space-between;align-items:flex-start;gap:15px}
.eyebrow{font-size:11px;letter-spacing:1.5px;color:#8fd8ff;font-weight:800}
.hero h1{margin:4px 0 3px;font-size:30px;color:#fff}
.heroDate{color:#cbd5e1;font-size:14px}
.heroProfile{border:1px solid rgba(255,255,255,.18);background:rgba(255,255,255,.08);color:#fff;padding:10px 14px;border-radius:12px;font-weight:800}
.quickStats{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin-top:18px}
.quickStat{display:flex;align-items:center;gap:10px;padding:13px;border-radius:15px;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.08)}
.quickStat>span{font-size:25px}.quickStat small{display:block;color:#aebdd0;font-size:11px}.quickStat strong{display:block;color:#fff;font-size:15px;margin-top:3px}
.mealPanel{background:rgba(15,23,42,.84)!important}
.sectionTitle h2{margin:4px 0 0}
.meals{display:grid!important;grid-template-columns:repeat(5,1fr);gap:9px}
.meals button,.meals .meal,.mealBtn{min-height:64px!important;border-radius:15px!important;font-weight:800!important}
.card{box-shadow:0 10px 32px rgba(0,0,0,.16)}
@media(max-width:800px){.quickStats{grid-template-columns:repeat(2,1fr)}.meals{grid-template-columns:repeat(3,1fr)!important}}
@media(max-width:520px){main{padding:10px}.hero{padding:17px}.hero h1{font-size:24px}.quickStats{grid-template-columns:1fr 1fr}.meals{grid-template-columns:repeat(2,1fr)!important}}

/* V14 - layout aprovado / contraste */
main{width:min(1400px,calc(100vw - 28px))!important;max-width:none!important;margin:0 auto!important;padding:14px 0 44px!important}
.hero,.mealPanel{width:100%!important}
.meals button{
  background:linear-gradient(135deg,rgba(18,31,49,.96),rgba(27,43,66,.92))!important;
  color:#fff!important;
  border:1px solid rgba(255,255,255,.13)!important;
  min-height:74px!important;
  font-size:14px!important;
  box-shadow:0 8px 20px rgba(0,0,0,.16);
}
.meals button:hover{background:linear-gradient(135deg,#1d4f36,#173b2b)!important}
.meals .on{background:linear-gradient(135deg,#15803d,#166534)!important;color:#fff!important}
.heroTop{align-items:center}
.quickStats{grid-template-columns:repeat(4,minmax(0,1fr))}
.card{font-size:14px}
.item .act button{background:#1e293b!important;color:#f8fafc!important;border:1px solid #475569!important}
.date button,.add button{background:linear-gradient(135deg,#15803d,#166534)!important}
.search,.add input,.date input{background:rgba(15,23,42,.78)!important;color:#fff!important}
@media(max-width:850px){main{width:calc(100vw - 20px)!important}.quickStats{grid-template-columns:repeat(2,1fr)}}
@media(max-width:520px){main{width:calc(100vw - 12px)!important}.quickStats{grid-template-columns:1fr 1fr}}

/* V20 — acabamento visual inspirado no layout aprovado */
:root{
  --bg:#07111f;
  --panel:rgba(11,24,42,.88);
  --panel2:rgba(16,31,52,.92);
  --line:rgba(148,163,184,.18);
  --muted:#9fb0c4;
  --text:#f8fafc;
  --green:#16a34a;
  --green2:#15803d;
  --blue:#2563eb;
}
html{
  min-height:100%;
  background-color:#07111f!important;
  background-image:
    linear-gradient(rgba(3,10,20,.08),rgba(3,10,20,.24)),
    url("/a_wide_high_resolution_panoramic_landscape_photo.png?v=43")!important;
  background-size:cover!important;
  background-position:center center!important;
  background-repeat:no-repeat!important;
}
body{
  min-height:100vh;
  background:transparent!important;
}
@media (max-width:768px){
  html{
    background-attachment:scroll!important;
    background-position:center top!important;
    background-size:cover!important;
  }
}
body:before{
  content:"";
  position:fixed;
  inset:0;
  background:rgba(3,10,20,.10)!important;
  pointer-events:none;
  z-index:-1;
}
body:after{
  display:none!important;
}
header{
  background:rgba(5,12,24,.58)!important;
  backdrop-filter:blur(3px)!important;
}
main{
  width:min(1180px,calc(100vw - 24px))!important;
  max-width:1180px!important;
  margin:12px auto 48px!important;
}
.hero,.mealPanel,.card{
  background:rgba(7,22,38,.48)!important;
  border:1px solid rgba(255,255,255,.18)!important;
  box-shadow:0 18px 50px rgba(0,0,0,.22)!important;
  backdrop-filter:blur(2px)!important;
}
.quickStat{
  background:rgba(16,35,57,.48)!important;
}
.mealPanel{
  background:rgba(7,22,38,.44)!important;
}
.search,.add input,.date input{
  background:rgba(7,20,35,.48)!important;
}
.item{
  background:rgba(7,20,35,.12)!important;
}
.bottomDashboard,.bottomGoal{
  background:rgba(7,22,38,.42)!important;
  border-color:rgba(255,255,255,.16)!important;
}

/* V28 — foto aprovada + vidro legível */
.hero,.mealPanel,.card{
  background:rgba(7,22,38,.68)!important;
  border:1px solid rgba(255,255,255,.18)!important;
  box-shadow:0 16px 42px rgba(0,0,0,.22)!important;
  backdrop-filter:blur(1px)!important;
}
.quickStat{
  background:rgba(14,32,52,.72)!important;
}
.meals button,.meals .meal,.mealBtn{
  background:rgba(13,31,51,.72)!important;
}
.search,.add input,.date input{
  background:rgba(7,20,35,.72)!important;
}
.item{
  background:rgba(7,20,35,.28)!important;
}
.bottomDashboard,.bottomGoal{
  background:rgba(7,22,38,.64)!important;
}

.nutrient-source{cursor:pointer;position:relative}
#nutrientTooltip{
  display:none;position:fixed;z-index:300;
  width:min(330px,calc(100vw - 24px));max-height:300px;overflow:auto;
  padding:12px 14px;border-radius:12px;
  background:rgba(6,18,31,.96);color:#fff;
  border:1px solid rgba(255,255,255,.18);
  box-shadow:0 14px 40px rgba(0,0,0,.35);
  font-size:12px;line-height:1.35;pointer-events:none;
  backdrop-filter:blur(8px);
}
#nutrientTooltip .tipTitle{font-weight:900;font-size:13px;margin-bottom:7px}
#nutrientTooltip .tipTotal{color:#8fe3a8;font-weight:800;margin-bottom:8px}
#nutrientTooltip .tipRow{
  display:flex;justify-content:space-between;gap:12px;
  padding:5px 0;border-top:1px solid rgba(255,255,255,.08)
}
#nutrientTooltip .tipFood{color:#f8fafc}
#nutrientTooltip .tipVal{color:#b9c9d8;white-space:nowrap}
#nutrientTooltip .tipEmpty{color:#aab8c7}
.quickStats{grid-template-columns:repeat(7,minmax(0,1fr))!important;gap:8px}
.quickStat{display:block!important;min-width:0;padding:10px!important}
.quickStatHead{display:flex;align-items:center;gap:5px;min-width:0}
.quickStatHead span{font-size:18px!important;line-height:1}
.quickStatHead small{overflow:visible;text-overflow:clip;white-space:normal;font-size:13px!important;font-weight:800;line-height:1.14}
.quickStat strong{font-size:11px!important;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin:7px 0 6px!important}
.quickMeter{height:6px;border-radius:99px;overflow:hidden;background:rgba(255,255,255,.18)}
.quickMeter i{display:block;height:100%;width:0;border-radius:inherit;background:linear-gradient(90deg,#38bdf8,#22c55e);transition:width .28s ease}
.quickStat.water .quickMeter i{background:linear-gradient(90deg,#38bdf8,#0ea5e9)}
.waterVisual{display:flex;align-items:center;justify-content:center;min-height:178px;margin:8px 0 5px;position:relative;overflow:hidden}
.waterFigure{display:flex;align-items:center;gap:17px;justify-content:center}
.waterArtwork{position:relative;width:116px;height:164px;flex:0 0 116px;filter:drop-shadow(0 7px 12px rgba(14,165,233,.25))}
.waterArtwork::before,.waterArtwork::after{content:"";position:absolute;inset:0;background:#718096;mask:var(--silhouette) center/contain no-repeat;-webkit-mask:var(--silhouette) center/contain no-repeat;transform:scale(1.01);filter:blur(.18px)}
.waterArtwork::after{background:linear-gradient(0deg,#0284c7,#38bdf8 78%,#7dd3fc);clip-path:inset(calc(100% - var(--water-level)) 0 0 0);transition:clip-path .35s ease}
.waterFigureText{font-size:13px;color:#cbd5e1;line-height:1.42;max-width:164px}
.waterFigureText b{display:block;color:#e0f2fe;font-size:17px;margin-bottom:3px}
.waterPercent{min-width:118px;color:#7dd3fc;font-size:32px;font-weight:900;line-height:1;text-align:center;text-shadow:0 2px 12px rgba(14,165,233,.35)}
.waterPercent small{display:block;margin-top:6px;color:#cbd5e1;font-size:10px;font-weight:700;letter-spacing:.04em;text-transform:uppercase}
.waterFirework{position:absolute;width:4px;height:4px;border-radius:50%;pointer-events:none;z-index:4;animation:waterSpark .76s ease-out forwards}
@keyframes waterSpark{from{transform:translate(0,0) scale(1);opacity:1}to{transform:translate(var(--dx),var(--dy)) scale(.25);opacity:0}}
.waterRecordsHeader{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-top:14px}
.waterRecordsToggle{padding:6px 9px;border:1px solid rgba(255,255,255,.2);border-radius:8px;background:#16263a;color:#e0f2fe;font-size:11px;font-weight:bold}
.finalDashboard{padding:0!important;overflow:hidden}
.finalDashboardGrid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr)}
.finalDashboardPane{min-width:0;padding:18px}
.historyPane{border-right:1px solid rgba(255,255,255,.16)}
.finalDashboardPane h2{margin-top:0}
.hydrationPane .waterVisual{min-height:150px;margin:4px 0}
.hydrationPane .waterArtwork{width:120px;height:170px;flex-basis:120px}
.hydrationPane .waterFigure{gap:12px}
.hydrationPane .waterPercent{min-width:108px;font-size:30px}
.waterQuickButtons{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:5px;margin-top:8px}
.waterQuickButtons button{padding:6px 3px!important;min-height:31px;border:0;border-radius:8px;background:#e5f3ff;font-size:11px;line-height:1.15}
.goalCards{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:8px;margin-top:12px}
.goalMiniCard{min-width:0;text-align:left;padding:10px;border:1px solid rgba(255,255,255,.15);border-radius:12px;background:rgba(10,29,48,.58);color:#fff;cursor:pointer}
.goalMiniCard:hover{border-color:rgba(125,211,252,.7);background:rgba(17,50,78,.78)}
.goalMiniCard small{display:block;color:#b9c9d8;font-size:10px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.goalMiniCard b{display:block;font-size:12px;margin:5px 0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.goalMiniCard i{display:block;height:5px;border-radius:99px;background:linear-gradient(90deg,#38bdf8,#22c55e)}
.goalMiniCard.limit i{background:linear-gradient(90deg,#fbbf24,#fb7185)}
@media(max-width:700px){.goalCards{grid-template-columns:repeat(2,minmax(0,1fr))!important}}
@media(max-width:1000px){.quickStats{grid-template-columns:repeat(4,minmax(0,1fr))!important}}
@media(max-width:760px){.finalDashboardGrid{grid-template-columns:1fr}.historyPane{border-right:0;border-bottom:1px solid rgba(255,255,255,.16)}.hydrationPane .waterVisual{min-height:168px}.hydrationPane .waterArtwork{width:116px;height:164px;flex-basis:116px}.hydrationPane .waterPercent{min-width:116px;font-size:31px}}
@media(max-width:520px){.quickStats{grid-template-columns:repeat(2,minmax(0,1fr))!important}.quickStat{padding:9px!important}.quickStat strong{font-size:12px!important}.quickStatHead small{font-size:13px!important}.waterVisual{min-height:170px}.waterArtwork{width:108px;height:154px;flex-basis:108px}.waterFigure{gap:12px}.waterPercent{min-width:95px;font-size:28px}.finalDashboardPane{padding:14px}.waterQuickButtons button{font-size:10px;min-height:29px}}
</style></head><body>
<div id="authScreen" style="display:flex;position:fixed;inset:0;z-index:500;background:#07111f;align-items:center;justify-content:center;padding:18px"><div style="width:min(430px,100%);background:#0b1728;color:#fff;border:1px solid #ffffff25;border-radius:18px;padding:22px;box-shadow:0 20px 70px #0009"><h1 style="margin:0 0 6px">🥗 Diário Alimentar</h1><p style="color:#b9c7d7;font-size:13px;margin:0 0 16px">Entre ou crie sua conta para manter seus dados protegidos.</p><label style="display:block;font-size:12px;font-weight:bold;margin:9px 0">E-mail<input id="authEmail" type="email" autocomplete="email" style="width:100%;padding:11px;margin-top:5px;border-radius:10px;border:1px solid #ffffff30;background:#ffffff10;color:#fff"></label><label style="display:block;font-size:12px;font-weight:bold;margin:9px 0">Senha<input id="authPassword" type="password" autocomplete="current-password" minlength="8" style="width:100%;padding:11px;margin-top:5px;border-radius:10px;border:1px solid #ffffff30;background:#ffffff10;color:#fff"></label><div id="authStatus" style="min-height:20px;color:#fca5a5;font-size:12px;margin:8px 0"></div><div style="display:flex;gap:8px"><button onclick="login()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#22c55e;color:#06210f;font-weight:bold">ENTRAR</button><button onclick="register()" style="flex:1;padding:12px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:#fff;font-weight:bold">CRIAR CONTA</button></div></div></div><header><div class="headrow"><div><h1 id="appTitle">V45 · Diário Alimentar · Segurança P0</h1><p id="greeting">Alimentação, nutrientes e histórico</p><small id="userEmail" style="color:#9fb0c4"></small></div><div style="display:flex;gap:8px"><button class="profileBtn" onclick="openProfile()">👤 Perfil</button><button class="profileBtn" onclick="logout()">Sair</button></div></div></header>
<main>
<section class="hero">
  <div class="heroTop">
    <div>
      <div class="eyebrow">V45 · DIÁRIO ALIMENTAR</div>
      <h1 id="heroGreeting">Olá! 👋</h1>
      <div id="heroDate" class="heroDate"></div>
    </div>
    <button class="heroProfile" onclick="openProfile()">👤 Perfil</button>
  </div>
  <div class="quickStats">
    <div class="quickStat"><div class="quickStatHead"><span>🔥</span><small>Calorias</small></div><strong id="heroKcal">0 / —</strong><div class="quickMeter"><i id="heroKcalFill"></i></div></div>
    <div class="quickStat"><div class="quickStatHead"><span>💪</span><small>Proteínas</small></div><strong id="heroProtein">0 / —</strong><div class="quickMeter"><i id="heroProteinFill"></i></div></div>
    <div class="quickStat"><div class="quickStatHead"><span>🍚</span><small>Carboidratos</small></div><strong id="heroCarbs">0 / —</strong><div class="quickMeter"><i id="heroCarbsFill"></i></div></div>
    <div class="quickStat"><div class="quickStatHead"><span>🥑</span><small>Gorduras</small></div><strong id="heroFat">0 / —</strong><div class="quickMeter"><i id="heroFatFill"></i></div></div>
    <div class="quickStat"><div class="quickStatHead"><span>🌱</span><small>Fibras</small></div><strong id="heroFiber">0 / —</strong><div class="quickMeter"><i id="heroFiberFill"></i></div></div>
    <div class="quickStat"><div class="quickStatHead"><span>🧂</span><small>Sódio</small></div><strong id="heroSodium">0 / —</strong><div class="quickMeter"><i id="heroSodiumFill"></i></div></div>
    <div class="quickStat water"><div class="quickStatHead"><span>💧</span><small>Água</small></div><strong id="heroWater">0 / —</strong><div class="quickMeter"><i id="heroWaterFill"></i></div></div>
  </div>
</section>

<section class="mealPanel card">
  <div class="sectionTitle"><div><span class="eyebrow">REGISTRO RÁPIDO</span><h2>🍽️ O que você vai registrar?</h2></div></div>
  <div id="meals" class="meals"></div>
</section>

<div class="card"><h2>Data</h2><div class="date"><input id="day" type="date"><button onclick="refresh()">OK</button></div></div>
<div class="card" id="platePhotoCard" style="border:1px solid #4ade8055;background:linear-gradient(135deg,#10243a,#17304a)">
  <div class="sectionTitle"><div><span class="eyebrow">REGISTRO POR FOTO</span><h2>🍽️ Fotografar prato</h2></div></div>
  <p style="margin:0 0 11px;color:#cbd5e1;font-size:13px;line-height:1.4">Escolha uma imagem ou fotografe o prato. Você confere os alimentos e as quantidades antes de adicionar ao diário.</p>
  <div style="display:grid;grid-template-columns:1fr 1fr;gap:9px">
    <label style="display:flex;align-items:center;justify-content:center;gap:8px;padding:13px 9px;border:1px solid #7dd3fc66;border-radius:12px;background:#ffffff12;color:#fff;font-weight:bold;cursor:pointer"><input id="plateGalleryInput" type="file" accept="image/*" style="display:none" onchange="onPlatePhoto(this.files[0]);this.value=''">🖼️ <span>Galeria</span></label>
    <label style="display:flex;align-items:center;justify-content:center;gap:8px;padding:13px 9px;border:1px solid #86efac66;border-radius:12px;background:#22c55e20;color:#fff;font-weight:bold;cursor:pointer"><input id="plateCameraInput" type="file" accept="image/*" capture="environment" style="display:none" onchange="onPlatePhoto(this.files[0]);this.value=''">📷 <span>Câmera</span></label>
  </div>
  <div id="platePhotoStatus" style="min-height:18px;margin-top:9px;color:#bfdbfe;font-size:12px"></div>
</div>
<div class="card"><h2>➕ Adicionar alimento</h2>
<input id="search" class="search" placeholder="Digite o nome do alimento..."><div id="foods" class="foods"></div>
<div class="add"><input id="weight" type="number" value="100" min="0.1" step="0.1"><select id="quantityUnit" aria-label="Unidade da quantidade" style="width:72px;border:1px solid #ffffff25;border-radius:10px;background:#16263a;color:#fff;font-weight:bold"><option value="g">g</option><option value="ml">ml</option></select><button onclick="add()">ADICIONAR</button></div>
<div id="sel" class="sel">Nenhum alimento selecionado.</div>
<div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:9px"><button onclick="favoriteChosen()" style="flex:1;padding:10px;border:1px solid #ffffff30;border-radius:10px;background:#16263a;color:#fff;font-weight:bold">☆ FAVORITO</button><button onclick="savePortion()" style="flex:1;padding:10px;border:1px solid #ffffff30;border-radius:10px;background:#16263a;color:#fff;font-weight:bold">💾 SALVAR PORÇÃO</button></div>
<div id="personalLists" style="margin-top:10px"></div>
<button id="newBase" style="display:none;margin-top:9px;width:100%;padding:11px;border:1px solid #111827;border-radius:10px;background:#111827;color:white;font-weight:bold" onclick="openNewFood()">NOVO ALIMENTO</button>
<button id="editBase" style="display:none;margin-top:9px;width:100%;padding:11px;border:1px solid #ddd;border-radius:10px;background:white;font-weight:bold" onclick="openFoodEditor()">EDITAR ALIMENTO DA BASE</button></div>
<div class="card" id="consumedFoodsCard">
  <h2 style="display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:0">
    <span>Alimentos consumidos</span>
    <button id="consumedFoodsToggle" onclick="toggleConsumedFoods()" aria-expanded="true"
      style="width:42px;height:34px;padding:0;border:1px solid #ffffff25;border-radius:10px;background:#111827;color:#fff;font-size:20px;line-height:1;cursor:pointer"
      title="Mostrar ou ocultar alimentos consumidos">▲</button>
  </h2>
  <div id="items" style="display:block;margin-top:12px"></div>
</div>

<div class="bottomDashboard card" id="goalsDashboard">
  <div class="sectionTitle">
    <div><span class="eyebrow">SEU OBJETIVO</span><h2>🎯 Metas do dia</h2></div>
    <button id="goalsToggle" onclick="toggleGoalsDashboard()" class="miniSummaryBtn" aria-expanded="false">VER METAS</button>
  </div>
  <div id="goalCards" class="goalCards" style="display:none"></div>
  <button onclick="openSummary()" style="width:100%;margin-top:10px;padding:10px;border:1px solid #ffffff25;border-radius:10px;background:#16263a;color:#fff;font-weight:bold">⚙️ AJUSTAR METAS</button>
</div>
<div class="card" id="accumulatedCard">
  <h2 style="display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:0">
    <span>Acumulado: <span id="pm"></span></span>
    <button id="accumulatedToggle" onclick="toggleAccumulated()" aria-expanded="false"
      style="width:42px;height:34px;padding:0;border:1px solid #ffffff25;border-radius:10px;background:#111827;color:#fff;font-size:20px;line-height:1;cursor:pointer"
      title="Mostrar ou ocultar acumulados">▼</button>
  </h2>
  <div id="partial" class="metrics" style="display:none;margin-top:12px"></div>
</div>
<section class="card finalDashboard" id="finalDashboard"><div class="finalDashboardGrid">
  <div class="finalDashboardPane historyPane" id="periodCard"><h2>📅 Histórico por período</h2>
    <p style="margin:0 0 10px;color:#cbd5e1;font-size:13px">Escolha as datas para comparar meta e consumo no intervalo.</p>
    <button onclick="openPeriod()" style="width:100%;padding:12px;border:0;border-radius:12px;background:#111827;color:#fff;font-weight:bold;font-size:14px">📄 RELATÓRIO POR PERÍODO</button>
    <p style="margin:8px 0 0;color:#b9c9d8;font-size:11px">Escolha 7, 15, 30 dias ou um período personalizado e baixe o PDF sem sair do aplicativo.</p>
  </div>
  <div class="finalDashboardPane hydrationPane"><h2>💧 Hidratação</h2><div id="waterBox"></div>
    <div class="waterQuickButtons">
      <button onclick="addWater(200)">💧 200 ml</button><button onclick="addWater(300)">💧 300 ml</button><button onclick="addWater(500)">💧 500 ml</button>
      <button onclick="addWater(750)">💧 750 ml</button><button onclick="addWater(1000)">💧 1 L</button><button onclick="customWater()">✏️ Outra</button>
    </div>
  </div>
</div></section>
</main>
<div id="nutrientTooltip"></div>



<div id="profileModal" style="display:none;position:fixed;inset:0;background:#0009;z-index:90;overflow:auto;padding:18px">
  <div style="max-width:560px;margin:35px auto;background:#0b1728;color:#fff;border:1px solid #ffffff20;border-radius:18px;padding:18px;box-shadow:0 20px 60px #0008">
    <h2 style="margin:0 0 6px">👤 Cadastro da pessoa</h2>
    <p style="font-size:12px;color:#cbd5e1;margin:0 0 12px">Esses dados serão usados para estimar suas metas diárias.</p>
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:9px">
      <label style="font-size:12px;font-weight:bold">Nome
        <input id="profileName" type="text" maxlength="60" placeholder="Seu nome" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">
      </label>
      <label style="font-size:12px;font-weight:bold">Idade
        <input id="profileAge" type="number" min="10" max="120" placeholder="Ex.: 48" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">
      </label>
      <label style="font-size:12px;font-weight:bold">Peso atual (kg)
        <input id="profileWeight" type="number" min="20" max="400" step="0.1" placeholder="Ex.: 88,0" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">
        <small style="display:block;color:#9fb0c2;margin-top:4px">Altere quando seu peso mudar.</small>
      </label>
      <label style="font-size:12px;font-weight:bold">Altura (cm)
        <input id="profileHeight" type="number" min="100" max="250" step="0.1" placeholder="Ex.: 170" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">
      </label>
      <label style="font-size:12px;font-weight:bold">Peso-meta (kg)
        <input id="profileTargetWeight" type="number" min="20" max="400" step="0.1" placeholder="Ex.: 80,0" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">
      </label>
      <label style="font-size:12px;font-weight:bold">Ritmo (kg/semana)
        <input id="profileRate" type="number" min="0" max="1" step="0.1" placeholder="Ex.: 0,5" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">
      </label>
      <label style="font-size:12px;font-weight:bold">Sexo
        <select id="profileSex" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#16263a;color:white">
          <option value="">Selecione</option><option value="M">Masculino</option><option value="F">Feminino</option>
        </select>
      </label>
      <label style="font-size:12px;font-weight:bold">Nível de atividade
        <select id="profileActivity" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#16263a;color:white">
          <option value="">Selecione</option>
          <option value="sedentario">Sedentário</option>
          <option value="leve">Levemente ativo</option>
          <option value="moderado">Moderadamente ativo</option>
          <option value="alto">Muito ativo</option>
          <option value="atleta">Extremamente ativo</option>
        </select>
      </label>
    </div>
    <label style="display:block;font-size:12px;font-weight:bold;margin-top:9px">Objetivo
      <select id="profileGoal" style="width:100%;padding:11px;margin-top:5px;border:1px solid #ffffff30;border-radius:10px;background:#16263a;color:white">
        <option value="">Selecione</option>
        <option value="manter">Manter peso</option>
        <option value="perder">Perder gordura</option>
        <option value="ganhar">Ganhar massa muscular</option>
      </select>
    </label>
    <div id="profileEstimate" style="display:none;margin-top:12px;padding:11px;border-radius:12px;background:#ffffff08;border:1px solid #ffffff14;font-size:12px"></div>
    <div style="display:flex;gap:8px;margin-top:14px">
      <button onclick="calculateProfileGoals()" style="flex:1;padding:12px;border:1px solid #ffffff25;border-radius:10px;background:#16263a;color:white;font-weight:bold">RECALCULAR METAS</button>
      <button onclick="saveProfile()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#22c55e;color:#06210f;font-weight:bold">SALVAR</button>
      <button onclick="closeProfile()" style="padding:12px;border:1px solid #ffffff30;border-radius:10px;background:#ffffff10;color:white">FECHAR</button>
    </div>
  </div>
</div>

<div id="summaryModal" style="display:none;position:fixed;inset:0;background:#0008;z-index:60;overflow:auto;padding:18px">
  <div style="max-width:680px;margin:20px auto;background:#111827;color:#f8fafc;border:1px solid #334155;border-radius:18px;padding:16px">
    <div style="display:flex;justify-content:space-between;align-items:center">
      <h2 style="margin:0">📊 Resumo do dia</h2>
      <button onclick="closeSummary()" style="border:1px solid #475569;background:#1e293b;color:#f8fafc;border-radius:10px;padding:8px 12px;font-size:18px">✕</button>
    </div>
    <div style="font-size:12px;color:#cbd5e1;margin:6px 0 12px">Acumulado registrado até este momento.</div>
    <div id="goalModeNotice" style="font-size:12px;color:#9fe6b0;margin:6px 0 12px"></div>
    <div id="summaryContent"></div>
    <hr style="border:0;border-top:1px solid #334155;margin:16px 0">
    <h2>🎯 Metas diárias</h2>
    <div id="goalForm" class="metrics"></div>
    <div style="display:flex;gap:8px;margin-top:14px">
      <button onclick="closeSummary()" style="flex:1;padding:12px;border:1px solid #475569;border-radius:10px;background:#1e293b;color:#f8fafc">FECHAR</button>
      <button onclick="saveGoals()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#111827;color:#fff;font-weight:bold">SALVAR METAS MANUAIS</button>
      <button onclick="applyCalculatedGoals()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#22a447;color:#06210f;font-weight:bold">USAR CÁLCULO DO PERFIL</button>
    </div>
  </div>
</div>

<div id="consumeEditModal" style="display:none;position:fixed;inset:0;background:#0008;z-index:75;overflow:auto;padding:18px">
  <div style="max-width:460px;margin:48px auto;background:#111827;color:#f8fafc;border:1px solid #334155;border-radius:18px;padding:17px">
    <div style="display:flex;justify-content:space-between;align-items:center;gap:12px">
      <h2 id="consumeEditTitle" style="margin:0;font-size:20px">✏️ Alterar consumo</h2>
      <button onclick="closeConsumeEdit()" style="border:1px solid #475569;background:#1e293b;color:#f8fafc;border-radius:10px;padding:7px 11px;font-size:17px">✕</button>
    </div>
    <p style="margin:8px 0 14px;color:#cbd5e1;font-size:13px">Ajuste a quantidade e escolha uma refeição válida para este alimento.</p>
    <label id="consumeEditQuantityLabel" style="display:block;font-size:12px;font-weight:bold;margin-top:10px">Quantidade
      <div style="display:flex;gap:7px;margin-top:5px"><input id="consumeEditWeight" type="number" min="0.1" step="0.1" style="flex:1;min-width:0;padding:11px;border:1px solid #475569;border-radius:10px;background:#172033;color:#fff;font-size:16px"><select id="consumeEditUnit" style="width:76px;padding:11px;border:1px solid #475569;border-radius:10px;background:#172033;color:#fff;font-size:16px"><option value="g">g</option><option value="ml">ml</option></select></div>
    </label>
    <label style="display:block;font-size:12px;font-weight:bold;margin-top:12px">Tipo de refeição
      <select id="consumeEditMeal" style="width:100%;padding:11px;margin-top:5px;border:1px solid #475569;border-radius:10px;background:#172033;color:#fff;font-size:16px">
        <option value="Café da manhã">☕ Café da manhã</option>
        <option value="Almoço">🍽️ Almoço</option>
        <option value="Lanche">🥪 Lanche</option>
        <option value="Jantar">🍴 Jantar</option>
        <option value="Ceia">🌙 Ceia</option>
      </select>
    </label>
    <div style="display:flex;gap:8px;margin-top:16px">
      <button onclick="closeConsumeEdit()" style="flex:1;padding:12px;border:1px solid #475569;border-radius:10px;background:#1e293b;color:#fff;font-weight:bold">CANCELAR</button>
      <button onclick="saveConsumeEdit()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#22a447;color:#06210f;font-weight:bold">SALVAR ALTERAÇÃO</button>
    </div>
  </div>
</div>


<div id="periodModal" style="display:none;position:fixed;inset:0;background:#0008;z-index:65;overflow:auto;padding:18px">
  <div style="max-width:760px;margin:20px auto;background:#111827;color:#f8fafc;border:1px solid #334155;border-radius:18px;padding:16px">
    <div style="display:flex;justify-content:space-between;align-items:center">
      <h2 style="margin:0">📄 Relatório de alimentação</h2>
      <button onclick="closePeriod()" style="border:1px solid #475569;background:#1e293b;color:#f8fafc;border-radius:10px;padding:8px 12px;font-size:18px">✕</button>
    </div>
    <div style="font-size:12px;color:#cbd5e1;margin:6px 0 12px">
      Escolha o período para gerar um PDF com tabela diária, metas, gráficos de evolução e acumulados.
    </div>

    <div style="display:grid;grid-template-columns:1fr 1fr;gap:8px">
      <div><small>Data inicial</small><input id="periodStart" type="date" style="width:100%;padding:10px;border:1px solid #ddd;border-radius:9px"></div>
      <div><small>Data final</small><input id="periodEnd" type="date" style="width:100%;padding:10px;border:1px solid #ddd;border-radius:9px"></div>
    </div>

    <div style="display:grid;grid-template-columns:repeat(4,1fr);gap:7px;margin:10px 0">
      <button onclick="setPeriod(7)" style="padding:10px;border:0;border-radius:9px;background:#eef2f7">7 dias</button>
      <button onclick="setPeriod(15)" style="padding:10px;border:0;border-radius:9px;background:#eef2f7">15 dias</button>
      <button onclick="setPeriod(30)" style="padding:10px;border:0;border-radius:9px;background:#eef2f7">30 dias</button>
      <button onclick="loadPeriod()" style="padding:10px;border:0;border-radius:9px;background:#dbeafe;color:#10243a;font-weight:bold">Atualizar</button>
    </div>
    <button onclick="loadPeriod()" style="width:100%;padding:12px;border:0;border-radius:10px;background:#111827;color:#fff;font-weight:bold">ATUALIZAR PERÍODO</button>

    <div id="periodInfo" style="margin-top:12px"></div>
    <div id="periodContent"></div>
    <div id="historyChart" style="margin-top:14px"></div>

    <div style="display:flex;gap:8px;margin-top:14px;flex-wrap:wrap">
      <button id="downloadReportBtn" onclick="downloadReport()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#0ea5e9;color:#06223a;font-weight:bold">⬇️ BAIXAR RELATÓRIO PDF</button>
      <button onclick="closePeriod()" style="flex:1;padding:12px;border:1px solid #475569;border-radius:10px;background:#1e293b;color:#f8fafc">← VOLTAR AO APLICATIVO</button>
    </div>
  </div>
</div>

<div id="newFoodModal" style="display:none;position:fixed;inset:0;background:#0008;z-index:51;overflow:auto;padding:18px">
  <div style="max-width:680px;margin:20px auto;background:#111827;color:#f8fafc;border:1px solid #334155;border-radius:16px;padding:16px">
    <h2>Novo alimento</h2>
    <div style="font-size:12px;color:#cbd5e1;margin-bottom:10px">
      Cadastre os valores por 100 g. Depois de salvar, o alimento ficará disponível na pesquisa.
    </div>
    <div id="newFoodForm"></div>
    <div style="display:flex;gap:8px;margin-top:14px">
      <button onclick="closeNewFood()" style="flex:1;padding:12px;border:1px solid #475569;border-radius:10px;background:#1e293b;color:#f8fafc">CANCELAR</button>
      <button onclick="saveNewFood()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#111827;color:#fff;font-weight:bold">SALVAR</button>
    </div>
  </div>
</div>

<div id="foodModal" style="display:none;position:fixed;inset:0;background:#0008;z-index:50;overflow:auto;padding:18px">
  <div style="max-width:680px;margin:20px auto;background:#111827;color:#f8fafc;border:1px solid #334155;border-radius:16px;padding:16px">
    <h2>Editar alimento da base</h2>
    <div style="font-size:12px;color:#cbd5e1;margin-bottom:10px">
      Os valores abaixo são considerados por 100 g do alimento.
    </div>
    <div id="foodForm"></div>
    <div style="display:flex;gap:8px;margin-top:14px">
      <button onclick="closeFoodModal()" style="flex:1;padding:12px;border:1px solid #475569;border-radius:10px;background:#1e293b;color:#f8fafc">CANCELAR</button>
      <button onclick="saveFood()" style="flex:1;padding:12px;border:0;border-radius:10px;background:#111827;color:#fff;font-weight:bold">SALVAR</button>
    </div>
  </div>
</div>

<script>
let profileName="";
function renderProfileGreeting(){
  const hero=document.getElementById("heroGreeting");
  const header=document.getElementById("greeting");
  if(hero) hero.textContent=profileName?`Olá, ${profileName}! 👋`:"Olá! 👋";
  if(header) header.textContent=profileName?`Bom dia, ${profileName}! 👋 · Seu controle diário, seu melhor resultado.` : "Alimentação, nutrientes e histórico";
}
function setQuickMetric(valueId,fillId,value,goal,unit){
  const valueEl=document.getElementById(valueId),fillEl=document.getElementById(fillId),p=pct(value,goal);
  if(valueEl)valueEl.textContent=`${fmt(value)} / ${fmt(goal)} ${unit}`;
  if(fillEl){fillEl.style.width=p+"%";fillEl.parentElement.setAttribute("aria-label",`${fmt(p)}% da meta`)}
}
function updateHeroFromDay(j){
  const g=j.goals||{}, t=j.daily||{};
  renderProfileGreeting();
  const d=document.getElementById("day").value;
  document.getElementById("heroDate").textContent=new Date(d+"T12:00:00").toLocaleDateString("pt-BR",{weekday:"long",day:"2-digit",month:"long",year:"numeric"});
  setQuickMetric("heroKcal","heroKcalFill",Number(t.energia_kcal||0),Number(g.calorias_kcal||0),"kcal");
  setQuickMetric("heroProtein","heroProteinFill",Number(t.proteina_g||0),Number(g.proteina_g||0),"g");
  setQuickMetric("heroCarbs","heroCarbsFill",Number(t.carboidrato_g||0),Number(g.carboidratos_g||0),"g");
  setQuickMetric("heroFat","heroFatFill",Number(t.lipidios_g||0),Number(g.gorduras_g||0),"g");
  setQuickMetric("heroFiber","heroFiberFill",Number(t.fibra_g||0),Number(g.fibras_g||0),"g");
  setQuickMetric("heroSodium","heroSodiumFill",Number(t.sodio_mg||0),Number(g.sodio_mg||0),"mg");
  setQuickMetric("heroWater","heroWaterFill",Number(j.water||0)/1000,Number(g.agua_ml||0)/1000,"L");
}

const meals=["Café da manhã","Almoço","Lanche","Jantar","Ceia"];let meal=meals[0],chosen=null,timer,profileSex="";
async function loadProfile(){
  try{
    const j=await api('/api/profile');
    profileName=(j.nome||'').trim();profileSex=j.sexo==="F"?"F":j.sexo==="M"?"M":"";
    document.getElementById('profileName').value=j.nome||'';
    document.getElementById('profileAge').value=j.idade||'';
    document.getElementById('profileWeight').value=j.peso_kg||'';
    document.getElementById('profileHeight').value=j.altura_cm||'';
    document.getElementById('profileTargetWeight').value=j.peso_meta_kg||'';
    document.getElementById('profileRate').value=j.ritmo_kg_semana||'';
    document.getElementById('profileSex').value=j.sexo||'';
    document.getElementById('profileActivity').value=j.atividade||'';
    document.getElementById('profileGoal').value=j.objetivo||'';
    renderProfileGreeting();
    if(window.lastDaySnapshot){drawWater(Number(window.lastDaySnapshot.water||0),Number((window.lastDaySnapshot.goals||{}).agua_ml||0),window.lastDaySnapshot.water_entries||[]);}
    if(!profileName) openProfile(true);
  }catch(e){console.error(e)}
}
function openProfile(first=false){
  document.getElementById('profileModal').style.display='block';
  const goal=document.getElementById('profileGoal').value;
  updateRateHelp(goal);
  if(first) document.getElementById('profileName').focus();
}
function closeProfile(){document.getElementById('profileModal').style.display='none';}
function updateRateHelp(goal){
  const el=document.getElementById('profileRate');
  if(!el)return;
  if(goal==='perder'){el.placeholder='Ex.: 0,5 kg/semana';el.max=1}
  else if(goal==='ganhar'){el.placeholder='Ex.: 0,2 kg/semana';el.max=.5}
  else {el.placeholder='0 kg/semana';el.value='0';el.max=0}
}
function calculateProfileGoals(){
  const age=Number(document.getElementById('profileAge').value);
  const weight=Number(document.getElementById('profileWeight').value);
  const height=Number(document.getElementById('profileHeight').value);
  const target=Number(document.getElementById('profileTargetWeight').value)||weight;
  const sex=document.getElementById('profileSex').value;
  const act=document.getElementById('profileActivity').value;
  const goal=document.getElementById('profileGoal').value;
  let rate=Number(document.getElementById('profileRate').value)||0;

  if(!age||!weight||!height||!sex||!act||!goal){
    alert('Preencha idade, peso, altura, sexo, atividade e objetivo.');return null;
  }
  if(goal==='perder' && rate<=0){alert('Informe o ritmo de perda em kg/semana.');return null}
  if(goal==='ganhar' && rate<=0){alert('Informe o ritmo de ganho em kg/semana.');return null}
  if(goal==='manter')rate=0;

  const mult={sedentario:1.20,leve:1.375,moderado:1.55,alto:1.725,atleta:1.90}[act];
  const bmr=10*weight+6.25*height-5*age+(sex==='M'?5:-161);
  const tdee=bmr*mult;

  // 7.700 kcal/kg é uma aproximação de planejamento energético.
  let kcal=tdee;
  if(goal==='perder')kcal=tdee-(rate*7700/7);
  if(goal==='ganhar')kcal=tdee+(rate*7700/7);

  // Limite mínimo apenas para evitar metas acidentalmente extremas.
  kcal=Math.max(1200,Math.round(kcal));

  // Proteína: faixa alta para preservar/construir massa magra.
  const protein=Math.round(weight*(goal==='ganhar'?2.0:1.8));

  // Gordura: piso de ~0,7 g/kg; usamos 0,8 g/kg como meta inicial.
  const fat=Math.max(45,Math.round(weight*0.8));

  // Fibras: referência prática de ~14 g/1000 kcal, com mínimo de 25 g.
  const fiber=Math.max(25,Math.round(kcal*14/1000));

  // Carboidratos: todo o restante das calorias, depois de proteína e gordura.
  const used=protein*4+fat*9;
  let carbs=Math.round((kcal-used)/4);

  // Se a combinação escolhida ultrapassar as calorias, reduzimos gordura
  // até um piso seguro antes de permitir carboidratos negativos.
  let finalFat=fat;
  if(carbs<0){
    finalFat=Math.max(45,Math.floor((kcal-protein*4)/9));
    carbs=Math.max(0,Math.round((kcal-protein*4-finalFat*9)/4));
  }

  const water=Math.round(weight*35);
  const sodium=2000;
  const weeks=rate>0?Math.abs(weight-target)/rate:0;

  const totalFromMacros=protein*4+carbs*4+finalFat*9;
  const diff=Math.round(kcal-totalFromMacros);

  const estimate=document.getElementById('profileEstimate');
  estimate.style.display='block';
  estimate.innerHTML=`<b>🎯 Meta personalizada</b><br>
    Gasto diário estimado: <b>${fmt(tdee)} kcal</b><br>
    Meta calórica: <b>${fmt(kcal)} kcal</b> · Ritmo: <b>${fmt(rate)} kg/semana</b><br>
    Proteína: <b>${fmt(protein)} g</b> · Carboidratos: <b>${fmt(carbs)} g</b> ·
    Gorduras: <b>${fmt(finalFat)} g</b> · Fibras: <b>${fmt(fiber)} g</b> · Água: <b>${fmt(water)} ml</b><br>
    ${goal==='manter'?'Objetivo: manter o peso.':`Peso atual: <b>${fmt(weight)} kg</b> · Peso-meta: <b>${fmt(target)} kg</b> · Estimativa de ${fmt(weeks)} semanas até a meta.`}<br>
    <small style="color:#9fb0c2">Macros: ${fmt(totalFromMacros)} kcal de ${fmt(kcal)} kcal (diferença de arredondamento: ${fmt(diff)} kcal).</small>`;

  window.profileCalculatedGoals={
    calorias_kcal:kcal,
    proteina_g:protein,
    carboidratos_g:carbs,
    gorduras_g:finalFat,
    fibras_g:fiber,
    sodio_mg:sodium,
    agua_ml:water
  };
  return window.profileCalculatedGoals;
}
async function saveProfile(){
  const name=document.getElementById('profileName').value.trim();
  if(!name){alert('Digite seu nome.');return;}
  const data={
    nome:name,
    idade:document.getElementById('profileAge').value,
    peso_kg:document.getElementById('profileWeight').value,
    altura_cm:document.getElementById('profileHeight').value,
    peso_meta_kg:document.getElementById('profileTargetWeight').value,
    ritmo_kg_semana:document.getElementById('profileRate').value,
    sexo:document.getElementById('profileSex').value,
    atividade:document.getElementById('profileActivity').value,
    objetivo:document.getElementById('profileGoal').value
  };
  const saved=await api('/api/profile',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(data)});
  if(saved.goals_updated) document.getElementById('profileEstimate').style.display='block';
  profileName=name;profileSex=data.sexo==="F"?"F":data.sexo==="M"?"M":"";
  renderProfileGreeting();
  closeProfile();
  await refresh();
}
document.getElementById('profileGoal')?.addEventListener('change',e=>updateRateHelp(e.target.value));
let weightRecalcTimer=null;
document.getElementById('profileWeight')?.addEventListener('input',()=>{
  clearTimeout(weightRecalcTimer);
  weightRecalcTimer=setTimeout(()=>{
    const w=Number(document.getElementById('profileWeight').value);
    const t=Number(document.getElementById('profileTargetWeight').value);
    const g=document.getElementById('profileGoal').value;
    if(w&&t&&g) calculateProfileGoals();
  },500);
});
day.value=new Date().toISOString().slice(0,10);
function fmt(x){return Number(x||0).toLocaleString("pt-BR",{minimumFractionDigits:2,maximumFractionDigits:2})}
function escAttr(s){return String(s).replace(/&/g,'&amp;').replace(/\"/g,'&quot;').replace(/</g,'&lt;').replace(/>/g,'&gt;')}
function esc(s){return String(s).replace(/[&<>"']/g,m=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[m]))}
let csrfToken="";
async function api(u,o={}){const method=(o.method||"GET").toUpperCase();const headers={...(o.headers||{})};if(["POST","PUT","DELETE"].includes(method)&&csrfToken)headers["X-CSRF-Token"]=csrfToken;let r=await fetch(u,{...o,headers}),j=await r.json();if(!r.ok)throw Error(j.error||"Erro");return j}
function setAuthStatus(msg){const el=document.getElementById("authStatus");if(el)el.textContent=msg||""}
function showApp(user,csrf=""){csrfToken=csrf||"";document.getElementById("authScreen").style.display="none";document.getElementById("userEmail").textContent=user?.email||"";mealsUI();loadPersonalLists();Promise.all([loadProfile(),refresh()]).catch(e=>console.error("carregamento inicial:",e))}
async function login(){try{setAuthStatus("Entrando...");const j=await api("/api/auth/login",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({email:document.getElementById("authEmail").value,password:document.getElementById("authPassword").value})});showApp(j.user,j.csrf)}catch(e){setAuthStatus(e.message)}}
async function register(){try{setAuthStatus("Criando conta...");const j=await api("/api/auth/register",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({email:document.getElementById("authEmail").value,password:document.getElementById("authPassword").value})});showApp(j.user,j.csrf)}catch(e){setAuthStatus(e.message)}}
async function logout(){try{await api("/api/auth/logout",{method:"POST"})}finally{location.reload()}}
async function bootstrap(){const j=await fetch("/api/me").then(r=>r.json());if(j.authenticated)showApp(j.user,j.csrf);else document.getElementById("authScreen").style.display="flex"}
function mealsUI(){const icons={"Café da manhã":"☕","Almoço":"🍽️","Lanche":"🥪","Jantar":"🍴","Ceia":"🌙"};mealsEl.innerHTML=meals.map(m=>"<button class='"+(m==meal?"on":"")+"' onclick='meal="+JSON.stringify(m)+";mealsUI();refresh()'>"+icons[m]+" "+m+"</button>").join("");pm.textContent=icons[meal]+" "+meal}
const searchCache=new Map();let searchController=null,searchSequence=0,searchTimer=null;
function renderSearchResults(result){
  if(result.length){
    foods.innerHTML=result.map(f=>"<div class='food' onclick='selectFood("+JSON.stringify(f)+")'>"+esc(f.nome)+" <small style='opacity:.7'>· 100 "+esc(foodUnit(f))+"</small></div>").join("");
  }else{
    foods.innerHTML="<div class='empty'>Nenhum alimento encontrado.</div>";
    document.getElementById("newBase").style.display="block";
  }
}
async function search(){
  const q=searchEl.value.trim(),key=q.toLocaleLowerCase();
  chosen=null;
  sel.textContent="Nenhum alimento selecionado.";
  document.getElementById("editBase").style.display="none";
  document.getElementById("newBase").style.display="none";
  if(!q){foods.innerHTML="";return;}
  if(q.length<2){foods.innerHTML="<div class='empty'>Digite pelo menos 2 letras para buscar.</div>";return;}
  const cached=searchCache.get(key);
  if(cached&&Date.now()-cached.at<120000){renderSearchResults(cached.foods);return;}
  const warm=[...searchCache.entries()].find(([cachedKey,entry])=>key.startsWith(cachedKey)&&Date.now()-entry.at<120000);
  if(warm){
    const warmResults=warm[1].foods.filter(f=>String(f.nome||"").toLocaleLowerCase().includes(key));
    if(warmResults.length)renderSearchResults(warmResults);
  }
  if(searchController)searchController.abort();
  searchController=new AbortController();
  const sequence=++searchSequence;
  if(!warm)foods.innerHTML="<div class='empty'>Buscando alimentos...</div>";
  try{
    const j=await api("/api/foods?q="+encodeURIComponent(q),{signal:searchController.signal});
    if(sequence!==searchSequence||searchEl.value.trim().toLocaleLowerCase()!==key)return;
    const result=(j.foods||[]).slice(0,30);
    searchCache.set(key,{at:Date.now(),foods:result});
    if(searchCache.size>30)searchCache.delete(searchCache.keys().next().value);
    renderSearchResults(result);
  }catch(e){
    if(e.name!=="AbortError")foods.innerHTML="<div class='empty'>Não foi possível buscar agora. Tente novamente.</div>";
  }
}
function foodUnit(f){return String(f?.unidade||"").toLowerCase()==="ml"||String(f?.base_calculo||"").toLowerCase()==="100ml"||String(f?.porcao_unidade||"").toLowerCase()==="ml"?"ml":"g"}
function setQuantityUnit(unit){const u=unit==="ml"?"ml":"g",el=document.getElementById("quantityUnit");if(el)el.value=u;return u}
function selectFood(f){
  chosen=f;
  chosen.unidade=foodUnit(f);
  setQuantityUnit(chosen.unidade);
  searchSequence++;
  if(searchController){searchController.abort();searchController=null;}
  searchEl.value=f.nome;
  sel.textContent="Selecionado: "+f.nome;
  foods.innerHTML="";
  const edit=document.getElementById("editBase");edit.style.display="block";edit.disabled=Number(f.id)>=0;edit.textContent=Number(f.id)<0?"EDITAR MEU ALIMENTO":"BASE COMPARTILHADA · SOMENTE LEITURA";edit.style.opacity=Number(f.id)<0?"1":".65";
  document.getElementById("newBase").style.display="none";
  if(f.unidade===undefined&&Number(f.id)<0){api("/api/food/"+f.id).then(j=>{if(chosen&&chosen.id===f.id){chosen.unidade=foodUnit(j.food||{});setQuantityUnit(chosen.unidade)}}).catch(()=>{})}
}
async function favoriteChosen(){
  if(!chosen){alert("Selecione um alimento primeiro.");return}
  try{await api("/api/favorite",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({alimento_id:chosen.id,alimento_nome:chosen.nome})});await loadPersonalLists();alert("Alimento salvo nos favoritos.")}catch(e){alert(e.message)}
}
async function savePortion(){
  if(!chosen){alert("Selecione um alimento primeiro.");return}
  const nome=prompt("Nome da porção (ex.: 1 colher, 1 fatia):","Porção habitual");if(nome===null)return;
  const q=Number(document.getElementById("weight").value);if(!(q>0)){alert("Informe uma quantidade válida.");return}
  const unidade=document.getElementById("quantityUnit").value;
  try{await api("/api/portion",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({alimento_id:chosen.id,alimento_nome:chosen.nome,nome,quantidade_g:q,unidade})});await loadPersonalLists();alert("Porção salva.")}catch(e){alert(e.message)}
}
async function loadPersonalLists(){
  const box=document.getElementById("personalLists");if(!box)return;
  try{const [fav,port]=await Promise.all([api("/api/favorites"),api("/api/portions")]);
    const fhtml=fav.length?`<div style="font-size:12px;font-weight:bold;margin:8px 0 4px">⭐ Favoritos</div>`+fav.map(f=>`<button onclick='selectFood(${JSON.stringify({id:f.alimento_id,nome:f.alimento_nome})})' style="margin:3px;padding:7px 9px;border:1px solid #ffffff25;border-radius:9px;background:#172b42;color:#fff">${esc(f.alimento_nome)}</button>`).join(""):"";
    const phtml=port.length?`<div style="font-size:12px;font-weight:bold;margin:8px 0 4px">💾 Porções salvas</div>`+port.map(p=>`<button onclick='selectFood(${JSON.stringify({id:p.alimento_id,nome:p.alimento_nome,unidade:p.unidade||"g"})});document.getElementById("weight").value=${Number(p.quantidade_g)||0};setQuantityUnit(${JSON.stringify(p.unidade||"g")})' style="margin:3px;padding:7px 9px;border:1px solid #ffffff25;border-radius:9px;background:#172b42;color:#fff">${esc(p.alimento_nome)} · ${esc(p.nome)} (${fmt(p.quantidade_g)} ${esc(p.unidade||"g")})</button>`).join(""):"";
    box.innerHTML=fhtml+phtml;
  }catch(e){box.innerHTML=""}
}
const editFields=[["nome","Nome","text"],["energia_kcal","Calorias (kcal)","number"],["proteina_g","Proteína (g)","number"],["carboidrato_g","Carboidratos (g)","number"],["lipidios_g","Gorduras (g)","number"],["fibra_g","Fibras (g)","number"],["colesterol_mg","Colesterol (mg)","number"],["calcio_mg","Cálcio (mg)","number"],["magnesio_mg","Magnésio (mg)","number"],["fosforo_mg","Fósforo (mg)","number"],["ferro_mg","Ferro (mg)","number"],["sodio_mg","Sódio (mg)","number"],["potassio_mg","Potássio (mg)","number"],["zinco_mg","Zinco (mg)","number"],["vitamina_c_mg","Vitamina C (mg)","number"]];
function syncFoodBase(prefix){const unit=document.getElementById(prefix+"_base_unit")?.value==="ml"?"ml":"g",hint=document.getElementById(prefix+"_base_hint");if(hint)hint.textContent="Valores por 100 "+unit}

async function resizePhoto(file){
  return await new Promise((resolve,reject)=>{const r=new FileReader();r.onload=()=>{const img=new Image();img.onload=()=>{const max=1600,scale=Math.min(1,max/Math.max(img.width,img.height)),cv=document.createElement("canvas");cv.width=Math.round(img.width*scale);cv.height=Math.round(img.height*scale);cv.getContext("2d").drawImage(img,0,0,cv.width,cv.height);resolve(cv.toDataURL("image/jpeg",.82))};img.onerror=reject;img.src=r.result};r.onerror=reject;r.readAsDataURL(file)})
}
async function readNutritionPhoto(){
  const status=document.getElementById("photoStatus"),file=window.nutritionPhotoFile;if(!file){alert("Escolha uma imagem da galeria ou fotografe a tabela nutricional.");return}
  try{status.textContent="Lendo a fotografia...";const image_data=await resizePhoto(file);const j=await api("/api/read_nutrition_label",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({image_data})});const d=j.data||{};for(const x of editFields){const el=document.getElementById("nf_"+x[0]);if(el&&d[x[0]]!==null&&d[x[0]]!==undefined)el.value=d[x[0]]}if(d.nome)document.getElementById("nf_nome").value=d.nome;const unit=(d.base_calculo==="100ml"||d.porcao_unidade==="ml")?"ml":"g",unitEl=document.getElementById("nf_base_unit");if(unitEl){unitEl.value=unit;syncFoodBase("nf")}status.textContent="Campos preenchidos. Confira se a referência é por 100 "+unit+" antes de salvar."}catch(e){status.textContent="";alert(e.message)}
}
let plateState={items:[],meal:""};
const plateMeals=["Café da manhã","Almoço","Lanche","Jantar","Ceia"];
function ensurePlateReview(){
  let modal=document.getElementById("plateReviewModal");
  if(modal)return modal;
  modal=document.createElement("div");modal.id="plateReviewModal";
  modal.style.cssText="display:none;position:fixed;inset:0;background:#000b;z-index:120;overflow:auto;padding:14px";
  document.body.appendChild(modal);return modal;
}
async function onPlatePhoto(file){
  if(!file)return;
  const status=document.getElementById("platePhotoStatus");
  try{
    status.textContent="Analisando o prato...";
    const image_data=await resizePhoto(file);
    const j=await api("/api/analyze_plate",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({image_data})});
    plateState={items:(j.items||[]).map(x=>({...x,gramas_por_colher:Number(x.gramas_por_colher||15)})),meal:meal||"Almoço"};
    if(!plateState.items.length)throw Error("Não foi possível identificar alimentos suficientes na foto.");
    status.textContent="Estimativa pronta. Confira as quantidades antes de confirmar.";
    renderPlateReview();
  }catch(e){status.textContent="";alert("Não foi possível analisar o prato: "+e.message)}
}
function plateQtyGrams(i,value){const it=plateState.items[i],q=Number(value);if(q>0){it.quantidade_g=q;it.colheres_sopa=Math.round((q/(Number(it.gramas_por_colher)||15))*10)/10}renderPlateReview()}
function plateQtySpoons(i,value){const it=plateState.items[i],q=Number(value);if(q>0){it.colheres_sopa=q;it.quantidade_g=Math.round(q*(Number(it.gramas_por_colher)||15))}renderPlateReview()}
function removePlateItem(i){plateState.items.splice(i,1);renderPlateReview()}
function openPlateFinder(i){
  const slot=document.getElementById("plateFinder_"+i);if(!slot)return;
  slot.innerHTML=`<div style="display:flex;gap:6px;margin-top:8px"><input id="plateSearch_${i}" value="${escAttr(plateState.items[i].alimento_nome||plateState.items[i].nome||"")}" placeholder="Buscar alimento correto" style="flex:1;padding:9px;border:1px solid #ffffff35;border-radius:9px;background:#ffffff12;color:white"><button onclick="searchPlateFood(${i})" style="padding:9px;border:0;border-radius:9px;background:#38bdf8;color:#082f49;font-weight:bold">BUSCAR</button></div><div id="plateFindResults_${i}" style="margin-top:6px"></div>`;
}
async function searchPlateFood(i){
  const input=document.getElementById("plateSearch_"+i),out=document.getElementById("plateFindResults_"+i);const q=input?.value.trim();if(!q)return;
  try{const j=await api("/api/foods?q="+encodeURIComponent(q));out.innerHTML=(j.foods||[]).slice(0,6).map(f=>`<button data-id="${Number(f.id)}" data-name="${escAttr(f.nome)}" onclick="setPlateFood(${i},Number(this.dataset.id),this.dataset.name)" style="display:block;width:100%;text-align:left;margin-top:4px;padding:8px;border:1px solid #ffffff25;border-radius:8px;background:#0f2740;color:white">${esc(f.nome)}</button>`).join("")||"<small>Nenhum alimento encontrado. Cadastre-o primeiro na base.</small>"}catch(e){out.textContent=e.message}
}
function setPlateFood(i,id,name){plateState.items[i].alimento_id=Number(id);plateState.items[i].alimento_nome=name;plateState.items[i].encontrado=true;plateState.items[i].nutrientes_estimados=null;renderPlateReview()}
function addPlateItem(){plateState.items.push({nome:"Novo alimento",alimento_nome:"",alimento_id:null,quantidade_g:100,colheres_sopa:6.7,gramas_por_colher:15,encontrado:false});renderPlateReview();setTimeout(()=>openPlateFinder(plateState.items.length-1),0)}
function renderPlateReview(){
  const modal=ensurePlateReview();
  const rows=plateState.items.map((it,i)=>{
    const found=Number.isFinite(Number(it.alimento_id)),estimated=!found&&!!it.nutrientes_estimados;
    const note=found?"Vinculado à base nutricional":estimated?"Será cadastrado na sua base com nutrientes estimados por IA":"Escolha o alimento correto antes de confirmar";
    return `<div style="padding:11px;margin-top:9px;border:1px solid ${found?"#4ade8055":estimated?"#7dd3fc88":"#fbbf2466"};border-radius:12px;background:#ffffff0d"><div style="display:flex;gap:8px;align-items:center;justify-content:space-between"><div style="min-width:0"><b>${esc(it.alimento_nome||it.nome||"Alimento")}</b><div style="font-size:11px;color:${found?"#86efac":estimated?"#7dd3fc":"#fcd34d"};margin-top:3px">${note}</div></div><div style="display:flex;gap:5px"><button onclick="openPlateFinder(${i})" style="padding:7px 8px;border:1px solid #ffffff30;border-radius:8px;background:#1e3a5f;color:white;font-weight:bold">CORRIGIR</button><button onclick="removePlateItem(${i})" style="padding:7px 8px;border:1px solid #fecaca55;border-radius:8px;background:#7f1d1d;color:white">✕</button></div></div><div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:10px"><label style="font-size:12px;font-weight:bold">Gramas<input type="number" min="1" step="1" value="${Number(it.quantidade_g)||0}" onchange="plateQtyGrams(${i},this.value)" style="width:100%;margin-top:4px;padding:9px;border:1px solid #ffffff35;border-radius:9px;background:#ffffff12;color:white"></label><label style="font-size:12px;font-weight:bold">Colheres de sopa<input type="number" min="0.1" step="0.1" value="${Number(it.colheres_sopa||0).toFixed(1)}" onchange="plateQtySpoons(${i},this.value)" style="width:100%;margin-top:4px;padding:9px;border:1px solid #ffffff35;border-radius:9px;background:#ffffff12;color:white"></label></div><div id="plateFinder_${i}"></div></div>`;
  }).join("");
  modal.innerHTML=`<div style="max-width:620px;margin:20px auto 42px;background:#0b1728;color:white;border:1px solid #ffffff25;border-radius:18px;padding:17px;box-shadow:0 20px 60px #000a"><h2 style="margin:0">🍽️ Conferir prato</h2><p style="margin:7px 0 12px;color:#cbd5e1;font-size:13px;line-height:1.4">A foto gera estimativas. Ajuste apenas gramas ou colheres de sopa, corrija os alimentos e escolha a refeição. Itens em azul serão cadastrados na sua base pessoal com nutrientes estimados por IA somente após a confirmação.</p><label style="display:block;font-size:12px;font-weight:bold">Registrar como<select id="plateMeal" onchange="plateState.meal=this.value" style="display:block;width:100%;margin-top:5px;padding:11px;border:1px solid #ffffff35;border-radius:10px;background:#16263a;color:white">${plateMeals.map(m=>`<option ${m===plateState.meal?"selected":""}>${m}</option>`).join("")}</select></label><div id="plateItems">${rows||"<p>Nenhum item no prato.</p>"}</div><button onclick="addPlateItem()" style="width:100%;margin-top:10px;padding:11px;border:1px dashed #7dd3fc88;border-radius:11px;background:#0c3552;color:#e0f2fe;font-weight:bold">＋ ADICIONAR ALIMENTO</button><div style="display:grid;grid-template-columns:1fr 1.4fr;gap:8px;margin-top:13px"><button onclick="closePlateReview()" style="padding:12px;border:1px solid #ffffff35;border-radius:11px;background:#ffffff10;color:white;font-weight:bold">CANCELAR</button><button onclick="confirmPlateItems()" style="padding:12px;border:0;border-radius:11px;background:#22c55e;color:#052e16;font-weight:bold">✓ CONFIRMAR E ADICIONAR</button></div></div>`;
  modal.style.display="block";
}
function closePlateReview(){const modal=document.getElementById("plateReviewModal");if(modal)modal.style.display="none"}
function validPlateFoodId(value){return value!==null&&value!==undefined&&value!==""&&Number.isFinite(Number(value))&&Number(value)!==0}
async function confirmPlateItems(){
  const items=plateState.items.map(x=>({alimento_id:validPlateFoodId(x.alimento_id)?Number(x.alimento_id):null,alimento_nome:x.alimento_nome,quantidade_g:Number(x.quantidade_g),nutrientes_estimados:x.nutrientes_estimados||null,confianca:Number(x.confianca)||0}));
  if(!items.length){alert("Inclua ao menos um alimento.");return}
  if(items.some(x=>(x.alimento_id===null&&!x.nutrientes_estimados)||!x.alimento_nome||!(x.quantidade_g>0))){alert("Corrija os alimentos sem estimativa ou selecione-os na base antes de confirmar.");return}
  const btn=[...document.querySelectorAll("#plateReviewModal button")].find(x=>x.textContent.includes("CONFIRMAR"));if(btn){btn.disabled=true;btn.textContent="ADICIONANDO..."}
  try{const result=await api("/api/consume_batch",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({data:day.value,refeicao:plateState.meal||meal,items})});closePlateReview();const created=(result.created_foods||[]).length;document.getElementById("platePhotoStatus").textContent="Prato adicionado em "+(plateState.meal||meal)+(created?". "+created+" alimento(s) também foram salvos na sua base pessoal.":".");await refresh()}catch(e){alert("Não foi possível adicionar o prato: "+e.message);if(btn){btn.disabled=false;btn.textContent="✓ CONFIRMAR E ADICIONAR"}}
}
function chooseNutritionPhoto(file,origin){
  if(!file)return;
  window.nutritionPhotoFile=file;
  const name=document.getElementById("nutritionPhotoName"),status=document.getElementById("photoStatus");
  if(name)name.textContent=(origin==="camera"?"📷 Foto tirada: ":"🖼️ Imagem escolhida: ")+file.name;
  if(status)status.textContent="Agora toque em LER TABELA E PREENCHER.";
}
function openNewFood(){
  const form=document.getElementById("newFoodForm");
  window.nutritionPhotoFile=null;
  form.innerHTML=`<div style="padding:13px;background:#10243a;border:1px solid #7dd3fc55;border-radius:13px;margin-bottom:13px;color:#fff"><b style="display:block;font-size:15px">📋 Ler tabela nutricional</b><p style="margin:6px 0 10px;font-size:12px;line-height:1.4;color:#cbd5e1">Escolha uma imagem salva ou fotografe a tabela do produto. Depois, confira os campos antes de cadastrar.</p><input id="nutritionGalleryInput" type="file" accept="image/*" style="display:none" onchange="chooseNutritionPhoto(this.files[0],'gallery');this.value=''"><input id="nutritionCameraInput" type="file" accept="image/*" capture="environment" style="display:none" onchange="chooseNutritionPhoto(this.files[0],'camera');this.value=''"><div style="display:grid;grid-template-columns:1fr 1fr;gap:8px"><button type="button" onclick="document.getElementById('nutritionGalleryInput').click()" style="padding:12px 8px;border:1px solid #7dd3fc66;border-radius:10px;background:#16334f;color:#e0f2fe;font-weight:bold;font-size:13px">🖼️ GALERIA</button><button type="button" onclick="document.getElementById('nutritionCameraInput').click()" style="padding:12px 8px;border:1px solid #86efac66;border-radius:10px;background:#1f5138;color:#ecfdf5;font-weight:bold;font-size:13px">📷 CÂMERA</button></div><div id="nutritionPhotoName" style="min-height:17px;margin-top:8px;font-size:12px;color:#bfdbfe"></div><button type="button" onclick="readNutritionPhoto()" style="width:100%;margin-top:9px;padding:12px;border:0;border-radius:10px;background:#2563eb;color:#fff;font-weight:bold;font-size:13px">✨ LER TABELA E PREENCHER</button><div id="photoStatus" style="min-height:17px;font-size:12px;margin-top:7px;color:#bfdbfe">A leitura preenche os campos; o salvamento só ocorre após sua conferência.</div></div>`+editFields.map(x=>{
    return "<label style='display:block;margin:9px 0;font-size:13px;font-weight:bold'>"+
      x[1]+"<input id='nf_"+x[0]+"' type='"+x[2]+"' "+
      (x[2]=="number"?"step='0.01'":"")+
      " value='' style='width:100%;padding:10px;border:1px solid #ddd;border-radius:9px;font-size:16px'></label>";
  }).join("");
  form.insertAdjacentHTML("afterbegin",`<div style="display:flex;gap:8px;align-items:end;padding:11px;margin-bottom:12px;background:#ffffff0d;border:1px solid #ffffff20;border-radius:11px"><label style="flex:1;font-size:12px;font-weight:bold">Referência nutricional<select id="nf_base_unit" onchange="syncFoodBase('nf')" style="display:block;width:100%;margin-top:5px;padding:10px;border:1px solid #ffffff35;border-radius:9px;background:#16263a;color:#fff"><option value="g">Por 100 g · alimento sólido</option><option value="ml">Por 100 ml · bebida</option></select></label><b id="nf_base_hint" style="font-size:13px;color:#7dd3fc;white-space:nowrap">Valores por 100 g</b></div>`);
  const q=searchEl.value.trim();
  document.getElementById("nf_nome").value=q;
  syncFoodBase("nf");
  document.getElementById("newFoodModal").style.display="block";
}
function closeNewFood(){document.getElementById("newFoodModal").style.display="none";}
async function saveNewFood(){
  try{
    let d={};
    for(let x of editFields){
      const el=document.getElementById("nf_"+x[0]);
      const v=el.value;
      d[x[0]]=x[0]=="nome" ? v.trim() : (v==="" ? null : Number(v));
    }
    if(!d.nome){alert("Informe o nome do alimento.");return;}
    const unit=document.getElementById("nf_base_unit").value;d.base_calculo=unit==="ml"?"100ml":"100g";d.porcao_unidade=unit;
    await api("/api/food",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(d)});
    closeNewFood();
    searchEl.value=d.nome;
    await search();
    alert("Alimento cadastrado na base.");
  }catch(e){alert("Não foi possível cadastrar: "+e.message);}
}

async function openFoodEditor(){
  if(!chosen){alert("Selecione um alimento primeiro.");return}
  if(Number(chosen.id)>=0){alert("A base nutricional compartilhada é somente leitura. Cadastre uma versão personalizada se precisar alterá-la.");return}
  try{
    let j=await api("/api/food/"+chosen.id);
    let f=j.food;
    document.getElementById("foodForm").innerHTML=editFields.map(x=>{
      let v=(f[x[0]]===null || f[x[0]]===undefined) ? "" : f[x[0]];
      return "<label style='display:block;margin:9px 0;font-size:13px;font-weight:bold'>"+
        x[1]+"<input id='ef_"+x[0]+"' type='"+x[2]+"' "+
        (x[2]=="number"?"step='0.01'":"")+
        " value='"+escAttr(v)+"' style='width:100%;padding:10px;border:1px solid #ddd;border-radius:9px;font-size:16px'></label>";
    }).join("");
    const unit=foodUnit(f);document.getElementById("foodForm").insertAdjacentHTML("afterbegin",`<div style="display:flex;gap:8px;align-items:end;padding:11px;margin-bottom:12px;background:#ffffff0d;border:1px solid #ffffff20;border-radius:11px"><label style="flex:1;font-size:12px;font-weight:bold">Referência nutricional<select id="ef_base_unit" onchange="syncFoodBase('ef')" style="display:block;width:100%;margin-top:5px;padding:10px;border:1px solid #ffffff35;border-radius:9px;background:#16263a;color:#fff"><option value="g" ${unit==="g"?"selected":""}>Por 100 g · alimento sólido</option><option value="ml" ${unit==="ml"?"selected":""}>Por 100 ml · bebida</option></select></label><b id="ef_base_hint" style="font-size:13px;color:#7dd3fc;white-space:nowrap">Valores por 100 ${unit}</b></div>`);syncFoodBase("ef");
    document.getElementById("foodModal").style.display="block";
  }catch(e){alert("Não foi possível abrir o cadastro: "+e.message)}
}
function closeFoodModal(){
  document.getElementById("foodModal").style.display="none";
}
async function saveFood(){
  if(!chosen)return;
  try{
    let d={};
    for(let x of editFields){
      let el=document.getElementById("ef_"+x[0]);
      let v=el.value;
      d[x[0]]=x[0]=="nome" ? v.trim() : (v==="" ? null : Number(v));
    }
    if(!d.nome){alert("Nome obrigatório.");return}
    const unit=document.getElementById("ef_base_unit").value;d.base_calculo=unit==="ml"?"100ml":"100g";d.porcao_unidade=unit;
    await api("/api/food/"+chosen.id,{
      method:"PUT",
      headers:{"Content-Type":"application/json"},
      body:JSON.stringify(d)
    });
    chosen.nome=d.nome;chosen.unidade=unit;setQuantityUnit(unit);
    document.getElementById("sel").textContent="Selecionado: "+d.nome;
    closeFoodModal();
    refresh();
    alert("Alimento atualizado na base.");
  }catch(e){alert("Não foi possível salvar: "+e.message)}
}
async function add(){
  if(!chosen){alert("Selecione um alimento.");return}
  const w=Number(weight.value);
  const unidade=document.getElementById("quantityUnit").value;
  if(w<=0){alert("Quantidade inválida.");return}
  try{
    await api("/api/consume",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({data:day.value,refeicao:meal,alimento_id:chosen.id,alimento_nome:chosen.nome,quantidade_g:w,unidade})});
    searchEl.value="";foods.innerHTML="";sel.textContent="Nenhum alimento selecionado.";chosen=null;
    const list=document.getElementById("items"), toggle=document.getElementById("consumedFoodsToggle");
    if(list){list.style.display="block";if(toggle){toggle.textContent="▲";toggle.setAttribute("aria-expanded","true");}}
    await refresh();
  }catch(e){alert("Não foi possível adicionar o alimento: "+e.message)}
}

const nutrientTip=document.getElementById("nutrientTooltip");
let tipCache={};
function nutrientLabel(k){
  const m={energia_kcal:"Calorias",proteina_g:"Proteína",carboidrato_g:"Carboidratos",lipidios_g:"Gorduras",fibra_g:"Fibras",calcio_mg:"Cálcio",magnesio_mg:"Magnésio",manganes_mg:"Manganês",fosforo_mg:"Fósforo",ferro_mg:"Ferro",sodio_mg:"Sódio",potassio_mg:"Potássio",cobre_mg:"Cobre",zinco_mg:"Zinco",vitamina_c_mg:"Vitamina C",tiamina_mg:"B1",riboflavina_mg:"B2",niacina_mg:"B3",piridoxina_mg:"B6",colesterol_mg:"Colesterol"};
  return m[k]||k;
}
function nutrientUnit(k){return k==="energia_kcal"?"kcal":(["proteina_g","carboidrato_g","lipidios_g","fibra_g"].includes(k)?"g":"mg")}
function tipPos(ev){
  const w=nutrientTip.offsetWidth,h=nutrientTip.offsetHeight,p=12;
  let x=ev.clientX+14,y=ev.clientY+14;
  if(x+w>innerWidth-p)x=ev.clientX-w-14;
  if(y+h>innerHeight-p)y=innerHeight-h-p;
  nutrientTip.style.left=Math.max(p,x)+"px";nutrientTip.style.top=Math.max(p,y)+"px";
}
async function showNutrientTip(el,ev){
  const nutrient=el.dataset.nutrient;if(!nutrient)return;
  const start=el.dataset.start||day.value,end=el.dataset.end||start,key=nutrient+"|"+start+"|"+end;
  nutrientTip.style.display="block";
  nutrientTip.innerHTML=`<div class="tipTitle">🔎 ${esc(nutrientLabel(nutrient))}</div><div class="tipEmpty">Calculando de onde veio...</div>`;
  tipPos(ev);
  try{
    let j=tipCache[key];
    if(!j){j=await api("/api/nutrient_sources?nutrient="+encodeURIComponent(nutrient)+"&start="+encodeURIComponent(start)+"&end="+encodeURIComponent(end));tipCache[key]=j}
    if(!el.matches(":hover"))return;
    const unit=nutrientUnit(nutrient);
    const rows=(j.sources||[]).map(s=>`<div class="tipRow"><span class="tipFood">${esc(s.nome)}<br><small>${esc(s.refeicao)} · ${fmt(s.quantidade_g)} ${esc(s.unidade||"g")}${start!==end?" · "+esc(s.data):""}</small></span><span class="tipVal">${fmt(s.valor)} ${unit}</span></div>`).join("");
    nutrientTip.innerHTML=`<div class="tipTitle">🔎 ${esc(nutrientLabel(nutrient))}</div><div class="tipTotal">Total: ${fmt(j.total)} ${unit}</div>${rows||'<div class="tipEmpty">Nenhum alimento contribuiu para este nutriente.</div>'}`;
    tipPos(ev);
  }catch(e){nutrientTip.innerHTML=`<div class="tipTitle">🔎 ${esc(nutrientLabel(nutrient))}</div><div class="tipEmpty">Não foi possível calcular as fontes.</div>`}
}
document.addEventListener("mouseover",e=>{const el=e.target.closest(".nutrient-source");if(el)showNutrientTip(el,e)});
document.addEventListener("mousemove",e=>{const el=e.target.closest(".nutrient-source");if(el&&nutrientTip.style.display==="block")tipPos(e)});
document.addEventListener("mouseout",e=>{const el=e.target.closest(".nutrient-source");if(el&&!el.contains(e.relatedTarget))nutrientTip.style.display="none"});

function toggleConsumedFoods(){
  const el=document.getElementById("items");
  const btn=document.getElementById("consumedFoodsToggle");
  if(!el||!btn)return;
  const open=el.style.display!=="none";
  el.style.display=open?"none":"block";
  btn.textContent=open?"▼":"▲";
  btn.setAttribute("aria-expanded",String(!open));
}
function toggleAccumulated(){
  const el=document.getElementById("partial");
  const btn=document.getElementById("accumulatedToggle");
  if(!el||!btn)return;
  const open=el.style.display!=="none";
  el.style.display=open?"none":"grid";
  btn.textContent=open?"▼":"▲";
  btn.setAttribute("aria-expanded",String(!open));
}
function toggleGoalsDashboard(){
  const el=document.getElementById("goalCards"),btn=document.getElementById("goalsToggle");
  if(!el||!btn)return;
  const open=el.style.display!=="none";
  el.style.display=open?"none":"grid";
  btn.textContent=open?"VER METAS":"OCULTAR METAS";
  btn.setAttribute("aria-expanded",String(!open));
}
function renderGoalCards(j){
  const g=j.goals||{},t=j.daily||{},water=Number(j.water||0);
  const data=[
    ["🔥","Calorias",Number(t.energia_kcal||0),Number(g.calorias_kcal||0),"kcal",false],
    ["💪","Proteína",Number(t.proteina_g||0),Number(g.proteina_g||0),"g",false],
    ["🍚","Carboidratos",Number(t.carboidrato_g||0),Number(g.carboidratos_g||0),"g",false],
    ["🥑","Gorduras",Number(t.lipidios_g||0),Number(g.gorduras_g||0),"g",false],
    ["🌱","Fibras",Number(t.fibra_g||0),Number(g.fibras_g||0),"g",false],
    ["🧂","Sódio",Number(t.sodio_mg||0),Number(g.sodio_mg||0),"mg",true],
    ["💧","Água",water/1000,Number(g.agua_ml||0)/1000,"L",false]
  ];
  const el=document.getElementById("goalCards");if(!el)return;
  el.innerHTML=data.map(([icon,label,value,target,unit,limit])=>{const p=pct(value,target);return `<button type="button" class="goalMiniCard ${limit?"limit":""}" onclick="openSummary()"><small>${icon} ${label}</small><b>${fmt(value)} / ${fmt(target)} ${unit}</b><i style="width:${p}%"></i><small>${fmt(p)}% da meta</small></button>`}).join("");
}
async function refresh(){
  try{
    const j=await api("/api/day?data="+day.value+"&refeicao="+encodeURIComponent(meal));
    window.lastDaySnapshot=j;
    const consumed=Array.isArray(j.items)?j.items:[];
    const goals=j.goals||{};
    items.innerHTML=consumed.map(x=>"<div class='item'><div><div class='name'>"+esc(x.alimento_nome)+"</div><div class='info'>"+esc(x.refeicao)+" · "+fmt(x.quantidade_g)+" "+esc(x.unidade||"g")+" · "+fmt(x.kcal)+" kcal</div></div><div class='act'><button onclick='edit("+x.id+")'>Alterar</button><button onclick='del("+x.id+")'>Excluir</button></div></div>").join("")||"<div class='empty'>Nenhum alimento neste dia.</div>";
    if(consumed.length){const toggle=document.getElementById("consumedFoodsToggle");items.style.display="block";if(toggle){toggle.textContent="▲";toggle.setAttribute("aria-expanded","true");}}
    try{draw(partial,j.partial||{});}catch(e){console.error("nutrientes:",e)}
    try{drawWater(Number(j.water||0),Number(goals.agua_ml||0),j.water_entries||[]);}catch(e){console.error("hidratação:",e)}
    try{updateHeroFromDay({...j,goals});renderGoalCards({...j,goals});renderBottomProgress({...j,goals});}catch(e){console.error("resumo:",e)}
  }catch(e){console.error("refresh:",e)}
}function pct(v,m){if(!m||m<=0)return 0;return Math.min(100,(v/m)*100)}
function renderBottomProgress(j){
  const g=j.goals||{}, t=j.daily||{}, water=Number(j.water||0);
  const data=[
    ["🔥","Calorias",Number(t.energia_kcal||0),Number(g.calorias_kcal||0),"kcal",false],
    ["💪","Proteína",Number(t.proteina_g||0),Number(g.proteina_g||0),"g",false],
    ["🌱","Fibras",Number(t.fibra_g||0),Number(g.fibras_g||0),"g",false],
    ["💧","Água",water,Number(g.agua_ml||0),"L",true]
  ];
  const el=document.getElementById("bottomProgress");
  if(!el)return;
  el.innerHTML=data.map(x=>{
    const [icon,label,v,m,unit,isWater]=x;
    const p=m>0?Math.min(100,(v/m)*100):0;
    const vv=isWater?fmt(v/1000):fmt(v);
    const mm=isWater?fmt(m/1000):fmt(m);
    return `<div class="bottomGoal">
      <div class="goalRing ${isWater?'water':''}" style="--p:${p}%"><span>${fmt(p)}%</span></div>
      <div class="goalText"><small>${icon} ${label}</small><b>${vv} / ${mm} ${unit}</b><em>Meta diária</em></div>
    </div>`;
  }).join("");
}

const WATER_SILHOUETTES={
  M:"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAGMAAADgCAMAAAAgwSjRAAADAFBMVEX///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////+/LkhhAAABAHRSTlMAAQIDBAUGBwgJCgsMDQ4PEBESExQVFhcYGRobHB0eHyAhIiMkJSYnKCkqKywtLi8wMTIzNDU2Nzg5Ojs8PT4/QEFCQ0RFRkdISUpLTE1O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",
  F:"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAEYAAADgCAMAAACJteBFAAADAFBMVEX///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////+/LkhhAAABAHRSTlMAAQIDBAUGBwgJCgsMDQ4PEBESExQVFhcYGRobHB0eHyAhIiMkJSYnKCkqKywtLi8wMTIzNDU2Nzg5Ojs8PT4/QEFCQ0RFRkdISUpLTE1O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"
};
function waterSilhouette(sex,p){
  const isFemale=sex==="F",asset=isFemale?WATER_SILHOUETTES.F:WATER_SILHOUETTES.M;
  const label=isFemale?"Silhueta feminina com cabelo":sex==="M"?"Silhueta masculina":"Silhueta de hidratação";
  return `<div class="waterFigure"><div class="waterArtwork" role="img" aria-label="${label}" style="--water-level:${Math.min(100,Math.max(0,p))}%;--silhouette:url('${asset}')"></div><div class="waterPercent">${fmt(p)}%<small>consumido</small></div></div>`;
}
let activeWaterCelebration="";
function celebrateWaterGoal(percent){
  if(percent<100)return;
  const key="water-fireworks-v52:"+(day.value||isoDate(new Date()));
  if(activeWaterCelebration===key)return;
  let completed=Number(sessionStorage.getItem(key)||0);
  if(completed>=4)return;
  activeWaterCelebration=key;
  const launch=()=>{
    const host=document.querySelector(".waterVisual");
    if(!host){activeWaterCelebration="";return}
    const colors=["#fbbf24","#f472b6","#38bdf8","#86efac","#fff"];
    for(let i=0;i<24;i++){const spark=document.createElement("i"),angle=(Math.PI*2*i/24)+(Math.random()*.22),distance=28+Math.random()*72;spark.className="waterFirework";spark.style.left=(48+Math.random()*8)+"%";spark.style.top=(30+Math.random()*22)+"%";spark.style.background=colors[i%colors.length];spark.style.setProperty("--dx",Math.cos(angle)*distance+"px");spark.style.setProperty("--dy",Math.sin(angle)*distance+"px");host.appendChild(spark);setTimeout(()=>spark.remove(),850)}
    completed+=1;sessionStorage.setItem(key,String(completed));
    if(completed<4)setTimeout(launch,780);else activeWaterCelebration="";
  };
  launch();
}
function drawWater(w,goal,entries=[]){
  let p=pct(w,goal);
  const recordRows=entries.length?entries.map(x=>`<div style="display:flex;justify-content:space-between;align-items:center;padding:8px 0;border-bottom:1px solid rgba(255,255,255,.10)"><span>💧 ${fmt(Number(x.quantidade_ml)/1000)} L <small style="color:#94a3b8">${esc(x.hora||'')}</small></span><button onclick="deleteWater(${x.id})" style="padding:5px 9px;border-radius:7px;border:1px solid rgba(255,255,255,.15);background:#26364a;color:#fff">Excluir</button></div>`).join(''):`<div style="font-size:12px;color:#94a3b8;margin-top:7px">Nenhum registro de água.</div>`;
  document.getElementById("waterBox").innerHTML=`<div style="display:flex;justify-content:space-between"><b>💧 ${fmt(w/1000)} L</b><span>${fmt(goal/1000)} L meta</span></div><div class="waterVisual">${waterSilhouette(profileSex,p)}</div><div style="font-size:12px;color:#cbd5e1;text-align:center">${fmt(p)}% · ${fmt(Math.max(0,goal-w)/1000)} L restantes</div><div class="waterRecordsHeader"><b>Registros de hoje (${entries.length})</b><button id="waterRecordsToggle" class="waterRecordsToggle" onclick="toggleWaterRecords()" aria-expanded="false">VER REGISTROS ▼</button></div><div id="waterRecords" style="display:none">${recordRows}</div>`;
  setTimeout(()=>celebrateWaterGoal(p),40);
}
function toggleWaterRecords(){const box=document.getElementById("waterRecords"),btn=document.getElementById("waterRecordsToggle");if(!box||!btn)return;const open=box.style.display!=="none";box.style.display=open?"none":"block";btn.textContent=open?"VER REGISTROS ▼":"OCULTAR REGISTROS ▲";btn.setAttribute("aria-expanded",String(!open));}
async function deleteWater(id){if(!confirm("Excluir este registro de água?"))return;try{await api("/api/water/"+id,{method:"DELETE"});await refresh();}catch(e){alert(e.message)}}
function setWaterButtonsBusy(busy){document.querySelectorAll(".waterQuickButtons button").forEach(b=>{b.disabled=busy;b.style.opacity=busy?".65":"1";});}
async function addWater(ml){
  if(window.waterSubmitting)return;
  const previous=window.lastDaySnapshot?JSON.parse(JSON.stringify(window.lastDaySnapshot)):null;
  window.waterSubmitting=true;setWaterButtonsBusy(true);
  if(window.lastDaySnapshot){
    const now=new Date(),hora=String(now.getHours()).padStart(2,"0")+":"+String(now.getMinutes()).padStart(2,"0");
    window.lastDaySnapshot={...window.lastDaySnapshot,water:Number(window.lastDaySnapshot.water||0)+Number(ml),water_entries:[{id:"pending-"+Date.now(),hora,quantidade_ml:Number(ml),pending:true},...(window.lastDaySnapshot.water_entries||[])]};
    const snapshot=window.lastDaySnapshot,goals=snapshot.goals||{};
    drawWater(Number(snapshot.water||0),Number(goals.agua_ml||0),snapshot.water_entries||[]);renderGoalCards(snapshot);renderBottomProgress(snapshot);
  }
  try{await api("/api/water",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({data:day.value,quantidade_ml:ml})});await refresh();}
  catch(e){if(previous){window.lastDaySnapshot=previous;const goals=previous.goals||{};drawWater(Number(previous.water||0),Number(goals.agua_ml||0),previous.water_entries||[]);renderGoalCards(previous);renderBottomProgress(previous);}alert("Não foi possível registrar a água: "+e.message)}
  finally{window.waterSubmitting=false;setWaterButtonsBusy(false);}
}
async function customWater(){let v=prompt("Quantidade de água em ml:","500");if(v===null)return;let ml=Number(v);if(!(ml>0)){alert("Quantidade inválida.");return}await addWater(ml)}
async function openSummary(){let j=await api("/api/summary?data="+day.value);document.getElementById("goalModeNotice").textContent=j.goals.manual_override?"As metas atuais foram ajustadas manualmente e não serão substituídas ao salvar o perfil ou recalcular os dados.":"As metas atuais estão no modo automático e podem ser atualizadas pelo cálculo do perfil.";let a=[['energia_kcal','calorias_kcal','🔥 Calorias','kcal'],['proteina_g','proteina_g','💪 Proteína','g'],['carboidrato_g','carboidratos_g','🍚 Carboidratos','g'],['lipidios_g','gorduras_g','🥑 Gorduras','g'],['fibra_g','fibras_g','🌱 Fibras','g'],['sodio_mg','sodio_mg','🧂 Sódio','mg']];document.getElementById("summaryContent").innerHTML=a.map(x=>{let v=Number(j.daily[x[0]]||0),m=Number(j.goals[x[1]]||0),p=pct(v,m),left=Math.max(0,m-v);return `<div class="metric nutrient-source" data-nutrient="${x[0]}" data-start="${day.value}" data-end="${day.value}" style="margin-bottom:8px"><small>${x[2]} ⓘ</small><b>${fmt(v)} / ${fmt(m)} ${x[3]}</b><div style="height:10px;background:#e5e7eb;border-radius:20px;overflow:hidden"><div style="height:100%;width:${p}%;background:#22a447"></div></div><small>${m>0?(x[1]==='sodio_mg'?'Restam ':'Faltam ')+fmt(left)+' '+x[3]:''}</small></div>`}).join('')+`<div class="metric"><small>💧 Água</small><b>${fmt(j.water/1000)} / ${fmt(Number(j.goals.agua_ml||0)/1000)} L</b><div style="height:10px;background:#e5e7eb;border-radius:20px;overflow:hidden"><div style="height:100%;width:${pct(j.water,Number(j.goals.agua_ml||0))}%;background:#1683ff"></div></div><small>${Number(j.goals.agua_ml||0)>0?fmt(Math.max(0,Number(j.goals.agua_ml)-Number(j.water))/1000)+' L restantes':''}</small></div>`;document.getElementById("goalForm").innerHTML=[['calorias_kcal','🔥 Calorias','kcal'],['proteina_g','💪 Proteína','g'],['carboidratos_g','🍚 Carboidratos','g'],['gorduras_g','🥑 Gorduras','g'],['fibras_g','🌱 Fibras','g'],['sodio_mg','🧂 Sódio','mg'],['agua_ml','💧 Água','ml']].map(x=>`<div class="metric"><small>${x[1]}</small><input id="g_${x[0]}" type="number" step="0.01" value="${j.goals[x[0]]??''}" style="width:100%;padding:9px;border:1px solid #ddd;border-radius:8px"><small>${x[2]}</small></div>`).join('');document.getElementById("summaryModal").style.display="block"}
function closeSummary(){document.getElementById("summaryModal").style.display="none"}
async function saveGoals(){let d={manual_override:true};for(const k of ['calorias_kcal','proteina_g','carboidratos_g','gorduras_g','fibras_g','sodio_mg','agua_ml'])d[k]=Number(document.getElementById('g_'+k).value)||0;await api('/api/goals',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(d)});await refresh();await openSummary();alert('Metas manuais salvas.')}
async function applyCalculatedGoals(){
  if(!confirm('Aplicar novamente as metas calculadas com base no perfil atual? Isso substituirá os valores manuais.'))return;
  const goals=calculateProfileGoals();
  if(!goals)return;
  await api('/api/goals',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({...goals,manual_override:false})});
  await refresh();
  await openSummary();
  alert('Metas calculadas aplicadas.');
}

function isoDate(d){
  const y=d.getFullYear(),m=String(d.getMonth()+1).padStart(2,'0'),day=String(d.getDate()).padStart(2,'0');
  return `${y}-${m}-${day}`;
}
function shiftDays(base,n){const d=new Date(base+"T12:00:00");d.setDate(d.getDate()+n);return isoDate(d);}
function setPeriod(days){
  const end=day.value || isoDate(new Date());
  document.getElementById("periodEnd").value=end;
  document.getElementById("periodStart").value=shiftDays(end,-(days-1));
  loadPeriod();
}
function openPeriod(){
  const end=day.value || isoDate(new Date());
  document.getElementById("periodEnd").value=end;
  document.getElementById("periodStart").value=shiftDays(end,-6);
  document.getElementById("periodModal").style.display="block";
  loadPeriod();
}
function closePeriod(){document.getElementById("periodModal").style.display="none";}
async function downloadReport(){
  const start=document.getElementById("periodStart").value,end=document.getElementById("periodEnd").value,button=document.getElementById("downloadReportBtn");
  if(!start||!end||start>end){alert("Informe um período válido antes de gerar o relatório.");return}
  const days=Math.round((new Date(end+"T12:00:00")-new Date(start+"T12:00:00"))/86400000)+1;
  if(days<1||days>90){alert("Escolha um período entre 1 e 90 dias.");return}
  try{
    if(button){button.disabled=true;button.textContent="GERANDO PDF..."}
    const response=await fetch("/api/report.pdf?start="+encodeURIComponent(start)+"&end="+encodeURIComponent(end),{credentials:"same-origin"});
    if(!response.ok){let message="Não foi possível gerar o relatório.";try{message=(await response.json()).error||message}catch(e){}throw new Error(message)}
    const blob=await response.blob(),url=URL.createObjectURL(blob),link=document.createElement("a");
    link.href=url;link.download="resumo_alimentacao_"+start+"_"+end+".pdf";document.body.appendChild(link);link.click();link.remove();setTimeout(()=>URL.revokeObjectURL(url),1500);
  }catch(error){alert(error.message||"Não foi possível gerar o relatório PDF.")}
  finally{if(button){button.disabled=false;button.textContent="⬇️ BAIXAR RELATÓRIO PDF"}}
}
async function loadHistory(start,end){
  const box=document.getElementById("historyChart");if(!box)return;
  try{const j=await api("/api/history?start="+encodeURIComponent(start)+"&end="+encodeURIComponent(end));const max=Math.max(1,...j.days.map(x=>Number(x.energia_kcal||0)));box.innerHTML="<h3 style='margin:8px 0'>📈 Evolução diária</h3>"+`<div style='display:grid;grid-template-columns:repeat(${Math.min(14,Math.max(1,j.days.length))},minmax(28px,1fr));gap:6px;align-items:end;height:190px;padding:12px;background:#172033;border-radius:12px'>`+j.days.map(x=>{const pct=Math.max(3,Math.round(Number(x.energia_kcal||0)/max*100));const d=x.data.slice(5).split('-').reverse().join('/');return `<div title='${d}: ${fmt(x.energia_kcal)} kcal · ${fmt(x.proteina_g)} g proteína · ${fmt(x.agua_ml)} ml água' style='display:flex;flex-direction:column;align-items:center;justify-content:end;height:100%;gap:4px'><small style='font-size:10px;color:#cbd5e1'>${fmt(x.energia_kcal)}</small><div style='width:100%;height:${pct}%;min-height:5px;background:linear-gradient(#22c55e,#166534);border-radius:6px 6px 2px 2px'></div><small style='font-size:10px;color:#cbd5e1'>${d}</small></div>`}).join("")+"</div><small style='display:block;color:#9fb0c4;margin-top:6px'>Passe o cursor sobre uma barra para ver calorias, proteína e água do dia.</small>"}catch(e){box.innerHTML=""}
}
function periodCard(key,label,icon,total,goal,unit,days,limit=false,start, end){
  total=Number(total||0);goal=Number(goal||0);
  const avg=days>0?total/days:0;
  const target=goal*days;
  const pct=target>0?Math.min(100,total/target*100):0;
  const diff=target-total;
  const text=goal>0 ? (limit ? (diff>=0?`Dentro do limite · restam ${fmt(diff)} ${unit}`:`Acima do limite em ${fmt(-diff)} ${unit}`)
                     : (diff>=0?`Faltam ${fmt(diff)} ${unit}`:`Meta superada em ${fmt(-diff)} ${unit}`)) : "Meta não cadastrada";
  return `<div class="metric nutrient-source" data-nutrient="${key}" data-start="${start}" data-end="${end}" style="margin-bottom:9px">
    <small>${icon} ${label}</small>
    <b>${fmt(total)} ${unit} / ${fmt(target)} ${unit}</b>
    <div style="height:10px;background:#e5e7eb;border-radius:20px;overflow:hidden">
      <div style="height:100%;width:${pct}%;background:#22a447"></div>
    </div>
    <small>${fmt(pct)}% da meta do período · média ${fmt(avg)} ${unit}/dia<br>${text}</small>
  </div>`;
}
async function loadPeriod(){
  const s=document.getElementById("periodStart").value,e=document.getElementById("periodEnd").value;
  if(!s||!e){alert("Informe as duas datas.");return;}
  if(s>e){alert("A data inicial não pode ser maior que a final.");return;}
  try{
    const j=await api("/api/period?start="+encodeURIComponent(s)+"&end="+encodeURIComponent(e));
    const days=j.days;
    document.getElementById("periodInfo").innerHTML=
      `<div style="padding:10px;background:#f8fafc;border-radius:10px;font-size:13px">
        <b>${j.start_br} a ${j.end_br}</b> · ${days} ${days===1?"dia":"dias"}<br>
        O consumo é o total realmente registrado no diário nesse intervalo.
      </div>`;
    const g=j.goals;
    document.getElementById("periodContent").innerHTML=
      `<h3 style="margin:14px 0 8px">📊 Principais nutrientes</h3>`+
      periodCard("energia_kcal","Calorias","🔥",j.daily.energia_kcal,g.calorias_kcal,"kcal",days,false,j.start,j.end)+
      periodCard("proteina_g","Proteína","💪",j.daily.proteina_g,g.proteina_g,"g",days,false,j.start,j.end)+
      periodCard("carboidrato_g","Carboidratos","🍚",j.daily.carboidrato_g,g.carboidratos_g,"g",days,false,j.start,j.end)+
      periodCard("lipidios_g","Gorduras","🥑",j.daily.lipidios_g,g.gorduras_g,"g",days,false,j.start,j.end)+
      periodCard("fibra_g","Fibras","🌱",j.daily.fibra_g,g.fibras_g,"g",days,false,j.start,j.end)+
      periodCard("sodio_mg","Sódio","🧂",j.daily.sodio_mg,g.sodio_mg,"mg",days,true,j.start,j.end)+
      periodCard("","Água","💧",j.water,g.agua_ml,"ml",days,false,j.start,j.end)+
      `<details style="margin-top:12px"><summary style="font-weight:bold;cursor:pointer">🔬 Ver micronutrientes</summary>
        <div class="metrics" style="margin-top:8px">${[
          ["calcio_mg","Cálcio","mg"],["magnesio_mg","Magnésio","mg"],["manganes_mg","Manganês","mg"],
          ["fosforo_mg","Fósforo","mg"],["ferro_mg","Ferro","mg"],["potassio_mg","Potássio","mg"],
          ["cobre_mg","Cobre","mg"],["zinco_mg","Zinco","mg"],["vitamina_c_mg","Vitamina C","mg"],
          ["tiamina_mg","B1","mg"],["riboflavina_mg","B2","mg"],["niacina_mg","B3","mg"],
          ["piridoxina_mg","B6","mg"],["colesterol_mg","Colesterol","mg"]
        ].map(x=>`<div class="metric nutrient-source" data-nutrient="${x[0]}" data-start="${j.start}" data-end="${j.end}"><small>${x[1]} ⓘ</small><b>${fmt(j.daily[x[0]])} ${x[2]}</b><small>Média: ${fmt(Number(j.daily[x[0]]||0)/days)} ${x[2]}/dia</small></div>`).join("")}</div>
      </details>`;
    loadHistory(s,e);
  }catch(err){alert("Não foi possível carregar o período: "+err.message);}
}

function draw(el,t){
  let a=[["energia_kcal","Calorias","kcal"],["proteina_g","Proteína","g"],["carboidrato_g","Carboidratos","g"],["lipidios_g","Gorduras","g"],["fibra_g","Fibras","g"],["calcio_mg","Cálcio","mg"],["magnesio_mg","Magnésio","mg"],["manganes_mg","Manganês","mg"],["fosforo_mg","Fósforo","mg"],["ferro_mg","Ferro","mg"],["sodio_mg","Sódio","mg"],["potassio_mg","Potássio","mg"],["cobre_mg","Cobre","mg"],["zinco_mg","Zinco","mg"],["vitamina_c_mg","Vitamina C","mg"],["tiamina_mg","B1","mg"],["riboflavina_mg","B2","mg"],["niacina_mg","B3","mg"],["piridoxina_mg","B6","mg"],["colesterol_mg","Colesterol","mg"]];
  el.innerHTML=a.map(n=>"<div class='metric nutrient-source' data-nutrient='"+n[0]+"' data-start='"+day.value+"' data-end='"+day.value+"'><small>"+n[1]+" ⓘ</small><b>"+fmt(t[n[0]])+"</b><small>"+n[2]+"</small></div>").join("");
  if(el===daily){
    document.getElementById("heroKcal").textContent=fmt(t.energia_kcal)+" kcal";
    document.getElementById("heroProtein").textContent=fmt(t.proteina_g)+" g";
    document.getElementById("heroFiber").textContent=fmt(t.fibra_g)+" g";
  }
}
async function del(id){if(confirm("Excluir este alimento?")){await api("/api/consume/"+id,{method:"DELETE"});refresh()}}
let editingConsumeId=null;
async function edit(id){
  try{
    const j=await api("/api/consume/"+id),x=j.item;
    editingConsumeId=Number(id);
    document.getElementById("consumeEditTitle").textContent="✏️ Alterar · "+(x.alimento_nome||"Alimento");
    document.getElementById("consumeEditWeight").value=Number(x.quantidade_g)||"";
    document.getElementById("consumeEditUnit").value=x.unidade==="ml"?"ml":"g";
    document.getElementById("consumeEditMeal").value=meals.includes(x.refeicao)?x.refeicao:meals[0];
    document.getElementById("consumeEditModal").style.display="block";
  }catch(e){alert("Não foi possível abrir este consumo: "+e.message)}
}
function closeConsumeEdit(){editingConsumeId=null;document.getElementById("consumeEditModal").style.display="none"}
async function saveConsumeEdit(){
  const w=Number(document.getElementById("consumeEditWeight").value),r=document.getElementById("consumeEditMeal").value,u=document.getElementById("consumeEditUnit").value;
  if(!editingConsumeId||!(w>0)||!meals.includes(r)){alert("Informe uma quantidade válida e selecione uma refeição.");return}
  try{
    await api("/api/consume/"+editingConsumeId,{method:"PUT",headers:{"Content-Type":"application/json"},body:JSON.stringify({quantidade_g:w,unidade:u,refeicao:r})});
    closeConsumeEdit();await refresh();
  }catch(e){alert("Não foi possível salvar a alteração: "+e.message)}
}
const searchEl=document.getElementById("search"),foods=document.getElementById("foods"),items=document.getElementById("items"),partial=document.getElementById("partial"),daily=document.getElementById("daily"),sel=document.getElementById("sel"),mealsEl=document.getElementById("meals"),pm=document.getElementById("pm");
searchEl.oninput=()=>{clearTimeout(searchTimer);searchTimer=setTimeout(search,40)};bootstrap();
</script></body></html>
"""
HTML = HTML.replace("V45 · Diário Alimentar · Segurança P0", "V55 · Diário Alimentar · Bebidas em ml").replace("V45 · DIÁRIO ALIMENTAR", "V55 · DIÁRIO ALIMENTAR").replace("<title>V43 - Diário Alimentar · Base pessoal confirmada</title>", "<title>V55 · Diário Alimentar · Bebidas em ml</title>")

class H(BaseHTTPRequestHandler):
    def end_headers(self):
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        self.send_header("Permissions-Policy", "camera=(self), microphone=(), geolocation=()")
        self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'; object-src 'none'; form-action 'self'")
        if IS_PRODUCTION:
            self.send_header("Strict-Transport-Security", "max-age=31536000; includeSubDomains")
        super().end_headers()
    def js(self,o,s=200,headers=None):
        if isinstance(o, dict) and isinstance(o.get("error"), str):
            o = {**o, "error": public_error_message(o["error"])}
        b=json.dumps(o,ensure_ascii=False,default=json_default).encode();self.send_response(s);self.send_header("Content-Type", "application/json; charset=utf-8");self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0");self.send_header("Content-Length",str(len(b)));
        for k,v in (headers or {}).items(): self.send_header(k,v)
        self.end_headers();self.wfile.write(b)
    def client_ip(self):
        forwarded = self.headers.get("X-Forwarded-For", "")
        return forwarded.split(",", 1)[0].strip() if forwarded else self.client_address[0]
    def enforce_rate_limit(self, action, limit, window_seconds, user_id=None):
        identity = f"user:{user_id}" if user_id else f"ip:{self.client_ip()}"
        if allow_request(f"{action}:{identity}", limit, window_seconds):
            return True
        self.js({"error":"Muitas tentativas. Aguarde alguns minutos antes de tentar novamente."}, 429)
        return False
    def body(self, image=False):
        try:
            size = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            raise ValueError("Tamanho da requisição inválido.")
        limit = MAX_IMAGE_BODY if image else MAX_JSON_BODY
        if size < 0 or size > limit:
            raise ValueError("A requisição excede o tamanho permitido.")
        try:
            payload = json.loads(self.rfile.read(size).decode() or "{}")
        except (UnicodeDecodeError, json.JSONDecodeError):
            raise ValueError("JSON inválido.")
        if not isinstance(payload, dict):
            raise ValueError("O corpo da requisição deve ser um objeto JSON.")
        return payload
    def csrf_token(self):
        token = _cookie_value(self, SESSION_COOKIE)
        return _csrf_for_token(token) if token else ""
    def verify_csrf(self):
        origin = self.headers.get("Origin", "")
        host = self.headers.get("Host", "")
        if origin and urlparse(origin).netloc != host:
            self.js({"error":"Origem da requisição não permitida."}, 403)
            return False
        supplied = self.headers.get("X-CSRF-Token", "")
        expected = self.csrf_token()
        if not expected or not supplied or not hmac.compare_digest(supplied, expected):
            self.js({"error":"Sessão expirada. Atualize a página e tente novamente."}, 403)
            return False
        return True
    def safe_error(self, error, status=400, message="Não foi possível concluir a solicitação."):
        LOG.warning("request_failed path=%s method=%s type=%s", self.path, self.command, type(error).__name__, exc_info=True)
        self.js({"error":message}, status)
    def require_user(self):
        user=_current_user(self)
        if not user:
            self.js({"error":"Autenticação necessária"},401)
            return None
        c=ddb()
        try:
            _ensure_user_records(c,user["id"])
            c.commit()
        finally:
            c.close()
        self.user=user
        return user
    def do_GET(self):
        p=urlparse(self.path)
        if p.path=="/":
            b=HTML.encode();self.send_response(200);self.send_header("Content-Type","text/html; charset=utf-8");self.send_header("Cache-Control","no-store, no-cache, must-revalidate, max-age=0");self.send_header("Pragma","no-cache");self.send_header("Content-Length",str(len(b)));self.end_headers();self.wfile.write(b);return
        if p.path=="/health":
            self.send_response(200);self.send_header("Content-Type","text/plain; charset=utf-8");self.send_header("Cache-Control","no-store");self.end_headers();self.wfile.write(APP_VERSION.encode("utf-8"));return
        if p.path=="/api/me":
            user=_current_user(self)
            if user:self.js({"authenticated":True,"user":user,"csrf":self.csrf_token()})
            else:self.js({"authenticated":False})
            return
        if p.path=="/api/auth/logout":
            token=_cookie_value(self,SESSION_COOKIE);c=ddb()
            try:
                if token:c.execute("DELETE FROM sessoes WHERE token_hash=?",(_token_hash(token),));c.commit()
            finally:c.close()
            self.js({"ok":True},headers={"Set-Cookie":_session_cookie("",0)});return
        if p.path=="/a_wide_high_resolution_panoramic_landscape_photo.png":
            img=BASE/"a_wide_high_resolution_panoramic_landscape_photo.png"
            if not img.exists():
                self.send_error(404);return
            b=img.read_bytes()
            self.send_response(200)
            self.send_header("Content-Type","image/png")
            self.send_header("Cache-Control","no-store, no-cache, must-revalidate, max-age=0")
            self.send_header("Content-Length",str(len(b)))
            self.end_headers()
            self.wfile.write(b)
            return

        user=self.require_user()
        if not user:return

        if p.path=="/api/profile":
            c=ddb()
            try:r=c.execute("SELECT * FROM perfis WHERE usuario_id=?",(self.user["id"],)).fetchone()
            finally:c.close()
            self.js(dict(r) if r else {"nome":""})
            return

        if p.path=="/api/goals":
            c=ddb()
            try:g=c.execute("SELECT * FROM metas_usuario WHERE usuario_id=?",(self.user["id"],)).fetchone()
            finally:c.close()
            self.js(goal_dict(g))
            return

        if p.path=="/api/foods":
            q=parse_qs(p.query).get("q",[""])[0].strip().lower()[:60]
            if len(q)<2:self.js({"foods":[]});return
            nc=ndb();pc=ddb()
            try:
                prefix=f"{q}%";contains=f"%{q}%"
                base=list(nc.execute("SELECT id,nome,'g' AS unidade FROM alimentos WHERE nome LIKE ? COLLATE NOCASE ORDER BY nome LIMIT 30",(prefix,)).fetchall())
                own=list(pc.execute("SELECT -id AS id,nome,CASE WHEN base_calculo='100ml' OR LOWER(COALESCE(porcao_unidade,''))='ml' THEN 'ml' ELSE 'g' END AS unidade FROM alimentos_usuario WHERE usuario_id=? AND nome ILIKE ? ORDER BY nome LIMIT 30",(self.user["id"],prefix)).fetchall())
                if len(base)<20:
                    extra=nc.execute("SELECT id,nome,'g' AS unidade FROM alimentos WHERE nome LIKE ? COLLATE NOCASE AND nome NOT LIKE ? COLLATE NOCASE ORDER BY nome LIMIT ?",(contains,prefix,30-len(base))).fetchall();base.extend(extra)
                if len(own)<20:
                    extra=pc.execute("SELECT -id AS id,nome,CASE WHEN base_calculo='100ml' OR LOWER(COALESCE(porcao_unidade,''))='ml' THEN 'ml' ELSE 'g' END AS unidade FROM alimentos_usuario WHERE usuario_id=? AND nome ILIKE ? AND nome NOT ILIKE ? ORDER BY nome LIMIT ?",(self.user["id"],contains,prefix,30-len(own))).fetchall();own.extend(extra)
            finally:
                nc.close();pc.close()
            self.js({"foods":[dict(x) for x in own+base][:40]});return
        if p.path=="/api/day":
            q=parse_qs(p.query);d=q.get("data",[date.today().isoformat()])[0];m=q.get("refeicao",[MEALS[0]])[0];c=ddb()
            try:rows=c.execute("SELECT * FROM consumo WHERE usuario_id=? AND data=? ORDER BY id",(self.user["id"],d,)).fetchall()
            finally:c.close()
            nc=ndb();pc=ddb();items=[]
            try:
                for x in rows:
                    aid=int(x["alimento_id"])
                    f=pc.execute("SELECT energia_kcal FROM alimentos_usuario WHERE id=? AND usuario_id=?",(-aid,self.user["id"])).fetchone() if aid<0 else nc.execute("SELECT energia_kcal FROM alimentos WHERE id=?",(aid,)).fetchone()
                    z=x["quantidade_g"]/100
                    items.append({"id":x["id"],"refeicao":x["refeicao"],"alimento_nome":x["alimento_nome"],"quantidade_g":x["quantidade_g"],"unidade":x.get("unidade","g"),"kcal":(f["energia_kcal"] or 0)*z if f else 0})
            finally:
                nc.close();pc.close()
            c=ddb()
            try:
                water=c.execute("SELECT COALESCE(SUM(quantidade_ml),0) AS total_water FROM hidratacao WHERE usuario_id=? AND data=?",(self.user["id"],d,)).fetchone()["total_water"]
                water_entries=c.execute("SELECT id,hora,quantidade_ml FROM hidratacao WHERE usuario_id=? AND data=? ORDER BY id DESC",(self.user["id"],d,)).fetchall()
                g=c.execute("SELECT * FROM metas_usuario WHERE usuario_id=?",(self.user["id"],)).fetchone()
            finally:
                c.close()
            self.js({"items":items,"daily":calc(rows,self.user["id"]),"partial":calc([x for x in rows if x["refeicao"]==m],self.user["id"]),"water":float(water or 0),"water_entries":[dict(x) for x in water_entries],"goals":goal_dict(g)});return
        if p.path.startswith("/api/food/"):
            try: food_id=int(p.path.rsplit("/",1)[1])
            except ValueError:
                self.js({"error":"ID inválido"},400);return
            if food_id<0:
                c=ddb()
                try: row=c.execute("SELECT * FROM alimentos_usuario WHERE id=? AND usuario_id=?",(-food_id,self.user["id"])).fetchone()
                finally:c.close()
                data=dict(row) if row else None
                if data:data["id"]=food_id
            else:
                c=ndb()
                try: row=c.execute("SELECT * FROM alimentos WHERE id=?",(food_id,)).fetchone()
                finally:c.close()
                data=dict(row) if row else None
            self.js({"food":data} if data else {"error":"Alimento não encontrado"},200 if data else 404);return


        if p.path=="/api/nutrient_sources":
            q=parse_qs(p.query)
            nutrient=q.get("nutrient",[""])[0]
            start=q.get("start",[q.get("data",[date.today().isoformat()])[0]])[0]
            end=q.get("end",[start])[0]
            if nutrient not in [x[0] for x in NUTS]:
                self.js({"error":"Nutriente inválido"},400);return
            c=ddb()
            try:
                rows=c.execute("SELECT * FROM consumo WHERE usuario_id=? AND data>=? AND data<=? ORDER BY data,id",(self.user["id"],start,end)).fetchall()
            finally:c.close()
            nc=ndb();pc=ddb();sources=[]
            try:
                for r in rows:
                    aid=int(r["alimento_id"]);f=pc.execute("SELECT * FROM alimentos_usuario WHERE id=? AND usuario_id=?",(-aid,self.user["id"])).fetchone() if aid<0 else nc.execute("SELECT * FROM alimentos WHERE id=?",(aid,)).fetchone()
                    if not f or nutrient not in f.keys() or f[nutrient] is None: continue
                    amount=float(f[nutrient])*float(r["quantidade_g"])/100.0
                    if abs(amount)<0.000001: continue
                    sources.append({"nome":r["alimento_nome"],"quantidade_g":float(r["quantidade_g"]),"unidade":r.get("unidade","g"),"refeicao":r["refeicao"],"data":r["data"],"valor":amount})
            finally:
                nc.close();pc.close()
            sources.sort(key=lambda x:x["valor"],reverse=True)
            self.js({"nutrient":nutrient,"total":sum(x["valor"] for x in sources),"sources":sources})
            return

        if p.path=="/api/history":
            q=parse_qs(p.query);start=q.get("start",[date.today().isoformat()])[0];end=q.get("end",[start])[0]
            c=ddb()
            try:
                rows=c.execute("SELECT * FROM consumo WHERE usuario_id=? AND data>=? AND data<=? ORDER BY data,id",(self.user["id"],start,end)).fetchall()
                waters=c.execute("SELECT data,COALESCE(SUM(quantidade_ml),0) AS water FROM hidratacao WHERE usuario_id=? AND data>=? AND data<=? GROUP BY data ORDER BY data",(self.user["id"],start,end)).fetchall()
            finally:c.close()
            by_day={}
            for r in rows:by_day.setdefault(r["data"],[]).append(r)
            wmap={x["data"]:float(x["water"] or 0) for x in waters};d1=date.fromisoformat(start);d2=date.fromisoformat(end);out=[];cur=d1
            while cur<=d2:
                ds=cur.isoformat();t=calc(by_day.get(ds,[]),self.user["id"]);out.append({"data":ds,"energia_kcal":t["energia_kcal"],"proteina_g":t["proteina_g"],"agua_ml":wmap.get(ds,0)});cur+=timedelta(days=1)
            self.js({"days":out});return
        if p.path=="/api/period":
            q=parse_qs(p.query)
            start=q.get("start",[""])[0]
            end=q.get("end",[""])[0]
            try:
                d1=date.fromisoformat(start);d2=date.fromisoformat(end)
                if d1>d2: raise ValueError("Período inválido")
            except Exception as e:
                self.js({"error":"Datas inválidas"},400);return
            c=ddb()
            try:
                rows=c.execute("SELECT * FROM consumo WHERE usuario_id=? AND data>=? AND data<=? ORDER BY data,id",(self.user["id"],start,end)).fetchall()
                water=c.execute("SELECT COALESCE(SUM(quantidade_ml),0) AS total_water FROM hidratacao WHERE usuario_id=? AND data>=? AND data<=?",(self.user["id"],start,end)).fetchone()["total_water"]
                g=c.execute("SELECT * FROM metas_usuario WHERE usuario_id=?",(self.user["id"],)).fetchone()
            finally:c.close()
            days=(d2-d1).days+1
            self.js({
                "start":start,"end":end,"days":days,
                "start_br":d1.strftime("%d/%m/%Y"),"end_br":d2.strftime("%d/%m/%Y"),
                "daily":calc(rows,self.user["id"]),"water":float(water or 0),"goals":goal_dict(g)
            })
            return

        if p.path=="/api/report.pdf":
            q = parse_qs(p.query)
            start = q.get("start", [date.today().isoformat()])[0]
            end = q.get("end", [start])[0]
            if not allow_request(f"report:{self.user['id']}", 6, 600):
                self.js({"error":"Muitas solicitações de relatório. Aguarde alguns minutos."}, 429)
                return
            try:
                pdf_data = build_food_report_pdf(self.user["id"], start, end)
            except ValueError as error:
                self.js({"error": public_error_message(error)}, 400)
                return
            except Exception as error:
                LOG.warning("report_pdf_failed user_id=%s", self.user["id"], exc_info=True)
                self.js({"error":"Não foi possível gerar o relatório PDF. Tente novamente."}, 500)
                return
            filename = f"resumo_alimentacao_{start}_{end}.pdf"
            self.send_response(200)
            self.send_header("Content-Type", "application/pdf")
            self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Content-Length", str(len(pdf_data)))
            self.end_headers()
            self.wfile.write(pdf_data)
            return

        if p.path=="/api/summary":
            q=parse_qs(p.query);d=q.get("data",[date.today().isoformat()])[0];c=ddb()
            try:
                rows=c.execute("SELECT * FROM consumo WHERE usuario_id=? AND data=?",(self.user["id"],d,)).fetchall();water=c.execute("SELECT COALESCE(SUM(quantidade_ml),0) AS total_water FROM hidratacao WHERE usuario_id=? AND data=?",(self.user["id"],d,)).fetchone()["total_water"];g=c.execute("SELECT * FROM metas_usuario WHERE usuario_id=?",(self.user["id"],)).fetchone()
            finally:c.close()
            self.js({"daily":calc(rows,self.user["id"]),"water":float(water or 0),"goals":goal_dict(g)})
            return
        if p.path=="/api/water":
            q=parse_qs(p.query);d=q.get("data",[date.today().isoformat()])[0];c=ddb()
            try: rows=c.execute("SELECT id,hora,quantidade_ml FROM hidratacao WHERE usuario_id=? AND data=? ORDER BY id DESC",(self.user["id"],d,)).fetchall()
            finally:c.close()
            self.js([dict(r) for r in rows]);return

        if p.path=="/api/favorites":
            c=ddb()
            try:r=c.execute("SELECT id,alimento_id,alimento_nome,criado_em FROM favoritos WHERE usuario_id=? ORDER BY alimento_nome",(self.user["id"],)).fetchall()
            finally:c.close()
            self.js([dict(x) for x in r]);return
        if p.path=="/api/portions":
            c=ddb()
            try:r=c.execute("SELECT id,alimento_id,alimento_nome,nome,quantidade_g,unidade FROM porcoes WHERE usuario_id=? ORDER BY alimento_nome,nome",(self.user["id"],)).fetchall()
            finally:c.close()
            self.js([dict(x) for x in r]);return
        if p.path.startswith("/api/consume/"):
            i=int(p.path.rsplit("/",1)[1]);c=ddb()
            try:r=c.execute("SELECT * FROM consumo WHERE id=? AND usuario_id=?",(i,self.user["id"])).fetchone()
            finally:c.close()
            self.js({"item":dict(r)} if r else {"error":"Não encontrado"},200 if r else 404);return
        self.send_error(404)
    def do_POST(self):
        if self.path=="/api/auth/register":
            c=None
            try:
                if not self.enforce_rate_limit("register",3,3600): return
                x=self.body();email=str(x.get("email","")).strip().lower();password=str(x.get("password",""))
                if not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+",email): raise ValueError("Informe um e-mail válido.")
                if len(password)<8: raise ValueError("A senha deve ter pelo menos 8 caracteres.")
                c=ddb();existing=int(c.execute("SELECT COUNT(*) AS n FROM usuarios").fetchone()["n"])
                row=c.execute("INSERT INTO usuarios(email,senha_hash) VALUES(?,?) RETURNING id,email",(email,_hash_password(password))).fetchone()
                _ensure_user_records(c,row["id"],migrate_legacy=(existing==0));token=secrets.token_urlsafe(32)
                c.execute("INSERT INTO sessoes(usuario_id,token_hash,expira_em) VALUES(?,?,NOW()+INTERVAL '30 days')",(row["id"],_token_hash(token)));c.commit()
                self.js({"ok":True,"user":{"id":row["id"],"email":row["email"]},"csrf":_csrf_for_token(token)},headers={"Set-Cookie":_session_cookie(token)})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":"Não foi possível criar a conta: "+str(e)},400)
            finally:
                if c:c.close()
            return
        if self.path=="/api/auth/login":
            c=None
            try:
                if not self.enforce_rate_limit("login",5,900): return
                x=self.body();email=str(x.get("email","")).strip().lower();password=str(x.get("password",""));c=ddb()
                row=c.execute("SELECT id,email,senha_hash FROM usuarios WHERE email=?",(email,)).fetchone()
                if not row or not _verify_password(password,row["senha_hash"]): raise ValueError("E-mail ou senha inválidos.")
                token=secrets.token_urlsafe(32);c.execute("INSERT INTO sessoes(usuario_id,token_hash,expira_em) VALUES(?,?,NOW()+INTERVAL '30 days')",(row["id"],_token_hash(token)));c.commit()
                self.js({"ok":True,"user":{"id":row["id"],"email":row["email"]},"csrf":_csrf_for_token(token)},headers={"Set-Cookie":_session_cookie(token)})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},401)
            finally:
                if c:c.close()
            return
        if self.path=="/api/auth/logout":
            if not self.verify_csrf(): return
            token=_cookie_value(self,SESSION_COOKIE);c=ddb()
            try:
                if token:c.execute("DELETE FROM sessoes WHERE token_hash=?",(_token_hash(token),));c.commit()
            finally:c.close()
            self.js({"ok":True},headers={"Set-Cookie":_session_cookie("",0)});return
        user=self.require_user()
        if not user:return
        if not self.verify_csrf(): return
        if self.path=="/api/favorite":
            c=None
            try:
                x=self.body();aid=int(x.get("alimento_id"));nome=str(x.get("alimento_nome","")).strip()
                if not nome:raise ValueError("Nome do alimento obrigatório.")
                c=ddb();c.execute("INSERT INTO favoritos(usuario_id,alimento_id,alimento_nome) VALUES(?,?,?) ON CONFLICT(usuario_id,alimento_id) DO UPDATE SET alimento_nome=EXCLUDED.alimento_nome",(self.user["id"],aid,nome));c.commit();self.js({"ok":True})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return
        if self.path=="/api/portion":
            c=None
            try:
                x=self.body();aid=int(x.get("alimento_id"));nome=str(x.get("alimento_nome","")).strip();label=str(x.get("nome","")).strip();q=float(x.get("quantidade_g",0));unidade=str(x.get("unidade","g")).lower()
                if unidade not in ("g","ml"): raise ValueError("Unidade inválida.")
                if not nome or not label or q<=0:raise ValueError("Informe nome, porção e quantidade válida.")
                c=ddb();c.execute("INSERT INTO porcoes(usuario_id,alimento_id,alimento_nome,nome,quantidade_g,unidade) VALUES(?,?,?,?,?,?) ON CONFLICT(usuario_id,alimento_id,nome) DO UPDATE SET quantidade_g=EXCLUDED.quantidade_g,unidade=EXCLUDED.unidade,alimento_nome=EXCLUDED.alimento_nome",(self.user["id"],aid,nome,label,q,unidade));c.commit();self.js({"ok":True})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return
        if self.path=="/api/analyze_plate":
            try:
                if not self.enforce_rate_limit("vision-user",10,3600,self.user["id"]): return
                if not self.enforce_rate_limit("vision-ip",20,3600): return
                if not os.environ.get("OPENAI_API_KEY"): raise ValueError("A análise de prato requer OPENAI_API_KEY configurada no Render.")
                if OpenAI is None: raise ValueError("A dependência openai não está instalada.")
                x=self.body(image=True);image=str(x.get("image_data", ""))
                validate_image_data(image)
                client_args={"api_key":os.environ.get("OPENAI_API_KEY")}
                if os.environ.get("OPENAI_API_BASE"): client_args["base_url"]=os.environ.get("OPENAI_API_BASE")
                nutrient_schema={field:"número estimado por 100 g ou null" for field in ESTIMATED_NUTRIENT_FIELDS}
                schema={"items":[{"nome":"nome comum do alimento em português","quantidade_g":"número estimado","colheres_sopa":"número estimado ou null","confianca":"número de 0 a 1","nutrientes_por_100g":nutrient_schema}]}
                prompt="Analise esta fotografia de um prato pronto. Retorne SOMENTE JSON válido com exatamente esta estrutura: "+json.dumps(schema,ensure_ascii=False)+". Liste cada alimento visível separadamente, usando nomes brasileiros comuns que possam ser buscados numa base nutricional, como arroz cozido, feijão cozido, frango grelhado, alface ou tomate. Estime a quantidade em gramas e colheres de sopa quando fizer sentido. Para TODO item, preencha nutrientes_por_100g com estimativas realistas e não nulas de energia_kcal, proteina_g, carboidrato_g e lipidios_g; os demais campos podem ser 0 quando não houver estimativa. Esses valores são referência aproximada, não valores de rótulo. Não invente ingredientes, óleo, molhos ou alimentos não visíveis. Se a imagem estiver incerta, mantenha a melhor estimativa com confiança baixa."
                client=OpenAI(**client_args)
                resp=client.chat.completions.create(model=VISION_MODEL,messages=[{"role":"user","content":[{"type":"text","text":prompt},{"type":"image_url","image_url":{"url":image,"detail":"high"}}]}],response_format={"type":"json_object"},max_tokens=1800)
                raw=resp.choices[0].message.content or "{}";data=json.loads(raw);out=[]
                for item in (data.get("items") or [])[:15]:
                    name=re.sub(r"\s+", " ", str(item.get("nome", "")).strip())
                    if not name: continue
                    try: grams=float(item.get("quantidade_g") or 0)
                    except Exception: grams=0
                    if not math.isfinite(grams) or grams<=0: continue
                    grams=min(max(round(grams),1),5000)
                    try: spoons=float(item.get("colheres_sopa") or 0)
                    except Exception: spoons=0
                    if not math.isfinite(spoons) or spoons<=0: spoons=round(grams/15.0,1)
                    spoons=min(max(round(spoons,1),0.1),250)
                    match=find_plate_food(name,self.user["id"])
                    estimated = None if match else normalize_estimated_nutrients(item.get("nutrientes_por_100g"))
                    try: confidence = float(item.get("confianca") or 0)
                    except Exception: confidence = 0.0
                    confidence = min(max(confidence, 0.0), 1.0)
                    out.append({"nome":name,"alimento_id":match["id"] if match else None,"alimento_nome":match["nome"] if match else name,"quantidade_g":grams,"colheres_sopa":spoons,"gramas_por_colher":round(grams/spoons,3),"encontrado":bool(match),"confianca":confidence,"nutrientes_estimados":estimated})
                self.js({"ok":True,"items":out})
            except Exception as e:self.safe_error(e,400,"Não foi possível analisar o prato. Confira a imagem e tente novamente.")
            return
        if self.path=="/api/read_nutrition_label":
            try:
                if not self.enforce_rate_limit("vision-user",10,3600,self.user["id"]): return
                if not self.enforce_rate_limit("vision-ip",20,3600): return
                if not os.environ.get("OPENAI_API_KEY"):raise ValueError("A leitura por foto ainda não está configurada. No Render, adicione a variável OPENAI_API_KEY em Environment e faça um novo deploy.")
                if OpenAI is None:raise ValueError("A dependência openai não está instalada.")
                x=self.body(image=True);image=str(x.get("image_data","")
                )
                validate_image_data(image)
                client_args={"api_key":os.environ.get("OPENAI_API_KEY")}
                if os.environ.get("OPENAI_API_BASE"):client_args["base_url"]=os.environ.get("OPENAI_API_BASE")
                client=OpenAI(**client_args)
                schema={"nome":"string ou null","porcao_valor":"number ou null","porcao_unidade":"g, ml ou null","base_calculo":"100g, 100ml ou por_porcao","energia_kcal":"number ou null","proteina_g":"number ou null","carboidrato_g":"number ou null","lipidios_g":"number ou null","fibra_g":"number ou null","colesterol_mg":"number ou null","calcio_mg":"number ou null","magnesio_mg":"number ou null","fosforo_mg":"number ou null","ferro_mg":"number ou null","sodio_mg":"number ou null","potassio_mg":"number ou null","zinco_mg":"number ou null","vitamina_c_mg":"number ou null"}
                prompt="Leia a tabela nutricional desta imagem. Retorne SOMENTE JSON válido com exatamente estas chaves: "+json.dumps(schema,ensure_ascii=False)+". Preserve os números da tabela e não invente valores. Se um campo não estiver legível, use null. Identifique se os valores são por 100 g, 100 ml ou por porção; não converta valores."
                resp=client.chat.completions.create(model=VISION_MODEL,messages=[{"role":"user","content":[{"type":"text","text":prompt},{"type":"image_url","image_url":{"url":image,"detail":"high"}}]}],response_format={"type":"json_object"},max_tokens=1800)
                raw=resp.choices[0].message.content or "{}";data=json.loads(raw)
                original_base=data.get("base_calculo");portion=data.get("porcao_valor");unit=str(data.get("porcao_unidade") or "").lower();normalizado=False
                if original_base=="por_porcao" and portion and float(portion)>0:
                    factor=100.0/float(portion)
                    for key in ["energia_kcal","proteina_g","carboidrato_g","lipidios_g","fibra_g","colesterol_mg","calcio_mg","magnesio_mg","fosforo_mg","ferro_mg","sodio_mg","potassio_mg","zinco_mg","vitamina_c_mg"]:
                        if isinstance(data.get(key),(int,float)):data[key]=round(float(data[key])*factor,4)
                    data["base_calculo"]="100ml" if "ml" in unit else "100g";normalizado=True
                allowed=set(schema);clean={k:data.get(k) for k in allowed};clean["base_calculo_original"]=original_base;clean["normalizado"]=normalizado;clean["confianca"]=float(data.get("confianca",0) or 0);self.js({"ok":True,"data":clean})
            except Exception as e:self.safe_error(e,400,"Não foi possível ler a tabela nutricional. Confira a imagem e tente novamente.")
            return
        if self.path=="/api/profile":
            c=None
            try:
                x=self.body();name=str(x.get("nome","")).strip()
                if not name: raise ValueError("Nome obrigatório")
                idade=int(x["idade"]) if str(x.get("idade","")).strip() else None
                sexo=str(x.get("sexo","")).strip() or None
                peso=float(x["peso_kg"]) if str(x.get("peso_kg","")).strip() else None
                altura=float(x["altura_cm"]) if str(x.get("altura_cm","")).strip() else None
                atividade=str(x.get("atividade","")).strip() or None
                objetivo=str(x.get("objetivo","")).strip() or None
                peso_meta=float(x["peso_meta_kg"]) if str(x.get("peso_meta_kg","")).strip() else None
                ritmo=float(x["ritmo_kg_semana"]) if str(x.get("ritmo_kg_semana","")).strip() else None
                if idade is not None and not 10<=idade<=120:raise ValueError("Idade fora do intervalo permitido.")
                if peso is not None and not 20<=peso<=400:raise ValueError("Peso fora do intervalo permitido.")
                if altura is not None and not 100<=altura<=250:raise ValueError("Altura fora do intervalo permitido.")
                if peso_meta is not None and not 20<=peso_meta<=400:raise ValueError("Peso-meta fora do intervalo permitido.")
                if ritmo is not None and not 0<=ritmo<=1:raise ValueError("Ritmo fora do intervalo permitido.")
                c=ddb()
                c.execute("""INSERT INTO perfis(usuario_id,nome,idade,sexo,peso_kg,altura_cm,atividade,objetivo,peso_meta_kg,ritmo_kg_semana)
                             VALUES(?,?,?,?,?,?,?,?,?,?)
                             ON CONFLICT(usuario_id) DO UPDATE SET nome=EXCLUDED.nome,idade=EXCLUDED.idade,sexo=EXCLUDED.sexo,peso_kg=EXCLUDED.peso_kg,altura_cm=EXCLUDED.altura_cm,atividade=EXCLUDED.atividade,objetivo=EXCLUDED.objetivo,peso_meta_kg=EXCLUDED.peso_meta_kg,ritmo_kg_semana=EXCLUDED.ritmo_kg_semana""",
                          (self.user["id"],name,idade,sexo,peso,altura,atividade,objetivo,peso_meta,ritmo))
                goals = calculate_profile_goals(idade, sexo, peso, altura, atividade, objetivo, ritmo)
                existing = c.execute("SELECT manual_override FROM metas_usuario WHERE usuario_id=?", (self.user["id"],)).fetchone()
                goals_updated = False
                if goals and not bool(existing and existing["manual_override"]):
                    c.execute("""INSERT INTO metas_usuario(usuario_id,calorias_kcal,proteina_g,carboidratos_g,gorduras_g,fibras_g,sodio_mg,agua_ml,manual_override)
                                 VALUES(?,?,?,?,?,?,?,?,FALSE)
                                 ON CONFLICT(usuario_id) DO UPDATE SET calorias_kcal=EXCLUDED.calorias_kcal,proteina_g=EXCLUDED.proteina_g,carboidratos_g=EXCLUDED.carboidratos_g,gorduras_g=EXCLUDED.gorduras_g,fibras_g=EXCLUDED.fibras_g,sodio_mg=EXCLUDED.sodio_mg,agua_ml=EXCLUDED.agua_ml,manual_override=FALSE,atualizado_em=NOW()""",
                              (self.user["id"],goals["calorias_kcal"],goals["proteina_g"],goals["carboidratos_g"],goals["gorduras_g"],goals["fibras_g"],goals["sodio_mg"],goals["agua_ml"]))
                    goals_updated = True
                c.commit();self.js({"ok":True,"profile":{"nome":name},"goals":goals,"goals_updated":goals_updated,"manual_override":bool(existing and existing["manual_override"])})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return

        if self.path=="/api/water":
            c=None
            try:
                x=self.body();ml=float(x.get("quantidade_ml",0));
                if ml<=0: raise ValueError("Quantidade de água inválida")
                if ml>10000:raise ValueError("Quantidade de água muito alta para um único registro.")
                c=ddb();c.execute("INSERT INTO hidratacao(usuario_id,data,hora,quantidade_ml) VALUES(?,?,?,?)",(self.user["id"],x.get("data",date.today().isoformat()),datetime.now().strftime("%H:%M"),ml));c.commit();self.js({"ok":True})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return
        if self.path=="/api/goals":
            c=None
            try:
                x=self.body()
                manual=bool(x.get('manual_override',False))
                values=[float(x.get(k,0) or 0) for k in ['calorias_kcal','proteina_g','carboidratos_g','gorduras_g','fibras_g','sodio_mg','agua_ml']]
                if any((not math.isfinite(v) or v<0) for v in values):raise ValueError("As metas devem ser números não negativos.")
                c=ddb()
                c.execute("""INSERT INTO metas_usuario(usuario_id,calorias_kcal,proteina_g,carboidratos_g,gorduras_g,fibras_g,sodio_mg,agua_ml,manual_override)
                             VALUES(?,?,?,?,?,?,?,?,?)
                             ON CONFLICT(usuario_id) DO UPDATE SET calorias_kcal=EXCLUDED.calorias_kcal,proteina_g=EXCLUDED.proteina_g,carboidratos_g=EXCLUDED.carboidratos_g,gorduras_g=EXCLUDED.gorduras_g,fibras_g=EXCLUDED.fibras_g,sodio_mg=EXCLUDED.sodio_mg,agua_ml=EXCLUDED.agua_ml,manual_override=EXCLUDED.manual_override,atualizado_em=NOW()""",
                          (self.user["id"],*values,manual))
                c.commit();self.js({"ok":True,"manual_override":manual,"goals":dict(zip(['calorias_kcal','proteina_g','carboidratos_g','gorduras_g','fibras_g','sodio_mg','agua_ml'],values))})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return
        if self.path=="/api/food":
            c=None
            try:
                data=self.body();nome=str(data.get("nome","")).strip()
                if not nome: raise ValueError("Nome do alimento é obrigatório.")
                base_calculo="100ml" if str(data.get("base_calculo","")).lower()=="100ml" or str(data.get("porcao_unidade","")).lower()=="ml" else "100g"
                data["base_calculo"]=base_calculo;data["porcao_unidade"]="ml" if base_calculo=="100ml" else "g"
                allowed={"nome","energia_kcal","proteina_g","carboidrato_g","lipidios_g","fibra_g","colesterol_mg","calcio_mg","magnesio_mg","fosforo_mg","ferro_mg","sodio_mg","potassio_mg","zinco_mg","vitamina_c_mg","porcao_valor","porcao_unidade","base_calculo"}
                fields=["usuario_id"];vals=[self.user["id"]]
                for k,v in data.items():
                    if k in allowed and v is not None:
                        if k not in ("nome","porcao_unidade","base_calculo"):
                            v=float(v)
                            if v<0: raise ValueError(f"Valor inválido para {k}.")
                        fields.append(k);vals.append(str(v).strip() if k in ("nome","porcao_unidade","base_calculo") else v)
                if "nome" not in fields:fields.append("nome");vals.append(nome)
                placeholders=",".join(["?"]*len(fields));c=ddb()
                row=c.execute(f'INSERT INTO alimentos_usuario ({",".join(fields)}) VALUES ({placeholders}) RETURNING id',vals).fetchone()
                c.commit();self.js({"ok":True,"id":-int(row["id"])})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return

        if self.path=="/api/consume_batch":
            c=None
            try:
                x=self.body();meal_name=str(x.get("refeicao","")).strip();record_date=str(x.get("data",date.today().isoformat()));items=x.get("items")
                if meal_name not in MEALS: raise ValueError("Selecione uma refeição válida.")
                try: date.fromisoformat(record_date)
                except Exception: raise ValueError("Data inválida.")
                if not isinstance(items,list) or not 1<=len(items)<=30: raise ValueError("Inclua entre 1 e 30 alimentos.")
                c=ddb();valid=[];created={};created_foods=[]
                for item in items:
                    raw_id=item.get("alimento_id");name=re.sub(r"\s+", " ", str(item.get("alimento_nome","")).strip());weight=float(item.get("quantidade_g",0))
                    if not name or not math.isfinite(weight) or not 0<weight<=5000: raise ValueError("Alimento ou quantidade inválidos.")
                    if raw_id is not None:
                        aid=int(raw_id)
                        if aid == 0: raise ValueError("Identificador inválido para alimento. Corrija o item antes de confirmar.")
                        if aid < 0:
                            owned=c.execute("SELECT 1 FROM alimentos_usuario WHERE id=? AND usuario_id=?",(-aid,self.user["id"])).fetchone()
                            if not owned: raise ValueError("Alimento pessoal não encontrado.")
                        else:
                            source=ndb()
                            try: exists=source.execute("SELECT 1 FROM alimentos WHERE id=?",(aid,)).fetchone()
                            finally: source.close()
                            if not exists: raise ValueError("Alimento da base não encontrado.")
                    else:
                        nutrients=normalize_estimated_nutrients(item.get("nutrientes_estimados"))
                        if not nutrients: raise ValueError("O alimento ausente precisa de uma estimativa nutricional da IA ou deve ser selecionado na base.")
                        key=name.lower()
                        if key in created:
                            aid=created[key]
                        else:
                            existing=c.execute("SELECT id,nome,energia_kcal,proteina_g,carboidrato_g,lipidios_g FROM alimentos_usuario WHERE usuario_id=? AND LOWER(nome)=LOWER(?) LIMIT 1",(self.user["id"],name)).fetchone()
                            if existing:
                                aid=-int(existing["id"]);name=existing["nome"]
                                if not has_usable_energy(existing):
                                    confidence=float(item.get("confianca") or 0)
                                    sets=",".join([f"{field}=?" for field in ESTIMATED_NUTRIENT_FIELDS])
                                    c.execute(f"UPDATE alimentos_usuario SET {sets},porcao_valor=?,porcao_unidade=?,base_calculo=?,origem=?,confianca_ia=?,atualizado_em=NOW() WHERE id=? AND usuario_id=?",[*[nutrients[field] for field in ESTIMATED_NUTRIENT_FIELDS],100,"g","100g","ia_prato",min(max(confidence,0),1),-aid,self.user["id"]])
                            else:
                                confidence=float(item.get("confianca") or 0)
                                cols=["usuario_id","nome",*ESTIMATED_NUTRIENT_FIELDS,"porcao_valor","porcao_unidade","base_calculo","origem","confianca_ia"]
                                vals=[self.user["id"],name,*[nutrients[k] for k in ESTIMATED_NUTRIENT_FIELDS],100,"g","100g","ia_prato",min(max(confidence,0),1)]
                                marks=",".join(["?"]*len(cols))
                                row=c.execute(f"INSERT INTO alimentos_usuario ({','.join(cols)}) VALUES ({marks}) RETURNING id",vals).fetchone()
                                aid=-int(row["id"])
                                created_foods.append({"id":aid,"nome":name})
                            created[key]=aid
                    valid.append((aid,name,weight))
                for aid,name,weight in valid:
                    c.execute("INSERT INTO consumo(usuario_id,data,refeicao,alimento_id,alimento_nome,quantidade_g) VALUES(?,?,?,?,?,?)",(self.user["id"],record_date,meal_name,aid,name,weight))
                c.commit();self.js({"ok":True,"count":len(valid),"created_foods":created_foods})
            except Exception as e:
                if c:c.rollback()
                self.js({"error":str(e)},400)
            finally:
                if c:c.close()
            return
        if self.path!="/api/consume":self.send_error(404);return
        try:
            x=self.body();w=float(x["quantidade_g"]);meal=str(x.get("refeicao","")).strip();aid=int(x["alimento_id"]);name=str(x.get("alimento_nome","")).strip();unidade=str(x.get("unidade","g")).lower()
            if unidade not in ("g","ml"):raise ValueError("Unidade inválida.")
            if meal not in MEALS or not name or not math.isfinite(w) or not 0<w<=5000:raise ValueError("Refeição, alimento ou quantidade inválidos.")
            c=ddb();row=c.execute("INSERT INTO consumo(usuario_id,data,refeicao,alimento_id,alimento_nome,quantidade_g,unidade) VALUES(?,?,?,?,?,?,?) RETURNING id",(self.user["id"],x["data"],meal,aid,name,w,unidade)).fetchone();c.commit();c.close();self.js({"ok":True,"id":row["id"]})
        except Exception as e:self.js({"error":str(e)},400)
    def do_PUT(self):
        user=self.require_user()
        if not user:return
        if not self.verify_csrf(): return
        try:
            if self.path.startswith("/api/food/"):
                i=int(self.path.rsplit("/",1)[1])
                if i>=0: raise ValueError("A base nutricional compartilhada não pode ser alterada por este cadastro.")
                x=self.body();base_calculo="100ml" if str(x.get("base_calculo","")).lower()=="100ml" or str(x.get("porcao_unidade","")).lower()=="ml" else "100g";x["base_calculo"]=base_calculo;x["porcao_unidade"]="ml" if base_calculo=="100ml" else "g";allowed={"nome","energia_kcal","proteina_g","carboidrato_g","lipidios_g","fibra_g","colesterol_mg","calcio_mg","magnesio_mg","fosforo_mg","ferro_mg","sodio_mg","potassio_mg","zinco_mg","vitamina_c_mg","porcao_valor","porcao_unidade","base_calculo"};sets=[];vals=[]
                for k,v in x.items():
                    if k in allowed:
                        if k not in ("nome","porcao_unidade","base_calculo") and v is not None:v=float(v)
                        sets.append('"'+k+'"=?');vals.append(v)
                if not sets: raise ValueError("Nenhum campo válido")
                vals.extend([-i,self.user["id"]]);c=ddb();c.execute("UPDATE alimentos_usuario SET "+",".join(sets)+",atualizado_em=NOW() WHERE id=? AND usuario_id=?",vals);c.commit();c.close();self.js({"ok":True});return
            i=int(self.path.rsplit("/",1)[1]);x=self.body();w=float(x["quantidade_g"]);unidade=str(x.get("unidade","g")).lower()
            if unidade not in ("g","ml"):raise ValueError("Unidade inválida.")
            c=ddb();c.execute("UPDATE consumo SET quantidade_g=?,unidade=?,refeicao=? WHERE id=? AND usuario_id=?",(w,unidade,x["refeicao"],i,self.user["id"]));c.commit();c.close();self.js({"ok":True})
        except Exception as e:self.js({"error":str(e)},400)
    def do_DELETE(self):
        user=self.require_user()
        if not user:return
        if not self.verify_csrf(): return
        try:
            if self.path.startswith("/api/water/"):
                i=int(self.path.rsplit("/",1)[1]);c=ddb();c.execute("DELETE FROM hidratacao WHERE id=? AND usuario_id=?",(i,self.user["id"]));c.commit();c.close();self.js({"ok":True});return
            if self.path.startswith("/api/favorite/"):
                i=int(self.path.rsplit("/",1)[1]);c=ddb();c.execute("DELETE FROM favoritos WHERE id=? AND usuario_id=?",(i,self.user["id"]));c.commit();c.close();self.js({"ok":True});return
            if self.path.startswith("/api/portion/"):
                i=int(self.path.rsplit("/",1)[1]);c=ddb();c.execute("DELETE FROM porcoes WHERE id=? AND usuario_id=?",(i,self.user["id"]));c.commit();c.close();self.js({"ok":True});return
            i=int(self.path.rsplit("/",1)[1]);c=ddb();c.execute("DELETE FROM consumo WHERE id=? AND usuario_id=?",(i,self.user["id"]));c.commit();c.close();self.js({"ok":True})
        except Exception as e:self.js({"error":str(e)},400)

if __name__=="__main__":
    if not NUT.exists(): print("ERRO: banco_nutrientes.db não encontrado.");input("ENTER para sair...");raise SystemExit
    print(f"{APP_VERSION}: preparando estrutura do banco...")
    init_db()
    print(f"{APP_VERSION} iniciado.");print("No PC: http://127.0.0.1:5000");print("Para encerrar: Ctrl+C")
    ThreadingHTTPServer((HOST,PORT),H).serve_forever()
