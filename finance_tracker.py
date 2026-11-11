"""Personal finance tracker (Python 3.9+ and Tkinter).

Run: python finance_tracker.py
Optional dependencies: python -m pip install cryptography reportlab
Encrypted databases require Python 3.11+ with SQLite serialization support.
Run beside an existing expenses.db to migrate it without deleting its records.
All accounts use one currency. Transfers preserve total bank balance; savings
contributions reduce bank balances but are not everyday spending. Loan schedules
are estimates, not lender statements. Loan registration does not create cash.
Recurring items require individual review; CSV suggestions must be reviewed.
Backups are retained beside the database. CSV/PDF exports are unencrypted.
The dashboard's spending chart groups subsections under their parent section;
it excludes savings, income and transfers and includes archived sections.
"""
import calendar
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import sqlite3
import tempfile
import time
import tkinter as tk
from contextlib import contextmanager
from datetime import date, datetime, timedelta
from decimal import Decimal, DecimalException, InvalidOperation, ROUND_HALF_UP
from tkinter import filedialog, font, messagebox, simpledialog, ttk

DB_FILE = Path("expenses.db")
MAGIC = b"FINANCE1"
SQLITE_MAGIC = b"SQLite format 3\x00"
LIMIT = 9_000_000_000_000_000
DEFAULTS = {
    "Income": ["Salary", "Freelance", "Interest", "Dividends", "Refunds", "Other income"],
    "Expense": ["Housing", "Groceries", "Utilities", "Transport", "Loans",
                "Investments", "Insurance / Policies", "Health", "Education",
                "Subscriptions", "Travel", "Personal", "Taxes and fees", "Other expense"],
}


def cents(text, positive=False):
    try:
        value = Decimal(str(text).strip().replace(",", ""))
        scaled = value * 100
        if not value.is_finite() or scaled != scaled.to_integral_value():
            raise ValueError("Amounts must have at most two decimal places.")
        result = int(scaled)
        if abs(result) > LIMIT or (positive and result <= 0):
            raise ValueError("Amount is out of range or is not positive.")
        return result
    except (DecimalException, OverflowError):
        raise ValueError("Enter a valid amount with at most two decimal places.") from None


def money(value):
    sign = "-" if value < 0 else ""
    value = abs(value)
    return f"{sign}{value // 100:,}.{value % 100:02d}"


def iso_date(text, fmt="%Y-%m-%d"):
    for pattern in dict.fromkeys((fmt, "%Y-%m-%d")):
        try:
            return datetime.strptime(text.strip(), pattern).date().isoformat()
        except ValueError:
            pass
    raise ValueError(f"Enter a valid date using {fmt}, or YYYY-MM-DD.")


def next_due(day, frequency, anchor):
    current = date.fromisoformat(day)
    if frequency in ("Daily", "Weekly"):
        return (current + timedelta(days=1 if frequency == "Daily" else 7)).isoformat()
    months = {"Monthly": 1, "Quarterly": 3, "Yearly": 12}[frequency]
    month_index = current.year * 12 + current.month - 1 + months
    year, month = divmod(month_index, 12)
    month += 1
    return date(year, month, min(anchor, calendar.monthrange(year, month)[1])).isoformat()


def add_months(day, months, anchor):
    current = date.fromisoformat(day)
    index = current.year * 12 + current.month - 1 + months
    year, month = divmod(index, 12)
    month += 1
    if not 1 <= year <= 9999:
        raise ValueError("Payment schedule extends beyond supported calendar dates.")
    return date(year, month, min(anchor, calendar.monthrange(year, month)[1])).isoformat()


def crypto():
    try:
        from cryptography.exceptions import InvalidTag
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        from cryptography.hazmat.primitives.kdf.scrypt import Scrypt
    except ImportError:
        raise RuntimeError("Encryption requires: python -m pip install cryptography") from None
    return AESGCM, Scrypt, InvalidTag


def seal(raw, password):
    AESGCM, Scrypt, _ = crypto()
    salt, nonce = os.urandom(16), os.urandom(12)
    key = Scrypt(salt=salt, length=32, n=2**14, r=8, p=1).derive(password.encode())
    return MAGIC + salt + nonce + AESGCM(key).encrypt(nonce, raw, MAGIC)


def unseal(raw, password):
    AESGCM, Scrypt, InvalidTag = crypto()
    if len(raw) < len(MAGIC) + 44:
        raise ValueError("Encrypted file is incomplete.")
    salt, nonce = raw[8:24], raw[24:36]
    key = Scrypt(salt=salt, length=32, n=2**14, r=8, p=1).derive(password.encode())
    try:
        return AESGCM(key).decrypt(nonce, raw[36:], MAGIC)
    except InvalidTag:
        raise ValueError("Incorrect password, or damaged encrypted file.") from None


def atomic_write(path, raw):
    path = Path(path)
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


class Store:
    def __init__(self, path=DB_FILE):
        self.path = Path(path).resolve()
        self.db = None
        self.password = None
        self.lock_handle = open(str(self.path) + ".lock", "a+b")
        try:
            if os.name == "nt":
                import msvcrt
                self.lock_handle.seek(0)
                self.lock_handle.write(b"\0")
                self.lock_handle.flush()
                self.lock_handle.seek(0)
                msvcrt.locking(self.lock_handle.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(self.lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            self.lock_handle.close()
            raise RuntimeError("This database is already open in another tracker.") from None

    @staticmethod
    def require_encryption_support():
        if not (hasattr(sqlite3.Connection, "serialize") and
                hasattr(sqlite3.Connection, "deserialize")):
            raise RuntimeError("Encrypted databases require Python 3.11+ with SQLite serialization support. "
                               "Upgrade Python to open or create encrypted databases.")

    def database_bytes(self):
        if hasattr(self.db, "serialize"):
            return self.db.serialize()
        if self.password:
            self.require_encryption_support()
        # Older Python lacks SQLite serialization; only plaintext databases use
        # this temporary file. Encrypted databases must never take this path.
        with tempfile.TemporaryDirectory(prefix="finance-tracker-") as directory:
            path = Path(directory) / "snapshot.db"
            target = sqlite3.connect(str(path))
            try:
                self.db.backup(target)
            finally:
                target.close()
            return path.read_bytes()

    def connect(self, raw=None):
        db = sqlite3.connect(":memory:")
        try:
            if raw is not None:
                if not raw.startswith(SQLITE_MAGIC):
                    raise ValueError("Not a finance SQLite database.")
                if hasattr(db, "deserialize"):
                    db.deserialize(raw)
                else:
                    with tempfile.TemporaryDirectory(prefix="finance-tracker-") as directory:
                        path = Path(directory) / "restore.db"
                        path.write_bytes(raw)
                        source = sqlite3.connect(str(path))
                        try:
                            source.backup(db)
                        finally:
                            source.close()
            db.row_factory = sqlite3.Row
            db.execute("PRAGMA foreign_keys=ON")
            if db.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
                raise ValueError("Database integrity check failed.")
            return db
        except Exception:
            db.close()
            raise

    def open(self, password=None):
        if self.path.exists():
            raw = self.path.read_bytes()
            if raw.startswith(MAGIC):
                self.require_encryption_support()
                if not password:
                    raise ValueError("A password is required.")
                self.db = self.connect(unseal(raw, password))
                self.password = password
            else:
                # Checkpoint legacy WAL before atomic file replacement. An open
                # external WAL connection must not later overwrite the new file.
                source = sqlite3.connect(self.path, timeout=1)
                try:
                    mode = source.execute("PRAGMA journal_mode=DELETE").fetchone()[0]
                    if mode != "delete":
                        raise ValueError("Close other database tools before opening this database.")
                    self.db = self.connect()
                    source.backup(self.db)
                finally:
                    source.close()
                self.password = None
        else:
            self.db = self.connect()
        try:
            if self.db.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
                raise ValueError("Database integrity check failed.")
            self.backup(daily=True)
            self.migrate()
        except Exception:
            self.db.close()
            self.db = None
            self.password = None
            raise

    @contextmanager
    def change(self):
        before = sqlite3.connect(":memory:")
        self.db.backup(before)
        try:
            with self.db:
                yield self.db
            self.persist()
        except Exception:
            self.db.close()
            self.db = before
            before = None
            self.db.row_factory = sqlite3.Row
            self.db.execute("PRAGMA foreign_keys=ON")
            raise
        finally:
            if before is not None:
                before.close()

    def persist(self):
        raw = self.database_bytes()
        atomic_write(self.path, seal(raw, self.password) if self.password else raw)

    def backup(self, daily=False):
        if not self.path.exists():
            return None
        folder = self.path.parent / (self.path.name + ".backups")
        folder.mkdir(mode=0o700, exist_ok=True)
        if daily and any(folder.glob(date.today().isoformat() + "_*.bak")):
            return None
        stamp = datetime.now().strftime("%Y-%m-%d_%H%M%S_%f")
        target = folder / (stamp + ".bak")
        if self.db is not None:
            raw = self.database_bytes()
            raw = seal(raw, self.password) if self.password else raw
        else:
            raw = self.path.read_bytes()
        atomic_write(target, raw)
        return target

    def migrate(self):
        version = self.db.execute("PRAGMA user_version").fetchone()[0]
        if version > 1:
            raise ValueError("This database requires a newer version of the tracker.")
        self.db.executescript("""
            CREATE TABLE IF NOT EXISTS accounts (
                id INTEGER PRIMARY KEY, name TEXT NOT NULL COLLATE NOCASE UNIQUE,
                opening_balance INTEGER NOT NULL DEFAULT 0);
            CREATE TABLE IF NOT EXISTS categories (
                id INTEGER PRIMARY KEY, kind TEXT NOT NULL CHECK(kind IN ('Income','Expense')),
                name TEXT NOT NULL COLLATE NOCASE, UNIQUE(kind,name));
            CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY, date TEXT NOT NULL,
                kind TEXT NOT NULL CHECK(kind IN ('Income','Expense','Transfer')),
                description TEXT NOT NULL, amount INTEGER NOT NULL CHECK(amount>0),
                category_id INTEGER REFERENCES categories(id),
                account_id INTEGER REFERENCES accounts(id),
                to_account_id INTEGER REFERENCES accounts(id));
        """)
        with self.change() as db:
            additions = {
                "accounts": {"nickname": "TEXT NOT NULL DEFAULT ''"},
                "categories": {"bucket": "TEXT NOT NULL DEFAULT 'Spending'",
                               "parent_id": "INTEGER REFERENCES categories(id)",
                               "archived": "INTEGER NOT NULL DEFAULT 0"},
                "transactions": {"loan_id": "INTEGER REFERENCES loans(id)",
                                 "principal": "INTEGER NOT NULL DEFAULT 0",
                                 "policy_id": "INTEGER REFERENCES policies(id)",
                                 "import_key": "TEXT"},
            }
            for table, columns in additions.items():
                present = {row[1] for row in db.execute(f"PRAGMA table_info({table})")}
                for column, definition in columns.items():
                    if column not in present:
                        db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")
            statements = [
                """CREATE TABLE IF NOT EXISTS loans (
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, lender TEXT NOT NULL DEFAULT '',
                    principal INTEGER NOT NULL CHECK(principal>0), annual_rate TEXT NOT NULL DEFAULT '0',
                    emi INTEGER NOT NULL CHECK(emi>0), first_due TEXT NOT NULL, notes TEXT NOT NULL DEFAULT '')""",
                """CREATE TABLE IF NOT EXISTS policies (
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, provider TEXT NOT NULL DEFAULT '',
                    policy_number TEXT NOT NULL DEFAULT '', premium INTEGER NOT NULL CHECK(premium>0),
                    coverage INTEGER NOT NULL DEFAULT 0, renewal_date TEXT NOT NULL,
                    frequency TEXT NOT NULL DEFAULT 'Yearly', nominee TEXT NOT NULL DEFAULT '',
                    document TEXT NOT NULL DEFAULT '', notes TEXT NOT NULL DEFAULT '',
                    anchor INTEGER NOT NULL DEFAULT 1)""",
                """CREATE TABLE IF NOT EXISTS budgets (
                    id INTEGER PRIMARY KEY, month TEXT NOT NULL,
                    category_id INTEGER NOT NULL REFERENCES categories(id),
                    amount INTEGER NOT NULL CHECK(amount>0), warning INTEGER NOT NULL DEFAULT 80,
                    UNIQUE(month,category_id))""",
                """CREATE TABLE IF NOT EXISTS recurring (
                    id INTEGER PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
                    amount INTEGER NOT NULL CHECK(amount>0), category_id INTEGER REFERENCES categories(id),
                    account_id INTEGER NOT NULL REFERENCES accounts(id),
                    to_account_id INTEGER REFERENCES accounts(id), next_date TEXT NOT NULL,
                    frequency TEXT NOT NULL, anchor INTEGER NOT NULL, active INTEGER NOT NULL DEFAULT 1,
                    loan_id INTEGER REFERENCES loans(id), principal INTEGER NOT NULL DEFAULT 0,
                    policy_id INTEGER REFERENCES policies(id))""",
                """CREATE TABLE IF NOT EXISTS reconciliations (
                    id INTEGER PRIMARY KEY, account_id INTEGER NOT NULL REFERENCES accounts(id),
                    date TEXT NOT NULL, statement INTEGER NOT NULL, recorded INTEGER NOT NULL,
                    notes TEXT NOT NULL DEFAULT '')""",
                "CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY,value TEXT NOT NULL)",
                "CREATE UNIQUE INDEX IF NOT EXISTS import_unique ON transactions(import_key) WHERE import_key IS NOT NULL",
                "CREATE INDEX IF NOT EXISTS tx_date_account ON transactions(date,account_id)",
            ]
            for statement in statements:
                db.execute(statement)
            policy_columns = {row[1] for row in db.execute("PRAGMA table_info(policies)")}
            if "anchor" not in policy_columns:
                db.execute("ALTER TABLE policies ADD COLUMN anchor INTEGER NOT NULL DEFAULT 1")
                db.execute("UPDATE policies SET anchor=CAST(substr(renewal_date,9,2) AS INTEGER)")
            if version == 0:
                for kind, names in DEFAULTS.items():
                    for name in names:
                        db.execute("INSERT OR IGNORE INTO categories(kind,name) VALUES (?,?)", (kind, name))
                db.execute("UPDATE categories SET bucket='Savings' WHERE kind='Expense' AND name='Investments'")
                db.execute("PRAGMA user_version=1")
            for key, value in {"currency": "INR", "date_format": "%Y-%m-%d", "idle_minutes": "10"}.items():
                db.execute("INSERT OR IGNORE INTO settings VALUES (?,?)", (key, value))
            violations = db.execute("PRAGMA foreign_key_check").fetchall()
            if violations:
                raise ValueError("Database contains invalid account/category references.")

    def rows(self, sql, params=()):
        return self.db.execute(sql, params).fetchall()

    def scalar(self, sql, params=()):
        return self.db.execute(sql, params).fetchone()[0]

    def setting(self, key):
        return self.scalar("SELECT value FROM settings WHERE key=?", (key,))

    def balance(self, account_id, through="9999-12-31"):
        return self.scalar("""
            SELECT opening_balance + COALESCE((
              SELECT SUM(CASE WHEN account_id=a.id THEN
                CASE WHEN kind='Income' THEN amount ELSE -amount END ELSE 0 END
                + CASE WHEN kind='Transfer' AND to_account_id=a.id THEN amount ELSE 0 END)
              FROM transactions WHERE date<=? AND (account_id=a.id OR to_account_id=a.id)
            ),0) FROM accounts a WHERE id=?""", (through, account_id))

    def outstanding(self, loan_id, exclude=None):
        return self.scalar("""SELECT principal-COALESCE((
            SELECT SUM(principal) FROM transactions WHERE loan_id=l.id AND id!=?
            ),0) FROM loans l WHERE id=?""", (exclude or -1, loan_id))

    def validate_transaction(self, values, tx_id=None):
        if values["kind"] not in ("Income", "Expense", "Transfer"):
            raise ValueError("Invalid transaction type.")
        account = values["account_id"]
        if not self.scalar("SELECT COUNT(*) FROM accounts WHERE id=?", (account,)):
            raise ValueError("Choose a valid account.")
        values["date"] = iso_date(values["date"])
        if not 0 < values["amount"] <= LIMIT:
            raise ValueError("Enter a positive amount.")
        if values["kind"] == "Transfer":
            target = values["to_account_id"]
            if target == account or not self.scalar("SELECT COUNT(*) FROM accounts WHERE id=?", (target,)):
                raise ValueError("Transfers require two different accounts.")
            values.update(category_id=None, loan_id=None, principal=0, policy_id=None)
        else:
            categories = self.rows("SELECT * FROM categories WHERE id=?", (values["category_id"],))
            if not categories or categories[0]["kind"] != values["kind"]:
                raise ValueError("Section type must match the transaction type.")
            if categories[0]["archived"] and not (tx_id and self.scalar(
                "SELECT COUNT(*) FROM transactions WHERE id=? AND category_id=?",
                (tx_id, values["category_id"]))):
                raise ValueError("This section is archived. Choose an active section.")
            values["to_account_id"] = None
            if values.get("loan_id"):
                if not self.scalar("SELECT COUNT(*) FROM loans WHERE id=?", (values["loan_id"],)):
                    raise ValueError("The selected loan no longer exists.")
                if values["kind"] != "Expense" or categories[0]["bucket"] != "Spending":
                    raise ValueError("Loan repayments must use an Expense / Spending section.")
                if not 0 <= values["principal"] <= min(values["amount"], self.outstanding(values["loan_id"], tx_id)):
                    raise ValueError("Principal must be between zero and the outstanding balance, and not exceed payment.")
            elif values.get("principal", 0):
                raise ValueError("Select a loan when entering principal.")
            if values.get("policy_id") and (values["kind"] != "Expense" or categories[0]["bucket"] != "Spending"):
                raise ValueError("Premiums must use an Expense / Spending section.")
            if values.get("policy_id") and not self.scalar("SELECT COUNT(*) FROM policies WHERE id=?", (values["policy_id"],)):
                raise ValueError("The selected policy no longer exists.")
            if values.get("policy_id") and values.get("loan_id"):
                raise ValueError("A payment cannot be linked to both a loan and a policy.")
        values.setdefault("loan_id", None)
        values.setdefault("principal", 0)
        values.setdefault("policy_id", None)
        values.setdefault("import_key", None)

    def post(self, values, tx_id=None, rule=None):
        self.validate_transaction(values, tx_id)
        keys = ("date", "kind", "description", "amount", "category_id", "account_id",
                "to_account_id", "loan_id", "principal", "policy_id", "import_key")
        with self.change() as db:
            if rule:
                current = db.execute("SELECT next_date,active FROM recurring WHERE id=?", (rule["id"],)).fetchone()
                if not current or not current["active"] or current["next_date"] != rule["next_date"]:
                    raise ValueError("This occurrence was already posted or its schedule changed. Review due items again.")
            if tx_id is None:
                cursor = db.execute(f"INSERT INTO transactions ({','.join(keys)}) VALUES ({','.join('?' for _ in keys)})",
                                    tuple(values[key] for key in keys))
                tx_id = cursor.lastrowid
            else:
                db.execute(f"UPDATE transactions SET {','.join(key+'=?' for key in keys)} WHERE id=?",
                           (*[values[key] for key in keys], tx_id))
            if rule:
                db.execute("UPDATE recurring SET next_date=? WHERE id=?",
                           (next_due(rule["next_date"], rule["frequency"], rule["anchor"]), rule["id"]))
        return tx_id

    def replace(self, source, password=None):
        raw = Path(source).read_bytes()
        if raw.startswith(MAGIC):
            self.require_encryption_support()
        restored = self.connect(unseal(raw, password or "") if raw.startswith(MAGIC) else raw)
        required = {"accounts", "categories", "transactions"}
        names = {row[0] for row in restored.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if not required <= names:
            restored.close()
            raise ValueError("The selected file is not a finance tracker database.")
        self.backup()
        previous = self.db
        self.db = restored
        try:
            self.migrate()
        except Exception:
            self.db.close()
            self.db = previous
            raise
        previous.close()

    def close(self):
        if self.db:
            self.db.close()
            self.db = None
        self.password = None
        self.lock_handle.close()


class FinanceTracker:
    def __init__(self, root, path=DB_FILE):
        self.root = root
        self.root.title("Personal Finance Tracker")
        self.root.geometry("1280x800")
        self.store = Store(path)
        self.last_activity = time.monotonic()
        self.open_database()
        self.summary = ttk.Label(root, padding=10, font=("TkDefaultFont", 11, "bold"))
        self.summary.pack(fill="x")
        self.tabs = ttk.Notebook(root)
        self.tabs.pack(fill="both", expand=True, padx=8, pady=8)
        self.trees, self.frames = {}, {}
        self.build_ui()
        self.root.bind_all("<KeyPress>", self.activity, add="+")
        self.root.bind_all("<ButtonPress>", self.activity, add="+")
        self.root.bind_all("<Motion>", self.activity, add="+")
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.after(1000, self.check_idle)
        self.refresh()

    def open_database(self):
        encrypted = self.store.path.exists() and self.store.path.read_bytes().startswith(MAGIC)
        if encrypted:
            self.store.require_encryption_support()
        while True:
            password = simpledialog.askstring("Unlock database", "Database password:", show="*", parent=self.root) if encrypted else None
            if encrypted and password is None:
                raise ValueError("Unlock cancelled.")
            try:
                self.store.open(password)
                return
            except ValueError as error:
                if not encrypted:
                    raise
                messagebox.showerror("Cannot unlock", str(error), parent=self.root)

    def activity(self, _event=None):
        self.last_activity = time.monotonic()

    def check_idle(self):
        if self.store.db and self.store.password:
            minutes = int(self.store.setting("idle_minutes"))
            if minutes and time.monotonic() - self.last_activity >= minutes * 60:
                self.lock()
        self.root.after(1000, self.check_idle)

    def safe(self, callback):
        def run():
            try:
                callback()
            except (ValueError, sqlite3.Error, OSError, RuntimeError) as error:
                messagebox.showerror("Operation failed", str(error), parent=self.root)
        return run

    def page(self, name, columns, buttons):
        frame = ttk.Frame(self.tabs, padding=8)
        self.tabs.add(frame, text=name)
        bar = ttk.Frame(frame)
        bar.pack(fill="x", pady=(0, 8))
        for label, action in buttons:
            ttk.Button(bar, text=label, command=self.safe(action)).pack(side="left", padx=3)
        container = ttk.Frame(frame)
        container.pack(fill="both", expand=True)
        tree = ttk.Treeview(container, columns=columns, show="headings", selectmode="browse")
        for column in columns:
            tree.heading(column, text=column.replace("_", " ").title())
            tree.column(column, width=140, minwidth=90)
        vertical = ttk.Scrollbar(container, orient="vertical", command=tree.yview)
        horizontal = ttk.Scrollbar(container, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=vertical.set, xscrollcommand=horizontal.set)
        tree.grid(row=0, column=0, sticky="nsew")
        vertical.grid(row=0, column=1, sticky="ns")
        horizontal.grid(row=1, column=0, sticky="ew")
        container.rowconfigure(0, weight=1)
        container.columnconfigure(0, weight=1)
        self.trees[name], self.frames[name] = tree, frame
        return frame

    def build_ui(self):
        self.dashboard = ttk.Frame(self.tabs, padding=10)
        self.tabs.add(self.dashboard, text="Dashboard")
        line = ttk.Frame(self.dashboard)
        line.pack(fill="x")
        self.month = tk.StringVar(value=date.today().strftime("%Y-%m"))
        ttk.Label(line, text="Month (YYYY-MM):").pack(side="left")
        ttk.Entry(line, textvariable=self.month, width=10).pack(side="left", padx=6)
        ttk.Button(line, text="Refresh", command=self.safe(self.refresh)).pack(side="left")
        ttk.Button(line, text="Review due items", command=self.safe(self.review_due)).pack(side="left", padx=6)
        self.dashboard_text = tk.Text(self.dashboard, height=16, wrap="word", state="disabled")
        self.dashboard_text.pack(fill="x", pady=10)
        charts = ttk.Frame(self.dashboard)
        charts.pack(fill="both", expand=True)
        charts.columnconfigure(0, weight=1, uniform="charts")
        charts.columnconfigure(1, weight=1, uniform="charts")
        charts.rowconfigure(0, weight=1)
        overview = ttk.LabelFrame(charts, text="Monthly overview")
        overview.grid(row=0, column=0, sticky="nsew", padx=(0, 5))
        breakdown = ttk.LabelFrame(charts, text="Spending by section (includes subsections)")
        breakdown.grid(row=0, column=1, sticky="nsew", padx=(5, 0))
        breakdown.columnconfigure(0, weight=1)
        breakdown.rowconfigure(0, weight=1)
        self.chart = tk.Canvas(overview, height=260, background="white")
        self.chart.pack(fill="both", expand=True)
        self.chart.bind("<Configure>", lambda _event: self.draw_chart())
        self.spending_chart = tk.Canvas(breakdown, height=260, background="white")
        vertical = ttk.Scrollbar(breakdown, orient="vertical", command=self.spending_chart.yview)
        horizontal = ttk.Scrollbar(breakdown, orient="horizontal", command=self.spending_chart.xview)
        self.spending_chart.configure(yscrollcommand=vertical.set, xscrollcommand=horizontal.set)
        self.spending_chart.grid(row=0, column=0, sticky="nsew")
        vertical.grid(row=0, column=1, sticky="ns")
        horizontal.grid(row=1, column=0, sticky="ew")
        self.spending_chart.bind("<Configure>", lambda _event: self.draw_spending_chart())
        self.page("Transactions", ("date", "type", "description", "section", "account", "amount", "principal", "interest"),
                  [("Add", self.transaction), ("Edit", lambda: self.transaction(self.selected("Transactions"))),
                   ("Delete", lambda: self.delete("Transactions", "transactions")),
                   ("Import CSV", self.import_csv), ("Export filtered CSV", self.export_transactions)])
        filters = ttk.Frame(self.frames["Transactions"])
        filters.pack(fill="x", before=self.frames["Transactions"].winfo_children()[1])
        self.filters = {}
        self.filter_boxes = {}
        for index, label in enumerate(("From", "To", "Account", "Section", "Description")):
            variable = tk.StringVar()
            self.filters[label] = variable
            ttk.Label(filters, text=label).grid(row=0, column=index * 2, padx=2)
            if label in ("Account", "Section"):
                widget = ttk.Combobox(filters, textvariable=variable, state="readonly", width=20)
                self.filter_boxes[label] = widget
            else:
                widget = ttk.Entry(filters, textvariable=variable, width=14)
            widget.grid(row=0, column=index * 2 + 1, padx=2)
        ttk.Button(filters, text="Apply", command=self.safe(self.refresh)).grid(row=1, column=0, pady=5)
        ttk.Button(filters, text="Clear", command=self.safe(self.clear_filters)).grid(row=1, column=1)
        self.page("Accounts", ("name", "nickname", "opening_balance", "current_balance"),
                  [("Add", self.account), ("Edit", lambda: self.account(self.selected("Accounts"))),
                   ("Delete", lambda: self.delete("Accounts", "accounts"))])
        self.page("Sections", ("type", "name", "bucket", "parent", "archived"),
                  [("Add", self.category), ("Edit", lambda: self.category(self.selected("Sections"))),
                   ("Delete", lambda: self.delete("Sections", "categories"))])
        self.page("Loans", ("name", "lender", "principal", "outstanding", "annual_rate", "emi", "estimated_next_due", "progress"),
                  [("Add", self.loan), ("Edit", lambda: self.loan(self.selected("Loans"))),
                   ("Repay", self.repay), ("Payment schedule", self.loan_schedule),
                   ("Delete", lambda: self.delete("Loans", "loans"))])
        self.page("Policies", ("name", "provider", "premium", "coverage", "renewal", "nominee", "document"),
                  [("Add", self.policy), ("Edit", lambda: self.policy(self.selected("Policies"))),
                   ("Pay premium", self.pay_premium), ("Advance renewal", self.advance_policy),
                   ("Delete", lambda: self.delete("Policies", "policies"))])
        self.page("Budgets", ("month", "section", "limit", "spent", "used", "status"),
                  [("Add", self.budget), ("Edit", lambda: self.budget(self.selected("Budgets"))),
                   ("Delete", lambda: self.delete("Budgets", "budgets"))])
        self.page("Recurring", ("name", "type", "amount", "account", "next_due", "frequency", "active"),
                  [("Add", self.recurring), ("Edit", lambda: self.recurring(self.selected("Recurring"))),
                   ("Review due", self.review_due), ("Delete", lambda: self.delete("Recurring", "recurring"))])
        self.page("Reconciliation", ("date", "account", "statement", "recorded", "difference", "status", "notes"),
                  [("Compare statement", self.reconcile),
                   ("Delete", lambda: self.delete("Reconciliation", "reconciliations"))])
        self.page("Reports", ("month", "income", "spending", "savings", "net_after_savings", "change_in_spending"),
                  [("Refresh", self.refresh), ("Export CSV", self.export_report), ("Export PDF", self.export_pdf)])
        settings = ttk.Frame(self.tabs, padding=12)
        self.tabs.add(settings, text="Settings / Backup")
        for text, action in [
            ("Currency, date format and idle timeout", self.settings),
            ("Enable encryption / change password", self.encrypt),
            ("Disable encryption", self.decrypt),
            ("Lock now", self.lock), ("Create backup", self.backup),
            ("Restore backup", self.restore)]:
            ttk.Button(settings, text=text, command=self.safe(action)).pack(anchor="w", pady=5)
        ttk.Label(settings, wraplength=1000, text=(
            "Savings contributions are Expense transactions in Savings sections; they reduce bank balances "
            "but are excluded from everyday spending. Use Transfers when moving money between tracked accounts.\n\n"
            "Encryption protects the database file, not screenshots, CSV/PDF exports, referenced documents, "
            "old plaintext backups, OS swap, or a compromised computer. Encrypted databases stay in memory "
            "while unlocked. Keep your password: there is no recovery backdoor.\n\n"
            "Automatic backups are made once per day on opening, and before restore/encryption changes. "
            "Backups are retained in expenses.db.backups; manage retention yourself. Use only this app to edit "
            "the database. All accounts share the configured currency; there is no exchange-rate conversion."
        )).pack(anchor="w", pady=15)

    def selected(self, name):
        selection = self.trees[name].selection()
        if not selection:
            raise ValueError("Select a row first.")
        return int(selection[0])

    def fill(self, name, rows):
        tree = self.trees[name]
        children = tree.get_children()
        if children:
            tree.delete(*children)
        for identifier, values in rows:
            tree.insert("", "end", iid=str(identifier), values=values)

    def choices(self, table, include_none=False, where="1", params=()):
        result = {"— None —": None} if include_none else {}
        for row in self.store.rows(f"SELECT id,name FROM {table} WHERE {where} ORDER BY name", params):
            result[f'{row["name"]} [#{row["id"]}]'] = row["id"]
        return result

    def form(self, title, specs, save):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.transient(self.root)
        win.grab_set()
        frame = ttk.Frame(win, padding=12)
        frame.pack(fill="both", expand=True)
        variables = {}
        for index, (key, label, kind, default) in enumerate(specs):
            ttk.Label(frame, text=label).grid(row=index, column=0, sticky="w", padx=4, pady=3)
            if isinstance(kind, dict):
                current = next((name for name, value in kind.items() if value == default), "")
                variable = tk.StringVar(value=current)
                widget = ttk.Combobox(frame, textvariable=variable, values=list(kind), state="readonly", width=40)
            elif isinstance(kind, tuple):
                variable = tk.StringVar(value=default)
                widget = ttk.Combobox(frame, textvariable=variable, values=kind, state="readonly", width=40)
            else:
                variable = tk.StringVar(value=str(default))
                widget = ttk.Entry(frame, textvariable=variable, width=43)
            variables[key] = (variable, kind)
            widget.grid(row=index, column=1, sticky="ew", padx=4, pady=3)
        def submit():
            try:
                values = {}
                for key, (variable, kind) in variables.items():
                    text = variable.get().strip()
                    if isinstance(kind, dict):
                        if text not in kind:
                            raise ValueError(f"Choose a value for {key}.")
                        values[key] = kind[text]
                    else:
                        values[key] = text
                save(values)
                win.destroy()
                self.refresh()
            except (ValueError, sqlite3.Error, OSError, RuntimeError) as error:
                messagebox.showerror("Cannot save", str(error), parent=win)
        actions = ttk.Frame(frame)
        actions.grid(row=len(specs), columnspan=2, sticky="e", pady=10)
        ttk.Button(actions, text="Save", command=submit).pack(side="left", padx=4)
        ttk.Button(actions, text="Cancel", command=win.destroy).pack(side="left")

    def get(self, table, identifier):
        if identifier is None:
            return {}
        rows = self.store.rows(f"SELECT * FROM {table} WHERE id=?", (identifier,))
        if not rows:
            raise ValueError("This record no longer exists.")
        return dict(rows[0])

    def write(self, table, values, identifier=None):
        keys = list(values)
        with self.store.change() as db:
            if identifier is None:
                db.execute(f"INSERT INTO {table} ({','.join(keys)}) VALUES ({','.join('?' for _ in keys)})", tuple(values.values()))
            else:
                db.execute(f"UPDATE {table} SET {','.join(key+'=?' for key in keys)} WHERE id=?", (*values.values(), identifier))

    def delete(self, page, table):
        identifier = self.selected(page)
        if messagebox.askyesno("Delete record", "Delete this record? Referenced accounts, sections, loans and policies cannot be deleted.", parent=self.root):
            with self.store.change() as db:
                db.execute(f"DELETE FROM {table} WHERE id=?", (identifier,))
            self.refresh()

    def parse_date(self, text):
        return iso_date(text, self.store.setting("date_format"))

    def display_date(self, text):
        return date.fromisoformat(text).strftime(self.store.setting("date_format"))

    def transaction(self, identifier=None, preset=None, rule=None):
        existing = self.get("transactions", identifier)
        data = existing or preset or {}
        accounts = self.choices("accounts")
        if not accounts:
            raise ValueError("Add an account before entering transactions.")
        sections = self.choices("categories", True, "archived=0 OR id=?", (data.get("category_id", -1),))
        def save(values):
            values["date"] = self.parse_date(values["date"])
            values["amount"] = cents(values["amount"], True)
            values["principal"] = cents(values["principal"])
            values["description"] = values["description"] or values["kind"]
            values["import_key"] = existing.get("import_key")
            self.store.post(values, identifier, rule)
        self.form("Transaction — principal is part of the amount, not extra", [
            ("kind", "Type", ("Income", "Expense", "Transfer"), data.get("kind", "Expense")),
            ("date", "Date", str, self.display_date(data.get("date", date.today().isoformat()))),
            ("description", "Description", str, data.get("description", "")),
            ("amount", "Total amount", str, money(data.get("amount", 0))),
            ("category_id", "Section (None for transfers)", sections, data.get("category_id")),
            ("account_id", "Account / transfer from", accounts, data.get("account_id", next(iter(accounts.values())))),
            ("to_account_id", "Transfer to (otherwise ignored)", self.choices("accounts", True), data.get("to_account_id")),
            ("loan_id", "Loan (optional)", self.choices("loans", True), data.get("loan_id")),
            ("principal", "Principal part of loan payment", str, money(data.get("principal", 0))),
            ("policy_id", "Policy (optional)", self.choices("policies", True), data.get("policy_id")),
        ], save)

    def account(self, identifier=None):
        data = self.get("accounts", identifier)
        def save(values):
            if not values["name"]:
                raise ValueError("Account name is required.")
            values["opening_balance"] = cents(values["opening_balance"])
            self.write("accounts", values, identifier)
        self.form("Account", [
            ("name", "Bank / account name", str, data.get("name", "")),
            ("nickname", "Nickname", str, data.get("nickname", "")),
            ("opening_balance", "Opening balance", str, money(data.get("opening_balance", 0))),
        ], save)

    def category(self, identifier=None):
        data = self.get("categories", identifier)
        parents = self.choices("categories", True, "parent_id IS NULL AND id!=?", (identifier or -1,))
        def save(values):
            if not values["name"]:
                raise ValueError("Section name is required.")
            values["archived"] = int(values["archived"] == "Yes")
            parent = self.get("categories", values["parent_id"])
            if parent and (parent["kind"] != values["kind"] or parent["bucket"] != values["bucket"]):
                raise ValueError("Subsections must match their parent's type and bucket.")
            if identifier:
                children = self.store.rows("SELECT * FROM categories WHERE parent_id=?", (identifier,))
                if children and (values["parent_id"] or any(row["kind"] != values["kind"] or row["bucket"] != values["bucket"] for row in children)):
                    raise ValueError("Update/remove child sections before changing this hierarchy or bucket.")
                if values["kind"] != data["kind"] and (
                    self.store.scalar("SELECT COUNT(*) FROM transactions WHERE category_id=?", (identifier,)) or
                    self.store.scalar("SELECT COUNT(*) FROM recurring WHERE category_id=?", (identifier,))):
                    raise ValueError("A section in use cannot change type.")
                if values["bucket"] == "Savings" and (
                    self.store.scalar("SELECT COUNT(*) FROM budgets WHERE category_id=?", (identifier,)) or
                    self.store.scalar("SELECT COUNT(*) FROM transactions WHERE category_id=? AND (loan_id IS NOT NULL OR policy_id IS NOT NULL)", (identifier,)) or
                    self.store.scalar("SELECT COUNT(*) FROM recurring WHERE category_id=? AND (loan_id IS NOT NULL OR policy_id IS NOT NULL)", (identifier,))):
                    raise ValueError("A budgeted section or loan/premium section cannot become Savings. Reassign those records first.")
            if values["kind"] == "Income" and values["bucket"] == "Savings":
                raise ValueError("Savings sections must be Expense sections.")
            self.write("categories", values, identifier)
        self.form("Section / subsection", [
            ("kind", "Type", ("Income", "Expense"), data.get("kind", "Expense")),
            ("name", "Unique section name", str, data.get("name", "")),
            ("bucket", "Classification (also changes history)", ("Spending", "Savings"), data.get("bucket", "Spending")),
            ("parent_id", "Parent (one subsection level)", parents, data.get("parent_id")),
            ("archived", "Archived", ("No", "Yes"), "Yes" if data.get("archived") else "No"),
        ], save)

    def loan(self, identifier=None):
        data = self.get("loans", identifier)
        def save(values):
            if not values["name"]:
                raise ValueError("Loan name is required.")
            values["principal"], values["emi"] = cents(values["principal"], True), cents(values["emi"], True)
            try:
                rate = Decimal(values["annual_rate"])
            except InvalidOperation:
                raise ValueError("Enter a valid annual interest rate.") from None
            if not rate.is_finite() or not 0 <= rate <= 100:
                raise ValueError("Annual rate must be between 0 and 100 percent.")
            values["annual_rate"] = str(rate)
            values["first_due"] = self.parse_date(values["first_due"])
            if identifier and values["principal"] < self.store.scalar("SELECT COALESCE(SUM(principal),0) FROM transactions WHERE loan_id=?", (identifier,)):
                raise ValueError("Principal cannot be less than recorded repayments.")
            self.write("loans", values, identifier)
        self.form("Loan — register existing debt; disbursements are entered separately", [
            ("name", "Loan name", str, data.get("name", "")),
            ("lender", "Lender", str, data.get("lender", "")),
            ("principal", "Original / tracked principal", str, money(data.get("principal", 0))),
            ("annual_rate", "Annual interest rate (%)", str, data.get("annual_rate", "0")),
            ("emi", "Monthly payment / EMI", str, money(data.get("emi", 0))),
            ("first_due", "First due date", str, self.display_date(data.get("first_due", date.today().isoformat()))),
            ("notes", "Notes", str, data.get("notes", "")),
        ], save)

    def loan_due(self, loan):
        if self.store.outstanding(loan["id"]) <= 0:
            return "Paid off"
        paid = self.store.scalar("SELECT COALESCE(SUM(amount),0) FROM transactions WHERE loan_id=?", (loan["id"],))
        periods = paid // loan["emi"]
        return add_months(loan["first_due"], periods, date.fromisoformat(loan["first_due"]).day)

    def repay(self):
        loan = self.get("loans", self.selected("Loans"))
        outstanding = self.store.outstanding(loan["id"])
        if outstanding <= 0:
            raise ValueError("This loan is already paid off.")
        interest = int((Decimal(outstanding) * Decimal(loan["annual_rate"]) / 1200).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
        principal = min(outstanding, max(0, loan["emi"] - interest))
        category = self.store.scalar("SELECT id FROM categories WHERE name='Loans' AND kind='Expense'") if self.store.scalar("SELECT COUNT(*) FROM categories WHERE name='Loans' AND kind='Expense'") else None
        self.transaction(preset={"loan_id": loan["id"], "amount": principal + interest,
                                 "principal": principal, "description": f'Loan payment: {loan["name"]}',
                                 "category_id": category})

    def loan_schedule(self):
        loan = self.get("loans", self.selected("Loans"))
        balance = self.store.outstanding(loan["id"])
        due = self.loan_due(loan)
        lines = ["Estimate from current principal; monthly reducing-balance interest.",
                 "Actual lender schedules may differ (fees, day-count, variable rates).",
                 "Due dates credit every EMI-worth of recorded payments as one period.",
                 "Due date     Payment      Principal    Interest     Remaining"]
        for _ in range(1200):
            if balance <= 0:
                break
            interest = int((Decimal(balance) * Decimal(loan["annual_rate"]) / 1200).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
            if loan["emi"] <= interest:
                lines.append("EMI does not cover interest; increase EMI to amortize this loan.")
                break
            principal = min(balance, loan["emi"] - interest)
            balance -= principal
            lines.append(f"{due}  {money(principal+interest):>12} {money(principal):>12} {money(interest):>12} {money(balance):>12}")
            due = next_due(due, "Monthly", date.fromisoformat(loan["first_due"]).day)
        if balance > 0 and len(lines) >= 1204:
            lines.append("Schedule truncated at 1,200 months.")
        self.text_window("Loan payment schedule", "\n".join(lines))

    def policy(self, identifier=None):
        data = self.get("policies", identifier)
        def save(values):
            if not values["name"]:
                raise ValueError("Policy name is required.")
            values["premium"], values["coverage"] = cents(values["premium"], True), cents(values["coverage"])
            if values["coverage"] < 0:
                raise ValueError("Coverage cannot be negative.")
            values["renewal_date"] = self.parse_date(values["renewal_date"])
            values["anchor"] = data.get("anchor", 1) if values["renewal_date"] == data.get("renewal_date") else date.fromisoformat(values["renewal_date"]).day
            self.write("policies", values, identifier)
        self.form("Insurance / policy", [
            ("name", "Policy name", str, data.get("name", "")),
            ("provider", "Insurer", str, data.get("provider", "")),
            ("policy_number", "Policy number", str, data.get("policy_number", "")),
            ("premium", "Premium", str, money(data.get("premium", 0))),
            ("coverage", "Coverage", str, money(data.get("coverage", 0))),
            ("renewal_date", "Next premium / renewal date", str, self.display_date(data.get("renewal_date", date.today().isoformat()))),
            ("frequency", "Premium frequency", ("Monthly", "Quarterly", "Yearly"), data.get("frequency", "Yearly")),
            ("nominee", "Nominee(s)", str, data.get("nominee", "")),
            ("document", "Document path / reference", str, data.get("document", "")),
            ("notes", "Notes", str, data.get("notes", "")),
        ], save)

    def pay_premium(self):
        policy = self.get("policies", self.selected("Policies"))
        self.transaction(preset={"policy_id": policy["id"], "amount": policy["premium"],
                                 "description": f'Premium: {policy["name"]}'})

    def advance_policy(self):
        policy = self.get("policies", self.selected("Policies"))
        if messagebox.askyesno("Advance renewal", "Move the next due date forward one premium period? Record the premium payment separately.", parent=self.root):
            self.write("policies", {"renewal_date": next_due(policy["renewal_date"], policy["frequency"], policy["anchor"])}, policy["id"])
            self.refresh()

    def budget(self, identifier=None):
        data = self.get("budgets", identifier)
        def save(values):
            self.validate_month(values["month"])
            values["amount"] = cents(values["amount"], True)
            try:
                values["warning"] = int(values["warning"])
            except ValueError:
                raise ValueError("Warning percentage must be a whole number.") from None
            if not 1 <= values["warning"] <= 100:
                raise ValueError("Warning percentage must be 1–100.")
            self.write("budgets", values, identifier)
        self.form("Monthly budget — parent limits include subsections", [
            ("month", "Month (YYYY-MM)", str, data.get("month", self.month.get())),
            ("category_id", "Spending section", self.choices("categories", False, "kind='Expense' AND bucket='Spending'"), data.get("category_id")),
            ("amount", "Monthly limit", str, money(data.get("amount", 0))),
            ("warning", "Warn at (%)", str, data.get("warning", 80)),
        ], save)

    def recurring(self, identifier=None):
        data = self.get("recurring", identifier)
        def save(values):
            values["amount"] = cents(values["amount"], True)
            values["principal"] = cents(values["principal"])
            values["next_date"] = self.parse_date(values["next_date"])
            values["anchor"] = data.get("anchor", 1) if values["next_date"] == data.get("next_date") else date.fromisoformat(values["next_date"]).day
            values["active"] = int(values["active"] == "Yes")
            if not values["name"]:
                raise ValueError("Schedule name is required.")
            if values["kind"] == "Transfer":
                if values["account_id"] == values["to_account_id"] or values["to_account_id"] is None:
                    raise ValueError("Choose two different transfer accounts.")
                values.update(category_id=None, loan_id=None, policy_id=None, principal=0)
            else:
                category = self.get("categories", values["category_id"])
                if not category or category["kind"] != values["kind"]:
                    raise ValueError("Choose a section matching the transaction type.")
                values["to_account_id"] = None
                if values["loan_id"] or values["policy_id"]:
                    if values["kind"] != "Expense" or category["bucket"] != "Spending":
                        raise ValueError("Loan/policy schedules require a Spending section.")
                if values["loan_id"] and values["policy_id"]:
                    raise ValueError("Choose a loan or a policy, not both.")
                if not 0 <= values["principal"] <= values["amount"] or (values["principal"] and not values["loan_id"]):
                    raise ValueError("Principal must be part of a linked loan payment.")
            self.write("recurring", values, identifier)
        self.form("Recurring — nothing posts without confirmation", [
            ("name", "Description / schedule name", str, data.get("name", "")),
            ("kind", "Type", ("Income", "Expense", "Transfer"), data.get("kind", "Expense")),
            ("amount", "Amount", str, money(data.get("amount", 0))),
            ("category_id", "Section", self.choices("categories", True, "archived=0 OR id=?", (data.get("category_id", -1),)), data.get("category_id")),
            ("account_id", "Account", self.choices("accounts"), data.get("account_id")),
            ("to_account_id", "Transfer to", self.choices("accounts", True), data.get("to_account_id")),
            ("next_date", "Next due date", str, self.display_date(data.get("next_date", date.today().isoformat()))),
            ("frequency", "Frequency", ("Daily", "Weekly", "Monthly", "Quarterly", "Yearly"), data.get("frequency", "Monthly")),
            ("active", "Active", ("Yes", "No"), "Yes" if data.get("active", 1) else "No"),
            ("loan_id", "Loan", self.choices("loans", True), data.get("loan_id")),
            ("principal", "Principal portion", str, money(data.get("principal", 0))),
            ("policy_id", "Policy", self.choices("policies", True), data.get("policy_id")),
        ], save)

    def review_due(self):
        rules = self.store.rows("SELECT * FROM recurring WHERE active=1 AND next_date<=? ORDER BY next_date,id", (date.today().isoformat(),))
        if not rules:
            messagebox.showinfo("Due schedules", "No recurring transactions are due. Loan and policy reminders are on the Dashboard.", parent=self.root)
            return
        rule = dict(rules[0])
        if messagebox.askyesno("Confirm scheduled transaction", f'{rule["name"]}\nDue {rule["next_date"]}: {money(rule["amount"])}\nReview and post this occurrence? Nothing is posted if you cancel.', parent=self.root):
            preset = dict(rule)
            preset.update(date=rule["next_date"], description=rule["name"])
            self.transaction(preset=preset, rule=rule)

    def reconcile(self):
        def save(values):
            values["date"] = self.parse_date(values["date"])
            values["statement"] = cents(values["statement"])
            values["recorded"] = self.store.balance(values["account_id"], values["date"])
            self.write("reconciliations", values)
        self.form("Reconcile — snapshot through the statement date; no automatic adjustment", [
            ("account_id", "Account", self.choices("accounts"), None),
            ("date", "Statement date", str, self.display_date(date.today().isoformat())),
            ("statement", "Statement closing balance", str, "0.00"),
            ("notes", "Statement reference / notes", str, ""),
        ], save)

    def validate_month(self, month):
        if len(month) != 7 or date.fromisoformat(month + "-01").strftime("%Y-%m") != month:
            raise ValueError("Month must be YYYY-MM.")

    def tx_rows(self):
        clauses, params = ["1"], []
        for key, operator in (("From", ">="), ("To", "<=")):
            if self.filters[key].get().strip():
                clauses.append("t.date" + operator + "?")
                params.append(self.parse_date(self.filters[key].get()))
        if self.filters["From"].get() and self.filters["To"].get() and params[0] > params[1]:
            raise ValueError("The start date must not follow the end date.")
        account = self.filters["Account"].get()
        if account:
            identifier = self.choices("accounts").get(account)
            if identifier is None:
                raise ValueError("Selected account no longer exists.")
            clauses.append("(t.account_id=? OR t.to_account_id=?)")
            params.extend((identifier, identifier))
        section = self.filters["Section"].get()
        if section:
            identifier = self.choices("categories").get(section)
            if identifier is None:
                raise ValueError("Selected section no longer exists.")
            clauses.append("(c.id=? OR c.parent_id=?)")
            params.extend((identifier, identifier))
        description = self.filters["Description"].get().strip()
        if description:
            clauses.append("instr(lower(t.description),lower(?))>0")
            params.append(description)
        return self.store.rows(f"""
            SELECT t.*, c.name AS section, a.name AS account, b.name AS target
            FROM transactions t LEFT JOIN categories c ON c.id=t.category_id
            LEFT JOIN accounts a ON a.id=t.account_id LEFT JOIN accounts b ON b.id=t.to_account_id
            WHERE {' AND '.join(clauses)} ORDER BY t.date DESC,t.id DESC""", params)

    def clear_filters(self):
        for variable in self.filters.values():
            variable.set("")
        self.refresh()

    def monthly(self, month):
        return self.store.db.execute("""
            SELECT COALESCE(SUM(CASE WHEN t.kind='Income' THEN t.amount ELSE 0 END),0),
              COALESCE(SUM(CASE WHEN t.kind='Expense' AND COALESCE(c.bucket,'Spending')='Spending' THEN t.amount ELSE 0 END),0),
              COALESCE(SUM(CASE WHEN t.kind='Expense' AND c.bucket='Savings' THEN t.amount ELSE 0 END),0)
            FROM transactions t LEFT JOIN categories c ON c.id=t.category_id WHERE substr(t.date,1,7)=?""", (month,)).fetchone()

    def spending_by_section(self, month):
        return self.store.rows("""
            SELECT COALESCE(p.name, c.name, 'Uncategorized') AS name, SUM(t.amount) AS total
            FROM transactions t
            LEFT JOIN categories c ON c.id=t.category_id
            LEFT JOIN categories p ON p.id=c.parent_id
            WHERE t.kind='Expense' AND COALESCE(c.bucket,'Spending')='Spending'
              AND substr(t.date,1,7)=?
            GROUP BY COALESCE(c.parent_id,c.id)
            ORDER BY total DESC, name COLLATE NOCASE""", (month,))

    def budget_rows(self):
        result = []
        for budget in self.store.rows("SELECT b.*,c.name FROM budgets b JOIN categories c ON c.id=b.category_id ORDER BY month DESC,c.name"):
            spent = self.store.scalar("""
                SELECT COALESCE(SUM(t.amount),0) FROM transactions t JOIN categories c ON c.id=t.category_id
                WHERE t.kind='Expense' AND c.bucket='Spending' AND substr(t.date,1,7)=?
                AND (c.id=? OR c.parent_id=?)""", (budget["month"], budget["category_id"], budget["category_id"]))
            percent = Decimal(spent) * 100 / budget["amount"]
            status = "EXCEEDED" if spent > budget["amount"] else "AT LIMIT" if spent == budget["amount"] else "WARNING" if percent >= budget["warning"] else "OK"
            result.append((budget["id"], (budget["month"], budget["name"], money(budget["amount"]), money(spent), f"{percent:.1f}%", status)))
        return result

    def report_rows(self):
        rows = []
        for offset in range(11, -1, -1):
            current = date.fromisoformat(self.month.get() + "-01")
            index = current.year * 12 + current.month - 1 - offset
            year, month = divmod(index, 12)
            label = f"{year:04d}-{month+1:02d}"
            income, spending, savings = self.monthly(label)
            prior_index = index - 1
            prior_year, prior_month = divmod(prior_index, 12)
            previous = self.monthly(f"{prior_year:04d}-{prior_month+1:02d}")[1]
            change = "N/A" if previous == 0 else f"{Decimal(spending-previous)*100/previous:+.1f}%"
            rows.append((label, (label, money(income), money(spending), money(savings), money(income-spending-savings), change)))
        return rows

    def refresh(self):
        self.validate_month(self.month.get())
        accounts = self.store.rows("SELECT * FROM accounts ORDER BY name")
        total = sum(self.store.balance(row["id"]) for row in accounts)
        currency = self.store.setting("currency")
        self.summary.config(text=f"TOTAL BALANCE (all banks, current): {currency} {money(total)}")
        for key, table in (("Account", "accounts"), ("Section", "categories")):
            self.filter_boxes[key]["values"] = [""] + list(self.choices(table))
        self.fill("Accounts", [(row["id"], (row["name"], row["nickname"], money(row["opening_balance"]), money(self.store.balance(row["id"])))) for row in accounts])
        self.fill("Sections", [(row["id"], (row["kind"], row["name"], row["bucket"], row["parent"] or "", "Yes" if row["archived"] else "No")) for row in self.store.rows("SELECT c.*,p.name AS parent FROM categories c LEFT JOIN categories p ON p.id=c.parent_id ORDER BY c.kind,c.name")])
        self.fill("Transactions", [(row["id"], (self.display_date(row["date"]), row["kind"], row["description"], row["section"] or "",
                  row["account"] + (" → " + row["target"] if row["kind"] == "Transfer" else "") if row["account"] else "",
                  money(row["amount"]), money(row["principal"]) if row["loan_id"] else "",
                  money(row["amount"]-row["principal"]) if row["loan_id"] else "")) for row in self.tx_rows()])
        loans = self.store.rows("SELECT * FROM loans ORDER BY name")
        self.fill("Loans", [(row["id"], (row["name"], row["lender"], money(row["principal"]), money(self.store.outstanding(row["id"])),
                  row["annual_rate"] + "%", money(row["emi"]), self.loan_due(row),
                  f'{Decimal(row["principal"]-self.store.outstanding(row["id"]))*100/row["principal"]:.1f}%')) for row in loans])
        policies = self.store.rows("SELECT * FROM policies ORDER BY renewal_date")
        self.fill("Policies", [(row["id"], (row["name"], row["provider"], money(row["premium"]), money(row["coverage"]),
                  self.display_date(row["renewal_date"]), row["nominee"], row["document"])) for row in policies])
        budgets = self.budget_rows()
        self.fill("Budgets", budgets)
        self.fill("Recurring", [(row["id"], (row["name"], row["kind"], money(row["amount"]), row["account"], self.display_date(row["next_date"]), row["frequency"], "Yes" if row["active"] else "No")) for row in self.store.rows("SELECT r.*,a.name AS account FROM recurring r JOIN accounts a ON a.id=r.account_id ORDER BY next_date")])
        self.fill("Reconciliation", [(row["id"], (self.display_date(row["date"]), row["name"], money(row["statement"]), money(row["recorded"]),
                  money(row["statement"]-row["recorded"]), "Matched" if row["statement"] == row["recorded"] else "DISCREPANCY",
                  row["notes"])) for row in self.store.rows("SELECT r.*,a.name FROM reconciliations r JOIN accounts a ON a.id=r.account_id ORDER BY r.date DESC,r.id DESC")])
        self.fill("Reports", self.report_rows())
        income, spending, savings = self.monthly(self.month.get())
        last = calendar.monthrange(int(self.month.get()[:4]), int(self.month.get()[5:]))[1]
        closing = sum(self.store.balance(row["id"], self.month.get() + f"-{last:02d}") for row in accounts)
        lines = [f'{self.month.get()} — {currency}',
                 f"Income: {money(income)}    Everyday spending: {money(spending)}    Savings contributions: {money(savings)}",
                 f"Income less spending: {money(income-spending)}    Remaining after savings: {money(income-spending-savings)}",
                 f"Month-end bank balance: {money(closing)}    Current bank balance: {money(total)}",
                 "", "Alerts / upcoming due items (next 30 days):"]
        today, soon = date.today().isoformat(), (date.today()+timedelta(days=30)).isoformat()
        for _, values in budgets:
            if values[0] == self.month.get() and values[-1] != "OK":
                lines.append(f"Budget {values[1]}: {values[-1]} ({values[4]} used)")
        for loan in loans:
            due = self.loan_due(loan)
            if due != "Paid off" and due <= soon:
                lines.append(f'Loan {loan["name"]}: {"OVERDUE" if due < today else "due"} {due} (estimated), EMI {money(loan["emi"])}')
        for policy in policies:
            if policy["renewal_date"] <= soon:
                lines.append(f'Policy {policy["name"]}: {"OVERDUE" if policy["renewal_date"] < today else "due"} {policy["renewal_date"]}, premium {money(policy["premium"])}')
        count = self.store.scalar("SELECT COUNT(*) FROM recurring WHERE active=1 AND next_date<=?", (today,))
        lines.append(f"Recurring occurrences awaiting review: {count} schedules. Review posts one occurrence at a time.")
        if self.store.scalar("SELECT COUNT(*) FROM reconciliations WHERE statement!=recorded"):
            lines.append("Statement discrepancies exist; see Reconciliation (historical snapshots).")
        self.dashboard_text.configure(state="normal")
        self.dashboard_text.delete("1.0", "end")
        self.dashboard_text.insert("1.0", "\n".join(lines))
        self.dashboard_text.configure(state="disabled")
        self.draw_chart()
        self.draw_spending_chart()

    def draw_chart(self):
        if not self.store.db:
            return
        try:
            self.validate_month(self.month.get())
        except ValueError:
            return
        income, spending, savings = self.monthly(self.month.get())
        self.chart.delete("all")
        width, height = max(400, self.chart.winfo_width()), max(200, self.chart.winfo_height())
        maximum = max(income, spending, savings, 1)
        for index, (label, value, color) in enumerate((("Income", income, "#268a52"), ("Spending", spending, "#cc5555"), ("Savings", savings, "#487bb8"))):
            x = 45 + index * (width-70) / 3
            bar_height = (height-80) * value / maximum
            self.chart.create_rectangle(x, height-40-bar_height, x+(width-100)/4, height-40, fill=color, outline="")
            self.chart.create_text(x, height-23, text=label, anchor="w")
            self.chart.create_text(x, height-52-bar_height, text=money(value), anchor="w")

    def draw_spending_chart(self):
        if not self.store.db:
            return
        try:
            self.validate_month(self.month.get())
        except ValueError:
            return
        canvas = self.spending_chart
        canvas.delete("all")
        rows = self.spending_by_section(self.month.get())
        if not rows:
            canvas.create_text(15, 20, text="No spending in this month.", anchor="w")
            canvas.configure(scrollregion=(0, 0, canvas.winfo_width(), canvas.winfo_height()))
            return
        text_font = font.nametofont("TkDefaultFont")
        label_width = max(text_font.measure(row["name"]) for row in rows) + 25
        value_width = max(text_font.measure(money(row["total"])) for row in rows) + 20
        width = max(canvas.winfo_width(), label_width + value_width + 150)
        bar_width = width - label_width - value_width - 20
        maximum = max(row["total"] for row in rows)
        for index, row in enumerate(rows):
            y = 20 + index * 36
            canvas.create_text(10, y, text=row["name"], anchor="w")
            canvas.create_rectangle(label_width, y-9, label_width + bar_width * row["total"] / maximum,
                                    y+9, fill="#cc5555", outline="")
            canvas.create_text(label_width + bar_width + 10, y, text=money(row["total"]), anchor="w")
        canvas.configure(scrollregion=(0, 0, width, max(canvas.winfo_height(), 40 + len(rows) * 36)))

    def text_window(self, title, text):
        win = tk.Toplevel(self.root)
        win.title(title)
        widget = tk.Text(win, width=100, height=30, wrap="none")
        widget.pack(fill="both", expand=True)
        widget.insert("1.0", text)
        widget.configure(state="disabled")
        scroll = ttk.Scrollbar(win, command=widget.yview)
        scroll.pack(side="right", fill="y")
        widget.configure(yscrollcommand=scroll.set)

    def csv_write(self, path, headers, rows):
        # Prevent spreadsheet formulas from executing in descriptions/names.
        def cell(value):
            text = str(value)
            return "'" + text if text.lstrip().startswith(("=", "+", "-", "@", "\t", "\r")) else text
        output = io.StringIO(newline="")
        writer = csv.writer(output)
        writer.writerow(headers)
        writer.writerows([[cell(value) for value in row] for row in rows])
        atomic_write(Path(path), output.getvalue().encode("utf-8-sig"))

    def export_transactions(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], parent=self.root)
        if path:
            rows = self.tx_rows()
            self.csv_write(path, ["date", "kind", "description", "amount", "section", "account", "transfer_to", "loan_principal"],
                           [(row["date"], row["kind"], row["description"], money(row["amount"]), row["section"] or "", row["account"] or "", row["target"] or "", money(row["principal"])) for row in rows])
            messagebox.showinfo("Exported", "Filtered transactions exported. Exports are not encrypted.", parent=self.root)

    def export_report(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], parent=self.root)
        if path:
            self.csv_write(path, self.trees["Reports"]["columns"], [values for _, values in self.report_rows()])
            messagebox.showinfo("Exported", "Monthly report exported. Exports are not encrypted.", parent=self.root)

    def export_pdf(self):
        try:
            from reportlab.lib import colors
            from reportlab.lib.pagesizes import A4, landscape
            from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
            from reportlab.lib.styles import getSampleStyleSheet
        except ImportError:
            raise RuntimeError("PDF export requires: python -m pip install reportlab") from None
        path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF", "*.pdf")], parent=self.root)
        if not path:
            return
        from xml.sax.saxutils import escape
        styles = getSampleStyleSheet()
        buffer = io.BytesIO()
        document = SimpleDocTemplate(buffer, pagesize=landscape(A4))
        table = Table([["Month", "Income", "Spending", "Savings", "Remaining", "Spending change"]] + [list(values) for _, values in self.report_rows()], repeatRows=1)
        table.setStyle(TableStyle([("BACKGROUND", (0, 0), (-1, 0), colors.lightgrey), ("GRID", (0, 0), (-1, -1), .5, colors.grey)]))
        document.build([Paragraph("Personal finance — " + escape(self.store.setting("currency")), styles["Title"]), Spacer(1, 12), table])
        atomic_write(Path(path), buffer.getvalue())
        messagebox.showinfo("Exported", "PDF report exported. Exports are not encrypted.", parent=self.root)

    def import_csv(self):
        path = filedialog.askopenfilename(filetypes=[("CSV", "*.csv")], parent=self.root)
        if not path:
            return
        def configure(values):
            self.preview_import(path, values)
        self.form("CSV mapping — signed amount: credit positive, debit negative", [
            ("account_id", "Import into account", self.choices("accounts"), None),
            ("date_column", "Date column header", str, "date"),
            ("description_column", "Description column header", str, "description"),
            ("amount_column", "Signed amount header (blank if split)", str, "amount"),
            ("debit_column", "Debit header (split mode)", str, "debit"),
            ("credit_column", "Credit header (split mode)", str, "credit"),
            ("date_format", "CSV date format", ("%Y-%m-%d", "%d/%m/%Y", "%m/%d/%Y", "%d-%m-%Y"), "%Y-%m-%d"),
        ], configure)

    def preview_import(self, path, mapping):
        sections = self.store.rows("SELECT * FROM categories WHERE archived=0 ORDER BY name")
        existing = {(row["date"], row["kind"], row["amount"], row["description"].strip().casefold()) for row in self.store.rows("SELECT * FROM transactions WHERE account_id=?", (mapping["account_id"],))}
        proposals, rejected = [], []
        with open(path, encoding="utf-8-sig", newline="") as handle:
            reader = csv.DictReader(handle)
            needed = [mapping["date_column"], mapping["description_column"]]
            needed += [mapping["amount_column"]] if mapping["amount_column"] else [mapping["debit_column"], mapping["credit_column"]]
            if not reader.fieldnames or any(name not in reader.fieldnames for name in needed):
                raise ValueError("CSV headers do not match the configured column names.")
            seen = set(existing)
            for number, row in enumerate(reader, 2):
                try:
                    day = iso_date(row[mapping["date_column"]], mapping["date_format"])
                    description = row[mapping["description_column"]].strip() or "Imported transaction"
                    if mapping["amount_column"]:
                        signed = cents(row[mapping["amount_column"]])
                    else:
                        debit = cents(row[mapping["debit_column"]] or "0")
                        credit = cents(row[mapping["credit_column"]] or "0")
                        if debit < 0 or credit < 0 or (debit and credit):
                            raise ValueError("Split rows require one nonnegative debit or credit.")
                        signed = credit - debit
                    if signed == 0:
                        raise ValueError("Zero amount.")
                    kind = "Income" if signed > 0 else "Expense"
                    fingerprint = (day, kind, abs(signed), description.casefold())
                    if fingerprint in seen:
                        rejected.append(f"Row {number}: possible duplicate; not selected.")
                        continue
                    seen.add(fingerprint)
                    available = [section for section in sections if section["kind"] == kind]
                    if not available:
                        raise ValueError(f"No active {kind} sections.")
                    history = self.store.rows("""SELECT category_id FROM transactions WHERE lower(description)=lower(?)
                        AND kind=? AND category_id IN (SELECT id FROM categories WHERE archived=0)
                        ORDER BY id DESC LIMIT 1""", (description, kind))
                    suggestion = next((section for section in available if section["name"].casefold() in description.casefold()), available[0])
                    category_id = history[0]["category_id"] if history else suggestion["id"]
                    key = hashlib.sha256(json.dumps([mapping["account_id"], *fingerprint], ensure_ascii=False).encode()).hexdigest()
                    proposals.append({"date": day, "kind": kind, "description": description, "amount": abs(signed),
                                      "account_id": mapping["account_id"], "to_account_id": None, "category_id": category_id,
                                      "loan_id": None, "principal": 0, "policy_id": None, "import_key": key})
                except (ValueError, TypeError, AttributeError) as error:
                    rejected.append(f"Row {number}: {error}")
        win = tk.Toplevel(self.root)
        win.title("Import preview — review suggestions; duplicate matching is conservative")
        tree = ttk.Treeview(win, columns=("date", "type", "description", "amount", "section"), show="headings", selectmode="extended", height=18)
        for key in tree["columns"]:
            tree.heading(key, text=key.title())
        tree.pack(fill="both", expand=True)
        names = {row["id"]: row["name"] for row in sections}
        for index, proposal in enumerate(proposals):
            tree.insert("", "end", iid=str(index), values=(proposal["date"], proposal["kind"], proposal["description"], money(proposal["amount"]), names[proposal["category_id"]]))
        tree.selection_set(tree.get_children())
        ttk.Label(win, text=f"{len(proposals)} candidates; {len(rejected)} duplicates/errors. Ctrl-click to deselect rows.").pack(pady=5)
        def recategorize():
            selected = tree.selection()
            if not selected:
                raise ValueError("Select preview rows first.")
            kinds = {proposals[int(item)]["kind"] for item in selected}
            if len(kinds) != 1:
                raise ValueError("Select only Income rows or only Expense rows to change sections.")
            def apply(values):
                for item in selected:
                    proposal = proposals[int(item)]
                    proposal["category_id"] = values["category_id"]
                    tree.set(item, "section", names[values["category_id"]])
            self.form("Change suggested section", [("category_id", "Section", self.choices("categories", False, "kind=? AND archived=0", (next(iter(kinds)),)), None)], apply)
        def post():
            selected = tree.selection()
            if not selected:
                raise ValueError("Select at least one preview row.")
            if not messagebox.askyesno("Confirm import", f"Post {len(selected)} selected transactions?", parent=win):
                return
            with self.store.change() as db:
                for item in selected:
                    proposal = proposals[int(item)]
                    self.store.validate_transaction(proposal)
                    matches = self.store.scalar("""SELECT COUNT(*) FROM transactions WHERE account_id=?
                        AND date=? AND kind=? AND amount=? AND lower(trim(description))=lower(?)""",
                        (proposal["account_id"], proposal["date"], proposal["kind"], proposal["amount"], proposal["description"]))
                    if matches:
                        raise ValueError("A previewed transaction has since been posted. Re-import to refresh duplicate detection.")
                    keys = list(proposal)
                    db.execute(f"INSERT INTO transactions ({','.join(keys)}) VALUES ({','.join('?' for _ in keys)})", tuple(proposal.values()))
            win.destroy()
            self.refresh()
        actions = ttk.Frame(win)
        actions.pack(fill="x", pady=5)
        for label, action in [("Change section", recategorize), ("Post selected", post),
                              ("Show skipped rows", lambda: self.text_window("Import issues", "\n".join(rejected) or "None")),
                              ("Cancel", win.destroy)]:
            ttk.Button(actions, text=label, command=self.safe(action)).pack(side="left", padx=4)

    def settings(self):
        def save(values):
            if not values["currency"] or len(values["currency"]) > 12:
                raise ValueError("Currency label must contain 1–12 characters.")
            try:
                minutes = int(values["idle_minutes"])
            except ValueError:
                raise ValueError("Idle timeout must be a whole number.") from None
            if not 0 <= minutes <= 1440:
                raise ValueError("Idle timeout must be 0–1440 minutes; zero disables it.")
            values["idle_minutes"] = str(minutes)
            with self.store.change() as db:
                for key, value in values.items():
                    db.execute("UPDATE settings SET value=? WHERE key=?", (value, key))
        self.form("Configuration", [
            ("currency", "Currency label (no conversion)", str, self.store.setting("currency")),
            ("date_format", "Display / entry date format", ("%Y-%m-%d", "%d/%m/%Y", "%m/%d/%Y", "%d-%m-%Y"), self.store.setting("date_format")),
            ("idle_minutes", "Auto-lock minutes (encrypted only)", str, self.store.setting("idle_minutes")),
        ], save)

    def encrypt(self):
        crypto()
        self.store.require_encryption_support()
        password = simpledialog.askstring("Encryption", "New password (at least 12 characters):", show="*", parent=self.root)
        if password is None:
            return
        if len(password) < 12:
            raise ValueError("Use a password of at least 12 characters.")
        confirm = simpledialog.askstring("Confirm password", "Repeat password:", show="*", parent=self.root)
        if confirm != password:
            raise ValueError("Passwords do not match.")
        self.store.backup()
        previous = self.store.password
        self.store.password = password
        try:
            self.store.persist()
        except Exception:
            self.store.password = previous
            raise
        messagebox.showinfo("Encrypted", "Database encryption enabled. Previous backups may still be plaintext; protect or securely remove them yourself.", parent=self.root)

    def decrypt(self):
        if not self.store.password:
            raise ValueError("Database is not encrypted.")
        if not messagebox.askyesno("Disable protection", "Write this database as unencrypted SQLite?", parent=self.root):
            return
        self.store.backup()
        previous = self.store.password
        self.store.password = None
        try:
            self.store.persist()
        except Exception:
            self.store.password = previous
            raise
        messagebox.showinfo("Encryption disabled", "The database file is now unencrypted.", parent=self.root)

    def lock(self):
        if not self.store.password:
            raise ValueError("Enable encryption first. A login alone does not protect the database.")
        for child in self.root.winfo_children():
            if isinstance(child, tk.Toplevel):
                child.destroy()
        self.store.db.close()
        self.store.db = None
        self.store.password = None
        for tree in self.trees.values():
            children = tree.get_children()
            if children:
                tree.delete(*children)
        self.summary.configure(text="Locked")
        self.dashboard_text.configure(state="normal")
        self.dashboard_text.delete("1.0", "end")
        self.dashboard_text.configure(state="disabled")
        self.chart.delete("all")
        self.spending_chart.delete("all")
        self.root.withdraw()
        gate = tk.Toplevel(self.root)
        gate.title("Finance tracker locked")
        gate.geometry("380x150")
        gate.protocol("WM_DELETE_WINDOW", self.close)
        ttk.Label(gate, text="Database is locked. Unlock to continue.").pack(pady=15)
        def unlock():
            password = simpledialog.askstring("Unlock", "Database password:", show="*", parent=gate)
            if password is None:
                return
            self.store.open(password)
            gate.destroy()
            self.root.deiconify()
            self.activity()
            self.refresh()
        ttk.Button(gate, text="Unlock", command=self.safe(unlock)).pack(pady=8)

    def backup(self):
        target = self.store.backup()
        messagebox.showinfo("Backup created", str(target), parent=self.root)

    def restore(self):
        path = filedialog.askopenfilename(filetypes=[("Database / backup", "*.db *.bak"), ("All files", "*")], parent=self.root)
        if not path:
            return
        password = None
        if Path(path).read_bytes().startswith(MAGIC):
            password = simpledialog.askstring("Backup password", "Password used to encrypt this backup:", show="*", parent=self.root)
            if password is None:
                return
        if messagebox.askyesno("Restore database", "Replace all current records with this backup? A safety backup will be retained. Current encryption mode/password will be kept.", parent=self.root):
            self.store.replace(path, password)
            self.clear_filters()
            messagebox.showinfo("Restored", "Backup restored and migrated.", parent=self.root)

    def close(self):
        self.store.close()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    try:
        app = FinanceTracker(root)
    except (ValueError, sqlite3.Error, OSError, RuntimeError) as error:
        messagebox.showerror("Cannot start finance tracker", str(error), parent=root)
        root.destroy()
    else:
        root.mainloop()
