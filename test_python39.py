import os
from pathlib import Path
import sqlite3
import tempfile
import tkinter as tk
import unittest
from unittest.mock import patch

from finance_tracker import FinanceTracker, MAGIC, Store


class Python39CompatibilityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.path = Path(self.tmp.name) / "expenses.db"
        self.store = Store(self.path)

    def tearDown(self):
        self.store.close()
        self.tmp.cleanup()

    def test_create_save_backup_restore_reopen_and_rollback(self):
        self.store.open()
        with self.store.change() as db:
            db.execute("INSERT INTO accounts(name,opening_balance) VALUES('Bank',10000)")
        backup = self.store.backup()
        with self.store.change() as db:
            db.execute("UPDATE accounts SET opening_balance=20000 WHERE name='Bank'")
        self.assertEqual(self.store.balance(1), 20000)
        with patch.object(self.store, "persist", side_effect=OSError("disk full")):
            with self.assertRaises(OSError):
                with self.store.change() as db:
                    db.execute("UPDATE accounts SET opening_balance=30000 WHERE name='Bank'")
        self.assertEqual(self.store.balance(1), 20000)
        self.assertEqual(self.store.scalar("PRAGMA foreign_keys"), 1)
        self.store.replace(backup)
        self.assertEqual(self.store.balance(1), 10000)
        self.store.close()
        self.store = Store(self.path)
        self.store.open()
        self.assertEqual(self.store.balance(1), 10000)

    def test_migrates_existing_records(self):
        db = sqlite3.connect(str(self.path))
        db.executescript("""
            CREATE TABLE accounts(id INTEGER PRIMARY KEY,name TEXT NOT NULL COLLATE NOCASE UNIQUE,
                opening_balance INTEGER NOT NULL DEFAULT 0);
            CREATE TABLE categories(id INTEGER PRIMARY KEY,kind TEXT NOT NULL CHECK(kind IN ('Income','Expense')),
                name TEXT NOT NULL COLLATE NOCASE,UNIQUE(kind,name));
            CREATE TABLE transactions(id INTEGER PRIMARY KEY,date TEXT NOT NULL,
                kind TEXT NOT NULL CHECK(kind IN ('Income','Expense','Transfer')),
                description TEXT NOT NULL,amount INTEGER NOT NULL CHECK(amount>0),
                category_id INTEGER REFERENCES categories(id),account_id INTEGER REFERENCES accounts(id),
                to_account_id INTEGER REFERENCES accounts(id));
            INSERT INTO accounts VALUES (1,'Old bank',12345);
            INSERT INTO categories VALUES (1,'Expense','Custom');
            INSERT INTO transactions VALUES (1,'2026-01-01','Expense','Old expense',345,1,1,NULL);
        """)
        db.close()
        self.store.open()
        self.assertEqual(self.store.balance(1), 12000)
        self.assertEqual(self.store.scalar("SELECT description FROM transactions"), "Old expense")
        self.assertTrue(list((self.path.parent / "expenses.db.backups").glob("*.bak")))

    def test_no_encrypted_data_is_decrypted_on_unsupported_python(self):
        if hasattr(sqlite3.Connection, "serialize"):
            self.skipTest("Requires Python without SQLite serialization")
        self.path.write_bytes(MAGIC + b"encrypted")
        with patch("finance_tracker.unseal", side_effect=AssertionError("must not decrypt")):
            with self.assertRaisesRegex(RuntimeError, r"Python 3\.11"):
                self.store.open("password")
            with self.assertRaisesRegex(RuntimeError, r"Python 3\.11"):
                self.store.replace(self.path, "password")

    @unittest.skipUnless(os.environ.get("DISPLAY"), "GUI needs a display")
    def test_gui_opens_and_shows_total_balance(self):
        self.store.close()
        root = tk.Tk()
        root.withdraw()
        app = FinanceTracker(root, self.path)
        try:
            with app.store.change() as db:
                db.execute("INSERT INTO accounts(name,opening_balance) VALUES ('A',10000)")
                db.execute("INSERT INTO accounts(name,opening_balance) VALUES ('B',20000)")
            app.refresh()
            self.assertIn("300.00", app.summary.cget("text"))
        finally:
            app.close()
        self.store = Store(self.path)


if __name__ == "__main__":
    unittest.main()
