import os
from pathlib import Path
import tempfile
import tkinter as tk
import unittest

from finance_tracker import FinanceTracker, Store


class SpendingChartTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.store = Store(Path(self.tmp.name) / "expenses.db")
        self.store.open()
        with self.store.change() as db:
            db.execute("INSERT INTO accounts(name) VALUES ('Bank A')")
            db.execute("INSERT INTO accounts(name) VALUES ('Bank B')")
            groceries = self.store.scalar("SELECT id FROM categories WHERE name='Groceries'")
            db.execute("UPDATE categories SET archived=1 WHERE id=?", (groceries,))
            db.execute("INSERT INTO categories(kind,name,parent_id) VALUES ('Expense','Produce',?)",
                       (groceries,))
            produce = db.execute("SELECT id FROM categories WHERE name='Produce'").fetchone()[0]
            savings = self.store.scalar("SELECT id FROM categories WHERE name='Investments'")
            salary = self.store.scalar("SELECT id FROM categories WHERE name='Salary'")
            db.executemany("""INSERT INTO transactions(date,kind,description,amount,category_id,account_id,to_account_id)
                              VALUES (?,?,?,?,?,?,?)""", [
                ("2026-11-01", "Expense", "Groceries", 1000, groceries, 1, None),
                ("2026-11-02", "Expense", "Produce", 500, produce, 1, None),
                ("2026-11-03", "Expense", "Legacy", 250, None, 1, None),
                ("2026-11-04", "Expense", "Invest", 3000, savings, 1, None),
                ("2026-11-05", "Income", "Salary", 9000, salary, 1, None),
                ("2026-11-06", "Transfer", "Transfer", 1000, None, 1, 2),
                ("2026-10-01", "Expense", "Earlier", 8000, groceries, 1, None),
            ])
        self.app = FinanceTracker.__new__(FinanceTracker)
        self.app.store = self.store

    def tearDown(self):
        self.store.close()
        self.tmp.cleanup()

    def test_sections_include_children_and_legacy_expenses_not_savings(self):
        rows = self.app.spending_by_section("2026-11")
        self.assertEqual([(row["name"], row["total"]) for row in rows],
                         [("Groceries", 1500), ("Uncategorized", 250)])
        self.assertEqual(sum(row["total"] for row in rows), self.app.monthly("2026-11")[1])
        self.assertEqual(self.app.spending_by_section("2026-12"), [])

    @unittest.skipUnless(os.name == "nt" or os.environ.get("DISPLAY"), "GUI needs a display")
    def test_chart_renders_and_updates_for_selected_month(self):
        root = tk.Tk()
        try:
            self.app.month = tk.StringVar(master=root, value="2026-11")
            self.app.spending_chart = tk.Canvas(root, width=500, height=120)
            self.app.spending_chart.pack()
            root.update()
            self.app.draw_spending_chart()
            canvas = self.app.spending_chart
            labels = [canvas.itemcget(item, "text") for item in canvas.find_all()
                      if canvas.type(item) == "text"]
            self.assertEqual(labels, ["Groceries", "15.00", "Uncategorized", "2.50"])
            self.assertEqual(sum(canvas.type(item) == "rectangle" for item in canvas.find_all()), 2)
            self.app.month.set("2026-12")
            self.app.draw_spending_chart()
            self.assertEqual(canvas.itemcget(canvas.find_all()[0], "text"),
                             "No spending in this month.")
        finally:
            root.destroy()


if __name__ == "__main__":
    unittest.main()
