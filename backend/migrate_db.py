# migrate_db.py
"""Schema migration bootstrap for the current IIT-G database model."""

import os
import sqlite3

import database as db
from config import DATABASE_FILE


EXPECTED_TABLES = [
    "departments",
    "users",
    "chief_admin_scopes",
    "active_sessions",
    "counselor_students",
    "sent_messages",
    "batches",
    "semesters",
    "tests",
    "test_metadata",
    "student_marks",
    "counselor_mark_overrides",
    "password_reset_tokens",
    "format_settings",
    "app_config",
]


def _list_tables():
    if not os.path.exists(DATABASE_FILE):
        return []

    conn = sqlite3.connect(DATABASE_FILE)
    try:
        rows = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' ORDER BY name"
        ).fetchall()
        return [r[0] for r in rows]
    finally:
        conn.close()


def migrate():
    """Run all schema migrations through the authoritative database module."""
    print("Running schema bootstrap and migrations...")
    db.init_database()

    current_tables = set(_list_tables())
    missing = [t for t in EXPECTED_TABLES if t not in current_tables]

    if missing:
        print("Migration finished with missing tables:")
        for table in missing:
            print(f"  - {table}")
        return False

    print("Migration complete. All expected tables are present.")
    return True


if __name__ == "__main__":
    ok = migrate()
    raise SystemExit(0 if ok else 1)
