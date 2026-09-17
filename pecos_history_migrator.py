#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Pecos History Migrator
Importa la memoria histórica auditada a /data/pecos.db sin modificar
file_fingerprints ni la lógica SHA-256.

Uso recomendado en Railway:
  python pecos_history_migrator.py \
      --source /data/pecos_conversations_1001775566217_AUDITED.db \
      --target /data/pecos.db

El script:
1. valida ambas bases;
2. crea backup timestamp de pecos.db;
3. crea tablas conversation_* aisladas;
4. importa en una transacción;
5. verifica conteos;
6. comprueba que file_fingerprints no cambió.
"""

from __future__ import annotations
import argparse
import shutil
import sqlite3
from datetime import datetime
from pathlib import Path


def table_count(con: sqlite3.Connection, table: str) -> int:
    return int(con.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0])


def table_exists(con: sqlite3.Connection, table: str) -> bool:
    row = con.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name=?",
        (table,),
    ).fetchone()
    return row is not None


def backup_database(target: Path) -> Path:
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup = target.with_name(f"{target.stem}_backup_before_history_{stamp}{target.suffix}")
    src = sqlite3.connect(target)
    dst = sqlite3.connect(backup)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()
    return backup


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, help="Base histórica AUDITED")
    parser.add_argument("--target", default="/data/pecos.db", help="pecos.db de Railway")
    args = parser.parse_args()

    source = Path(args.source).resolve()
    target = Path(args.target).resolve()

    if not source.is_file():
        raise SystemExit(f"No existe source: {source}")
    if not target.is_file():
        raise SystemExit(f"No existe target: {target}")

    s = sqlite3.connect(source)
    s.row_factory = sqlite3.Row

    required = {"messages", "message_classifications", "conversation_qa_pairs"}
    missing = [t for t in required if not table_exists(s, t)]
    if missing:
        raise SystemExit(f"Source incompleta. Faltan: {', '.join(missing)}")

    src_messages = table_count(s, "messages")
    src_classes = table_count(s, "message_classifications")
    src_pairs = table_count(s, "conversation_qa_pairs")

    if src_messages != 113176 or src_classes != 113176:
        raise SystemExit(
            f"Conteos inesperados: messages={src_messages}, classifications={src_classes}"
        )

    backup = backup_database(target)
    print(f"BACKUP_OK={backup}")

    t = sqlite3.connect(target, timeout=60)
    t.row_factory = sqlite3.Row

    before_fp = table_count(t, "file_fingerprints") if table_exists(t, "file_fingerprints") else None

    try:
        t.execute("PRAGMA journal_mode=WAL")
        t.execute("PRAGMA synchronous=NORMAL")
        t.execute("BEGIN IMMEDIATE")

        t.executescript("""
        CREATE TABLE IF NOT EXISTS conversation_messages (
            chat_id INTEGER NOT NULL,
            message_id INTEGER NOT NULL,
            date_utc TEXT NOT NULL,
            edit_date_utc TEXT NOT NULL DEFAULT '',
            sender_id INTEGER NOT NULL DEFAULT 0,
            sender_name TEXT NOT NULL DEFAULT '',
            sender_username TEXT NOT NULL DEFAULT '',
            reply_to_message_id INTEGER NOT NULL DEFAULT 0,
            text TEXT NOT NULL,
            normalized_text TEXT NOT NULL,
            message_link TEXT NOT NULL DEFAULT '',
            media_type TEXT NOT NULL DEFAULT '',
            PRIMARY KEY(chat_id, message_id)
        );

        CREATE INDEX IF NOT EXISTS idx_conv_messages_chat_date
            ON conversation_messages(chat_id, date_utc);
        CREATE INDEX IF NOT EXISTS idx_conv_messages_reply
            ON conversation_messages(chat_id, reply_to_message_id);

        CREATE TABLE IF NOT EXISTS conversation_classifications (
            chat_id INTEGER NOT NULL,
            message_id INTEGER NOT NULL,
            primary_label TEXT NOT NULL,
            is_question INTEGER NOT NULL DEFAULT 0,
            is_request INTEGER NOT NULL DEFAULT 0,
            is_answer INTEGER NOT NULL DEFAULT 0,
            is_helpful INTEGER NOT NULL DEFAULT 0,
            is_closure INTEGER NOT NULL DEFAULT 0,
            is_confirmed_solution INTEGER NOT NULL DEFAULT 0,
            question_score INTEGER NOT NULL DEFAULT 0,
            request_score INTEGER NOT NULL DEFAULT 0,
            answer_score INTEGER NOT NULL DEFAULT 0,
            help_score INTEGER NOT NULL DEFAULT 0,
            closure_score INTEGER NOT NULL DEFAULT 0,
            parent_message_id INTEGER NOT NULL DEFAULT 0,
            root_question_id INTEGER NOT NULL DEFAULT 0,
            classification_reason TEXT NOT NULL DEFAULT '',
            classified_at TEXT NOT NULL,
            PRIMARY KEY(chat_id, message_id)
        );

        CREATE INDEX IF NOT EXISTS idx_conv_class_label
            ON conversation_classifications(chat_id, primary_label);
        CREATE INDEX IF NOT EXISTS idx_conv_class_root
            ON conversation_classifications(chat_id, root_question_id);

        CREATE TABLE IF NOT EXISTS conversation_qa_pairs (
            chat_id INTEGER NOT NULL,
            question_message_id INTEGER NOT NULL,
            answer_message_id INTEGER NOT NULL,
            confirmation_message_id INTEGER NOT NULL DEFAULT 0,
            confidence REAL NOT NULL DEFAULT 0,
            status TEXT NOT NULL,
            reason TEXT NOT NULL DEFAULT '',
            PRIMARY KEY(chat_id, question_message_id, answer_message_id)
        );

        CREATE INDEX IF NOT EXISTS idx_conv_qa_status
            ON conversation_qa_pairs(chat_id, status);
        """)

        # Adjuntar source y copiar sin tocar ninguna tabla preexistente de Pecos.
        t.execute("ATTACH DATABASE ? AS hist", (str(source),))

        t.execute("""
        INSERT OR REPLACE INTO conversation_messages
        SELECT chat_id, message_id, date_utc, edit_date_utc, sender_id,
               sender_name, sender_username, reply_to_message_id, text,
               normalized_text, message_link, media_type
        FROM hist.messages
        """)

        t.execute("""
        INSERT OR REPLACE INTO conversation_classifications
        SELECT chat_id, message_id, primary_label,
               is_question, is_request, is_answer, is_helpful, is_closure,
               is_confirmed_solution,
               question_score, request_score, answer_score, help_score, closure_score,
               parent_message_id, root_question_id,
               classification_reason, classified_at
        FROM hist.message_classifications
        """)

        t.execute("""
        INSERT OR REPLACE INTO conversation_qa_pairs
        SELECT chat_id, question_message_id, answer_message_id,
               confirmation_message_id, confidence, status, reason
        FROM hist.conversation_qa_pairs
        """)

        t.commit()
        t.execute("DETACH DATABASE hist")

    except Exception:
        t.rollback()
        t.close()
        s.close()
        raise

    after_fp = table_count(t, "file_fingerprints") if table_exists(t, "file_fingerprints") else None

    dst_messages = table_count(t, "conversation_messages")
    dst_classes = table_count(t, "conversation_classifications")
    dst_pairs = table_count(t, "conversation_qa_pairs")

    print(f"MESSAGES={dst_messages}")
    print(f"CLASSIFICATIONS={dst_classes}")
    print(f"QA_PAIRS={dst_pairs}")
    print(f"FILE_FINGERPRINTS_BEFORE={before_fp}")
    print(f"FILE_FINGERPRINTS_AFTER={after_fp}")

    if dst_messages != src_messages:
        raise SystemExit("ERROR: cantidad de mensajes importados no coincide")
    if dst_classes != src_classes:
        raise SystemExit("ERROR: cantidad de clasificaciones no coincide")
    if dst_pairs != src_pairs:
        raise SystemExit("ERROR: cantidad de pares no coincide")
    if before_fp != after_fp:
        raise SystemExit("ERROR: file_fingerprints cambió; restaurar backup")

    integrity = t.execute("PRAGMA integrity_check").fetchone()[0]
    if integrity != "ok":
        raise SystemExit(f"ERROR integrity_check: {integrity}")

    print("INTEGRITY=ok")
    print("MIGRATION=OK")
    t.close()
    s.close()


if __name__ == "__main__":
    main()
