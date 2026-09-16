#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Importación segura del historial SHA-256 de YO REPARO RADIOS a Pecos.

Uso en Railway:
    python importar_historial_pecos.py

Requisitos:
- pecos.db en /data (o en RAILWAY_VOLUME_MOUNT_PATH)
- importar_en_pecos_1001775566217.sql en la misma carpeta que este script
"""

from __future__ import annotations

import os
import sqlite3
from datetime import datetime
from pathlib import Path

TARGET_CHAT_ID = -1001775566217
EXPECTED_UNIQUE_FINGERPRINTS = 1206
SQL_FILENAME = "importar_en_pecos_1001775566217.sql"


def main() -> None:
    volume = os.getenv("RAILWAY_VOLUME_MOUNT_PATH", "").strip() or "/data"
    db_path = Path(volume) / "pecos.db"
    sql_path = Path(__file__).resolve().parent / SQL_FILENAME

    print("=" * 72)
    print(" IMPORTADOR HISTÓRICO PECOS")
    print("=" * 72)
    print(f"DB:  {db_path}")
    print(f"SQL: {sql_path}")
    print(f"Grupo: {TARGET_CHAT_ID}")
    print()

    if not db_path.exists():
        raise SystemExit(f"ERROR: no existe {db_path}")

    if not sql_path.exists():
        raise SystemExit(f"ERROR: no existe {sql_path}")

    sql_text = sql_path.read_text(encoding="utf-8")

    insert_count = sql_text.count("INSERT OR IGNORE INTO file_fingerprints")
    print(f"INSERT encontrados en SQL: {insert_count}")

    if insert_count != EXPECTED_UNIQUE_FINGERPRINTS:
        raise SystemExit(
            f"ERROR: esperaba {EXPECTED_UNIQUE_FINGERPRINTS} INSERT y encontré {insert_count}. "
            "No se importó nada."
        )

    con = sqlite3.connect(db_path, timeout=60)
    con.row_factory = sqlite3.Row

    try:
        # Verificar estructura.
        cols = {
            row["name"]
            for row in con.execute("PRAGMA table_info(file_fingerprints)")
        }
        required = {
            "chat_id",
            "sha256",
            "message_id",
            "file_unique_id",
            "file_name",
            "file_size",
            "sender_id",
            "sender_name",
            "first_seen",
        }
        missing = required - cols
        if missing:
            raise SystemExit(
                "ERROR: la tabla file_fingerprints no tiene la estructura esperada. "
                f"Faltan: {sorted(missing)}"
            )

        before = con.execute(
            "SELECT COUNT(*) FROM file_fingerprints WHERE chat_id = ?",
            (TARGET_CHAT_ID,),
        ).fetchone()[0]

        print(f"Huellas actuales para el grupo: {before}")

        # Backup consistente usando la API de SQLite.
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        backup_path = Path(volume) / f"pecos_backup_before_history_{stamp}.db"

        print(f"Creando respaldo: {backup_path}")
        backup = sqlite3.connect(backup_path)
        try:
            con.backup(backup)
        finally:
            backup.close()

        if not backup_path.exists() or backup_path.stat().st_size == 0:
            raise SystemExit("ERROR: el respaldo no se creó correctamente.")

        print("Respaldo creado correctamente.")

        # Importación.
        print("Importando huellas...")
        con.executescript(sql_text)

        after = con.execute(
            "SELECT COUNT(*) FROM file_fingerprints WHERE chat_id = ?",
            (TARGET_CHAT_ID,),
        ).fetchone()[0]

        inserted = after - before

        print()
        print("=" * 72)
        print(" RESULTADO")
        print("=" * 72)
        print(f"Antes:      {before}")
        print(f"Después:    {after}")
        print(f"Agregadas:  {inserted}")
        print(f"Esperadas:  {EXPECTED_UNIQUE_FINGERPRINTS}")
        print(f"Backup:     {backup_path}")

        if after < EXPECTED_UNIQUE_FINGERPRINTS:
            raise SystemExit(
                "ADVERTENCIA: el total final es menor a las 1206 huellas históricas esperadas. "
                "Conserva el backup y revisa antes de continuar."
            )

        if after == EXPECTED_UNIQUE_FINGERPRINTS:
            print()
            print("✅ Importación completa: las 1206 huellas históricas están en Pecos.")
        else:
            print()
            print(
                "✅ Importación completada. El grupo ya tenía algunas huellas en Pecos, "
                "por eso el total final es superior a 1206."
            )

        print()
        print("NO elimines todavía el backup. Primero prueba Pecos con un archivo histórico.")

    finally:
        con.close()


if __name__ == "__main__":
    main()
