#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import os
import runpy
import sys
import traceback
from datetime import datetime

TARGET = "/app/main.py"
PERSISTENT_LOG = "/data/pecos_boot_error.log"


def emit(text: str = "") -> None:
    print(text, flush=True)
    try:
        with open(PERSISTENT_LOG, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")
            fh.flush()
    except Exception:
        pass


emit("=" * 72)
emit(f"[BOOT_DIAG] Inicio: {datetime.now().isoformat()}")
emit(f"[BOOT_DIAG] Python: {sys.version.replace(chr(10), ' ')}")
emit(f"[BOOT_DIAG] Executable: {sys.executable}")
emit(f"[BOOT_DIAG] CWD: {os.getcwd()}")
emit(f"[BOOT_DIAG] main.py: {TARGET}")
emit("=" * 72)

try:
    runpy.run_path(TARGET, run_name="__main__")
except BaseException as exc:
    emit("")
    emit("!" * 72)
    emit("[BOOT_DIAG] ERROR FATAL AL EJECUTAR PECOS")
    emit(f"[BOOT_DIAG] Tipo: {type(exc).__name__}")
    emit(f"[BOOT_DIAG] Mensaje: {exc}")
    emit("-" * 72)
    for line in traceback.format_exc().splitlines():
        emit(line)
    emit("!" * 72)
    raise
