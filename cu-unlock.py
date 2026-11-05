#!/usr/bin/env python3
"""
cu-unlock: пошаговый TUI для разблокировки CU6/CU7 и второго render backend
на HP Ryzen 5 5300U (Lucienne, 1002:164c rev c3, subsystem 103c:887a), Arch Linux.

Только стандартная библиотека. Каждый шаг: проверка до -> действие -> проверка
после, подтверждение там, где что-то пишется в систему. Патч зашит под эту одну
машину: на другой скрипт остановится на шаге «Железо».

  python3 cu-unlock.py              # curses
  python3 cu-unlock.py --plain      # без curses (ssh, TTY)
  python3 cu-unlock.py --dry-run    # ничего не меняет, печатает команды
  python3 cu-unlock.py --workdir D  # исходники ядра (по умолчанию ~/amdbuild)

Профили загрузчика: cuN (lucienne_cu_mode 1-3) и/или rbM (lucienne_rb_mode 1-2),
например cu3 или cu3rb1. Основная запись не меняется: создаются только копии
<запись>-<профиль>.conf. Состояние и лог: ~/.cache/cu-unlock/,
бэкап стокового модуля: ~/.local/share/cu-unlock/backup/<ядро>/.
"""
from __future__ import annotations

import argparse
import contextlib
import curses
import difflib
import gzip
import hashlib
import json
import locale
import os
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import textwrap
import time
import traceback
import urllib.request
from pathlib import Path

__version__ = "1.0"

# --------------------------------------------------------------------------
# константы
# --------------------------------------------------------------------------
HW = {"vendor": 0x1002, "device": 0x164C, "subvendor": 0x103C,
      "subdevice": 0x887A, "revision": 0xC3}
PARAM = "lucienne_cu_mode"
RB_PARAM = "lucienne_rb_mode"
# режим -> (ожидаемый active_cu_number, ожидаемый final CC_GC_SHADER_ARRAY_CONFIG)
MODE_INFO = {0: (6, 0xFFC00000), 1: (6, 0xFFC00000),
             2: (7, 0xFF800000), 3: (8, 0xFF000000)}
# RB-режим -> (ожидаемый backend_enable_mask, ожидаемый final CC_RB_BACKEND_DISABLE)
RB_INFO = {1: (0x1, 0x00020000), 2: (0x3, 0x00000000)}
STOCK_RASTER = 0x4A00126A  # PA_SC_RASTER_CONFIG, снят umr на стоке
STATE_DIR = Path.home() / ".cache" / "cu-unlock"
BACKUP_DIR = Path.home() / ".local" / "share" / "cu-unlock" / "backup"
OK_SYM = "✓" if "utf" in (locale.getpreferredencoding(False) or "").lower() else "+"
SYM = {"done": f"[{OK_SYM}]", "todo": "[ ]", "failed": "[!]", "skipped": "[-]"}


class StepError(Exception):
    pass


class Abort(Exception):
    pass


# --------------------------------------------------------------------------
# патч gfx_v9_0.c (та же логика, что в lucienne_probe.py)
# --------------------------------------------------------------------------
def tabify(s: str) -> str:
    return re.sub(r"^( {4})+", lambda m: "\t" * (len(m.group(0)) // 4), s,
                  flags=re.M)


C_PARAM = tabify('''\
/*
 * Experimental probe for one exact machine (HP Ryzen 5 5300U, Lucienne).
 * 0 = stock (default)
 * 1 = clear CU6 inactive bit, read back, restore stock
 * 2 = leave CU6 enabled
 * 3 = leave CU6 and CU7 enabled
 */
int lucienne_cu_mode;
module_param(lucienne_cu_mode, int, 0444);
MODULE_PARM_DESC(lucienne_cu_mode,
         "HP 5300U Lucienne: 0=stock, 1=probe CU6 and restore, 2=enable CU6, 3=enable CU6+CU7");

''')

C_HELPER = tabify('''\
#define LUCIENNE_5300U_CC_STOCK	0xffc00000U
#define LUCIENNE_5300U_CU6	(1U << 22)
#define LUCIENNE_5300U_CU7	(1U << 23)

/* Caller holds grbm_idx_mutex. */
static void lucienne_5300u_cu_probe(struct amdgpu_device *adev)
{
    u32 orig, user, target, after, final;
    bool restore;

    if (lucienne_cu_mode < 1 || lucienne_cu_mode > 3)
        return;

    if (adev->pdev->device != 0x164c ||
        adev->pdev->subsystem_vendor != 0x103c ||
        adev->pdev->subsystem_device != 0x887a ||
        adev->pdev->revision != 0xc3 ||
        amdgpu_ip_version(adev, GC_HWIP, 0) != IP_VERSION(9, 3, 0) ||
        adev->gfx.config.max_shader_engines != 1 ||
        adev->gfx.config.max_sh_per_se != 1 ||
        adev->gfx.config.max_cu_per_sh != 8) {
        dev_warn(adev->dev,
             "lucienne-5300u: identity/geometry mismatch, skipped\\n");
        return;
    }

    amdgpu_gfx_select_se_sh(adev, 0, 0, 0xffffffff, 0);
    orig = RREG32_SOC15(GC, 0, mmCC_GC_SHADER_ARRAY_CONFIG);
    user = RREG32_SOC15(GC, 0, mmGC_USER_SHADER_ARRAY_CONFIG);

    if (orig != LUCIENNE_5300U_CC_STOCK) {
        dev_warn(adev->dev,
             "lucienne-5300u: unexpected CC=0x%08x USER=0x%08x, skipped\\n",
             orig, user);
        goto out;
    }

    target = orig & ~LUCIENNE_5300U_CU6;
    if (lucienne_cu_mode == 3)
        target &= ~LUCIENNE_5300U_CU7;

    WREG32_SOC15(GC, 0, mmCC_GC_SHADER_ARRAY_CONFIG, target);
    after = RREG32_SOC15(GC, 0, mmCC_GC_SHADER_ARRAY_CONFIG);
    final = after;

    /* Probe mode, or write did not land exactly: go back to stock. */
    restore = lucienne_cu_mode == 1 || after != target;
    if (restore && after != orig) {
        WREG32_SOC15(GC, 0, mmCC_GC_SHADER_ARRAY_CONFIG, orig);
        final = RREG32_SOC15(GC, 0, mmCC_GC_SHADER_ARRAY_CONFIG);
    }

    dev_info(adev->dev,
         "lucienne-5300u: mode=%d CC=0x%08x USER=0x%08x write=0x%08x readback=0x%08x final=0x%08x\\n",
         lucienne_cu_mode, orig, user, target, after, final);

    if (after == target)
        dev_info(adev->dev, "lucienne-5300u: write ACCEPTED\\n");
    else
        dev_warn(adev->dev, "lucienne-5300u: write REJECTED\\n");

    if (restore && final != orig)
        dev_err(adev->dev,
            "lucienne-5300u: restore failed, CC=0x%08x\\n", final);
out:
    amdgpu_gfx_select_se_sh(adev, 0xffffffff, 0xffffffff, 0xffffffff, 0);
}

''')

C_CALL = "\tlucienne_5300u_cu_probe(adev);\n"
FUNC_RE = re.compile(r"^static int gfx_v9_0_get_cu_info\([^;{]*\)\s*\{", re.M)
CONSTANTS_RE = re.compile(
    r"^static void gfx_v9_0_constants_init\([^;{]*\)\s*\{", re.M)
FW_ANCHOR = 'MODULE_FIRMWARE("amdgpu/vega10_ce.bin");\n'
RB_CALL_ANCHOR = "\tif (adev->gfx.num_gfx_rings)\n\t\tgfx_v9_0_setup_rb(adev);\n"
CU_MARK = "int lucienne_cu_mode;"
RB_MARK = "int lucienne_rb_mode;"
MARKS = {"cu": CU_MARK, "rb": RB_MARK}
PARTS = ("cu", "rb")

C_RB_PARAM = tabify('''\
/*
 * Experimental second render-backend probe, same machine as the CU probe.
 * 0 = stock (default)
 * 1 = clear the RB1 disable bit, read back, restore stock
 * 2 = leave RB1 enabled
 */
int lucienne_rb_mode;
module_param(lucienne_rb_mode, int, 0444);
MODULE_PARM_DESC(lucienne_rb_mode,
         "HP 5300U Lucienne: 0=stock, 1=probe RB1 and restore, 2=enable RB1");

''')

C_RB_HELPER = tabify('''\
#define LUCIENNE_5300U_RB_STOCK 0x00020000U
#define LUCIENNE_5300U_RB1 (1U << 17)

static bool lucienne_5300u_rb_id_ok(struct amdgpu_device *adev)
{
    return adev->pdev->device == 0x164c &&
           adev->pdev->subsystem_vendor == 0x103c &&
           adev->pdev->subsystem_device == 0x887a &&
           adev->pdev->revision == 0xc3 &&
           amdgpu_ip_version(adev, GC_HWIP, 0) == IP_VERSION(9, 3, 0) &&
           adev->gfx.config.max_shader_engines == 1 &&
           adev->gfx.config.max_sh_per_se == 1 &&
           adev->gfx.config.max_backends_per_se == 2;
}

/* Runs before gfx_v9_0_setup_rb(); takes grbm_idx_mutex itself. */
static void lucienne_5300u_rb_probe(struct amdgpu_device *adev)
{
    u32 orig, user, target, after, final;
    bool restore;

    if (lucienne_rb_mode < 1 || lucienne_rb_mode > 2)
        return;

    if (!lucienne_5300u_rb_id_ok(adev)) {
        dev_warn(adev->dev,
             "lucienne-5300u-rb: identity/geometry mismatch (se=%u sh=%u be=%u), skipped\\n",
             adev->gfx.config.max_shader_engines,
             adev->gfx.config.max_sh_per_se,
             adev->gfx.config.max_backends_per_se);
        return;
    }

    mutex_lock(&adev->grbm_idx_mutex);
    amdgpu_gfx_select_se_sh(adev, 0, 0, 0xffffffff, 0);
    orig = RREG32_SOC15(GC, 0, mmCC_RB_BACKEND_DISABLE);
    user = RREG32_SOC15(GC, 0, mmGC_USER_RB_BACKEND_DISABLE);

    if (orig != LUCIENNE_5300U_RB_STOCK) {
        dev_warn(adev->dev,
             "lucienne-5300u-rb: unexpected CC_RB=0x%08x USER_RB=0x%08x, skipped\\n",
             orig, user);
        goto out;
    }

    target = orig & ~LUCIENNE_5300U_RB1;
    WREG32_SOC15(GC, 0, mmCC_RB_BACKEND_DISABLE, target);
    after = RREG32_SOC15(GC, 0, mmCC_RB_BACKEND_DISABLE);
    final = after;

    /* Probe mode, or write did not land exactly: go back to stock. */
    restore = lucienne_rb_mode == 1 || after != target;
    if (restore && after != orig) {
        WREG32_SOC15(GC, 0, mmCC_RB_BACKEND_DISABLE, orig);
        final = RREG32_SOC15(GC, 0, mmCC_RB_BACKEND_DISABLE);
    }

    dev_info(adev->dev,
         "lucienne-5300u-rb: mode=%d CC_RB=0x%08x USER_RB=0x%08x write=0x%08x readback=0x%08x final=0x%08x\\n",
         lucienne_rb_mode, orig, user, target, after, final);

    if (after == target)
        dev_info(adev->dev, "lucienne-5300u-rb: write ACCEPTED\\n");
    else
        dev_warn(adev->dev, "lucienne-5300u-rb: write REJECTED\\n");

    if (restore && final != orig)
        dev_err(adev->dev,
            "lucienne-5300u-rb: restore failed, CC_RB=0x%08x\\n", final);
out:
    amdgpu_gfx_select_se_sh(adev, 0xffffffff, 0xffffffff, 0xffffffff, 0);
    mutex_unlock(&adev->grbm_idx_mutex);
}

/* Runs after gfx_v9_0_setup_rb(): what the driver ended up with. */
static void lucienne_5300u_rb_report(struct amdgpu_device *adev)
{
    if (lucienne_rb_mode < 1 || lucienne_rb_mode > 2 ||
        !lucienne_5300u_rb_id_ok(adev))
        return;

    dev_info(adev->dev, "lucienne-5300u-rb: backend_enable_mask=0x%x\\n",
         adev->gfx.config.backend_enable_mask);
}

''')


class PatchError(Exception):
    pass


def apply_cu(src: str) -> str:
    if CU_MARK in src:
        raise PatchError("часть cu уже стоит")
    if src.count(FW_ANCHOR) != 1:
        raise PatchError("якорь MODULE_FIRMWARE(vega10_ce) не найден или не один")
    src = src.replace(FW_ANCHOR, C_PARAM + FW_ANCHOR)
    m = list(FUNC_RE.finditer(src))
    if len(m) != 1:
        raise PatchError("определение gfx_v9_0_get_cu_info не найдено или не одно")
    start = m[0].start()
    src = src[:start] + C_HELPER + src[start:]
    start += len(C_HELPER)  # определение сдвинулось на размер хелпера
    lock = "\tmutex_lock(&adev->grbm_idx_mutex);\n"
    pos = src.find(lock, start)
    if pos < 0:
        raise PatchError("mutex_lock(grbm_idx_mutex) внутри get_cu_info не найден")
    pos += len(lock)
    return src[:pos] + C_CALL + src[pos:]


def apply_rb(src: str) -> str:
    if RB_MARK in src:
        raise PatchError("часть rb уже стоит")
    if src.count(FW_ANCHOR) != 1:
        raise PatchError("якорь MODULE_FIRMWARE(vega10_ce) не найден или не один")
    src = src.replace(FW_ANCHOR, C_RB_PARAM + FW_ANCHOR)
    m = list(CONSTANTS_RE.finditer(src))
    if len(m) != 1:
        raise PatchError("определение gfx_v9_0_constants_init не найдено или не одно")
    start = m[0].start()
    src = src[:start] + C_RB_HELPER + src[start:]
    if src.count(RB_CALL_ANCHOR) != 1:
        raise PatchError("вызов gfx_v9_0_setup_rb(adev) в нужном виде не найден "
                         "или не один (код constants_init изменился?)")
    return src.replace(
        RB_CALL_ANCHOR,
        "\tlucienne_5300u_rb_probe(adev);\n" + RB_CALL_ANCHOR +
        "\tlucienne_5300u_rb_report(adev);\n")


APPLY = {"cu": apply_cu, "rb": apply_rb}


def apply_patch(src: str, parts=PARTS) -> str:
    for p in parts:
        src = APPLY[p](src)
    return src


def verify_cu(src: str) -> tuple[bool, str]:
    """Определение хелпера раньше get_cu_info, вызов внутри неё."""
    if src.count(CU_MARK) != 1:
        return False, "module_param не найден (или продублирован)"
    h = src.find("static void lucienne_5300u_cu_probe(")
    if h < 0:
        return False, "определение хелпера не найдено"
    defs = list(FUNC_RE.finditer(src))
    if len(defs) != 1:
        return False, "определение get_cu_info не найдено/не одно"
    f = defs[0].start()
    calls = [m.start() for m in
             re.finditer(r"^\tlucienne_5300u_cu_probe\(adev\);$", src, re.M)]
    if len(calls) != 1:
        return False, f"вызовов хелпера {len(calls)}, ожидался 1"
    end = src.find("\n}\n", f)
    if not (h < f < calls[0] < end):
        return False, "вызов вне get_cu_info или раньше определения хелпера"
    return True, "хелпер определён до get_cu_info, вызов внутри неё"


def verify_rb(src: str) -> tuple[bool, str]:
    """RB-хелперы раньше constants_init; probe -> setup_rb -> report внутри неё."""
    if src.count(RB_MARK) != 1:
        return False, "module_param не найден (или продублирован)"
    hp = src.find("static void lucienne_5300u_rb_probe(")
    hr = src.find("static void lucienne_5300u_rb_report(")
    if hp < 0 or hr < 0:
        return False, "определения RB-хелперов не найдены"
    defs = list(CONSTANTS_RE.finditer(src))
    if len(defs) != 1:
        return False, "определение gfx_v9_0_constants_init не найдено/не одно"
    f = defs[0].start()
    pc = [m.start() for m in
          re.finditer(r"^\tlucienne_5300u_rb_probe\(adev\);$", src, re.M)]
    rc = [m.start() for m in
          re.finditer(r"^\tlucienne_5300u_rb_report\(adev\);$", src, re.M)]
    if len(pc) != 1 or len(rc) != 1:
        return False, f"вызовов probe/report: {len(pc)}/{len(rc)}, ожидалось 1/1"
    end = src.find("\n}\n", f)
    if not (max(hp, hr) < f < pc[0] < rc[0] < end):
        return False, "вызовы вне constants_init или раньше определений хелперов"
    setups = [m.start() for m in
              re.finditer(r"^\t\tgfx_v9_0_setup_rb\(adev\);$", src, re.M)]
    if not any(pc[0] < s < rc[0] for s in setups):
        return False, "setup_rb не между probe и report"
    return True, "хелперы до constants_init, probe -> setup_rb -> report внутри неё"


VERIFY = {"cu": verify_cu, "rb": verify_rb}


def verify_patch(src: str, parts=PARTS) -> tuple[bool, str]:
    msgs = []
    for p in parts:
        ok, msg = VERIFY[p](src)
        if not ok:
            return False, f"{p}: {msg}"
        msgs.append(f"{p}: {msg}")
    return True, "; ".join(msgs)


# --------------------------------------------------------------------------
# разбор логов ядра
# --------------------------------------------------------------------------
RE_PROBE = re.compile(
    r"lucienne-5300u: mode=(\d+) CC=0x([0-9a-f]+) USER=0x([0-9a-f]+) "
    r"write=0x([0-9a-f]+) readback=0x([0-9a-f]+) final=0x([0-9a-f]+)")
RE_WRITE = re.compile(r"lucienne-5300u: write (ACCEPTED|REJECTED)")
RE_RB_PROBE = re.compile(
    r"lucienne-5300u-rb: mode=(\d+) CC_RB=0x([0-9a-f]+) USER_RB=0x([0-9a-f]+) "
    r"write=0x([0-9a-f]+) readback=0x([0-9a-f]+) final=0x([0-9a-f]+)")
RE_RB_WRITE = re.compile(r"lucienne-5300u-rb: write (ACCEPTED|REJECTED)")
RE_RB_MASK = re.compile(r"lucienne-5300u-rb: backend_enable_mask=0x([0-9a-f]+)")
RE_ACTIVE = re.compile(r"active_cu_number (\d+)")
RE_BAD = re.compile(
    r"ring \S+ timeout|GPU reset|page fault|VM_L2_PROTECTION_FAULT|\bhang\b|"
    r"restore failed", re.I)
RE_VKPEAK = {"scalar": re.compile(r"fp32-scalar\s*=\s*([\d.]+)"),
             "vec4": re.compile(r"fp32-vec4\s*=\s*([\d.]+)")}
RE_FM_FRAMES = re.compile(r"^-\s*frames\s*:\s*(\d+)", re.M)
RE_FM_MS = re.compile(r"^-\s*duration\s*:\s*(\d+)\s*ms", re.M)


def bad_lines(log: str) -> list[str]:
    return [ln for ln in log.splitlines()
            if RE_BAD.search(ln) and re.search(r"amdgpu|lucienne", ln, re.I)]


def bump(cur: str, new: str) -> str:
    order = ("ok", "fail", "rejected")
    return max(cur, new, key=order.index)


def evaluate(mode: int, log: str, rb_mode: int = 0) -> dict:
    """Чистая функция: вердикт по профилю (CU-режим + RB-режим) и ядерному логу."""
    probes = RE_PROBE.findall(log)
    writes = RE_WRITE.findall(log)
    active = RE_ACTIVE.findall(log)
    bad = bad_lines(log)
    exp_active, exp_final = MODE_INFO[mode]
    notes: list[str] = []
    verdict = "ok"
    got_active = int(active[-1]) if active else None
    if got_active is None:
        notes.append("в логе нет active_cu_number (amdgpu не загрузился?)")
        verdict = bump(verdict, "fail")
    elif got_active != exp_active:
        notes.append(f"active_cu_number={got_active}, ожидалось {exp_active}")
        verdict = bump(verdict, "fail")
    if mode >= 1:
        mine = [p for p in probes if int(p[0]) == mode]
        if not mine:
            notes.append("нет строки lucienne-5300u (параметр не дошёл до модуля, "
                         "модуль не наш или сработал guard)")
            verdict = bump(verdict, "fail")
        else:
            final = int(mine[-1][5], 16)
            if final != exp_final:
                notes.append(f"final=0x{final:08x}, ожидалось 0x{exp_final:08x}")
                verdict = bump(verdict, "fail")
        if writes and writes[-1] == "REJECTED":
            notes.append("запись в CC_GC_SHADER_ARRAY_CONFIG отклонена: на ранней "
                         "стадии регистр не пишется, дальше идти нет смысла")
            verdict = bump(verdict, "rejected")
    elif probes:
        notes.append("CU-режим 0, но проба сработала: в cmdline лишний параметр?")
    if rb_mode >= 1:
        exp_mask, exp_rb_final = RB_INFO[rb_mode]
        rprobes = [p for p in RE_RB_PROBE.findall(log) if int(p[0]) == rb_mode]
        rwrites = RE_RB_WRITE.findall(log)
        masks = RE_RB_MASK.findall(log)
        if "lucienne-5300u-rb: identity/geometry mismatch" in log:
            notes.append("RB: сработал guard идентичности/геометрии, смотри строку в логе")
            verdict = bump(verdict, "fail")
        elif not rprobes:
            notes.append("нет строки lucienne-5300u-rb (параметр не дошёл, модуль не наш "
                         "или регистр не в ожидаемом стоковом значении)")
            verdict = bump(verdict, "fail")
        else:
            final = int(rprobes[-1][5], 16)
            if final != exp_rb_final:
                notes.append(f"RB final=0x{final:08x}, ожидалось 0x{exp_rb_final:08x}")
                verdict = bump(verdict, "fail")
            if rwrites and rwrites[-1] == "REJECTED":
                notes.append("запись в CC_RB_BACKEND_DISABLE отклонена: RB1 на ранней "
                             "стадии не включается, дальше идти нет смысла")
                verdict = bump(verdict, "rejected")
            elif not masks:
                notes.append("нет backend_enable_mask (report не отработал)")
                verdict = bump(verdict, "fail")
            elif int(masks[-1], 16) != exp_mask:
                notes.append(f"backend_enable_mask=0x{int(masks[-1], 16):x}, "
                             f"ожидалось 0x{exp_mask:x}")
                verdict = bump(verdict, "fail")
    if bad:
        notes.append(f"подозрительных строк в логе: {len(bad)}")
        verdict = bump(verdict, "fail")
    return {"verdict": verdict, "active": got_active, "notes": notes, "bad": bad[:10]}


def next_hint(mode: int, verdict: str, rb: int = 0) -> str:
    if verdict == "rejected":
        return "Стоп: регистр не пишется на ранней стадии. Верни всё как было (r)."
    if verdict != "ok":
        return "Профиль не прошёл. Загрузись без параметров и разберись по логу (l)."
    if rb == 1:
        return "RB принимает запись. Дальше профиль с rb2, потом сравни PA_SC_RASTER_CONFIG."
    if rb == 2:
        return ("RB1 включён. Сравни PA_SC_RASTER_CONFIG со стоком, прогони FurMark "
                "и поживи с ним.")
    return {0: "Сток записан как база. Дальше режим 1.",
            1: "Запись принимается. Дальше режим 2 (запись -cu2).",
            2: "CU6 включён. Прогони нагрузку и vkpeak, потом режим 3.",
            3: "8 CU. Прогони нагрузку и vkpeak. Для RB: профиль cu3rb1."}[mode]


# --------------------------------------------------------------------------
# трансформация записи загрузчика
# --------------------------------------------------------------------------
def profile_name(mode: int, rb: int = 0) -> str:
    return (f"cu{mode}" if mode else "") + (f"rb{rb}" if rb else "")


def parse_profiles(raw: str) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for tok in re.split(r"[,\s]+", raw.strip().lower()):
        m = re.fullmatch(r"(?:cu([123]))?(?:rb([12]))?", tok)
        if tok and m and (m.group(1) or m.group(2)):
            p = (int(m.group(1) or 0), int(m.group(2) or 0))
            if p not in out:
                out.append(p)
    return out


def make_entry(text: str, mode: int, rb: int = 0) -> str:
    tag = profile_name(mode, rb)
    out, seen = [], False
    for ln in text.splitlines():
        if re.match(r"^title\s", ln) and f"[{tag}]" not in ln:
            ln = f"{ln} [{tag}]"
        elif re.match(r"^options\s", ln):
            ln = re.sub(r"\s+amdgpu\.lucienne_(?:cu|rb)_mode=\S+", "", ln)
            if mode:
                ln += f" amdgpu.{PARAM}={mode}"
            if rb:
                ln += f" amdgpu.{RB_PARAM}={rb}"
            seen = True
        out.append(ln)
    if not seen:
        raise StepError("в записи загрузчика нет строки options")
    return "\n".join(out) + "\n"


def parse_kernel_release(rel: str):
    m = re.match(r"^(\d+\.\d+(?:\.\d+)?-arch\d+)-(\d+)$", rel)
    if not m:
        return None
    return {"ver": m.group(1), "pkgrel": m.group(2), "tag": "v" + m.group(1)}


# --------------------------------------------------------------------------
# UI
# --------------------------------------------------------------------------
class BaseUI:
    def __init__(self):
        self.lines: list[str] = []
        self._f = None

    def log(self, line: str):
        self.lines.append(line)
        try:
            if self._f is None:
                STATE_DIR.mkdir(parents=True, exist_ok=True)
                self._f = open(STATE_DIR / "log.txt", "a", buffering=1)
            self._f.write(f"{time.strftime('%F %T')} {line}\n")
        except OSError:
            pass
        self.on_log()

    def on_log(self):
        pass


class PlainUI(BaseUI):
    def on_log(self):
        print(self.lines[-1], flush=True)

    def pager(self, text, title=""):
        print(f"--- {title} ---\n{text}\n---", flush=True)

    def confirm(self, q, detail=None, strict=False):
        if detail:
            self.pager(detail, q)
        try:
            if strict:
                return input(f"{q} Введи 'yes': ").strip().lower() == "yes"
            return input(f"{q} [y/N]: ").strip().lower() in ("y", "yes", "д", "да")
        except EOFError:
            return False

    def ask(self, prompt, default=""):
        try:
            s = input(f"{prompt} [{default}]: ").strip()
        except EOFError:
            s = ""
        return s or default

    @contextlib.contextmanager
    def suspended(self):
        yield


def put(win, y, x, s, attr=0):
    h, w = win.getmaxyx()
    if y < 0 or y >= h or x >= w - 1:
        return
    try:
        win.addstr(y, x, s[: max(0, w - x - 1)], attr)
    except curses.error:
        pass


class CursesUI(BaseUI):
    def __init__(self, scr):
        super().__init__()
        self.scr, self.ctx, self.sel, self._last = scr, None, 0, 0.0

    def on_log(self):
        now = time.time()
        if self.ctx and now - self._last > 0.1:
            self._last = now
            self.draw()

    def draw(self):
        c, scr = self.ctx, self.scr
        scr.erase()
        h, w = scr.getmaxyx()
        put(scr, 0, 0, f" cu-unlock | ядро {c.rel}" +
            ("  [DRY-RUN]" if c.dry else ""), curses.A_BOLD)
        for i, s in enumerate(STEPS):
            put(scr, 2 + i, 1, f"{SYM[c.status(s)]} {i + 1}. {s.title}",
                curses.A_REVERSE if i == self.sel else 0)
        x0 = 30
        log_h = max(5, (h - 4) // 2)
        top = h - 2 - log_h
        s = STEPS[self.sel]
        row = 2
        put(scr, row, x0, s.title, curses.A_BOLD)
        row += 1
        for ln in textwrap.wrap(s.desc, max(10, w - x0 - 2)):
            if row < top:
                put(scr, row, x0, ln)
            row += 1
        row += 1
        try:
            prev = s.preview(c)
        except Exception as e:  # превью только для показа, ошибка не должна ронять TUI
            prev = [f"(превью недоступно: {e})"]
        for ln in prev:
            for part in textwrap.wrap(ln, max(10, w - x0 - 4)) or [""]:
                if row < top:
                    put(scr, row, x0, "  " + part, curses.A_DIM)
                row += 1
        put(scr, top, 0, "-" * (w - 1))
        for i, ln in enumerate(self.lines[-(log_h - 1):]):
            put(scr, top + 1 + i, 0, ln)
        put(scr, h - 1, 0,
            " Enter выполнить  s пропуск  d dry-run  l лог  r откат  q выход ",
            curses.A_REVERSE)
        scr.refresh()

    def pager(self, text, title=""):
        scr = self.scr
        h, w = scr.getmaxyx()
        lines: list[str] = []
        for ln in text.splitlines():
            lines += textwrap.wrap(ln.expandtabs(4), max(10, w - 2),
                                   replace_whitespace=False,
                                   drop_whitespace=False) or [""]
        pos = 0
        while True:
            scr.erase()
            put(scr, 0, 0, title, curses.A_BOLD)
            for i, ln in enumerate(lines[pos:pos + h - 3]):
                put(scr, 1 + i, 0, ln)
            put(scr, h - 1, 0, " ↑/↓ PgUp/PgDn прокрутка, Enter или q: дальше ",
                curses.A_REVERSE)
            scr.refresh()
            k = scr.getch()
            if k in (ord("q"), 10, 13, curses.KEY_ENTER):
                return
            if k == curses.KEY_UP:
                pos = max(0, pos - 1)
            elif k == curses.KEY_DOWN:
                pos = min(max(0, len(lines) - 1), pos + 1)
            elif k == curses.KEY_PPAGE:
                pos = max(0, pos - (h - 4))
            elif k == curses.KEY_NPAGE:
                pos = min(max(0, len(lines) - 1), pos + (h - 4))

    def read_line(self, prompt):
        scr = self.scr
        h, _ = scr.getmaxyx()
        scr.move(h - 1, 0)
        scr.clrtoeol()
        put(scr, h - 1, 0, prompt, curses.A_BOLD)
        curses.echo()
        with contextlib.suppress(curses.error):
            curses.curs_set(1)
        scr.refresh()
        try:
            raw = scr.getstr(h - 1, min(len(prompt), scr.getmaxyx()[1] - 2), 80)
        finally:
            curses.noecho()
            with contextlib.suppress(curses.error):
                curses.curs_set(0)
        return raw.decode("utf-8", "ignore")

    def confirm(self, q, detail=None, strict=False):
        if detail:
            self.pager(detail, q)
        if strict:
            return self.read_line(f"{q} Введи 'yes': ").strip().lower() == "yes"
        return self.read_line(f"{q} [y/N]: ").strip().lower() in ("y", "yes", "д", "да")

    def ask(self, prompt, default=""):
        s = self.read_line(f"{prompt} [{default}]: ").strip()
        return s or default

    @contextlib.contextmanager
    def suspended(self):
        curses.def_prog_mode()
        curses.endwin()
        try:
            yield
        finally:
            curses.reset_prog_mode()
            self.scr.refresh()


# --------------------------------------------------------------------------
# контекст
# --------------------------------------------------------------------------
def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class Ctx:
    def __init__(self, ui, dry: bool, workdir: str):
        self.ui, self.dry = ui, dry
        self.workdir = Path(workdir).expanduser()
        self.rel = os.uname().release
        k = parse_kernel_release(self.rel)
        self.kinfo = k
        self.tag = k["tag"] if k else None
        self.pkgrel = k["pkgrel"] if k else None
        self.src = self.workdir / f"linux-{k['ver']}" if k else None
        self.nproc = str(os.cpu_count() or 1)
        self.failed: set[str] = set()
        self.cache: dict = {}
        self._status: dict[str, str] = {}
        try:
            self.state = json.loads((STATE_DIR / "state.json").read_text())
        except (OSError, ValueError):
            self.state = {}
        for key, val in (("done", {}), ("skipped", {}), ("results", {}),
                         ("vkpeak", {}), ("furmark", {}), ("entries", [])):
            self.state.setdefault(key, val)
        if self.state.get("rel") != self.rel:
            if self.state.get("rel"):
                self.state["done"] = {}
                self.state["skipped"] = {}
                self.log(f"[i] ядро сменилось ({self.state['rel']} -> {self.rel}): "
                         "статусы шагов сброшены, результаты замеров сохранены")
            self.state["rel"] = self.rel

    # пути
    @property
    def _amd(self):
        base = self.src or Path("/nonexistent/no-arch-kernel-source")
        return base / "drivers/gpu/drm/amd/amdgpu"
    @property
    def gfx(self): return self._amd / "gfx_v9_0.c"
    @property
    def ko(self): return self._amd / "amdgpu.ko"
    @property
    def zst(self): return self._amd / "amdgpu.ko.zst"
    @property
    def installed(self):
        return Path(f"/usr/lib/modules/{self.rel}/kernel/drivers/gpu/drm/amd/amdgpu/amdgpu.ko.zst")
    @property
    def backup(self): return BACKUP_DIR / self.rel / "amdgpu.ko.zst"

    def save(self):
        try:
            STATE_DIR.mkdir(parents=True, exist_ok=True)
            (STATE_DIR / "state.json").write_text(json.dumps(self.state, indent=1))
        except OSError:
            pass

    # UI-обёртки: в dry-run подтверждения принимаются автоматически
    def log(self, line): self.ui.log(line)

    def confirm(self, q, detail=None, strict=False):
        if self.dry:
            if detail:
                self.log(detail)
            self.log(f"[dry-run] авто-да: {q}")
            return True
        return self.ui.confirm(q, detail, strict)

    def ask(self, prompt, default=""):
        return default if self.dry else self.ui.ask(prompt, default)

    def pager(self, text, title=""):
        self.ui.pager(text, title)

    # запуск команд
    def ensure_sudo(self):
        if not shutil.which("sudo"):
            raise StepError("sudo не найден")
        if subprocess.run(["sudo", "-n", "true"], capture_output=True).returncode != 0:
            with self.ui.suspended():
                rc = subprocess.run(["sudo", "-v"]).returncode
            if rc != 0:
                raise StepError("sudo-пароль не принят")

    def sh(self, cmd, cwd=None, sudo=False, ro=False, quiet=False):
        """ro=True: команда только читает, выполняется даже в dry-run."""
        cmd = [str(x) for x in cmd]
        if sudo:
            cmd = ["sudo", "-n"] + cmd
        shown = "$ " + " ".join(shlex.quote(x) for x in cmd)
        if self.dry and not ro:
            self.log(f"[dry-run] {shown}")
            return 0, ""
        if sudo:
            self.ensure_sudo()
        if not quiet:
            self.log(shown)
        try:
            p = subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 text=True, errors="replace",
                                 env={**os.environ, "LC_ALL": "C"})
        except FileNotFoundError:
            return 127, f"{cmd[0]}: команда не найдена"
        out: list[str] = []
        try:
            for line in p.stdout:
                line = line.rstrip("\n")
                out.append(line)
                if not quiet:
                    self.log(line)
            p.wait()
        except KeyboardInterrupt:
            p.terminate()
            raise Abort("прервано")
        return p.returncode, "\n".join(out)

    # статусы
    def refresh(self):
        for s in STEPS:
            st = "todo"
            try:
                if s.id in self.failed:
                    st = "failed"
                elif self.state["skipped"].get(s.id):
                    st = "skipped"
                elif s.detect is not None:
                    st = "done" if s.detect(self) else "todo"
                elif self.state["done"].get(s.id):
                    st = "done"
            except Exception:
                st = "todo"
            self._status[s.id] = st

    def status(self, step): return self._status.get(step.id, "todo")


# --------------------------------------------------------------------------
# общие проверки
# --------------------------------------------------------------------------
def modinfo(c: Ctx, path: Path, field: str) -> str:
    rc, out = c.sh(["modinfo", "-F", field, path], ro=True, quiet=True)
    if rc == 0 and out.strip():
        return out
    if str(path).endswith(".zst") and shutil.which("zstd"):
        tmp = c.workdir / "_modinfo_tmp.ko"
        rc, _ = c.sh(["zstd", "-d", "-f", "-q", "-o", tmp, path], ro=True, quiet=True)
        if rc == 0:
            rc, out = c.sh(["modinfo", "-F", field, tmp], ro=True, quiet=True)
            if rc == 0:
                return out
    return ""


def check_ko(c: Ctx) -> tuple[bool, str]:
    if not c.ko.exists():
        return False, "amdgpu.ko не собран"
    vm = modinfo(c, c.ko, "vermagic").split()
    if not vm or vm[0] != c.rel:
        return False, f"vermagic {vm[:1]} не совпадает с {c.rel}"
    parm = modinfo(c, c.ko, "parm")
    for p in (PARAM, RB_PARAM):
        if p not in parm:
            return False, f"в модуле нет параметра {p} (пересобери после патча)"
    return True, "vermagic совпал, оба параметра на месте"


def klog(c: Ctx) -> str:
    for cmd, sudo in ((["journalctl", "-k", "-b", "--no-pager"], False),
                      (["dmesg"], False), (["dmesg"], True)):
        rc, out = c.sh(cmd, sudo=sudo, ro=True, quiet=True)
        if rc == 0 and "amdgpu" in out:
            return out
    return ""


def cmdline_param(name: str) -> int:
    try:
        m = re.search(r"amdgpu\.%s=(\d+)" % name, Path("/proc/cmdline").read_text())
    except OSError:
        return 0
    return int(m.group(1)) if m else 0


def cmdline_mode() -> int:
    return cmdline_param(PARAM)


def cmdline_rb_mode() -> int:
    return cmdline_param(RB_PARAM)


def esp_info(c: Ctx) -> dict:
    if "esp" in c.cache:
        return c.cache["esp"]
    try:
        cmdline = Path("/proc/cmdline").read_text()
    except OSError:
        cmdline = ""
    m = re.search(r"initrd=(\S+)", cmdline)
    if not m:
        raise StepError("в /proc/cmdline нет initrd= (не systemd-boot / EFISTUB?)")
    rp = m.group(1).replace("\\", "/").lstrip("/")
    for mp in ("/efi", "/boot/efi", "/boot"):
        p = f"{mp}/{rp}"
        rc, _ = c.sh(["test", "-e", p], sudo=True, ro=True, quiet=True)
        if rc == 0:
            c.cache["esp"] = {"esp": mp, "rel": rp, "path": p}
            return c.cache["esp"]
    raise StepError(f"образ {rp} не найден ни на /efi, ни на /boot/efi, ни на /boot")


def initrd_has_amdgpu(c: Ctx, path: str):
    tool = shutil.which("lsinitrd") or shutil.which("lsinitcpio")
    if not tool:
        return None
    rc, out = c.sh([tool, path], sudo=True, ro=True, quiet=True)
    return ("amdgpu.ko" in out) if rc == 0 else None


# --------------------------------------------------------------------------
# шаги
# --------------------------------------------------------------------------
def s_preflight(c: Ctx) -> str:
    if sys.version_info < (3, 8):
        raise StepError("нужен Python >= 3.8")
    if not c.kinfo:
        raise StepError(f"ядро {c.rel} не похоже на пакет Arch 'linux' (X.Y.Z-archN-M). "
                        "linux-lts / zen / custom скрипт не поддерживает")
    need = ["make", "gcc", "zstd", "modinfo", "bc", "cpio", "pahole", "sudo"]
    miss = [t for t in need if not shutil.which(t)]
    if miss:
        raise StepError("нет утилит: " + ", ".join(miss) +
                        "  (sudo pacman -S --needed base-devel bc cpio pahole zstd kmod)")
    sym = Path(f"/usr/lib/modules/{c.rel}/build/Module.symvers")
    if not sym.exists():
        raise StepError(f"нет {sym}: поставь linux-headers той же версии "
                        f"и перезагрузись на ядро {c.rel}")
    if not c.installed.exists():
        raise StepError(f"нет установленного модуля {c.installed} "
                        "(другая компрессия модулей?)")
    c.workdir.mkdir(parents=True, exist_ok=True)
    free = shutil.disk_usage(c.workdir).free >> 30
    if free < 4:
        raise StepError(f"на {c.workdir} свободно {free} ГиБ, нужно хотя бы 4")
    opt = [t for t in ("umr", "vkpeak", "lsinitrd", "bootctl", "dracut") if shutil.which(t)]
    return f"ядро {c.rel}, утилиты ок, свободно {free} ГиБ; опционально есть: {', '.join(opt) or '-'}"


def read_pci() -> list[dict]:
    out = []
    for d in Path("/sys/bus/pci/devices").glob("*"):
        try:
            v = {k: int((d / f).read_text().strip(), 16) for k, f in
                 (("vendor", "vendor"), ("device", "device"),
                  ("subvendor", "subsystem_vendor"),
                  ("subdevice", "subsystem_device"), ("revision", "revision"))}
        except (OSError, ValueError):
            continue
        v["addr"] = d.name
        out.append(v)
    return out


def s_hardware(c: Ctx) -> str:
    devs = read_pci()
    hit = [d for d in devs if all(d[k] == v for k, v in HW.items())]
    if not hit:
        amd = [f"{d['vendor']:04x}:{d['device']:04x} {d['subvendor']:04x}:"
               f"{d['subdevice']:04x} rev {d['revision']:02x}"
               for d in devs if d["vendor"] == 0x1002]
        raise StepError("нужен 1002:164c, subsystem 103c:887a, rev c3. Найдено у AMD: "
                        + ("; ".join(amd) or "ничего"))
    log = klog(c)
    info = ""
    m = re.search(r"CU per SH (\d+), active_cu_number (\d+)", log)
    if m:
        info = f", ядро видит {m.group(2)} из {m.group(1)} CU"
    return f"{hit[0]['addr']}: железо совпало{info}"


def s_source(c: Ctx) -> str:
    if c.gfx.exists():
        return f"исходники уже есть: {c.src}"
    url = f"https://github.com/archlinux/linux/archive/refs/tags/{c.tag}.tar.gz"
    tgz = c.workdir / f"{c.tag}.tar.gz"
    c.log(f"источник: {url}")
    if c.dry:
        c.log(f"[dry-run] скачать в {tgz} и распаковать в {c.workdir}")
        return "dry-run"
    c.workdir.mkdir(parents=True, exist_ok=True)
    if not tgz.exists():
        tmp = tgz.with_suffix(".part")
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "cu-unlock"})
            with urllib.request.urlopen(req, timeout=60) as r, open(tmp, "wb") as f:
                total, got, last = int(r.headers.get("Content-Length") or 0), 0, 0
                while True:
                    b = r.read(1 << 20)
                    if not b:
                        break
                    f.write(b)
                    got += len(b)
                    if got - last >= 8 << 20:
                        c.log(f"  {got >> 20} / {total >> 20} МиБ")
                        last = got
        except (OSError, ValueError) as e:
            raise StepError(f"не скачалось: {e} (тег {c.tag} есть на GitHub?)")
        tmp.replace(tgz)
    rc, _ = c.sh(["tar", "-xzf", tgz, "-C", c.workdir])
    if rc != 0 or not c.gfx.exists():
        raise StepError(f"после распаковки нет {c.gfx}")
    return f"распаковано в {c.src}"


def d_source(c): return bool(c.src and c.gfx.exists())


def s_config(c: Ctx) -> str:
    if not c.gfx.exists():
        raise StepError("нет исходников, сначала шаг «Исходники»")
    cfg_src = Path("/proc/config.gz")
    if not cfg_src.exists():
        cfg_src = Path(f"/usr/lib/modules/{c.rel}/build/.config")
    if not cfg_src.exists():
        raise StepError("нет ни /proc/config.gz, ни build/.config")
    if not c.dry:
        text = (gzip.open(cfg_src, "rt").read() if cfg_src.suffix == ".gz"
                else cfg_src.read_text())
        (c.src / ".config").write_text(text)
        (c.src / "localversion.10-pkgrel").write_text(f"-{c.pkgrel}\n")
    c.log(f"конфиг из {cfg_src}, localversion -{c.pkgrel}")
    rc, _ = c.sh(["make", "olddefconfig"], cwd=c.src)
    if rc != 0:
        raise StepError("make olddefconfig не прошёл")
    rc, out = c.sh(["make", "-j", c.nproc, "modules_prepare"], cwd=c.src)
    if rc != 0:
        if re.search(r"rust|bindgen", out, re.I) and c.confirm(
                "modules_prepare упал похоже из-за Rust. Отключить CONFIG_RUST и повторить?"):
            c.sh(["scripts/config", "--disable", "RUST"], cwd=c.src)
            c.sh(["make", "olddefconfig"], cwd=c.src)
            rc, out = c.sh(["make", "-j", c.nproc, "modules_prepare"], cwd=c.src)
        if rc != 0:
            raise StepError("modules_prepare не прошёл (см. лог, клавиша l)")
    if not c.dry:
        shutil.copy2(f"/usr/lib/modules/{c.rel}/build/Module.symvers",
                     c.src / "Module.symvers")
        conf = (c.src / ".config").read_text()
        if "CONFIG_DRM_AMDGPU=y" in conf:
            raise StepError("amdgpu собран в ядро (=y), заменой модуля не обойтись")
        if "CONFIG_DRM_AMDGPU=m" not in conf:
            raise StepError("в .config нет CONFIG_DRM_AMDGPU=m")
    return "конфиг и Module.symvers готовы" if not c.dry else "dry-run"


def d_config(c):
    return bool(c.src and (c.src / "Module.symvers").exists()
                and (c.src / "include/generated/autoconf.h").exists())


def s_patch(c: Ctx) -> str:
    f = c.gfx
    if not f.exists():
        raise StepError("нет gfx_v9_0.c, сначала шаг «Исходники»")
    src = f.read_text()
    orig = Path(str(f) + ".orig")
    have = [p for p in PARTS if MARKS[p] in src]
    broken = [(p, VERIFY[p](src)[1]) for p in have if not VERIFY[p](src)[0]]
    missing = [p for p in PARTS if p not in have]
    base = src
    if broken:
        why = "; ".join(f"{p}: {m}" for p, m in broken)
        if not orig.exists():
            raise StepError(f"патч стоит неправильно ({why}), а .orig нет")
        if not c.confirm(f"Патч стоит неправильно ({why}). "
                         "Взять .orig и пропатчить заново целиком?"):
            raise Abort("отменено")
        base, missing = orig.read_text(), list(PARTS)
    elif not missing:
        return "уже пропатчено: " + verify_patch(src)[1]
    try:
        new = apply_patch(base, missing)
    except PatchError as e:
        raise StepError(str(e))
    ok, msg = verify_patch(new)
    if not ok:
        raise StepError("самопроверка патча: " + msg)
    diff = "".join(difflib.unified_diff(
        src.splitlines(True), new.splitlines(True),
        "gfx_v9_0.c", "gfx_v9_0.c (patched)", n=2))
    if not c.confirm(f"Применить патч (части: {', '.join(missing)})?", detail=diff):
        raise Abort("отменено")
    if c.dry:
        return "dry-run"
    if not orig.exists():
        shutil.copy2(f, orig)
    f.write_text(new)
    ok, msg = verify_patch(f.read_text())
    if not ok:
        raise StepError("после записи: " + msg)
    return msg


def d_patch(c):
    return bool(c.src and c.gfx.exists() and verify_patch(c.gfx.read_text())[0])


def s_build(c: Ctx) -> str:
    ok, _ = verify_patch(c.gfx.read_text()) if c.gfx.exists() else (False, "")
    if not ok:
        raise StepError("файл не пропатчен корректно, сначала шаг «Патч»")
    rc, _ = c.sh(["make", "-j", c.nproc, "M=drivers/gpu/drm/amd/amdgpu", "modules"],
                 cwd=c.src)
    if rc != 0:
        raise StepError("сборка модуля упала (см. лог, клавиша l)")
    if c.dry:
        return "dry-run"
    ok, msg = check_ko(c)
    if not ok:
        raise StepError(msg)
    return msg


def d_build(c):
    return bool(c.src and c.ko.exists() and check_ko(c)[0])


def s_install(c: Ctx) -> str:
    if not c.dry:
        ok, msg = check_ko(c)
        if not ok:
            raise StepError("сначала сборка: " + msg)
    upd = Path(f"/usr/lib/modules/{c.rel}/updates")
    if upd.exists():
        hits = [str(p) for p in upd.rglob("amdgpu*")]
        if hits:
            raise StepError(f"в updates/ есть amdgpu и он перекроет наш: {hits}")
    inst = c.installed
    ours = PARAM in modinfo(c, inst, "parm")
    if not ours:
        c.log(f"бэкап стокового модуля -> {c.backup}")
        if not c.dry:
            c.backup.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(inst, c.backup)
            (c.backup.parent / "sha256").write_text(sha256(c.backup) + "\n")
        c.state["backup"] = str(c.backup)
    else:
        c.log("установлен уже наш модуль, бэкап не перезаписываю")
        if not c.backup.exists():
            c.log("[!] бэкапа стока нет, откат только через `sudo pacman -S linux`")
    rc, _ = c.sh(["zstd", "-f", "-q", "-o", c.zst, c.ko])
    if rc != 0:
        raise StepError("zstd не сжал модуль")
    if not c.confirm(f"Заменить {inst} собранным модулем?",
                     detail=f"{c.zst}\n  ->\n{inst}\n\nбэкап: {c.backup}"):
        raise Abort("отменено")
    rc, _ = c.sh(["install", "-m644", c.zst, inst], sudo=True)
    if rc != 0:
        raise StepError("install не прошёл")
    if not c.dry and sha256(c.zst) != sha256(inst):
        raise StepError("хэш установленного модуля не совпал со сборкой")
    # initramfs
    try:
        info = esp_info(c)
    except StepError as e:
        c.log(f"[!] initramfs не проверен: {e}")
        return "модуль установлен; initramfs проверь вручную"
    has = initrd_has_amdgpu(c, info["path"])
    if has is None:
        c.log("[!] не смогла прочитать образ (нет lsinitrd/lsinitcpio или он не читается). "
              "Если amdgpu у тебя в initramfs, пересобери его сам")
    elif has:
        bak = info["path"] + ".cu-unlock.bak"
        if shutil.which("dracut"):
            cmd = ["dracut", "--force", "--kver", c.rel, info["path"]]
        else:
            cmd = ["mkinitcpio", "-P"]  # не проверено на целевой схеме
        if c.confirm("amdgpu сидит в initramfs. Пересобрать образ? "
                     f"(бэкап: {bak})", detail=" ".join(cmd), strict=True):
            c.sh(["cp", "-n", info["path"], bak], sudo=True)
            rc, _ = c.sh(cmd, sudo=True)
            if rc != 0:
                raise StepError("пересборка initramfs не прошла, образ-бэкап: " + bak)
            c.state["initrd_backup"] = {"img": info["path"], "bak": bak}
        else:
            c.log("[!] initramfs не пересобран, а amdgpu в нём есть: старый модуль загрузится")
    else:
        c.log("amdgpu в initramfs нет, он грузится с корня: пересборка не нужна")
    return "модуль установлен, хэши совпали" if not c.dry else "dry-run"


def d_install(c):
    return bool(c.src and c.zst.exists() and c.installed.exists()
                and sha256(c.zst) == sha256(c.installed))


def s_entries(c: Ctx) -> str:
    info = esp_info(c)
    edir = f"{info['esp']}/loader/entries"
    rc, out = c.sh(["ls", edir], sudo=True, ro=True, quiet=True)
    if rc != 0:
        raise StepError(f"не могу прочитать {edir}")
    names = [n for n in out.split() if n.endswith(".conf")]
    cands, texts = [], {}
    for n in names:
        rc, t = c.sh(["cat", f"{edir}/{n}"], sudo=True, ro=True, quiet=True)
        texts[n] = t
        if re.search(r"-(?:cu|rb)\d\w*\.conf$", n):
            continue
        for m in re.finditer(r"^initrd\s+(\S+)", t, re.M):
            if m.group(1).replace("\\", "/").lstrip("/") == info["rel"]:
                cands.append(n)
    if len(cands) == 1:
        cur = cands[0]
    else:
        cur = c.ask("Не удалось однозначно определить текущую запись. Имя файла из: "
                    + ", ".join(names), cands[0] if cands else "")
        if cur not in names:
            raise StepError("такой записи нет")
    base = cur[:-5]
    raw = c.ask("Какие профили создать (cuN: режим CU 1-3, rbM: режим RB 1-2, "
                "можно вместе: cu3rb1)", "cu1,cu2,cu3,cu3rb1,cu3rb2")
    profiles = parse_profiles(raw)
    if not profiles:
        raise StepError("не выбран ни один профиль")
    new = {p: make_entry(texts[cur], *p) for p in profiles}
    first = profiles[0]
    diff = "".join(difflib.unified_diff(
        texts[cur].splitlines(True), new[first].splitlines(True),
        cur, f"{base}-{profile_name(*first)}.conf", n=1))
    names_txt = ", ".join(profile_name(*p) for p in profiles)
    if not c.confirm(f"Создать записи {names_txt} рядом с {cur}? "
                     "(основная не меняется)", detail=diff):
        raise Abort("отменено")
    created = []
    for p in profiles:
        name = profile_name(*p)
        dest = f"{edir}/{base}-{name}.conf"
        tmp = c.workdir / f"_entry_{name}.conf"
        if not c.dry:
            tmp.write_text(new[p])
        rc, _ = c.sh(["install", "-m644", tmp, dest], sudo=True)
        if rc != 0:
            raise StepError(f"не записалась {dest}")
        created.append(dest)
    c.state["entries"] = sorted(set(c.state["entries"]) | set(created))
    one = c.ask("Однократная загрузка профиля (например cu3rb1, Enter: пропустить)", "")
    if one:
        sel = parse_profiles(one)
        if sel and sel[0] in profiles:
            eid = f"{base}-{profile_name(*sel[0])}.conf"
            c.log("(`bootctl set-oneshot` по памяти; если не принял ID, смотри `bootctl list`)")
            c.sh(["bootctl", "set-oneshot", eid], sudo=True)
            c.state["pending_profile"] = profile_name(*sel[0])
    c.log("Перезагрузись (в меню выбери запись с [профиль]) и запусти шаг «Проверка».")
    return f"создано записей: {len(created)}"


def s_verify(c: Ctx) -> str:
    mode, rb = cmdline_mode(), cmdline_rb_mode()
    key = profile_name(mode, rb) or "stock"
    log = klog(c)
    if not log:
        raise StepError("не могу прочитать журнал ядра (journalctl -k / dmesg)")
    r = evaluate(mode, log, rb)
    c.state["results"][key] = {"verdict": r["verdict"], "active": r["active"],
                               "time": time.strftime("%F %T")}
    c.log(f"профиль в cmdline: {key}; active_cu_number: {r['active']}")
    for rx in (RE_PROBE, RE_RB_PROBE, RE_RB_MASK):
        for m in rx.finditer(log):
            c.log("  " + m.group(0))
    for n in r["notes"]:
        c.log("  ! " + n)
    for b in r["bad"]:
        c.log("  BAD " + b)
    if rb >= 1:
        sysp = Path("/sys/module/amdgpu/parameters") / RB_PARAM
        loaded_src = Path("/sys/module/amdgpu/srcversion")
        inst_src = modinfo(c, c.installed, "srcversion").strip()
        if loaded_src.exists() and inst_src:
            same = loaded_src.read_text().strip() == inst_src
            c.log("  загруженный amdgpu " + ("= установленному файлу" if same else
                  "НЕ совпадает с установленным файлом (грузится другой модуль?)"))
        if not sysp.exists():
            c.log(f"  ! в загруженном amdgpu нет параметра {RB_PARAM}: работает модуль "
                  "без RB-части (старая сборка). Повтори шаги Патч, Сборка, Установка")
        else:
            val = sysp.read_text().strip()
            c.log(f"  параметр {RB_PARAM} в загруженном модуле = {val}")
            if not RE_RB_PROBE.search(log) and "lucienne-5300u-rb:" not in log:
                c.log("  ! параметр дошёл, а строк RB в журнале нет: код пробы не "
                      "выполнился (constants_init не вызывается там, где я думала?)")
    have_rb_probe = any(int(x[0]) == rb for x in RE_RB_PROBE.findall(log))
    if rb >= 1 and have_rb_probe and shutil.which("umr"):
        rc, out = c.sh(["umr", "-r", "*.*.mmPA_SC_RASTER_CONFIG"], sudo=True,
                       ro=True, quiet=True)
        m = re.search(r"=>\s*0x([0-9a-f]+)", out)
        if m:
            v = int(m.group(1), 16)
            if v == STOCK_RASTER:
                c.log(f"  PA_SC_RASTER_CONFIG=0x{v:08x}: как на стоке. Это ничего не "
                      "доказывает ни в одну сторону (на стоке с одним RB картинка "
                      "тоже рисуется с этим значением): смотри FurMark и артефакты")
            else:
                c.log(f"  PA_SC_RASTER_CONFIG=0x{v:08x}: ОТЛИЧАЕТСЯ от стока "
                      f"0x{STOCK_RASTER:08x}, растеризатор перестроен")
        else:
            c.log("  PA_SC_RASTER_CONFIG прочитать не удалось")
    c.log(next_hint(mode, r["verdict"], rb))
    if r["verdict"] != "ok":
        raise StepError(f"профиль {key}: {r['verdict']}")
    return f"профиль {key}: всё по ожиданиям"


def s_stress(c: Ctx) -> str:
    mode, rb = cmdline_mode(), cmdline_rb_mode()
    key = profile_name(mode, rb) or "stock"
    base = set(bad_lines(klog(c)))
    c.ask("Запусти нагрузку в другом окне (glmark2 --run-forever, видео, игра) "
          "и нажми Enter, когда закончишь", "")
    after = set(bad_lines(klog(c)))
    new = sorted(after - base)
    for ln in new:
        c.log("  BAD " + ln)
    if new:
        raise StepError(f"в журнале появилось {len(new)} подозрительных строк")
    c.log("журнал чист после нагрузки")
    if shutil.which("vkpeak") and c.confirm("Прогнать vkpeak (compute, для CU)?"):
        idx = c.ask("Индекс устройства vkpeak", "0")
        n = max(1, int(c.ask("Сколько прогонов", "3") or 3))
        vals = {"scalar": [], "vec4": []}
        for _ in range(n):
            rc, out = c.sh(["vkpeak", idx])
            for k, rx in RE_VKPEAK.items():
                m = rx.search(out)
                if m:
                    vals[k].append(float(m.group(1)))
        if vals["scalar"]:
            c.state["vkpeak"][key] = {k: statistics.median(v)
                                      for k, v in vals.items() if v}
    if shutil.which("furmark") and c.confirm(
            "Прогнать FurMark 1080p (пиксели, для RB; ~60 с на прогон)?"):
        demo = c.ask("Имя демо (смотри furmark --demolist)", "furmark-vk")
        n = max(1, int(c.ask("Сколько прогонов", "3") or 3))
        fps = []
        for _ in range(n):
            rc, out = c.sh(["furmark", "--demo", demo, "--benchmark", "--p1080",
                            "--vsync", "0", "--no-score-box"])
            fr, ms = RE_FM_FRAMES.search(out), RE_FM_MS.search(out)
            if fr and ms and int(ms.group(1)):
                fps.append(int(fr.group(1)) * 1000 / int(ms.group(1)))
        if fps:
            c.state["furmark"][key] = statistics.median(fps)
    vb, fb = c.state["vkpeak"].get("stock"), c.state["furmark"].get("stock")
    for k in sorted(set(c.state["vkpeak"]) | set(c.state["furmark"])):
        parts = []
        v = c.state["vkpeak"].get(k)
        if v:
            s = f"vkpeak scalar {v.get('scalar', 0):.0f}"
            if vb and k != "stock" and vb.get("scalar"):
                s += f" ({100 * (v['scalar'] / vb['scalar'] - 1):+.1f}%)"
            parts.append(s)
        f_ = c.state["furmark"].get(k)
        if f_:
            s = f"furmark {f_:.2f} FPS"
            if fb and k != "stock":
                s += f" ({100 * (f_ / fb - 1):+.1f}%)"
            parts.append(s)
        c.log(f"  {k}: " + ", ".join(parts))
    return f"нагрузка без ошибок в журнале (профиль {key})"


class Step:
    def __init__(self, id, title, desc, run, preview, detect=None):
        self.id, self.title, self.desc = id, title, desc
        self.run, self.preview, self.detect = run, preview, detect


STEPS = [
    Step("preflight", "Окружение",
         "Версия ядра Arch, нужные утилиты, linux-headers, место на диске.",
         s_preflight, lambda c: ["make, gcc, zstd, modinfo, bc, cpio, pahole, sudo",
                                 f"/usr/lib/modules/{c.rel}/build/Module.symvers"]),
    Step("hardware", "Железо",
         "Читает PCI из /sys и сверяет 1002:164c, 103c:887a, rev c3. "
         "Патч зашит под эту машину, на другой скрипт остановится.",
         s_hardware, lambda c: ["/sys/bus/pci/devices/*/{vendor,device,subsystem_*,revision}"]),
    Step("source", "Исходники",
         "Тарбол ядра ровно твоей версии с GitHub Arch (без полного клона).",
         s_source, lambda c: [f"https://github.com/archlinux/linux/archive/refs/tags/{c.tag}.tar.gz",
                              f"-> {c.src}"], d_source),
    Step("config", "Конфиг",
         "config.gz, localversion, olddefconfig, modules_prepare, Module.symvers.",
         s_config, lambda c: ["make olddefconfig", "make modules_prepare",
                              "cp Module.symvers"], d_config),
    Step("patch", "Патч",
         "Две независимые части: проба CU (lucienne_cu_mode) и второй render backend "
         "(lucienne_rb_mode). Показывает diff и проверяет порядок (хелперы до "
         "get_cu_info / constants_init, вызовы внутри них). Дописывает недостающую "
         "часть поверх уже пропатченного дерева.",
         s_patch, lambda c: [str(c.gfx), "бэкап: gfx_v9_0.c.orig",
                             "cu: после mutex_lock в get_cu_info",
                             "rb: вокруг gfx_v9_0_setup_rb в constants_init"], d_patch),
    Step("build", "Сборка",
         "Сборка одного amdgpu.ko; проверка vermagic и параметра модуля.",
         s_build, lambda c: ["make M=drivers/gpu/drm/amd/amdgpu modules"], d_build),
    Step("install", "Установка",
         "Бэкап стокового модуля, zstd, install, сверка хэшей, проверка initramfs.",
         s_install, lambda c: [f"бэкап -> {c.backup}", f"install -> {c.installed}",
                               "lsinitrd образа с ESP; пересборка только если amdgpu внутри"],
         d_install),
    Step("entries", "Запись загрузчика",
         "Копии текущей записи systemd-boot с параметрами профиля "
         "(cu3, cu3rb1, ...), основная не меняется.",
         s_entries, lambda c: ["/efi/loader/entries/<текущая>-<профиль>.conf",
                               "профиль: cuN (CU 1-3) и/или rbM (RB 1-2)",
                               "по желанию: bootctl set-oneshot"]),
    Step("verify", "Проверка (после перезагрузки)",
         "Сверяет cmdline, строки lucienne-5300u и lucienne-5300u-rb, active_cu_number, "
         "backend_enable_mask, ошибки в журнале; для RB сравнивает PA_SC_RASTER_CONFIG.",
         s_verify, lambda c: [f"профиль сейчас: {profile_name(cmdline_mode(), cmdline_rb_mode()) or 'stock'}",
                              "ожидание CU: режим 1 -> 6, 2 -> 7, 3 -> 8",
                              "ожидание RB: режим 1 -> mask 0x1, 2 -> mask 0x3"]),
    Step("stress", "Нагрузка, vkpeak, FurMark",
         "Сравнивает журнал до/после твоей нагрузки; по желанию vkpeak (CU) и "
         "FurMark 1080p (RB), считает прирост относительно стока.",
         s_stress, lambda c: ["glmark2 / видео / игра в другом окне", "vkpeak <idx>",
                              "furmark --demo <имя> --benchmark --p1080 --vsync 0"]),
]


# --------------------------------------------------------------------------
# откат
# --------------------------------------------------------------------------
def do_rollback(c: Ctx) -> str:
    plan = []
    if c.backup.exists():
        plan.append(f"вернуть модуль {c.backup} -> {c.installed}")
    ib = c.state.get("initrd_backup")
    if ib:
        plan.append(f"вернуть initramfs {ib['bak']} -> {ib['img']}")
    for e in c.state.get("entries", []):
        plan.append(f"удалить запись {e}")
    if not plan:
        c.log("Откатывать нечего (бэкапов и созданных записей нет). "
              "Если модуль всё же наш: sudo pacman -S linux")
        return "нечего"
    if not c.confirm("Откат:", detail="\n".join(plan), strict=True):
        raise Abort("отменено")
    if c.backup.exists():
        c.sh(["install", "-m644", c.backup, c.installed], sudo=True)
    if ib:
        c.sh(["cp", ib["bak"], ib["img"]], sudo=True)
    for e in c.state.get("entries", []):
        c.sh(["rm", "-f", e], sudo=True)
    if not c.dry:
        c.state["entries"] = []
        c.state["done"] = {k: v for k, v in c.state["done"].items()
                           if k not in ("entries", "verify", "stress")}
    c.log("Готово. Если amdgpu в твоём initramfs, пересобери образ. "
          "Крайний вариант: sudo pacman -S linux")
    return "откат выполнен"


# --------------------------------------------------------------------------
# запуск шагов и главные циклы
# --------------------------------------------------------------------------
def run_step(c: Ctx, step_title: str, fn, step_id: str | None):
    c.log(f"=== {step_title} ===")
    try:
        msg = fn(c)
        c.log(f"[ok] {msg}")
        if step_id and not c.dry:
            c.state["done"][step_id] = time.strftime("%F %T")
            c.failed.discard(step_id)
    except StepError as e:
        if step_id:
            c.failed.add(step_id)
        c.log(f"[ОШИБКА] {e}")
    except Abort as e:
        c.log(f"[стоп] {e}")
    except Exception:
        if step_id:
            c.failed.add(step_id)
        for ln in traceback.format_exc().splitlines():
            c.log(ln)
    finally:
        c.save()
        c.refresh()


def main_plain(c: Ctx):
    while True:
        c.refresh()
        print()
        for i, s in enumerate(STEPS):
            print(f" {SYM[c.status(s)]} {i + 1}. {s.title}")
        try:
            a = input("номер шага | s<N> пропуск | d dry-run | r откат | q выход: ").strip().lower()
        except EOFError:
            return
        if a == "q":
            return
        if a == "d":
            c.dry = not c.dry
            print("dry-run:", c.dry)
        elif a == "r":
            run_step(c, "Откат", do_rollback, None)
        elif a.startswith("s") and a[1:].isdigit() and 1 <= int(a[1:]) <= len(STEPS):
            sid = STEPS[int(a[1:]) - 1].id
            c.state["skipped"][sid] = not c.state["skipped"].get(sid)
            c.save()
        elif a.isdigit() and 1 <= int(a) <= len(STEPS):
            s = STEPS[int(a) - 1]
            for ln in s.preview(c):
                print("  ", ln)
            run_step(c, s.title, s.run, s.id)


def main_curses(scr, args):
    with contextlib.suppress(curses.error):
        curses.curs_set(0)
    ui = CursesUI(scr)
    c = Ctx(ui, args.dry_run, args.workdir)
    ui.ctx = c
    c.refresh()
    while True:
        ui.draw()
        k = scr.getch()
        if k in (ord("q"), 27):
            return
        if k in (curses.KEY_UP, ord("k")):
            ui.sel = max(0, ui.sel - 1)
        elif k in (curses.KEY_DOWN, ord("j")):
            ui.sel = min(len(STEPS) - 1, ui.sel + 1)
        elif k == ord("d"):
            c.dry = not c.dry
        elif k == ord("l"):
            ui.pager("\n".join(ui.lines), "Лог")
        elif k == ord("r"):
            run_step(c, "Откат", do_rollback, None)
        elif k == ord("s"):
            sid = STEPS[ui.sel].id
            c.state["skipped"][sid] = not c.state["skipped"].get(sid)
            c.save()
            c.refresh()
        elif k in (10, 13, curses.KEY_ENTER):
            s = STEPS[ui.sel]
            run_step(c, s.title, s.run, s.id)
            if c.status(s) == "done" and ui.sel < len(STEPS) - 1:
                ui.sel += 1


def main():
    ap = argparse.ArgumentParser(description="Пошаговая разблокировка CU на 5300U")
    ap.add_argument("--plain", action="store_true", help="без curses")
    ap.add_argument("--dry-run", action="store_true", help="ничего не менять")
    ap.add_argument("--workdir", default="~/amdbuild", help="каталог для исходников")
    ap.add_argument("--version", action="version", version=f"cu-unlock {__version__}")
    args = ap.parse_args()
    locale.setlocale(locale.LC_ALL, "")
    if args.plain or not sys.stdout.isatty() or not sys.stdin.isatty():
        ui = PlainUI()
        main_plain(Ctx(ui, args.dry_run, args.workdir))
    else:
        curses.wrapper(main_curses, args)


if __name__ == "__main__":
    main()
