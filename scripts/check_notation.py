#!/usr/bin/env python3
"""Notation (binder-precedence) release check for the BasicElliptic statements and definitions.

Every statement or definition `Prop` with a big-operator binder (`∫`, `⨍`, `∑`, `⨆`, ...) followed
by an infix operator must be checked with `pp.notation false`, because

    ∫ y in s, ⟪G y, ∇ φ y⟫ + ∫ y in s, f y * φ y

parses as `∫ y in s, (⟪G y, ∇ φ y⟫ + ∫ y in s, f y * φ y)`.

This script

1. collects every `def` in the files `BasicElliptic/{Statements,Defs}/*.lean` and
   `BasicElliptic/Basic/HalfSpace.lean` (fully qualified, following `namespace`/`end`);
2. writes a scratch Lean file that imports `BasicElliptic` and `#print`s each of them with
   `set_option pp.notation false`, runs it with `lake env lean`, and saves the output to a log
   (default `.lake/notation-check/notation.log`) for inspection;
3. flags every big-operator binder whose body is directly an `HAdd.hAdd` / `HSub.hSub` application:
   * `SUSPECT` if that body itself contains another big operator (a binder that swallowed the
     following summand);
   * `note` otherwise (usually intended, e.g. `∫ y, (f y + g y)`; inspect).

Exit status: 0 if there is no `SUSPECT`, 1 otherwise, 2 if Lean failed. Requires a built library
(`lake build BasicElliptic`).

Usage:
    scripts/check_notation.py [--log FILE] [--keep-going]
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "BasicElliptic"
FROZEN = sorted((SRC / "Statements").glob("*.lean")) + sorted((SRC / "Defs").glob("*.lean")) + [
    SRC / "Basic" / "HalfSpace.lean"
]
WORK = ROOT / ".lake" / "notation-check"

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+([^\s(:{\[]+)")
NAMESPACE = re.compile(r"^namespace\s+(\S+)")
SECTION = re.compile(r"^(?:public\s+)?(?:noncomputable\s+)?section\b\s*(\S*)")
END = re.compile(r"^end\b\s*(\S*)")
# Heads of big operators as printed with `pp.notation false`.
BIG_OPS = (
    "MeasureTheory.integral",
    "MeasureTheory.lintegral",
    "MeasureTheory.average",
    "MeasureTheory.laverage",
    "Finset.sum",
    "Finset.prod",
    "tsum",
    "iSup",
    "iInf",
)
BIG_OP_RE = re.compile(r"\b(" + "|".join(re.escape(h) for h in BIG_OPS) + r")\b")
FUN_INFIX = re.compile(r"fun\s+[^=]*?=>\s*\(?\s*(HAdd\.hAdd|HSub\.hSub)\b")


def frozen_defs() -> list[str]:
    names: list[str] = []
    for path in FROZEN:
        stack: list[tuple[str, str]] = []  # (kind, name)
        in_comment = 0
        for raw in path.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            # crude block-comment skipping (docstrings and module docs)
            if in_comment:
                in_comment += line.count("/-") - line.count("-/")
                continue
            if line.startswith("/-"):
                in_comment = line.count("/-") - line.count("-/")
                continue
            if m := NAMESPACE.match(line):
                stack.append(("ns", m.group(1)))
            elif m := SECTION.match(line):
                stack.append(("sec", m.group(1)))
            elif m := END.match(line):
                if stack:
                    stack.pop()
            elif m := DECL.match(line):
                ns = ".".join(n for k, n in stack if k == "ns")
                names.append(f"{ns}.{m.group(1)}" if ns else m.group(1))
    return names


def body_after(text: str, start: int) -> str:
    """The expression starting at `start`, up to the first unmatched closing bracket."""
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                return text[start:i]
            depth -= 1
    return text[start:]


def scan(name: str, printed: str) -> list[tuple[str, str]]:
    flat = " ".join(printed.split())
    hits = []
    for op in BIG_OP_RE.finditer(flat):
        # the binder `fun` belonging to this big operator: the first `fun` after the head
        m = FUN_INFIX.match(flat, flat.find("fun", op.end())) if "fun" in flat[op.end():] else None
        if not m:
            continue
        # ignore if the `fun` is not the operator's own argument (another head in between)
        between = flat[op.end():m.start()]
        if BIG_OP_RE.search(between):
            continue
        body = body_after(flat, m.start(1))
        level = "SUSPECT" if BIG_OP_RE.search(body) else "note"
        snippet = flat[op.start():m.start(1) + min(len(body), 240)]
        hits.append((level, f"{name}: {snippet}"))
    return hits


def self_test() -> None:
    """The detector must flag a swallowed-summand `Div.IsWeakEqOn` shape and only note a plain sum."""
    bad = ("Eq (MeasureTheory.integral μ fun y => inner Real (A y) (g y)) "
           "(MeasureTheory.integral μ fun y => HAdd.hAdd (inner Real (G y) (g y)) "
           "(MeasureTheory.integral μ fun y => HMul.hMul (f y) (φ y)))")
    ok = "Finset.sum s fun i => HAdd.hAdd (f i) (g i)"
    assert [lv for lv, _ in scan("bad", bad)] == ["SUSPECT"], scan("bad", bad)
    assert [lv for lv, _ in scan("ok", ok)] == ["note"], scan("ok", ok)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", type=Path, default=WORK / "notation.log")
    ap.add_argument("--keep-going", action="store_true", help="exit 0 even with SUSPECT hits")
    args = ap.parse_args()
    self_test()

    names = frozen_defs()
    WORK.mkdir(parents=True, exist_ok=True)
    lean_file = WORK / "NotationCheck.lean"
    marker = "NOTATION-CHECK-DECL "
    lines = ["import BasicElliptic", "", "set_option pp.notation false",
             "set_option format.width 100", ""]
    for n in names:
        lines.append(f'#eval IO.println "{marker}{n}"')
        lines.append(f"#print {n}")
    lean_file.write_text("\n".join(lines) + "\n", encoding="utf-8")

    proc = subprocess.run(
        ["lake", "env", "lean", str(lean_file)], cwd=ROOT, capture_output=True, text=True
    )
    out = proc.stdout + proc.stderr
    args.log.parent.mkdir(parents=True, exist_ok=True)
    args.log.write_text(out, encoding="utf-8")
    if proc.returncode != 0:
        print(out[-4000:])
        print(f"check_notation: Lean failed (exit {proc.returncode}); log: {args.log}")
        return 2

    chunks = re.split(re.escape(marker), out)[1:]
    hits: list[tuple[str, str]] = []
    for chunk in chunks:
        name, _, printed = chunk.partition("\n")
        hits += scan(name.strip(), printed)

    shown = args.log.relative_to(ROOT) if args.log.is_relative_to(ROOT) else args.log
    print(f"check_notation: printed {len(chunks)} definitions (pp.notation false) to {shown}")
    for level, msg in hits:
        print(f"  [{level}] {msg}")
    suspects = sum(1 for level, _ in hits if level == "SUSPECT")
    notes = len(hits) - suspects
    print(f"check_notation: {suspects} suspect(s), {notes} note(s)")
    return 1 if suspects and not args.keep_going else 0


if __name__ == "__main__":
    sys.exit(main())
