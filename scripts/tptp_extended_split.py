#!/usr/bin/env python3
"""
Deterministic development sample of the TPTP-v9.3.1 THF fragments beyond strict THF0
(TH1 polymorphism, arithmetic, choice, modal logic, $let/$ite).

Draws only from the catalog rows with `strict_thf0 == False`. The locked Smoke, Dev and
Holdout splits are drawn from the strict THF0 pool alone (see `tptp_thf0_setup.py`), so
the sample is disjoint from all three without reading any of their problems. The
Holdout manifest is not opened.

Composition (each stratum ordered by SHA-256 of `seed:problem`):
  * every CounterSatisfiable/Satisfiable problem (soundness traps),
  * every modal, choice and $let/$ite problem,
  * then arithmetic and TH1-only theorems alternately until 150 problems.

Writes `tptp_extended_dev.txt` and `extended_manifest_lock.json` next to the catalog.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path

SEED = "astraea-tptp-v9.3.1-extended"
SIZE = 150
THM = {"Theorem", "ContradictoryAxioms"}
CSA = {"CounterSatisfiable", "Satisfiable"}
FRAGMENTS = ["has_th1", "has_arith", "has_choice", "has_modal", "has_let_ite"]


def key(problem: str) -> str:
    return hashlib.sha256(f"{SEED}:{problem}".encode("utf-8")).hexdigest()


def flag(row: dict, name: str) -> bool:
    return row[name] == "True"


def build(manifests: Path) -> dict:
    with (manifests / "thf_catalog.csv").open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    pool = [
        r
        for r in rows
        if not flag(r, "strict_thf0")
        and not flag(r, "is_bugged")
        and not flag(r, "missing_include")
        and r["status"] in THM | CSA
        and any(flag(r, k) for k in FRAGMENTS)
    ]
    pool.sort(key=lambda r: key(r["problem"]))

    chosen: list[dict] = []
    seen: set[str] = set()

    def take(rows_: list[dict], limit: int | None = None) -> None:
        for r in rows_:
            if limit is not None and limit <= 0:
                return
            if r["problem"] not in seen and len(chosen) < SIZE:
                chosen.append(r)
                seen.add(r["problem"])
                if limit is not None:
                    limit -= 1

    take([r for r in pool if r["status"] in CSA])
    take([r for r in pool if flag(r, "has_modal") or flag(r, "has_choice") or flag(r, "has_let_ite")])

    arith = [r for r in pool if flag(r, "has_arith") and r["problem"] not in seen]
    th1 = [r for r in pool if not flag(r, "has_arith") and r["problem"] not in seen]
    for a, t in zip(arith, th1):
        take([a, t])
    take(arith + th1)

    problems = sorted(r["problem"] for r in chosen)
    text = "\n".join(problems) + "\n"
    (manifests / "tptp_extended_dev.txt").write_text(text, encoding="utf-8")

    def count(pred) -> int:
        return sum(1 for r in chosen if pred(r))

    lock = {
        "tptp_version": "v9.3.1",
        "seed": SEED,
        "source": "thf_catalog.csv rows with strict_thf0 == False (disjoint from smoke/dev/holdout)",
        "total": len(problems),
        "thm": count(lambda r: r["status"] in THM),
        "csa": count(lambda r: r["status"] in CSA),
        "fragments": {k: count(lambda r, k=k: flag(r, k)) for k in FRAGMENTS},
        "sha256": {"extended": hashlib.sha256(text.encode("utf-8")).hexdigest()},
    }
    (manifests / "extended_manifest_lock.json").write_text(
        json.dumps(lock, indent=2) + "\n", encoding="utf-8"
    )
    return lock


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifests",
        type=Path,
        default=Path(__file__).resolve().parent.parent / "benchmarks" / "manifests",
    )
    print(json.dumps(build(parser.parse_args().manifests), indent=2))


if __name__ == "__main__":
    main()
