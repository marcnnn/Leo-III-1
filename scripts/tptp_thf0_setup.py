#!/usr/bin/env python3
"""
TPTP-v9.3.1 installer, strict THF0 classifier, deterministic splitter, and anonymizer.

Supports both:
  - `--full`: extract the complete TPTP-v9.3.1 library (~10.5 GB, ideal for `armix` with 1.1 TB free)
  - default THF-slice mode: extract only `Axioms/`, `Documents/`, and `Problems/*/*^*.p` (~300 MB)
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

TPTP_VERSION = "v9.3.1"
TPTP_ROOT_NAME = f"TPTP-{TPTP_VERSION}"
TPTP_TGZ_URL = f"https://tptp.org/TPTP/Distribution/{TPTP_ROOT_NAME}.tgz"
TPTP_BUGGED_URL = f"https://tptp.org/TPTP/Distribution/BuggedProblems-{TPTP_VERSION}.txt"
DEFAULT_SEED = "astraea-tptp-v9.3.1"

HEADER_STATUS_RE = re.compile(r"^%\s*Status\s*:\s*([A-Za-z]+)", re.MULTILINE)
HEADER_RATING_RE = re.compile(r"^%\s*Rating\s*:\s*([0-9.]+)", re.MULTILINE)
HEADER_SPC_RE = re.compile(r"^%\s*SPC\s*:\s*([A-Za-z0-9_]+)", re.MULTILINE)
HEADER_TYPE_CONNS_RE = re.compile(
    r"\(\s*\d+\s*>;\s*(\d+)\s*\*\s*;\s*(\d+)\s*\+\s*;\s*(\d+)\s*<<\s*\)"
)
HEADER_CHOICE_VARS_RE = re.compile(r"\(\s*(\d+)\s*@-;\s*(\d+)\s*@\+\s*\)")
INCLUDE_RE = re.compile(r"include\(\s*'([^']+)'(?:\s*,\s*\[[^\]]*\])?\s*\)\s*\.")

# Markers of polymorphic TH1, interpreted arithmetic, modal logic specs, choice, or tuples
TH1_POLY_RE = re.compile(r"(!>|\?\*|\?>|@@\+|@@-|@=|\$tType\s*>|>\s*\$tType)")
ARITH_RE = re.compile(
    r"\$(int|rat|real|uminus|sum|difference|product|quotient|less|lesseq|greater|greatereq|is_int|is_rat|to_int|to_rat|to_real)\b"
)
MODAL_LOGIC_RE = re.compile(r"\bthf\s*\([^,]+,\s*logic\s*,")
CHOICE_RE = re.compile(r"(@\+|@-)")
LET_ITE_RE = re.compile(r"\$(ite|let)\b")

TPTP_KEYWORDS_AND_BUILTINS = {
    "thf",
    "tff",
    "fof",
    "cnf",
    "tpi",
    "include",
    "type",
    "axiom",
    "hypothesis",
    "definition",
    "assumption",
    "lemma",
    "theorem",
    "corollary",
    "conjecture",
    "negated_conjecture",
    "plain",
    "unknown",
    "fi_domain",
    "fi_functors",
    "fi_predicates",
}

IDENT_TOKEN_RE = re.compile(
    r"('(?:\\.|[^'\\])*'|\$\$?[A-Za-z0-9_]+|[A-Za-z][A-Za-z0-9_]*)"
)

THM_STATUSES = {"Theorem", "ContradictoryAxioms"}
CSA_STATUSES = {"CounterSatisfiable", "Satisfiable"}


def parse_bugged_problems(text: str) -> Set[str]:
    """Extract problem stems like SYN000^2 or LCL452+1 from BuggedProblems-*.txt."""
    return set(re.findall(r"\b[A-Z]{3}\d{3}[\^+\-_=]\d+(?:\.\d+)?\b", text))


def stream_extract_tptp(url: str, bugged_url: str, dest: Path, full: bool) -> None:
    """Stream TPTP .tgz via curl | tar into dest.parent/<TPTP_ROOT_NAME>."""
    dest.mkdir(parents=True, exist_ok=True)
    parent = dest.parent
    print(f"[1/3] Fetching bugged problems list from {bugged_url} ...")
    subprocess.run(
        ["curl", "-fsSL", bugged_url, "-o", str(dest / f"BuggedProblems-{TPTP_VERSION}.txt")],
        check=True,
    )

    if full:
        print(f"[2/3] Streaming full {TPTP_ROOT_NAME} (~10.5 GB unpacked) from {url} into {dest} ...")
        cmd = f"curl -fsSL '{url}' | tar -xz -C '{parent}'"
    else:
        print(f"[2/3] Streaming THF slice (*^*.p + Axioms/) from {url} into {dest} ...")
        cmd = (
            f"curl -fsSL '{url}' | "
            f"tar -xz -C '{parent}' --wildcards "
            f"'{TPTP_ROOT_NAME}/Axioms/*' "
            f"'{TPTP_ROOT_NAME}/Problems/*/*^*.p'"
        )
    subprocess.run(["bash", "-o", "pipefail", "-c", cmd], check=True)
    print(f"[3/3] Extraction complete at {dest}")


def resolve_includes(
    problem_path: Path,
    tptp_root: Path,
    axiom_cache: Optional[Dict[Path, str]] = None,
    seen: Optional[Set[Path]] = None,
) -> Tuple[str, int, bool]:
    """Recursively load problem text with included Axioms. Returns (combined_text, include_count, missing)."""
    if seen is None:
        seen = set()
    if problem_path in seen:
        return ("", 0, False)
    seen.add(problem_path)

    if axiom_cache is not None and problem_path in axiom_cache:
        raw = axiom_cache[problem_path]
    else:
        raw = problem_path.read_text(encoding="utf-8", errors="replace")
        if axiom_cache is not None and "Axioms" in problem_path.parts:
            axiom_cache[problem_path] = raw

    includes = INCLUDE_RE.findall(raw)
    missing = False
    chunks: List[str] = []

    for rel in includes:
        candidates = [problem_path.parent / rel, tptp_root / rel]
        found = next((c for c in candidates if c.is_file()), None)
        if found is None:
            missing = True
            continue
        sub_text, _, sub_missing = resolve_includes(found, tptp_root, axiom_cache, seen)
        missing = missing or sub_missing
        chunks.append(sub_text)

    chunks.append(raw)
    return ("\n".join(chunks), len(includes), missing)


def strip_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        if line.startswith("%"):
            continue
        in_quote = False
        escaped = False
        out = []
        for ch in line:
            if escaped:
                out.append(ch)
                escaped = False
                continue
            if ch == "\\":
                out.append(ch)
                escaped = True
                continue
            if ch == "'":
                in_quote = not in_quote
                out.append(ch)
                continue
            if ch == "%" and not in_quote:
                break
            out.append(ch)
        cleaned = "".join(out).strip()
        if cleaned:
            lines.append(cleaned)
    return "\n".join(lines)


def classify_problem(
    problem_path: Path,
    tptp_root: Path,
    bugged: Set[str],
    axiom_cache: Dict[Path, str],
) -> Dict[str, object]:
    stem = problem_path.stem  # e.g. SYO001^1
    domain = stem[:3]
    raw_head = problem_path.read_text(encoding="utf-8", errors="replace")

    status_m = HEADER_STATUS_RE.search(raw_head)
    rating_m = HEADER_RATING_RE.search(raw_head)
    spc_m = HEADER_SPC_RE.search(raw_head)
    tc_m = HEADER_TYPE_CONNS_RE.search(raw_head)
    ch_m = HEADER_CHOICE_VARS_RE.search(raw_head)

    status = status_m.group(1) if status_m else "Unknown"
    rating = float(rating_m.group(1)) if rating_m else -1.0
    spc = spc_m.group(1) if spc_m else ""

    has_ext_type_conns = (
        any(int(tc_m.group(i)) > 0 for i in (1, 2, 3)) if tc_m else False
    )
    header_has_choice = (
        (int(ch_m.group(1)) + int(ch_m.group(2)) > 0) if ch_m else False
    )

    full_text, inc_count, missing_inc = resolve_includes(problem_path, tptp_root, axiom_cache)
    logic_body = strip_comments(full_text)

    is_bugged = stem in bugged
    spc_is_th1 = spc.startswith("TH1_")
    spc_is_ari = spc.endswith("_ARI")
    has_th1 = spc_is_th1 or bool(TH1_POLY_RE.search(logic_body))
    has_arith = spc_is_ari or bool(ARITH_RE.search(logic_body))
    has_modal = bool(MODAL_LOGIC_RE.search(logic_body))
    has_choice = header_has_choice or bool(CHOICE_RE.search(logic_body))
    has_let_ite = bool(LET_ITE_RE.search(logic_body))
    axiom_count = len(re.findall(r",\s*(?:axiom|hypothesis|definition)\s*,", logic_body))

    strict_thf0 = (
        not is_bugged
        and not missing_inc
        and not has_th1
        and not has_arith
        and not has_modal
        and not has_choice
        and not has_ext_type_conns
    )

    return {
        "problem": stem,
        "domain": domain,
        "spc": spc,
        "rel_path": str(problem_path.relative_to(tptp_root)),
        "status": status,
        "rating": rating,
        "includes": inc_count,
        "axioms": axiom_count,
        "strict_thf0": strict_thf0,
        "has_let_ite": has_let_ite,
        "has_choice": has_choice,
        "has_ext_types": has_ext_type_conns,
        "has_th1": has_th1,
        "has_arith": has_arith,
        "has_modal": has_modal,
        "is_bugged": is_bugged,
        "missing_include": missing_inc,
    }


def deterministic_key(seed: str, problem: str) -> str:
    return hashlib.sha256(f"{seed}:{problem}".encode("utf-8")).hexdigest()


def build_manifests(records: List[Dict[str, object]], out_dir: Path, seed: str) -> Dict[str, int]:
    out_dir.mkdir(parents=True, exist_ok=True)

    csv_path = out_dir / "thf_catalog.csv"
    fieldnames = [
        "problem",
        "domain",
        "spc",
        "rel_path",
        "status",
        "rating",
        "includes",
        "axioms",
        "strict_thf0",
        "has_let_ite",
        "has_choice",
        "has_ext_types",
        "has_th1",
        "has_arith",
        "has_modal",
        "is_bugged",
        "missing_include",
    ]
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in sorted(records, key=lambda x: str(x["problem"])):
            writer.writerow(r)

    eligible_thm = [
        r
        for r in records
        if r["strict_thf0"] and not r["has_let_ite"] and r["status"] in THM_STATUSES
    ]
    eligible_csa = [
        r
        for r in records
        if r["strict_thf0"] and not r["has_let_ite"] and r["status"] in CSA_STATUSES
    ]

    eligible_thm.sort(key=lambda r: deterministic_key(seed, str(r["problem"])))
    eligible_csa.sort(key=lambda r: deterministic_key(seed, str(r["problem"])))

    # Smoke: 35 easy THM (rating 0.00..0.25 if available) + 15 CSA traps
    easy_thm = [r for r in eligible_thm if 0.0 <= float(r["rating"]) <= 0.25]
    smoke_thm = easy_thm[:35] if len(easy_thm) >= 35 else eligible_thm[:35]
    smoke_thm_ids = {str(r["problem"]) for r in smoke_thm}
    smoke_csa = eligible_csa[:15]
    smoke_csa_ids = {str(r["problem"]) for r in smoke_csa}

    rem_thm = [r for r in eligible_thm if str(r["problem"]) not in smoke_thm_ids]
    rem_csa = [r for r in eligible_csa if str(r["problem"]) not in smoke_csa_ids]

    # Dev: 240 THM + 60 CSA; Holdout: up to 400 THM + 100 CSA (strictly disjoint)
    dev_thm = rem_thm[:240]
    dev_csa = rem_csa[:60]
    holdout_thm = rem_thm[240:640]
    holdout_csa = rem_csa[60:160]

    splits = {
        "smoke": sorted(str(r["problem"]) for r in (smoke_thm + smoke_csa)),
        "dev": sorted(str(r["problem"]) for r in (dev_thm + dev_csa)),
        "holdout": sorted(str(r["problem"]) for r in (holdout_thm + holdout_csa)),
    }

    lock_hashes: Dict[str, str] = {}
    for name, items in splits.items():
        txt = "\n".join(items) + ("\n" if items else "")
        p = out_dir / f"tptp_thf0_{name}.txt"
        p.write_text(txt, encoding="utf-8")
        lock_hashes[name] = hashlib.sha256(txt.encode("utf-8")).hexdigest()

    # Domain distribution summary
    domain_counts: Dict[str, int] = {}
    for r in eligible_thm + eligible_csa:
        dom = str(r["domain"])
        domain_counts[dom] = domain_counts.get(dom, 0) + 1

    summary = {
        "tptp_version": TPTP_VERSION,
        "seed": seed,
        "total_thf_scanned": len(records),
        "strict_thf0_thm_pool": len(eligible_thm),
        "strict_thf0_csa_pool": len(eligible_csa),
        "domains_in_strict_thf0": dict(sorted(domain_counts.items(), key=lambda kv: -kv[1])),
        "splits": {
            "smoke": {"total": len(splits["smoke"]), "thm": len(smoke_thm), "csa": len(smoke_csa)},
            "dev": {"total": len(splits["dev"]), "thm": len(dev_thm), "csa": len(dev_csa)},
            "holdout": {"total": len(splits["holdout"]), "thm": len(holdout_thm), "csa": len(holdout_csa)},
        },
        "sha256": lock_hashes,
    }
    (out_dir / "manifest_lock.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    return {k: len(v) for k, v in splits.items()}


def anonymize_problem(problem_path: Path, tptp_root: Path, seed: str) -> str:
    """Inline includes, strip all % headers/comments, and scramble user identifiers."""
    full_text, _, missing = resolve_includes(problem_path, tptp_root)
    if missing:
        raise RuntimeError(f"Missing included axiom file while expanding {problem_path}")

    body = strip_comments(full_text)
    body = INCLUDE_RE.sub("", body)

    var_map: Dict[str, str] = {}
    sym_map: Dict[str, str] = {}

    raw_tokens = set(IDENT_TOKEN_RE.findall(body))
    ordered = sorted(
        raw_tokens,
        key=lambda tok: hashlib.sha256(f"{seed}:{tok}".encode("utf-8")).hexdigest(),
    )

    for tok in ordered:
        if tok.startswith("$") or tok in TPTP_KEYWORDS_AND_BUILTINS:
            continue
        if tok[0].isupper():
            var_map[tok] = f"V_{len(var_map) + 1:04d}"
        else:
            sym_map[tok] = f"s_{len(sym_map) + 1:04d}"

    def repl(match: re.Match[str]) -> str:
        tok = match.group(0)
        if tok in var_map:
            return var_map[tok]
        if tok in sym_map:
            return sym_map[tok]
        return tok

    return IDENT_TOKEN_RE.sub(repl, body)


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_boot = sub.add_parser("bootstrap", help="Download/extract TPTP-v9.3.1 and build split manifests")
    p_boot.add_argument(
        "--dest",
        type=Path,
        default=Path.home() / ".local" / "share" / "tptp" / TPTP_ROOT_NAME,
        help="Destination directory for TPTP-v9.3.1",
    )
    p_boot.add_argument(
        "--manifests",
        type=Path,
        required=True,
        help="Output directory for smoke/dev/holdout manifests and lockfile",
    )
    p_boot.add_argument(
        "--full",
        action="store_true",
        help="Extract the complete TPTP-v9.3.1 archive (~10.5 GB) instead of only THF + Axioms",
    )
    p_boot.add_argument("--seed", default=DEFAULT_SEED)
    p_boot.add_argument("--skip-download", action="store_true")

    p_anon = sub.add_parser("anonymize", help="Inline axioms, strip comments, and scramble symbols")
    p_anon.add_argument("problem_file", type=Path)
    p_anon.add_argument(
        "--tptp-root",
        type=Path,
        default=Path.home() / ".local" / "share" / "tptp" / TPTP_ROOT_NAME,
    )
    p_anon.add_argument("--seed", default="run-001")

    args = parser.parse_args(argv)

    if args.cmd == "bootstrap":
        dest: Path = args.dest.expanduser().resolve()
        if not args.skip_download:
            stream_extract_tptp(TPTP_TGZ_URL, TPTP_BUGGED_URL, dest, full=args.full)

        bugged_file = dest / f"BuggedProblems-{TPTP_VERSION}.txt"
        bugged = (
            parse_bugged_problems(bugged_file.read_text(encoding="utf-8", errors="replace"))
            if bugged_file.is_file()
            else set()
        )

        problems_dir = dest / "Problems"
        thf_files = sorted(problems_dir.glob("*/*^*.p"))
        print(f"Scanning {len(thf_files)} THF problem files ...")
        axiom_cache: Dict[Path, str] = {}
        records = [classify_problem(p, dest, bugged, axiom_cache) for p in thf_files]
        counts = build_manifests(records, args.manifests.expanduser().resolve(), args.seed)
        print(f"Manifests written to {args.manifests}: {counts}")
        return 0

    if args.cmd == "anonymize":
        out = anonymize_problem(
            args.problem_file.expanduser().resolve(),
            args.tptp_root.expanduser().resolve(),
            args.seed,
        )
        sys.stdout.write(out + "\n")
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
