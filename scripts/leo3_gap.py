#!/usr/bin/env python3
"""Gap analysis between Leo-III and Astraea on TPTP-Smoke and TPTP-Dev.

    scripts/leo3_gap.py --raw ~/leo3_runs --results benchmarks/results

Reads the per-problem CSVs written by scripts/leo3_run.py and `mix external.eval
--csv`, extracts the inference rules of every Leo-III proof from the raw TSTP
output in --raw/<split>_<config>_<timeout>/<problem>.out, and writes:

  leo3_proof_features.csv  one row per (split, config, timeout, problem) Leo-III proof
  leo3_gap.csv             one row per THM problem: who solves it, gap features
  and a Markdown summary on stdout.

A rule appearing in a proof shows that Leo-III used it, not that the problem
needs it; the counts are an upper bound on what each feature buys.
"""

import argparse
import csv
import re
import shutil
from collections import Counter, defaultdict
from pathlib import Path

INFERENCE_RE = re.compile(r"inference\((\w+)")

# Leo-III rule name -> gap feature. Rules missing here (cnf, neg_conjecture,
# defexp_and_simp_and_etaexpand, simp, paramod_ordered, eqfactor_ordered,
# pattern_uni, lifteq, miniscope, polarity_switch, replace_leibeq,
# replace_andrewseq) are first-order or preprocessing steps Astraea also has.
FEATURES = {
    "choice": "choice",
    "prim_subst": "primitive substitution",
    "pre_uni": "pre-unification beyond patterns",
    "flex_uni": "pre-unification beyond patterns",
    "funcspec": "function synthesis",
    "bool_ext": "Boolean extensionality",
    "func_ext": "functional extensionality",
    "instance": "special instances",
    "instantiate_sets": "set instantiation",
    "rewrite": "unit rewriting (demodulation)",
    "ac_simp": "AC simplification",
    "e": "external cooperation (E)",
}
# Insertion order above is also the priority for the primary feature of a proof.
FEATURE_ORDER = list(dict.fromkeys(FEATURES.values()))
NO_FEATURE = "none of the above (search/time)"
SOLVED_STATUS = {"Theorem", "Unsatisfiable", "ContradictoryAxioms"}


def read_csv(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def proof_rules(out_file):
    """Inference rule counts of the proof in out_file, or None without a proof.
    A proof cut off by the kill still counts as E-assisted when Leo-III reported
    that E found a proof."""
    text = out_file.read_text(errors="replace")
    e_found = "External prover 'e' found a proof" in text
    start = text.find("% SZS output start")
    end = text.find("% SZS output end")
    if start < 0 or end < 0:
        return Counter(e=1) if e_found else None
    rules = Counter(INFERENCE_RE.findall(text[start:end]))
    if e_found:
        rules["e"] = max(rules["e"], 1)
    return rules


def features_of(rules):
    return sorted({FEATURES[r] for r in rules if r in FEATURES}, key=FEATURE_ORDER.index)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw", required=True, type=Path)
    ap.add_argument("--results", default=Path("benchmarks/results"), type=Path)
    ap.add_argument("--copy-proofs", type=Path,
                    help="copy the Leo-III output used for each gap problem into this directory")
    args = ap.parse_args()

    feature_rows = []
    leo = {}  # (split, config, timeout) -> {problem: row}
    rules_of = {}  # (split, config, timeout, problem) -> Counter
    for path in sorted(args.results.glob("leo3_*_*_*s.csv")):
        m = re.match(r"leo3_(smoke|dev)_(stock|e)_([\d.]+)s\.csv", path.name)
        if not m:
            continue
        split, config, t = m.groups()
        rows = read_csv(path)
        leo[(split, config, t)] = {r["problem"]: r for r in rows}
        for r in rows:
            if r["solved"] != "1":
                continue
            out = args.raw / f"{split}_{config}_{t}" / f"{r['problem']}.out"
            rules = proof_rules(out) if out.exists() else None
            if rules is None:
                continue
            rules_of[(split, config, t, r["problem"])] = rules
            feature_rows.append({
                "split": split, "config": config, "timeout_s": t, "problem": r["problem"],
                "domain": r["domain"], "features": ";".join(features_of(rules)),
                "rules": ";".join(f"{k}:{v}" for k, v in sorted(rules.items())),
            })

    with open(args.results / "leo3_proof_features.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["split", "config", "timeout_s", "problem", "domain", "features", "rules"])
        w.writeheader()
        w.writerows(feature_rows)

    print_time_views(leo)

    gap_rows = []
    for split in ("smoke", "dev"):
        astraea = defaultdict(dict)  # problem -> {"baseline@2500": row, ...}
        for path in sorted(args.results.glob(f"astraea_{split}_*ms.csv")):
            for r in read_csv(path):
                astraea[r["problem"]][f"{r['config']}@{r['timeout_ms']}"] = r
        if not astraea:
            continue
        runs = sorted({c for v in astraea.values() for c in v})

        def leo_solved(config, t, p):
            row = leo.get((split, config, t), {}).get(p)
            return row is not None and row["solved"] == "1"

        for p, by_run in sorted(astraea.items()):
            any_row = next(iter(by_run.values()))
            if any_row["expected"] != "Theorem":
                continue
            row = {"split": split, "problem": p, "domain": any_row["domain"]}
            for run in runs:
                r = by_run.get(run)
                row[f"astraea_{run}"] = "" if r is None else int(r["solved_lcf"] == "1")
                if r is not None and run.startswith("leo3@"):
                    row[f"astraea_{run}"] = int(r["external_unverified"] == "1")
            for config in ("stock", "e"):
                for t in ("2.5", "10"):
                    row[f"leo3_{config}_{t}s"] = int(leo_solved(config, t, p))
            # Prefer the stock 10 s proof, then the stock 2.5 s one, then E.
            src = next(((c, t) for c, t in [("stock", "10"), ("stock", "2.5"), ("e", "10"), ("e", "2.5")]
                        if (split, c, t, p) in rules_of), None)
            rules = rules_of.get((split, *src, p)) if src else None
            row["proof_source"] = f"{src[0]}_{src[1]}s" if src else ""
            row["features"] = ";".join(features_of(rules) or [NO_FEATURE]) if rules else ""
            gap_rows.append(row)

    if not gap_rows:
        return
    fields = list(dict.fromkeys(k for r in gap_rows for k in r))
    for r in gap_rows:
        r["gap_class"] = gap_class(r)
    fields.append("gap_class")
    with open(args.results / "leo3_gap.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(gap_rows)

    if args.copy_proofs:
        args.copy_proofs.mkdir(parents=True, exist_ok=True)
        for r in gap_rows:
            if r["gap_class"] and r["proof_source"]:
                src = args.raw / f"{r['split']}_{r['proof_source'][:-1]}" / f"{r['problem']}.out"
                shutil.copy(src, args.copy_proofs / f"{r['problem']}.{r['proof_source']}.out")

    summarize(gap_rows)


def print_time_views(leo):
    """Leo-III THM solved counts under a 2.5 s budget measured four ways: the
    2.5 s wall-clock run, and from the 10 s run the problems whose Leo-III-reported
    time (from JVM main, so without JVM startup), reasoning time without parsing,
    or CPU time (all threads and E) stayed within 2.5 s."""
    print("| Split | Config | 2.5 s wall run | 10 s run: Leo time <= 2.5 s | "
          "10 s run: w/o parsing <= 2.5 s | 10 s run: CPU <= 2.5 s | 10 s wall run |")
    print("| :--- | :--- | ---: | ---: | ---: | ---: | ---: |")
    for split in ("smoke", "dev"):
        for config in ("stock", "e"):
            short = leo.get((split, config, "2.5"), {})
            long = leo.get((split, config, "10"), {})
            solved = [r for r in long.values() if r["solved"] == "1"]

            def within(field, scale):
                return sum(1 for r in solved if r[field] and float(r[field]) / scale <= 2.5)

            print(f"| {split} | {config} | {sum(r['solved'] == '1' for r in short.values())} | "
                  f"{within('leo_ms', 1000)} | {within('leo_ms_noparse', 1000)} | "
                  f"{within('cpu_s', 1)} | {len(solved)} |")


def astraea_solves(r, prefix="baseline@"):
    return any(v == 1 for k, v in r.items() if k.startswith(f"astraea_{prefix}"))


def astraea_internal_any(r):
    """Any Astraea configuration whose proof is LCF-verified (all but standalone leo3)."""
    return any(v == 1 for k, v in r.items()
               if k.startswith("astraea_") and not k.startswith("astraea_leo3@"))


def gap_class(r):
    """Why Leo-III solves r and the Astraea baseline does not ("" if no gap)."""
    leo_stock = r["leo3_stock_2.5s"] or r["leo3_stock_10s"]
    leo_e = r["leo3_e_2.5s"] or r["leo3_e_10s"]
    if not (leo_stock or leo_e) or r.get("astraea_baseline@2500") == 1:
        return ""
    if r.get("astraea_baseline@10000") == 1:
        return "more search time (Astraea solves at 10 s)"
    # Leo-III with --atp e also solves problems on its own (run-to-run variance).
    if not leo_stock and "external cooperation (E)" in r["features"]:
        return "external cooperation (E)"
    return "calculus/search"


def primary_feature(r):
    """The first feature of r in FEATURE_ORDER, which lists the most specific
    higher-order features first."""
    fs = (r["features"] or "no proof recorded").split(";")
    return min(fs, key=lambda f: FEATURE_ORDER.index(f) if f in FEATURE_ORDER else len(FEATURE_ORDER))


def table_by_feature(gap):
    by_feature = defaultdict(list)
    for r in gap:
        for f in (r["features"] or "no proof recorded").split(";"):
            by_feature[f].append(r)
    primary = Counter(primary_feature(r) for r in gap)
    print("| Feature in Leo-III proof | Problems using it | As primary feature | Smoke | Dev | Examples |")
    print("| :--- | ---: | ---: | ---: | ---: | :--- |")
    for f in FEATURE_ORDER + [NO_FEATURE, "no proof recorded"]:
        ps = by_feature.get(f, [])
        if ps:
            ex = ", ".join(r["problem"] for r in ps[:6])
            print(f"| {f} | {len(ps)} | {primary[f]} | {sum(r['split'] == 'smoke' for r in ps)} | "
                  f"{sum(r['split'] == 'dev' for r in ps)} | {ex} |")


def summarize(rows):
    gap = [r for r in rows if r["gap_class"]]
    print(f"\n### Leo-III (any config, any timeout) solves, Astraea baseline at 2.5 s does not: {len(gap)}\n")
    print("| Gap class | Problems | Smoke | Dev | Solved by another LCF-verified Astraea config |")
    print("| :--- | ---: | ---: | ---: | ---: |")
    for c in sorted({r["gap_class"] for r in gap}):
        ps = [r for r in gap if r["gap_class"] == c]
        print(f"| {c} | {len(ps)} | {sum(r['split'] == 'smoke' for r in ps)} | "
              f"{sum(r['split'] == 'dev' for r in ps)} | {sum(astraea_internal_any(r) for r in ps)} |")

    calc = [r for r in gap if r["gap_class"] == "calculus/search"]
    print(f"\n#### Calculus/search gap: features in the stock Leo-III proof ({len(calc)} problems)\n")
    table_by_feature(calc)

    print("\n#### Gap by domain\n")
    print("| Domain | Problems | Gap classes | Features in calculus/search problems |")
    print("| :--- | ---: | :--- | :--- |")
    by_domain = defaultdict(list)
    for r in gap:
        by_domain[r["domain"]].append(r)
    for d, ps in sorted(by_domain.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        cc = Counter(r["gap_class"] for r in ps)
        fc = Counter(f for r in ps if r["gap_class"] == "calculus/search" for f in r["features"].split(";"))
        print(f"| {d} | {len(ps)} | " + ", ".join(f"{k} {v}" for k, v in cc.most_common()) + " | "
              + ", ".join(f"{k} {v}" for k, v in fc.most_common()) + " |")

    print("\n#### Gap problem list\n")
    for r in gap:
        print(f"- {r['split']} {r['problem']}: {r['gap_class']}; proof {r['proof_source']}: {r['features']}")

    leo_any = lambda r: any(r[k] for k in ("leo3_stock_2.5s", "leo3_stock_10s", "leo3_e_2.5s", "leo3_e_10s"))
    rev = [r for r in rows if astraea_internal_any(r) and not leo_any(r)]
    print(f"\n### Astraea solves (any LCF-verified config), Leo-III (any config) does not: {len(rev)}\n")
    for r in rev:
        runs = [k[len("astraea_"):] for k, v in r.items() if k.startswith("astraea_") and v == 1]
        print(f"- {r['split']} {r['problem']} ({', '.join(runs)})")


if __name__ == "__main__":
    main()
