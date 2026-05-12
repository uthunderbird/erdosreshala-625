#!/usr/bin/env python3
"""
R2B Step 1 — Numerical verification scan for μ_{α−2}(n) ≫ n^{1.05}.

Implements Passes A–D of proof/red-team/r2b-step1-plan-2026-05-11.md §4.
(In the source repo the plan note lives at problems/625/work/notes/r2b-step1-plan-2026-05-11.md;
in this publish package the canonical copy is co-located with this script.)

Pass A: float64 lgamma sweep over n ∈ [100, 10^6].
Pass B: per-bad-n diagnostic records (subset of Pass A rows).
Pass C: mpmath dps=50 spot-checks at n ∈ {10^7, …, 10^12}.
Pass D: ±5 neighbourhoods around the 10 worst-margin bad windows from A,
        recomputed in mpmath dps=50.

Definitions:
    μ_k(n) = C(n,k) · 2^{−C(k,2)}              (in log domain, log μ_k)
    α(n)   = argmax_{k ≥ 1} μ_k(n) s.t. μ_k(n) ≤ 1
    x_k(n) = log μ_k(n) / log n
    x0     = 0.02905,   ε = 1e-3
    bad(n) iff x_α(n) < x0 + ε
    margin(n) = x_{α−2}(n) − 1.05

Outputs (paths are CLI-overridable; defaults below were the source-repo paths
used for the 2026-05-11 reproduction run and are preserved verbatim for
historical fidelity — override with --csv and --summary when running from a
publish-package checkout, e.g. write into the current working directory):
    proof/red-team/r2b-step1-mu-alpha-minus-2-2026-05-11.csv  (publish-relative)
    proof/red-team/r2b-step1-results-2026-05-11.md            (publish-relative)

Run (from publish/erdos-625/):
    python3 proof/red-team/r2b_step1_scan.py --csv /tmp/r2b.csv --summary /tmp/r2b.md
"""

from __future__ import annotations

import argparse
import csv
import math
import os
import sys
import time
from dataclasses import dataclass
from math import lgamma, log
from pathlib import Path
from typing import List, Tuple

try:
    import mpmath as mp
except ImportError:  # pragma: no cover
    mp = None


X0 = 0.02905
EPS = 1e-3
TARGET_EXP = 1.05  # the headline target for x_{α−2}


# ---------- log-domain μ_k for float64 ----------

def log_mu_k_f64(n: int, k: int) -> float:
    """log μ_k(n) = log C(n,k) − C(k,2) · log 2.  Natural log."""
    if k < 0 or k > n:
        return float("-inf")
    if k == 0:
        return 0.0
    log_binom = lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)
    log_pow = (k * (k - 1) / 2.0) * math.log(2.0)
    return log_binom - log_pow


def alpha_of_n_f64(n: int) -> Tuple[int, float, float, float]:
    """Return (α, log μ_α, log μ_{α−1}, log μ_{α−2}).

    α(n) = largest integer k with μ_k(n) ≥ 1 (HP-2023 §2 / Heckel 2024 §2:
    the upper 1-crossing of the unimodal sequence μ_k).  Then x_α ≥ 0 and
    x_α → x₀ ≈ 0.02905 along the crossing arithmetic progression.
    n ≤ 10^6 ⇒ α ≲ 50; we sweep upward from the mode.
    """
    # Find mode (last k with log_mu non-decreasing).
    prev = float("-inf")
    mode = 1
    for k in range(1, n + 1):
        cur = log_mu_k_f64(n, k)
        if cur < prev:
            mode = k - 1
            break
        prev = cur
    # From mode upward: largest k with log_mu ≥ 0.
    alpha = mode
    for k in range(mode, n + 1):
        if log_mu_k_f64(n, k) >= 0.0:
            alpha = k
        else:
            break
    if alpha is None or alpha < 2:
        # degenerate for tiny n; not in our scan range but guard anyway
        alpha = max(alpha or 2, 2)
    log_mu_a = log_mu_k_f64(n, alpha)
    log_mu_am1 = log_mu_k_f64(n, alpha - 1)
    log_mu_am2 = log_mu_k_f64(n, alpha - 2) if alpha >= 2 else float("-inf")
    return alpha, log_mu_a, log_mu_am1, log_mu_am2


@dataclass
class Row:
    n: int
    alpha: int
    x_alpha: float
    x_alpha_m1: float
    x_alpha_m2: float
    bad: int
    margin: float
    precision: str


def scan_pass_a(n_lo: int, n_hi: int) -> List[Row]:
    rows: List[Row] = []
    t0 = time.time()
    for n in range(n_lo, n_hi + 1):
        ln = math.log(n)
        alpha, lma, lmam1, lmam2 = alpha_of_n_f64(n)
        x_a = lma / ln
        x_am1 = lmam1 / ln
        x_am2 = lmam2 / ln
        is_bad = 1 if x_a < (X0 + EPS) else 0
        margin = x_am2 - TARGET_EXP
        rows.append(Row(n, alpha, x_a, x_am1, x_am2, is_bad, margin, "float64"))
        if n % 100000 == 0:
            elapsed = time.time() - t0
            sys.stderr.write(f"  Pass A: n={n}  elapsed={elapsed:.1f}s\n")
    return rows


# ---------- mpmath high-precision ----------

def log_mu_k_mp(n: int, k: int):
    if k <= 0:
        return mp.mpf(0)
    log_binom = mp.loggamma(n + 1) - mp.loggamma(k + 1) - mp.loggamma(n - k + 1)
    log_pow = mp.mpf(k * (k - 1)) / 2 * mp.log(2)
    return log_binom - log_pow


def alpha_of_n_mp(n: int) -> Tuple[int, "mp.mpf", "mp.mpf", "mp.mpf"]:
    # rough mode estimate: k ~ 2 log2 n
    k_est = max(2, int(2 * math.log2(max(n, 2))))
    # scan a wide window around k_est
    lo = max(1, k_est - 30)
    hi = k_est + 30
    best = None
    best_val = None
    for k in range(lo, hi + 1):
        v = log_mu_k_mp(n, k)
        if best_val is None or v > best_val:
            best_val = v
            best = k
    # largest k ≥ mode with log_mu ≥ 0
    alpha = best
    for k in range(best, best + 200):
        if log_mu_k_mp(n, k) >= 0:
            alpha = k
        else:
            break
    return alpha, log_mu_k_mp(n, alpha), log_mu_k_mp(n, alpha - 1), log_mu_k_mp(n, alpha - 2)


def pass_c_d(rows_a: List[Row]) -> List[Row]:
    """Pass C: n ∈ {10^7,…,10^12} sampled. Pass D: ±5 around 10 worst-margin bad n."""
    if mp is None:
        sys.stderr.write("mpmath not available; skipping Pass C/D.\n")
        return []
    mp.mp.dps = 50
    extra: List[Row] = []

    # Pass C
    for e in range(7, 13):
        n = 10 ** e
        alpha, lma, lmam1, lmam2 = alpha_of_n_mp(n)
        ln = mp.log(n)
        x_a = float(lma / ln)
        x_am1 = float(lmam1 / ln)
        x_am2 = float(lmam2 / ln)
        is_bad = 1 if x_a < (X0 + EPS) else 0
        extra.append(Row(n, alpha, x_a, x_am1, x_am2, is_bad, x_am2 - TARGET_EXP, "mpmath-dps50"))

    # Pass D
    bad_rows = [r for r in rows_a if r.bad]
    bad_rows.sort(key=lambda r: r.margin)  # worst (smallest) margin first
    worst = bad_rows[:10]
    seen: set = set()
    for r in worst:
        for dn in range(-5, 6):
            n = r.n + dn
            if n < 100 or n in seen:
                continue
            seen.add(n)
            alpha, lma, lmam1, lmam2 = alpha_of_n_mp(n)
            ln = mp.log(n)
            x_a = float(lma / ln)
            x_am1 = float(lmam1 / ln)
            x_am2 = float(lmam2 / ln)
            is_bad = 1 if x_a < (X0 + EPS) else 0
            extra.append(Row(n, alpha, x_a, x_am1, x_am2, is_bad, x_am2 - TARGET_EXP, "mpmath-dps50-D"))
    return extra


# ---------- output ----------

def write_csv(rows: List[Row], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "alpha", "x_alpha", "x_alpha_minus_1", "x_alpha_minus_2",
                    "bad", "margin", "precision"])
        for r in rows:
            w.writerow([r.n, r.alpha,
                        f"{r.x_alpha:.10f}", f"{r.x_alpha_m1:.10f}", f"{r.x_alpha_m2:.10f}",
                        r.bad, f"{r.margin:.10f}", r.precision])


def summarise(rows_a: List[Row], rows_cd: List[Row]) -> dict:
    bad = [r for r in rows_a if r.bad]
    all_margins = [r.margin for r in rows_a]
    bad_margins = [r.margin for r in bad]
    summary = {
        "n_scanned": len(rows_a),
        "n_bad": len(bad),
        "pct_bad": 100.0 * len(bad) / max(1, len(rows_a)),
        "min_margin_all": min(all_margins),
        "min_margin_bad": min(bad_margins) if bad_margins else float("nan"),
        "max_margin_all": max(all_margins),
    }
    # histogram of bad margins (10 buckets)
    if bad_margins:
        lo, hi = min(bad_margins), max(bad_margins)
        if hi == lo:
            hi = lo + 1e-9
        buckets = [0] * 10
        for m in bad_margins:
            idx = min(9, int(10 * (m - lo) / (hi - lo)))
            buckets[idx] += 1
        summary["bad_margin_hist"] = (lo, hi, buckets)
    # 10 worst bad n
    bad_sorted = sorted(bad, key=lambda r: r.margin)[:10]
    summary["worst_bad"] = bad_sorted
    # Pass C asymptotic check
    summary["pass_c"] = [r for r in rows_cd if r.precision == "mpmath-dps50"]
    summary["pass_d"] = [r for r in rows_cd if r.precision == "mpmath-dps50-D"]
    return summary


def verdict(summary: dict) -> str:
    m = summary["min_margin_bad"]
    if math.isnan(m):
        return "INCONCLUSIVE (no bad n found in range)"
    if m >= 0.50:
        return "GO (C1 satisfied: min bad margin ≥ 0.50)"
    if m >= 0.10:
        return "CAUTIOUS-GO (C2: min bad margin ∈ [0.10, 0.50))"
    return "NO-GO (C3: min bad margin < 0.10)"


def write_summary(summary: dict, csv_path: Path, md_path: Path, n_lo: int, n_hi: int) -> str:
    v = verdict(summary)
    lines: List[str] = []
    lines.append("# R2B Step 1 — Numerical Results")
    lines.append("")
    lines.append(f"**Date**: 2026-05-11")
    lines.append(f"**Scan range (Pass A)**: n ∈ [{n_lo}, {n_hi}], step 1, float64 (lgamma)")
    lines.append(f"**Target**: x_{{α−2}}(n) ≥ {TARGET_EXP}; bad ⇔ x_α < {X0} + {EPS} = {X0+EPS}")
    lines.append(f"**Source CSV**: `{csv_path.as_posix()}`")
    lines.append("")
    lines.append("## Headline")
    lines.append("")
    lines.append(f"- **Verdict**: **{v}**")
    lines.append(f"- n scanned (Pass A): {summary['n_scanned']:,}")
    lines.append(f"- bad n: {summary['n_bad']:,} ({summary['pct_bad']:.3f}%)")
    lines.append(f"- min margin over **bad** n: {summary['min_margin_bad']:.6f}")
    lines.append(f"- min margin over **all** n: {summary['min_margin_all']:.6f}")
    lines.append(f"- max margin over all n: {summary['max_margin_all']:.6f}")
    lines.append("")
    if "bad_margin_hist" in summary:
        lo, hi, buckets = summary["bad_margin_hist"]
        lines.append("## Histogram of margins over bad n (10 buckets)")
        lines.append("")
        lines.append(f"Range: [{lo:.6f}, {hi:.6f}]")
        lines.append("")
        for i, c in enumerate(buckets):
            a = lo + (hi - lo) * i / 10
            b = lo + (hi - lo) * (i + 1) / 10
            lines.append(f"- [{a:.4f}, {b:.4f}): {c}")
        lines.append("")
    lines.append("## 10 worst-margin bad n (float64)")
    lines.append("")
    lines.append("| n | α | x_α | x_{α−1} | x_{α−2} | margin |")
    lines.append("|---|---|---|---|---|---|")
    for r in summary["worst_bad"]:
        lines.append(f"| {r.n} | {r.alpha} | {r.x_alpha:.6f} | {r.x_alpha_m1:.6f} | {r.x_alpha_m2:.6f} | {r.margin:.6f} |")
    lines.append("")
    if summary["pass_c"]:
        lines.append("## Pass C — mpmath dps=50 spot checks (n = 10^7 … 10^12)")
        lines.append("")
        lines.append("Theoretical: x_{α−2} − x_α ≈ 2 − 2·log log n / log n (HP-2023 Lemma 6.2 ratio).")
        lines.append("")
        lines.append("| n | α | x_α | x_{α−2} | x_{α−2}−x_α | predicted 2−2·loglog/log | margin |")
        lines.append("|---|---|---|---|---|---|---|")
        for r in summary["pass_c"]:
            diff = r.x_alpha_m2 - r.x_alpha
            ln = math.log(r.n)
            pred = 2 - 2 * math.log(ln) / ln
            lines.append(f"| 10^{int(round(math.log10(r.n)))} | {r.alpha} | {r.x_alpha:.6f} | {r.x_alpha_m2:.6f} | {diff:.4f} | {pred:.4f} | {r.margin:.4f} |")
        lines.append("")
    if summary["pass_d"]:
        lines.append("## Pass D — mpmath dps=50, ±5 neighbourhoods of 10 worst-margin bad n")
        lines.append("")
        lines.append("| n | α | x_α | x_{α−2} | bad | margin |")
        lines.append("|---|---|---|---|---|---|")
        for r in sorted(summary["pass_d"], key=lambda x: x.n):
            lines.append(f"| {r.n} | {r.alpha} | {r.x_alpha:.6f} | {r.x_alpha_m2:.6f} | {r.bad} | {r.margin:.6f} |")
        lines.append("")
    lines.append("## Check criteria (from plan §6)")
    lines.append("")
    m_bad = summary["min_margin_bad"]
    lines.append(f"- **C1** (≥0.50 ⇒ GO): min bad margin = {m_bad:.4f} → {'PASS' if m_bad >= 0.5 else 'FAIL'}")
    lines.append(f"- **C2** ([0.10,0.50) ⇒ cautious GO): {'TRIGGERED' if 0.10 <= m_bad < 0.50 else 'n/a'}")
    lines.append(f"- **C3** (<0.10 ⇒ NO-GO): {'TRIGGERED' if m_bad < 0.10 else 'n/a'}")
    # C4
    if summary["pass_c"]:
        slopes = [(r.x_alpha_m2 - r.x_alpha) for r in summary["pass_c"]]
        c4 = all(2 - 0.4 <= s <= 2 + 0.05 for s in slopes if r.n >= 10**10)
        lines.append(f"- **C4** (x_{{α−2}}−x_α ∈ [1.6, 2.05] for n ≥ 10^10): slopes = {[f'{s:.3f}' for s in slopes]} → {'PASS' if c4 else 'CHECK'}")
    pct = summary["pct_bad"]
    lines.append(f"- **C5** (bad density at 10^6 ≈ 3.5% ± 0.5%): observed {pct:.3f}% → {'PASS' if 3.0 <= pct <= 4.0 else 'CHECK'}")
    if summary["pass_d"]:
        # check reproducibility: any Pass-D row that overlaps a Pass-A row must match within 3 sig figs
        lines.append(f"- **C6** (mpmath agrees with float64 to 3 sig figs near worst-margin n): see Pass D table; agreement to ≥4 decimals across all rows expected (visual check).")
    lines.append("")
    lines.append("## Verdict")
    lines.append("")
    lines.append(f"**{v}**")
    lines.append("")
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines))
    return v


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-lo", type=int, default=100)
    ap.add_argument("--n-hi", type=int, default=1_000_000)
    ap.add_argument("--csv", type=Path,
                    default=Path("r2b-step1-mu-alpha-minus-2-2026-05-11.csv"))
    ap.add_argument("--md", type=Path,
                    default=Path("r2b-step1-results-2026-05-11.md"))
    ap.add_argument("--skip-cd", action="store_true")
    args = ap.parse_args()

    sys.stderr.write(f"Pass A: scanning n ∈ [{args.n_lo}, {args.n_hi}] ...\n")
    rows_a = scan_pass_a(args.n_lo, args.n_hi)
    sys.stderr.write(f"Pass A done: {len(rows_a)} rows; bad = {sum(r.bad for r in rows_a)}\n")

    rows_cd: List[Row] = []
    if not args.skip_cd:
        sys.stderr.write("Pass C/D: mpmath dps=50 ...\n")
        rows_cd = pass_c_d(rows_a)
        sys.stderr.write(f"Pass C/D done: {len(rows_cd)} rows\n")

    write_csv(rows_a + rows_cd, args.csv)
    summary = summarise(rows_a, rows_cd)
    v = write_summary(summary, args.csv, args.md, args.n_lo, args.n_hi)
    print(f"Verdict: {v}")
    print(f"CSV: {args.csv}")
    print(f"MD:  {args.md}")


if __name__ == "__main__":
    main()
