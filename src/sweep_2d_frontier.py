#!/usr/bin/env python3
"""Generate the v4 Two-Tier (Elementary + Full cbp1/SalbF) exact rational certificate suite.

Usage:
    python3 src/sweep_2d_frontier.py elemA     # Tier 1: unrestricted (1,1)=9/16 + imbalanced alpha in [0, 1/2]
    python3 src/sweep_2d_frontier.py elemB     # Tier 1: imbalanced alpha in {5/9, 2/3, 3/4, 4/5, 9/10}
    python3 src/sweep_2d_frontier.py elemC1    # Tier 1: sub-critical lam in {1/2, 3/5, 7/10, 4/5} at alpha=1
    python3 src/sweep_2d_frontier.py elemC2    # Tier 1: sub-critical lam in {9/10, 19/20} + alpha=1/2, lam in {4/5, 9/10}
    python3 src/sweep_2d_frontier.py fullA     # Tier 2: unrestricted (1,1)=4224/7637
    python3 src/sweep_2d_frontier.py fullB     # Tier 2: imbalanced alpha in {1/2, 5/9, 2/3, 3/4, 4/5, 9/10}
    python3 src/sweep_2d_frontier.py fullC1    # Tier 2: sub-critical lam in {7/10, 4/5} at alpha=1
    python3 src/sweep_2d_frontier.py fullC2    # Tier 2: sub-critical lam in {9/10, 19/20} + alpha=1/2, lam in {4/5, 9/10}
    python3 src/sweep_2d_frontier.py manifest  # Rebuild MANIFEST.sha256 and results/frontier_summary_v4.json
"""

from __future__ import annotations

from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, List

from branch_and_certify import build_certificate_tree, solve_exact_optimum
from model_grouped import GroupedModel, ModelConfig


REPO_ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = REPO_ROOT / "certificates"
RES_DIR = REPO_ROOT / "results"


def blt_thm12(lam: Q) -> Q:
    return (23 * lam + 3) / 40


def run_one(
    label: str,
    filename: str,
    cfg: ModelConfig,
    compute_blt_lp: bool = True,
    max_nodes: int = 55000,
    strong_k_solve: int = 2,
    strong_k_cert: int = 2,
    strong_max_depth: int = 10,
) -> Dict[str, Any]:
    t0 = time.perf_counter()
    model = GroupedModel(cfg)
    val, x_clean, _ = solve_exact_optimum(
        model, max_nodes=max_nodes, strong_k=strong_k_solve, verbose=False
    )
    t1 = time.perf_counter()
    tree, cstats = build_certificate_tree(
        model,
        val,
        max_nodes=max_nodes * 2,
        strong_k=strong_k_cert,
        strong_max_depth=strong_max_depth,
        verbose=False,
    )
    t2 = time.perf_counter()

    primal = {nm: str(v) for nm, v in zip(model.names, x_clean) if v != 0}
    cert = {
        "schema": "abc-exceptional-frontier-v4",
        "config": cfg.to_metadata(),
        "variables": model.names,
        "base_row_count": len(model.all_base_rows),
        "bound": str(val),
        "primal": primal,
        "tree": tree,
    }
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    (CERT_DIR / filename).write_text(json.dumps(cert, separators=(",", ":")) + "\n")

    blt_val = None
    if compute_blt_lp:
        bm = GroupedModel(ModelConfig.blt(cfg.alpha, cfg.lam, cfg.symmetry, d0=cfg.d0))
        blt_val, _, _ = solve_exact_optimum(bm, max_nodes=12000, strong_k=1, dive_every=0, verbose=False)

    rec = {
        "label": label,
        "file": filename,
        "d0": cfg.d0,
        "tier": cfg.tier,
        "alpha": str(cfg.alpha),
        "lam": str(cfg.lam),
        "symmetry": cfg.symmetry,
        "exact_bc_shell": cfg.exact_bc_shell,
        "our_bound": str(val),
        "our_float": round(float(val), 6),
        "blt_lp": str(blt_val) if blt_val is not None else None,
        "blt_lp_float": round(float(blt_val), 6) if blt_val is not None else None,
        "blt_thm12": str(blt_thm12(cfg.lam)),
        "blt_thm12_float": round(float(blt_thm12(cfg.lam)), 6),
        "gain_vs_blt_lp": str(blt_val - val) if blt_val is not None else None,
        "branches": cstats["branches"],
        "hua_cuts": cstats["hua_cuts"],
        "dual_leaves": cstats["dual_leaves"],
        "farkas_leaves": cstats["farkas_leaves"],
        "max_depth": cstats["max_depth"],
        "split_types": cstats["split_types"],
        "primal": primal,
        "solve_sec": round(t1 - t0, 2),
        "cert_sec": round(t2 - t1, 2),
    }
    print(
        f"{label:38s} | {str(val):13s} ({float(val):.6f}) | "
        f"br={cstats['branches']:5d} hua={cstats['hua_cuts']:3d} d={cstats['max_depth']:2d} | "
        f"{t2 - t0:6.2f}s",
        flush=True,
    )
    return rec


def save_batch_summary(batch_name: str, rows: List[Dict[str, Any]]) -> None:
    RES_DIR.mkdir(parents=True, exist_ok=True)
    (RES_DIR / f"summary_v4_{batch_name}.json").write_text(json.dumps(rows, indent=2) + "\n")


BATCH_ORDER = ("elemA", "elemB", "elemC1", "elemC2", "fullA", "fullB")


def write_manifest_and_merge() -> None:
    lines: List[str] = []
    for path in sorted(CERT_DIR.glob("*.json")):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {path.name}")
    (CERT_DIR / "MANIFEST.sha256").write_text("\n".join(lines) + "\n")

    merged: List[Dict[str, Any]] = []
    for name in BATCH_ORDER:
        p = RES_DIR / f"summary_v4_{name}.json"
        if p.exists():
            merged.extend(json.loads(p.read_text()))
    (RES_DIR / "frontier_summary_v4.json").write_text(json.dumps(merged, indent=2) + "\n")
    print(
        f"Updated MANIFEST.sha256 ({len(lines)} certificates) and "
        f"results/frontier_summary_v4.json ({len(merged)} rows)."
    )


def run_batch(cmd: str) -> None:
    if cmd == "elemA":
        rows = [
            run_one(
                "ELEM a=1 lam=1 d0=6",
                "elem_unres_alpha1_lam1.json",
                ModelConfig.elem(Q(1), Q(1), "abc", d0=6, exact_bc_shell=False),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=0 lam=1 d0=6",
                "elem_imbal_alpha_0_lam1.json",
                ModelConfig.elem(Q(0), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=1/3 lam=1 d0=6",
                "elem_imbal_alpha_1_3_lam1.json",
                ModelConfig.elem(Q(1, 3), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=2/5 lam=1 d0=6",
                "elem_imbal_alpha_2_5_lam1.json",
                ModelConfig.elem(Q(2, 5), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=4/9 lam=1 d0=6",
                "elem_imbal_alpha_4_9_lam1.json",
                ModelConfig.elem(Q(4, 9), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=15/32 lam=1 d0=6",
                "elem_imbal_alpha_15_32_lam1.json",
                ModelConfig.elem(Q(15, 32), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=97/206 lam=1 d0=6",
                "elem_imbal_alpha_97_206_lam1.json",
                ModelConfig.elem(Q(97, 206), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
            run_one(
                "ELEM a=1/2 lam=1 d0=6",
                "elem_imbal_alpha_1_2_lam1.json",
                ModelConfig.elem(Q(1, 2), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
        ]
        save_batch_summary("elemA", rows)

    elif cmd == "elemB":
        rows = []
        for alpha, slug in (
            (Q(5, 9), "5_9"),
            (Q(2, 3), "2_3"),
            (Q(3, 4), "3_4"),
            (Q(4, 5), "4_5"),
            (Q(9, 10), "9_10"),
        ):
            rows.append(
                run_one(
                    f"ELEM a={alpha} lam=1 d0=6",
                    f"elem_imbal_alpha_{slug}_lam1.json",
                    ModelConfig.elem(alpha, Q(1), "bc", d0=6, exact_bc_shell=True),
                    compute_blt_lp=False,
                )
            )
        save_batch_summary("elemB", rows)

    elif cmd == "elemC1":
        rows = []
        for lam, slug in (
            (Q(1, 2), "1_2"),
            (Q(3, 5), "3_5"),
            (Q(7, 10), "7_10"),
            (Q(4, 5), "4_5"),
        ):
            rows.append(
                run_one(
                    f"ELEM a=1 lam={lam} d0=6",
                    f"elem_unres_alpha1_lam_{slug}.json",
                    ModelConfig.elem(Q(1), lam, "abc", d0=6, exact_bc_shell=False),
                    compute_blt_lp=False,
                )
            )
        save_batch_summary("elemC1", rows)

    elif cmd == "elemC2":
        rows = []
        for lam, slug in ((Q(9, 10), "9_10"), (Q(19, 20), "19_20")):
            rows.append(
                run_one(
                    f"ELEM a=1 lam={lam} d0=6",
                    f"elem_unres_alpha1_lam_{slug}.json",
                    ModelConfig.elem(Q(1), lam, "abc", d0=6, exact_bc_shell=False),
                    compute_blt_lp=False,
                )
            )
        for lam, slug in ((Q(4, 5), "4_5"), (Q(9, 10), "9_10")):
            rows.append(
                run_one(
                    f"ELEM a=1/2 lam={lam} d0=6",
                    f"elem_imbal_alpha_1_2_lam_{slug}.json",
                    ModelConfig.elem(Q(1, 2), lam, "bc", d0=6, exact_bc_shell=True),
                    compute_blt_lp=False,
                )
            )
        save_batch_summary("elemC2", rows)

    elif cmd == "fullA":
        rows = [
            run_one(
                "FULL a=1 lam=1 d0=6",
                "full_unres_alpha1_lam1.json",
                ModelConfig.full(Q(1), Q(1), "abc", d0=6, exact_bc_shell=False),
                compute_blt_lp=False,
            ),
        ]
        save_batch_summary("fullA", rows)

    elif cmd == "fullB":
        # Tier 2 strict-improvement frontier over Tier 1 elementary:
        # (All alpha <= 4/5 at lam=1 and all lam <= 19/20 at alpha=1 already match Tier 1!)
        rows = [
            run_one(
                "FULL a=9/10 lam=1 d0=6",
                "full_imbal_alpha_9_10_lam1.json",
                ModelConfig.full(Q(9, 10), Q(1), "bc", d0=6, exact_bc_shell=True),
                compute_blt_lp=False,
            ),
        ]
        # Check if Tier 2 strictly improves (1/2, 4/5) or (1/2, 9/10) over Tier 1; save only if strictly sharper
        elem_c2 = {r["file"]: Q(r["our_bound"]) for r in json.loads((RES_DIR / "summary_v4_elemC2.json").read_text())}
        for lam, slug in ((Q(4, 5), "4_5"), (Q(9, 10), "9_10")):
            cfg = ModelConfig.full(Q(1, 2), lam, "bc", d0=6, exact_bc_shell=True)
            v_test, _, _ = solve_exact_optimum(GroupedModel(cfg), max_nodes=35000, strong_k=2, verbose=False)
            elem_v = elem_c2[f"elem_imbal_alpha_1_2_lam_{slug}.json"]
            if v_test < elem_v:
                rows.append(
                    run_one(
                        f"FULL a=1/2 lam={lam} d0=6",
                        f"full_imbal_alpha_1_2_lam_{slug}.json",
                        cfg,
                        compute_blt_lp=False,
                    )
                )
            else:
                print(f"FULL a=1/2 lam={lam} matches ELEM ({v_test} == {elem_v}); no redundant cert needed.", flush=True)
        save_batch_summary("fullB", rows)

    elif cmd == "fullC1":
        rows = []
        for lam, slug in ((Q(7, 10), "7_10"), (Q(4, 5), "4_5")):
            rows.append(
                run_one(
                    f"FULL a=1 lam={lam} d0=6",
                    f"full_unres_alpha1_lam_{slug}.json",
                    ModelConfig.full(Q(1), lam, "abc", d0=6, exact_bc_shell=False),
                    compute_blt_lp=False,
                )
            )
        save_batch_summary("fullC1", rows)

    elif cmd == "fullC2":
        rows = []
        for lam, slug in ((Q(9, 10), "9_10"), (Q(19, 20), "19_20")):
            rows.append(
                run_one(
                    f"FULL a=1 lam={lam} d0=6",
                    f"full_unres_alpha1_lam_{slug}.json",
                    ModelConfig.full(Q(1), lam, "abc", d0=6, exact_bc_shell=False),
                    compute_blt_lp=False,
                )
            )
        for lam, slug in ((Q(4, 5), "4_5"), (Q(9, 10), "9_10")):
            rows.append(
                run_one(
                    f"FULL a=1/2 lam={lam} d0=6",
                    f"full_imbal_alpha_1_2_lam_{slug}.json",
                    ModelConfig.full(Q(1, 2), lam, "bc", d0=6, exact_bc_shell=True),
                    compute_blt_lp=False,
                )
            )
        save_batch_summary("fullC2", rows)

    elif cmd == "manifest":
        write_manifest_and_merge()
    else:
        raise ValueError(f"Unknown command: {cmd}")


def main() -> None:
    if len(sys.argv) < 2:
        print(f"Specify one or more of {BATCH_ORDER} or 'manifest'")
        sys.exit(2)
    for cmd in sys.argv[1:]:
        run_batch(cmd)


if __name__ == "__main__":
    main()
