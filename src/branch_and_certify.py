#!/usr/bin/env python3
"""Exact rational n-way best-first B&B optimizer and Farkas/dual certificate generator (v4).

Combines greedy/periodic DFS primal diving, lazy single-block Hua cutting planes,
exact best-first branch-and-bound with immediate heap purging on incumbent
improvements, and O(depth)-RAM exact rational dual/Farkas proof-tree construction.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import heapq
import json
import math
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Optional, Sequence, Tuple

from exact_simplex import BareissTableau, build_initial_tableau, sparse_weights
from model_grouped import GroupedModel, ModelConfig


NEG_INF = Fraction(-10**9)


def build_root_tableau(model: GroupedModel) -> Tuple[BareissTableau, int]:
    """Build exact root tableau with canonical base rows followed by any exact shell cuts."""
    root, obj_scale, status = build_initial_tableau(
        model.nvar, model.base_rows, model.objective
    )
    if status != "optimal":
        raise RuntimeError(f"Root LP status: {status}")
    for vec, rhs, name in model.shell_rows:
        st = root.add_frac_cut_and_resolve(vec, rhs, name)
        if st != "optimal":
            raise RuntimeError(f"Root shell cut {name} failed with status: {st}")
    return root, obj_scale


def _choose_split(
    model: GroupedModel,
    node: BareissTableau,
    obj_scale: int,
    cands: List[Tuple[Fraction, Dict[str, Any]]],
    strong_k: int,
    cutoff: Optional[Fraction] = None,
) -> Tuple[Dict[str, Any], List[Tuple[str, Optional[Fraction], BareissTableau]]]:
    """Evaluate up to strong_k top violated n-way disjunctions via exact dual simplex."""
    parent_val = Fraction(node.tab[-1][-1], node.det * obj_scale)
    eps = Fraction(1, 100000)

    best_key: Optional[Tuple[int, int, Fraction, Fraction, Fraction]] = None
    best_sp: Optional[Dict[str, Any]] = None
    best_children: Optional[List[Tuple[str, Optional[Fraction], BareissTableau]]] = None

    limit = max(1, min(strong_k, len(cands)))
    for _, sp in cands[:limit]:
        cuts = model.split_branches_int(sp)
        children: List[Tuple[str, Optional[Fraction], BareissTableau]] = []
        vals: List[Fraction] = []
        pruned_all = True
        for cut in cuts:
            child = node.clone()
            st = child.add_int_cut_and_resolve(*cut)
            if st == "infeasible":
                children.append((st, None, child))
                vals.append(NEG_INF)
            elif st == "optimal":
                c_val = Fraction(child.tab[-1][-1], child.det * obj_scale)
                children.append((st, c_val, child))
                vals.append(c_val)
                if cutoff is None or c_val > cutoff:
                    pruned_all = False
            else:
                raise RuntimeError(f"Unexpected dual simplex status: {st}")

        open_cnt = 0 if cutoff is None else sum(1 for v in vals if v > cutoff)
        drops = [
            parent_val - (cutoff if v == NEG_INF and cutoff is not None else max(v, Fraction(0)))
            for v in vals
        ]
        hi = max(vals)
        lo = min(vals)
        avg_d = sum(d if d > eps else eps for d in drops) / len(drops)
        min_d = min(d if d > eps else eps for d in drops)
        score = min_d * avg_d
        key = (open_cnt, len(vals), -score, hi, lo)
        if best_key is None or key < best_key:
            best_key = key
            best_sp = sp
            best_children = children
        if cutoff is not None and pruned_all:
            break

    assert best_sp is not None and best_children is not None
    return best_sp, best_children


def _dive_for_witness(
    model: GroupedModel,
    tab: BareissTableau,
    obj_scale: int,
    cutoff: Fraction,
    max_steps: int = 80,
) -> Tuple[Fraction, Optional[List[Fraction]]]:
    """Fast single-path dive (highest-valued child first) to discover a strong feasible witness."""
    cur = tab.clone()
    for _ in range(max_steps):
        st = model.tighten_lazy_hua(cur)
        if st != "optimal":
            return NEG_INF, None
        val = Fraction(cur.tab[-1][-1], cur.det * obj_scale)
        if val <= cutoff:
            return NEG_INF, None
        nums = cur.primal_numerators()
        cands = model.find_top_violated_splits(nums, cur.det)
        if not cands:
            _, x, _ = cur.extract_exact_primal_dual(obj_scale)
            return val, x
        sp = cands[0][1]
        best_child = None
        best_v = NEG_INF
        for cut in model.split_branches_int(sp):
            ch = cur.clone()
            stc = ch.add_int_cut_and_resolve(*cut)
            if stc == "optimal":
                stc = model.tighten_lazy_hua(ch)
            if stc == "optimal":
                vc = Fraction(ch.tab[-1][-1], ch.det * obj_scale)
                if vc > cutoff and vc > best_v:
                    best_v = vc
                    best_child = ch
        if best_child is None:
            return NEG_INF, None
        cur = best_child
    return NEG_INF, None


def canonicalize_primal(model: GroupedModel, x: Sequence[Fraction]) -> List[Fraction]:
    """Tighten F_n to exact canonical lower bounds and clear superfluous W_n slack when n_r == 0."""
    x_clean = list(x)
    f_canon = model.canonical_f_values(x_clean)
    for n in range(3):
        x_clean[model.F[n]] = f_canon[n]

    def is_feasible(cand: Sequence[Fraction]) -> bool:
        for coeffs, rhs, _ in model.all_base_rows:
            if sum(c * v for c, v in zip(coeffs, cand)) > rhs:
                return False
        den = 1
        for v in cand:
            den = math.lcm(den, v.denominator)
        nums = [int(v * den) for v in cand]
        hua_sp, _ = model.find_most_violated_hua(nums, den)
        if hua_sp is not None:
            return False
        if model.find_top_violated_splits(nums, den):
            return False
        return True

    for l_idx in range(3):
        ri, wi = model.rem(l_idx), model.W[l_idx]
        if x_clean[ri] == 0 and x_clean[wi] != 0:
            cand = list(x_clean)
            cand[wi] = Fraction(0)
            if is_feasible(cand):
                x_clean = cand

    return x_clean


def solve_exact_optimum(
    model: GroupedModel,
    max_nodes: int = 45000,
    strong_k: int = 2,
    max_heap: int = 2500,
    dive_every: int = 400,
    verbose: bool = False,
) -> Tuple[Fraction, List[Fraction], Dict[str, int]]:
    """Find the exact global optimum U* and a canonical feasible primal witness x* via best-first B&B."""
    root, obj_scale = build_root_tableau(model)
    st_h = model.tighten_lazy_hua(root)
    if st_h != "optimal":
        raise RuntimeError(f"Root Hua tightening status: {st_h}")

    best_lb, best_x = _dive_for_witness(model, root, obj_scale, NEG_INF)
    if verbose and best_x is not None:
        print(f"  [seed] D={best_lb} ({float(best_lb):.6f})", flush=True)

    stats: Dict[str, int] = {
        "nodes_expanded": 0,
        "infeasible_pruned": 0,
        "bound_pruned": 0,
        "max_depth": 0,
    }

    root_val = Fraction(root.tab[-1][-1], root.det * obj_scale)
    counter = 0
    heap: List[Tuple[Fraction, int, int, BareissTableau]] = [(-root_val, counter, 0, root)]
    t0 = time.perf_counter()

    while heap:
        neg_val, _, depth, tab = heapq.heappop(heap)
        val = -neg_val
        if val <= best_lb:
            stats["bound_pruned"] += 1
            continue

        stats["nodes_expanded"] += 1
        if depth > stats["max_depth"]:
            stats["max_depth"] = depth
        if stats["nodes_expanded"] > max_nodes:
            raise RuntimeError(
                f"Exceeded max_nodes={max_nodes}; gap [{best_lb} ({float(best_lb):.6f}), {val} ({float(val):.6f})]"
            )

        nums = tab.primal_numerators()
        cands = model.find_top_violated_splits(nums, tab.det)
        if not cands:
            ex_val, ex_x, _ = tab.extract_exact_primal_dual(obj_scale)
            if ex_val > best_lb:
                best_lb = ex_val
                best_x = ex_x
                heap = [item for item in heap if -item[0] > best_lb]
                heapq.heapify(heap)
                if verbose:
                    print(
                        f"  [feasible] node={stats['nodes_expanded']} depth={depth} "
                        f"D={ex_val} ({float(ex_val):.6f}) heap={len(heap)}",
                        flush=True,
                    )
            continue

        if dive_every > 0 and stats["nodes_expanded"] % dive_every == 0:
            dv, dx = _dive_for_witness(model, tab, obj_scale, best_lb)
            if dx is not None and dv > best_lb:
                best_lb = dv
                best_x = dx
                heap = [item for item in heap if -item[0] > best_lb]
                heapq.heapify(heap)
                if verbose:
                    print(
                        f"  [dive] node={stats['nodes_expanded']} NEW LB D={best_lb} "
                        f"({float(best_lb):.6f}) heap={len(heap)}",
                        flush=True,
                    )
                if val <= best_lb:
                    continue

        if verbose and stats["nodes_expanded"] % 1000 == 0:
            dt = time.perf_counter() - t0
            print(
                f"  [prog] node={stats['nodes_expanded']} heap={len(heap)} depth={depth} "
                f"ub={float(val):.6f} lb={float(best_lb):.6f} ({dt:.1f}s)",
                flush=True,
            )

        k_here = strong_k if len(heap) < max_heap else 1
        sp, children = _choose_split(model, tab, obj_scale, cands, strong_k=k_here, cutoff=best_lb)
        st_key = f"splits_{sp['type']}"
        stats[st_key] = stats.get(st_key, 0) + 1
        for st, c_val, child in children:
            if st == "infeasible":
                stats["infeasible_pruned"] += 1
            elif c_val is not None:
                if c_val <= best_lb:
                    stats["bound_pruned"] += 1
                else:
                    st_ch = model.tighten_lazy_hua(child)
                    if st_ch == "infeasible":
                        stats["infeasible_pruned"] += 1
                    elif st_ch == "optimal":
                        c_val2 = Fraction(child.tab[-1][-1], child.det * obj_scale)
                        if c_val2 <= best_lb:
                            stats["bound_pruned"] += 1
                        else:
                            counter += 1
                            heapq.heappush(heap, (-c_val2, counter, depth + 1, child))
                    else:
                        raise RuntimeError(f"Unexpected Hua status: {st_ch}")

    if best_x is None:
        raise RuntimeError("No feasible point found!")
    return best_lb, canonicalize_primal(model, best_x), stats


def build_certificate_tree(
    model: GroupedModel,
    target: Fraction,
    max_nodes: int = 80000,
    strong_k: int = 2,
    strong_max_depth: int = 10,
    verbose: bool = False,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """Build an exact rational dual/Farkas proof tree proving D <= target using O(depth) RAM."""
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 4000))
    root, obj_scale = build_root_tableau(model)

    stats: Dict[str, Any] = {
        "branches": 0,
        "hua_cuts": 0,
        "dual_leaves": 0,
        "farkas_leaves": 0,
        "max_depth": 0,
        "split_types": {},
    }
    t0 = time.perf_counter()

    def visit(node: BareissTableau, depth: int) -> Dict[str, Any]:
        if depth > stats["max_depth"]:
            stats["max_depth"] = depth

        val = Fraction(node.tab[-1][-1], node.det * obj_scale)
        if val <= target:
            _, _, dual = node.extract_exact_primal_dual(obj_scale)
            stats["dual_leaves"] += 1
            return {"dual": sparse_weights(dual)}

        nums = node.primal_numerators()

        # 1. Apply any violated single-block Hua inequality as an explicit 1-child cut node
        hua_sp, hua_cut = model.find_most_violated_hua(nums, node.det)
        if hua_sp is not None and hua_cut is not None:
            stats["hua_cuts"] += 1
            stats["split_types"]["hua"] = stats["split_types"].get("hua", 0) + 1
            st_h = node.add_int_cut_and_resolve(*hua_cut)
            if st_h == "infeasible":
                stats["farkas_leaves"] += 1
                child_node: Dict[str, Any] = {
                    "farkas": sparse_weights(node.extract_farkas_certificate())
                }
            elif st_h == "optimal":
                child_node = visit(node, depth + 1)
            else:
                raise RuntimeError(f"Unexpected dual simplex status on Hua cut: {st_h}")
            return {"split": hua_sp, "children": [child_node]}

        # 2. Separate disjunctions
        if stats["branches"] >= max_nodes:
            raise RuntimeError(
                f"Certificate tree exceeded max_nodes={max_nodes} at depth={depth}, val={val}"
            )

        cands = model.find_top_violated_splits(nums, node.det)
        if not cands:
            raise RuntimeError(
                f"Target {target} is strictly below a feasible point! "
                f"Found feasible D={val} ({float(val):.6f})"
            )

        k_here = strong_k if depth <= strong_max_depth else 1
        sp, children_res = _choose_split(
            model, node, obj_scale, cands, strong_k=k_here, cutoff=target
        )

        stats["branches"] += 1
        sp_type = sp["type"]
        stats["split_types"][sp_type] = stats["split_types"].get(sp_type, 0) + 1
        if verbose and stats["branches"] % 2000 == 0:
            dt = time.perf_counter() - t0
            print(
                f"  [cert] branches={stats['branches']} hua={stats['hua_cuts']} "
                f"leaves={stats['dual_leaves'] + stats['farkas_leaves']} depth={depth} ({dt:.1f}s)",
                flush=True,
            )

        children_nodes: List[Dict[str, Any]] = []
        for st, _, child in children_res:
            if st == "infeasible":
                stats["farkas_leaves"] += 1
                children_nodes.append(
                    {"farkas": sparse_weights(child.extract_farkas_certificate())}
                )
            elif st == "optimal":
                children_nodes.append(visit(child, depth + 1))
            else:
                raise RuntimeError(f"Unexpected dual simplex status: {st}")
        return {"split": sp, "children": children_nodes}

    tree = visit(root, 0)
    return tree, stats


def generate_certificate(
    cfg: ModelConfig,
    target_override: Optional[Fraction] = None,
    max_nodes: int = 60000,
    strong_k_solve: int = 2,
    strong_k_cert: int = 2,
    strong_max_depth: int = 10,
    verbose: bool = True,
) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    """Solve for exact optimum (or prove target_override) and assemble JSON certificate."""
    t0 = time.perf_counter()
    model = GroupedModel(cfg)
    primal_dict: Optional[Dict[str, str]] = None

    if target_override is None:
        opt_val, opt_x, solve_stats = solve_exact_optimum(
            model, max_nodes=max_nodes, strong_k=strong_k_solve, verbose=verbose
        )
        target = opt_val
        primal_dict = {
            name: str(val) for name, val in zip(model.names, opt_x) if val != 0
        }
    else:
        target = target_override
        solve_stats = {}

    t1 = time.perf_counter()
    tree, cert_stats = build_certificate_tree(
        model,
        target,
        max_nodes=max_nodes,
        strong_k=strong_k_cert,
        strong_max_depth=strong_max_depth,
        verbose=verbose,
    )
    t2 = time.perf_counter()

    certificate: Dict[str, Any] = {
        "schema": "abc-exceptional-frontier-v4",
        "config": cfg.to_metadata(),
        "variables": model.names,
        "base_row_count": len(model.all_base_rows),
        "bound": str(target),
        "tree": tree,
    }
    if primal_dict is not None:
        certificate["primal"] = primal_dict

    summary = {
        "bound": str(target),
        "bound_float": round(float(target), 8),
        "solve_sec": round(t1 - t0, 3),
        "cert_sec": round(t2 - t1, 3),
        "solve_stats": solve_stats,
        "cert_stats": cert_stats,
    }
    return certificate, summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--d0", type=int, default=6)
    parser.add_argument("--alpha", type=Fraction, default=Fraction(1))
    parser.add_argument("--lam", type=Fraction, default=Fraction(1))
    parser.add_argument("--tier", choices=("elem", "full"), default="full")
    parser.add_argument("--symmetry", choices=("none", "bc", "abc"), default="abc")
    parser.add_argument("--exact-bc-shell", action="store_true")
    parser.add_argument("--target", type=Fraction, default=None)
    parser.add_argument("--max-nodes", type=int, default=60000)
    parser.add_argument("--strong-k", type=int, default=2)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    if args.tier == "elem":
        cfg = ModelConfig.elem(
            args.alpha, args.lam, args.symmetry, d0=args.d0, exact_bc_shell=args.exact_bc_shell
        )
    else:
        cfg = ModelConfig.full(
            args.alpha, args.lam, args.symmetry, d0=args.d0, exact_bc_shell=args.exact_bc_shell
        )
    cert, summary = generate_certificate(
        cfg,
        target_override=args.target,
        max_nodes=args.max_nodes,
        strong_k_solve=args.strong_k,
        strong_k_cert=args.strong_k,
        verbose=True,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(cert, separators=(",", ":")) + "\n")
        print(f"Wrote certificate to {args.output}")


if __name__ == "__main__":
    main()
