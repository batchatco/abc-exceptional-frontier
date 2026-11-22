#!/usr/bin/env python3
"""Independent zero-trust rational verifier for abc-exceptional-frontier v4 certificates.

Uses ONLY the Python 3 standard library (argparse, copy, fractions, hashlib,
itertools, json, math, pathlib, sys, typing). Imports ZERO solver, simplex, or
model-generation code, and performs ZERO floating-point arithmetic anywhere in
the verification path.

Strictly enforces two-tier separation:
  - Tier 1 (`tier == "elem"`): purely elementary rules only (`L442`, `GoN`, `stCL`,
    `coll_p`, `diffcl`, `qcoll`, `st_qcoll`, `modcoll`, `modcoll3` with `h1 == 1`,
    single-block `hua`, `cop_elem`, and optional `exact_bc_shell`). Strictly rejects
    `cbp1` and `salb_f` flags or splits.
  - Tier 2 (`tier == "full"`): Tier 1 plus 7-/5-branch `cbp1` (1D Salberger Thm. 1.2)
    and 4-branch `salb_f` (Salberger 2023 Cor. 6.5 / Thm. 3.16 for d in {4, 5, 6}).
"""

from __future__ import annotations

import argparse
import copy
from fractions import Fraction as Q
import hashlib
from itertools import combinations, product
import json
import math
from pathlib import Path
import sys
from typing import Any, Dict, List, Optional, Sequence, Tuple


LETTERS = ("a", "b", "c")

# Exact independently-verified rational constants for Salberger (2023) Cor. 6.5 / Thm. 3.16
# on F_i (d in {4, 5, 6}):
#   c1 >= 3/sqrt(d), c2 <= 1/(d*sqrt(d)),
#   c3 >= 3/(2*sqrt(d)) + 2/(d-1), c4 <= 1/(2*d*sqrt(d)).
SALB_F_PARAMS: Dict[int, Tuple[Q, Q, Q, Q]] = {
    4: (Q(3, 2), Q(1, 8), Q(17, 12), Q(1, 16)),
    5: (Q(161, 120), Q(4, 45), Q(281, 240), Q(2, 45)),
    6: (Q(49, 40), Q(1, 15), Q(81, 80), Q(1, 30)),
}

for _d, (_c1, _c2, _c3, _c4) in SALB_F_PARAMS.items():
    assert _d * (_c1 ** 2) >= 9
    assert (_d ** 3) * (_c2 ** 2) <= 1
    _r3 = _c3 - Q(2, _d - 1)
    assert _r3 > 0 and 4 * _d * (_r3 ** 2) >= 9
    assert 4 * (_d ** 3) * (_c4 ** 2) <= 1

# Pinned theorem registry binding every shipped v4 certificate in certificates/
# to its exact configuration and certified rational bound.
# Tuple format: (d0, tier, alpha, lam, symmetry, exact_bc_shell, bound)
EXPECTED_SUITE: Dict[str, Tuple[int, str, str, str, str, bool, str]] = {
    # Tier 1: Purely elementary (zero Bombieri-Pila, zero Salberger)
    "elem_unres_alpha1_lam1.json": (6, "elem", "1", "1", "abc", False, "9/16"),
    "elem_imbal_alpha_0_lam1.json": (6, "elem", "0", "1", "bc", True, "1/2"),
    "elem_imbal_alpha_1_3_lam1.json": (6, "elem", "1/3", "1", "bc", True, "1/2"),
    "elem_imbal_alpha_2_5_lam1.json": (6, "elem", "2/5", "1", "bc", True, "1/2"),
    "elem_imbal_alpha_4_9_lam1.json": (6, "elem", "4/9", "1", "bc", True, "1/2"),
    "elem_imbal_alpha_15_32_lam1.json": (6, "elem", "15/32", "1", "bc", True, "1/2"),
    "elem_imbal_alpha_97_206_lam1.json": (6, "elem", "97/206", "1", "bc", True, "1/2"),
    "elem_imbal_alpha_1_2_lam1.json": (6, "elem", "1/2", "1", "bc", True, "263/522"),
    "elem_imbal_alpha_5_9_lam1.json": (6, "elem", "5/9", "1", "bc", True, "23/45"),
    "elem_imbal_alpha_2_3_lam1.json": (6, "elem", "2/3", "1", "bc", True, "34/63"),
    "elem_imbal_alpha_3_4_lam1.json": (6, "elem", "3/4", "1", "bc", True, "137/251"),
    "elem_imbal_alpha_4_5_lam1.json": (6, "elem", "4/5", "1", "bc", True, "686/1255"),
    "elem_imbal_alpha_9_10_lam1.json": (6, "elem", "9/10", "1", "bc", True, "213/380"),
    "elem_unres_alpha1_lam_1_2.json": (6, "elem", "1", "1/2", "abc", False, "1/3"),
    "elem_unres_alpha1_lam_3_5.json": (6, "elem", "1", "3/5", "abc", False, "2/5"),
    "elem_unres_alpha1_lam_7_10.json": (6, "elem", "1", "7/10", "abc", False, "29/70"),
    "elem_unres_alpha1_lam_4_5.json": (6, "elem", "1", "4/5", "abc", False, "7/15"),
    "elem_unres_alpha1_lam_9_10.json": (6, "elem", "1", "9/10", "abc", False, "119/235"),
    "elem_unres_alpha1_lam_19_20.json": (6, "elem", "1", "19/20", "abc", False, "19/35"),
    "elem_imbal_alpha_1_2_lam_4_5.json": (6, "elem", "1/2", "4/5", "bc", True, "1759/4250"),
    "elem_imbal_alpha_1_2_lam_9_10.json": (6, "elem", "1/2", "9/10", "bc", True, "145/306"),
    # Tier 2: Full frontier (1D Salberger cbp1 + 2D large-coefficient salb_f)
    "full_unres_alpha1_lam1.json": (6, "full", "1", "1", "abc", False, "4224/7637"),
    "full_imbal_alpha_9_10_lam1.json": (6, "full", "9/10", "1", "bc", True, "84209/152740"),
}


class InvalidCertificate(Exception):
    """Raised whenever a certificate fails any structural or mathematical check."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)


def parse_rational(value: Any) -> Q:
    if isinstance(value, bool):
        raise InvalidCertificate(f"Boolean is not a rational number: {value!r}")
    if isinstance(value, (int, str)):
        try:
            return Q(value)
        except Exception as exc:
            raise InvalidCertificate(f"Invalid rational literal {value!r}") from exc
    raise InvalidCertificate(f"Unsupported rational type: {type(value).__name__}")


def primes_up_to(n: int) -> List[int]:
    out = []
    for p in range(2, n + 1):
        if all(p % d != 0 for d in range(2, math.isqrt(p) + 1)):
            out.append(p)
    return out


def build_variable_layout(d0: int) -> Tuple[List[str], Dict[str, int]]:
    names: List[str] = []
    for let in LETTERS:
        for i in range(1, d0 + 1):
            names.append(f"{let}{i}")
        names.append(f"{let}r")
    names.extend(["aV", "bV", "cV", "A", "B", "C", "D", "Wa", "Wb", "Wc"])
    return names, {nm: i for i, nm in enumerate(names)}


def make_row(
    idx: Dict[str, int], nvar: int, terms: Dict[str, Q | int], rhs: Q | int
) -> Tuple[List[Q], Q]:
    vec = [Q(0)] * nvar
    for name, coeff in terms.items():
        vec[idx[name]] += Q(coeff)
    return vec, Q(rhs)


def add_sigma_terms(terms: Dict[str, Q], let: str, d0: int, coeff: Q) -> None:
    for h in range(1, d0 + 1):
        terms[f"{let}{h}"] = terms.get(f"{let}{h}", Q(0)) + coeff * h
    terms[f"{let}r"] = terms.get(f"{let}r", Q(0)) + coeff
    terms[f"W{let}"] = terms.get(f"W{let}", Q(0)) + coeff


def add_mask_terms(
    terms: Dict[str, Q], let: str, d0: int, mask: int, cm: Q, cq: Q
) -> None:
    for h in range(1, d0 + 1):
        if mask & (1 << (h - 1)):
            terms[f"{let}{h}"] = terms.get(f"{let}{h}", Q(0)) + cm + cq * h
    if mask & (1 << d0):
        terms[f"{let}r"] = terms.get(f"{let}r", Q(0)) + cm + cq
        terms[f"W{let}"] = terms.get(f"W{let}", Q(0)) + cq


def check_perm(i: Any, j: Any, k: Any, label: str) -> Tuple[int, int, int]:
    require(
        type(i) is int and type(j) is int and type(k) is int and {i, j, k} == {0, 1, 2},
        f"Invalid letter permutation ({i!r}, {j!r}, {k!r}) in {label}",
    )
    return i, j, k


def check_mult_list(el: Any, div: int, d0: int, allow_zero_if_one: bool, label: str) -> List[int]:
    require(isinstance(el, list) and len(el) >= 1, f"{label} must be a nonempty list")
    seen = set()
    out: List[int] = []
    for m in el:
        require(type(m) is int and m not in seen, f"Duplicate or non-int multiplicity {m!r} in {label}")
        seen.add(m)
        if m == 0:
            require(
                allow_zero_if_one and div == 1,
                f"Remainder group 0 in {label} is only valid for degree 1",
            )
        else:
            require(
                div <= m <= d0 and m % div == 0,
                f"Invalid multiplicity {m!r} for degree {div} in {label}",
            )
        out.append(m)
    return out


def check_qmask_disjoint_from_p(q_mask: Any, p: int, d0: int, nonempty: bool, label: str) -> int:
    max_mask = (1 << (d0 + 1)) - 1
    min_mask = 1 if nonempty else 0
    require(
        type(q_mask) is int and min_mask <= q_mask <= max_mask,
        f"Invalid q_mask {q_mask!r} in {label}",
    )
    for h in range(p, d0 + 1, p):
        require(
            (q_mask & (1 << (h - 1))) == 0,
            f"q_mask {q_mask} overlaps p={p} multiple h={h} in {label}",
        )
    return q_mask


def reconstruct_base_rows(
    cfg: Dict[str, Any], idx: Dict[str, int], nvar: int
) -> List[Tuple[List[Q], Q]]:
    d0 = cfg["d0"]
    alpha = parse_rational(cfg["alpha"])
    lam = parse_rational(cfg["lam"])
    sizes = [alpha, Q(1), Q(1)]
    primes = primes_up_to(d0)
    rows: List[Tuple[List[Q], Q]] = []

    def add(terms: Dict[str, Q | int], rhs: Q | int) -> None:
        rows.append(make_row(idx, nvar, terms, rhs))

    # 0. Radical budget: aV + bV + cV <= lam
    add({"aV": 1, "bV": 1, "cV": 1}, lam)

    # Per-letter anatomy
    for l_idx, let in enumerate(LETTERS):
        id_t: Dict[str, Q | int] = {f"{let}{i}": 1 for i in range(1, d0 + 1)}
        id_t[f"{let}r"] = 1
        id_t[f"{let}V"] = -1
        add(id_t, 0)
        add({k: -v for k, v in id_t.items()}, 0)

        sz_t: Dict[str, Q | int] = {f"{let}{i}": i for i in range(1, d0 + 1)}
        sz_t[f"{let}r"] = 1
        sz_t[f"W{let}"] = 1
        add(sz_t, sizes[l_idx])

        add({f"{let}r": d0, f"W{let}": -1}, 0)

        f_name = ("A", "B", "C")[l_idx]
        for p in primes:
            p_t: Dict[str, Q | int] = {f"{let}{i}": 1 for i in range(p, d0 + 1, p)}
            p_t[f_name] = -1
            add(p_t, 0)

    # Pair bounds
    for x, y in (("aV", "bV"), ("aV", "cV"), ("bV", "cV")):
        add({"D": 1, x: -1, y: -1}, 0)

    # Asymmetric Fourier L^4-L^4-L^2 bounds
    for fi, fj, vi, vj, vk in (
        ("A", "B", "aV", "bV", "cV"),
        ("A", "C", "aV", "cV", "bV"),
        ("B", "C", "bV", "cV", "aV"),
    ):
        add({"D": 4, fi: 1, fj: 1, vi: -3, vj: -3, vk: -2}, 0)

    # Exact symmetry-breaking rows
    sym = cfg["symmetry"]
    if sym in ("bc", "abc"):
        add({"bV": 1, "cV": -1}, 0)
    if sym == "abc":
        add({"aV": 1, "bV": -1}, 0)

    # Exact dyadic shell cuts sigma_b >= 1, sigma_c >= 1 (appended after RHS >= 0 base rows)
    if cfg["exact_bc_shell"]:
        for let in ("b", "c"):
            t_sh: Dict[str, Q] = {}
            add_sigma_terms(t_sh, let, d0, Q(-1))
            rows.append(make_row(idx, nvar, t_sh, Q(-1)))

    return rows


def reconstruct_split_branches(
    split: Any, cfg: Dict[str, Any], idx: Dict[str, int], nvar: int
) -> List[Tuple[List[Q], Q]]:
    require(isinstance(split, dict) and "type" in split, "Split must be an object with 'type'")
    kind = split["type"]
    d0 = cfg["d0"]
    alpha = parse_rational(cfg["alpha"])
    primes = set(primes_up_to(d0))
    max_mask = (1 << (d0 + 1)) - 1

    # 1. Single-block elementary Hua (1938) Weyl-sum cut (1-branch)
    if kind == "hua":
        require(cfg["include_hua"], "Hua cut used when include_hua is False")
        require(set(split) == {"type", "i", "m", "moment"}, f"Malformed Hua cut keys: {set(split)}")
        i, m, mom = split["i"], split["m"], split["moment"]
        require(type(i) is int and i in (0, 1, 2), f"Invalid Hua letter {i!r}")
        require(type(m) is int and 3 <= m <= d0, f"Invalid Hua block multiplicity {m!r}")
        require(type(mom) is int and mom in (6, 8, 16, 32), f"Invalid Hua moment {mom!r}")
        j, k = [l for l in range(3) if l != i]
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]
        fi, fj, fk = ("A", "B", "C")[i], ("A", "B", "C")[j], ("A", "B", "C")[k]
        if mom == 6:
            terms = {"D": 12, fi: 1, fj: 1, fk: 1, f"{li}{m}": 3, f"{li}V": -11, f"{lj}V": -7, f"{lk}V": -7}
        elif mom == 8:
            terms = {"D": 16, fj: 1, fk: 1, f"{li}{m}": 6, f"{li}V": -16, f"{lj}V": -9, f"{lk}V": -9}
        elif mom == 16:
            require(m >= 4, f"Hua L16 requires m >= 4, got m={m}")
            terms = {"D": 32, fj: 1, fk: 1, f"{li}{m}": 8, f"{li}V": -32, f"{lj}V": -17, f"{lk}V": -17}
        else:
            require(m >= 5, f"Hua L32 requires m >= 5, got m={m}")
            terms = {"D": 64, fj: 1, fk: 1, f"{li}{m}": 10, f"{li}V": -64, f"{lj}V": -33, f"{lk}V": -33}
        return [make_row(idx, nvar, terms, 0)]

    # 2. BLT Geometry of Numbers (2-branch)
    if kind == "gon":
        require(set(split) == {"type", "masks"}, "Malformed GoN split keys")
        masks = split["masks"]
        require(isinstance(masks, list) and len(masks) == 3, "GoN masks must have length 3")
        t0: Dict[str, Q | int] = {"D": 1, "aV": -1, "bV": -1, "cV": -1}
        t1: Dict[str, Q | int] = {"D": 1, "aV": -1, "bV": -1, "cV": -1}
        for let, mask in zip(LETTERS, masks):
            require(
                type(mask) is int and 1 <= mask <= max_mask and (mask & 1) == 1,
                f"Invalid GoN mask {mask!r}",
            )
            for h in range(1, d0 + 1):
                if mask & (1 << (h - 1)):
                    t0[f"{let}{h}"] = 1
                    if h > 1:
                        t1[f"{let}{h}"] = -(h - 1)
            if mask & (1 << d0):
                t0[f"{let}r"] = 1
                t1[f"W{let}"] = -1
        return [make_row(idx, nvar, t0, 0), make_row(idx, nvar, t1, -1)]

    # 3. Congruence-Lattice / Self-Thinning Parallelogram stCL (2-branch)
    if kind == "cl":
        require(cfg["include_cl"], "CL split used when include_cl is False")
        require(
            set(split) == {"type", "target", "k", "e1", "e2", "j_mask"},
            f"Malformed CL split keys: {set(split)}",
        )
        tau, k, e1, e2, j_mask = split["target"], split["k"], split["e1"], split["e2"], split["j_mask"]
        require(type(tau) is int and tau in (0, 1, 2), f"Invalid CL target {tau!r}")
        require(type(k) is int and 1 <= k <= d0, f"Invalid CL degree k={k!r}")
        stcl = cfg["include_stcl"]
        min_j = 0 if (stcl or (tau == 0 and alpha < Q(1))) else 1
        require(type(j_mask) is int and min_j <= j_mask <= max_mask, f"Invalid CL j_mask {j_mask!r}")
        require(isinstance(e1, list) and isinstance(e2, list), "CL e1/e2 must be lists")
        require(len(e1) + len(e2) >= 1, "At least one of CL e1, e2 must be nonempty")
        for el in (e1, e2):
            if el:
                check_mult_list(el, k, d0, allow_zero_if_one=True, label="CL")

        others = [l for l in range(3) if l != tau]
        l1_let, l2_let, tau_let = LETTERS[others[0]], LETTERS[others[1]], LETTERS[tau]
        t0: Dict[str, Q] = {"D": Q(1), f"{l1_let}V": Q(-1), f"{l2_let}V": Q(-1)}
        t1: Dict[str, Q] = {"D": Q(1), f"{l1_let}V": Q(-1), f"{l2_let}V": Q(-1)}

        for let, el in ((l1_let, e1), (l2_let, e2)):
            for m in el:
                if m == 0:
                    t0[f"{let}r"] = t0.get(f"{let}r", Q(0)) + 1
                    t1[f"{let}r"] = t1.get(f"{let}r", Q(0)) + (1 - Q(1, k))
                    t1[f"W{let}"] = t1.get(f"W{let}", Q(0)) - Q(1, k)
                else:
                    t0[f"{let}{m}"] = t0.get(f"{let}{m}", Q(0)) + 1
                    t1[f"{let}{m}"] = t1.get(f"{let}{m}", Q(0)) + (1 - Q(m, k))

        add_mask_terms(t0, tau_let, d0, j_mask, Q(-1), Q(0))
        add_mask_terms(t1, tau_let, d0, j_mask, Q(-1), Q(1))

        if stcl:
            add_sigma_terms(t1, tau_let, d0, Q(-1))
            rhs1 = Q(-1)
        else:
            rhs1 = -(Q(1) - alpha) if tau == 0 else Q(0)
        return [make_row(idx, nvar, t0, 0), make_row(idx, nvar, t1, rhs1)]

    # 4. Safe prime-indexed cross-letter collision coll_p (2-branch)
    if kind == "coll_p":
        require(cfg["include_coll_p"], "coll_p split used when include_coll_p is False")
        require(set(split) == {"type", "i", "j", "k", "p"}, f"Malformed coll_p keys: {set(split)}")
        i, j, k = check_perm(split["i"], split["j"], split["k"], "coll_p")
        p = split["p"]
        require(type(p) is int and p in primes, f"Invalid prime p={p!r} in coll_p")
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]
        t0: Dict[str, Q] = {"D": Q(1), f"{li}V": Q(-1), f"{lj}V": Q(-1)}
        t1: Dict[str, Q] = {"D": Q(2), f"{li}V": Q(-1), f"{lj}V": Q(-1), f"{lk}V": Q(-2)}
        for h in range(p, d0 + 1, p):
            t0[f"{li}{h}"] = Q(1)
            t1[f"{li}{h}"] = Q(1)
        return [make_row(idx, nvar, t0, 0), make_row(idx, nvar, t1, 0)]

    # 5. Multi-block self-thinning difference congruence lattice diffcl (2- or 3-branch)
    if kind == "diffcl":
        require(cfg["include_diffcl"], "diffcl split used when include_diffcl is False")
        require(
            set(split) == {"type", "target", "h", "ell", "e1", "e2", "j_mask", "thinned"},
            f"Malformed diffcl keys: {set(split)}",
        )
        tau, h, ell = split["target"], split["h"], split["ell"]
        j_mask, thinned = split["j_mask"], split["thinned"]
        require(type(tau) is int and tau in (0, 1, 2), f"Invalid diffcl target {tau!r}")
        require(
            type(h) is int and type(ell) is int and 1 <= h <= d0 and 1 <= ell <= d0 and h != ell,
            f"Invalid diffcl degrees h={h!r}, ell={ell!r}",
        )
        require(type(j_mask) is int and 0 <= j_mask <= max_mask, f"Invalid diffcl j_mask {j_mask!r}")
        require(type(thinned) is bool, "diffcl thinned must be bool")
        if thinned:
            require(cfg["include_stcl"], "thinned diffcl requires include_stcl=True")
        e1 = check_mult_list(split["e1"], h, d0, allow_zero_if_one=True, label="diffcl e1")
        e2 = check_mult_list(split["e2"], ell, d0, allow_zero_if_one=True, label="diffcl e2")

        others = [l for l in range(3) if l != tau]
        l1_let, l2_let, tau_let = LETTERS[others[0]], LETTERS[others[1]], LETTERS[tau]
        g = math.gcd(h, ell)
        s, d = h // g, ell // g

        def base_f() -> Dict[str, Q]:
            t: Dict[str, Q] = {"D": Q(1), f"{l1_let}V": Q(-1), f"{l2_let}V": Q(-1)}
            for m in e1:
                key = f"{l1_let}r" if m == 0 else f"{l1_let}{m}"
                t[key] = t.get(key, Q(0)) + 1
            for m in e2:
                key = f"{l2_let}r" if m == 0 else f"{l2_let}{m}"
                t[key] = t.get(key, Q(0)) + 1
            add_mask_terms(t, tau_let, d0, j_mask, Q(-1), Q(0))
            return t

        def add_sz(t: Dict[str, Q], let: str, el: Sequence[int], cf: Q) -> None:
            for m in el:
                if m == 0:
                    t[f"{let}r"] = t.get(f"{let}r", Q(0)) + cf
                    t[f"W{let}"] = t.get(f"W{let}", Q(0)) + cf
                else:
                    t[f"{let}{m}"] = t.get(f"{let}{m}", Q(0)) + cf * m

        b0 = base_f()
        b1 = base_f()
        add_sz(b1, l1_let, e1, Q(-1, 2 * g))
        add_sz(b1, l2_let, e2, Q(-1, 2 * g))
        add_mask_terms(b1, tau_let, d0, j_mask, Q(0), Q(1, 2))
        if thinned:
            add_sigma_terms(b1, tau_let, d0, Q(-1, 2))
            rhs1 = Q(-1, 2)
        else:
            rhs1 = Q(0)

        out = [make_row(idx, nvar, b0, 0), make_row(idx, nvar, b1, rhs1)]
        if s == 1 or d == 1:
            b2 = base_f()
            if s == 1:
                add_sz(b2, l1_let, e1, Q(-1, g))
                add_sz(b2, l2_let, e2, Q(-1, 2 * g))
            else:
                add_sz(b2, l1_let, e1, Q(-1, 2 * g))
                add_sz(b2, l2_let, e2, Q(-1, g))
            add_mask_terms(b2, tau_let, d0, j_mask, Q(0), Q(1))
            if thinned:
                add_sigma_terms(b2, tau_let, d0, Q(-1))
                rhs2 = Q(-1)
            else:
                rhs2 = Q(0)
            out.append(make_row(idx, nvar, b2, rhs2))
        return out

    # 6. Cofactor-divisor collision qcoll (3-branch) & self-thinned st_qcoll (4-branch)
    if kind in ("qcoll", "st_qcoll"):
        if kind == "qcoll":
            require(cfg["include_qcoll"], "qcoll split used when include_qcoll is False")
        else:
            require(cfg["include_st_qcoll"], "st_qcoll split used when include_st_qcoll is False")
        require(
            set(split) == {"type", "variant", "i", "j", "k", "p", "q_mask", "m", "e_k"},
            f"Malformed {kind} keys: {set(split)}",
        )
        var = split["variant"]
        require(var in ("ac", "ap"), f"Invalid {kind} variant {var!r}")
        i, j, k = check_perm(split["i"], split["j"], split["k"], kind)
        p = split["p"]
        require(type(p) is int and p in primes, f"Invalid prime p={p!r} in {kind}")
        q_mask = check_qmask_disjoint_from_p(split["q_mask"], p, d0, nonempty=False, label=kind)
        m = split["m"]
        require(type(m) is int and 1 <= m <= d0, f"Invalid degree m={m!r} in {kind}")
        e_k = check_mult_list(split["e_k"], m, d0, allow_zero_if_one=True, label=f"{kind} e_k")
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]
        p_mults = [h for h in range(p, d0 + 1, p)]

        def add_rp(t: Dict[str, Q], cf: Q) -> None:
            t[f"{li}V"] = t.get(f"{li}V", Q(0)) + cf
            for h in p_mults:
                t[f"{li}{h}"] = t.get(f"{li}{h}", Q(0)) - cf

        def add_mk_u(t: Dict[str, Q], cm: Q, cu: Q) -> None:
            for h in e_k:
                if h == 0:
                    t[f"{lk}r"] = t.get(f"{lk}r", Q(0)) + cm + cu
                    t[f"W{lk}"] = t.get(f"W{lk}", Q(0)) + cu
                else:
                    t[f"{lk}{h}"] = t.get(f"{lk}{h}", Q(0)) + cm + cu * Q(h, m)

        b0: Dict[str, Q] = {"D": Q(1), f"{lj}V": Q(-1)}
        add_rp(b0, Q(-1))

        if var == "ac":
            b1: Dict[str, Q] = {"D": Q(2), f"{lj}V": Q(-1), f"{lk}V": Q(-2)}
            add_rp(b1, Q(-1))
            add_mask_terms(b1, li, d0, q_mask, Q(-1), Q(1))
            add_mk_u(b1, Q(2), Q(-2))

            b2: Dict[str, Q] = {"D": Q(4), f"{li}V": Q(-3), f"{lj}V": Q(-2), f"{lk}V": Q(-3)}
            for h in p_mults:
                b2[f"{li}{h}"] = b2.get(f"{li}{h}", Q(0)) + 1
            add_mask_terms(b2, li, d0, q_mask, Q(-1), Q(0))
            add_mk_u(b2, Q(3), Q(-1))
        else:
            b1 = {"D": Q(2), f"{lj}V": Q(-1), f"{lk}V": Q(-2)}
            add_rp(b1, Q(-1))
            add_mask_terms(b1, li, d0, q_mask, Q(-1), Q(0))
            add_mk_u(b1, Q(1), Q(0))

            b2 = {"D": Q(2), f"{lj}V": Q(-1), f"{lk}V": Q(-2)}
            add_rp(b2, Q(-1))
            add_mask_terms(b2, li, d0, q_mask, Q(-1), Q(1))
            add_mk_u(b2, Q(1), Q(-1))

        if kind == "qcoll":
            return [make_row(idx, nvar, b0, 0), make_row(idx, nvar, b1, 0), make_row(idx, nvar, b2, 0)]

        b_deg: Dict[str, Q] = {}
        add_sigma_terms(b_deg, lk, d0, Q(1))
        add_sigma_terms(b_deg, li, d0, Q(-1))
        target_b = b1 if var == "ac" else b2
        add_sigma_terms(target_b, lk, d0, Q(1))
        add_sigma_terms(target_b, li, d0, Q(-1))
        return [
            make_row(idx, nvar, b_deg, 0),
            make_row(idx, nvar, b0, 0),
            make_row(idx, nvar, b1, 0),
            make_row(idx, nvar, b2, 0),
        ]

    # 7. Modular cofactor collision modcoll (1-block: 3-branch; 2-block: 5-branch)
    if kind == "modcoll":
        require(cfg["include_modcoll"], "modcoll split used when include_modcoll is False")
        require(
            set(split) == {"type", "i", "j", "k", "p", "q_mask", "blocks"},
            f"Malformed modcoll keys: {set(split)}",
        )
        i, j, k = check_perm(split["i"], split["j"], split["k"], "modcoll")
        p = split["p"]
        require(type(p) is int and p in primes, f"Invalid prime p={p!r} in modcoll")
        q_mask = check_qmask_disjoint_from_p(split["q_mask"], p, d0, nonempty=True, label="modcoll")
        blocks = split["blocks"]
        require(
            isinstance(blocks, list) and len(blocks) in (1, 2)
            and all(type(b) is int and 1 <= b <= d0 for b in blocks)
            and len(set(blocks)) == len(blocks),
            f"Invalid modcoll blocks {blocks!r}",
        )
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]
        p_mults = [h for h in range(p, d0 + 1, p)]

        def add_g(t: Dict[str, Q], cf: Q) -> None:
            t[f"{li}V"] = t.get(f"{li}V", Q(0)) + cf
            for h in p_mults:
                t[f"{li}{h}"] = t.get(f"{li}{h}", Q(0)) - cf
            t[f"{lj}V"] = t.get(f"{lj}V", Q(0)) + cf

        b0: Dict[str, Q] = {"D": Q(1)}
        add_g(b0, Q(-1))
        out = [make_row(idx, nvar, b0, 0)]

        if len(blocks) == 1:
            h1 = blocks[0]
            for use_q in (True, False):
                t: Dict[str, Q] = {"D": Q(2), f"{lk}V": Q(-2)}
                add_g(t, Q(-1))
                add_mask_terms(t, li, d0, q_mask, Q(-1), Q(1) if use_q else Q(0))
                if not use_q:
                    t[f"{lk}{h1}"] = t.get(f"{lk}{h1}", Q(0)) + 1
                out.append(make_row(idx, nvar, t, 0))
        else:
            h1, h2 = blocks[0], blocks[1]
            for u1_q in (True, False):
                for u2_q in (True, False):
                    t = {"D": Q(4), f"{lk}V": Q(-4)}
                    add_g(t, Q(-2))
                    cq = Q((1 if u1_q else 0) + (1 if u2_q else 0))
                    add_mask_terms(t, li, d0, q_mask, Q(-2), cq)
                    if not u1_q:
                        t[f"{lk}{h1}"] = t.get(f"{lk}{h1}", Q(0)) + 2
                    if not u2_q:
                        t[f"{lk}{h2}"] = t.get(f"{lk}{h2}", Q(0)) + 2
                    out.append(make_row(idx, nvar, t, 0))
        return out

    # 8. 3-block modular cofactor collision modcoll3 with STRICT h1 == 1 (7-branch)
    if kind == "modcoll3":
        require(cfg["include_modcoll3"], "modcoll3 split used when include_modcoll3 is False")
        require(
            set(split) == {"type", "i", "j", "k", "p", "q_mask", "blocks"},
            f"Malformed modcoll3 keys: {set(split)}",
        )
        i, j, k = check_perm(split["i"], split["j"], split["k"], "modcoll3")
        p = split["p"]
        require(type(p) is int and p in primes, f"Invalid prime p={p!r} in modcoll3")
        q_mask = check_qmask_disjoint_from_p(split["q_mask"], p, d0, nonempty=True, label="modcoll3")
        blocks = split["blocks"]
        require(
            isinstance(blocks, list) and len(blocks) == 3
            and all(type(b) is int and 1 <= b <= d0 for b in blocks)
            and len(set(blocks)) == 3,
            f"Invalid modcoll3 blocks {blocks!r}",
        )
        require(blocks[0] == 1, f"modcoll3 strictly requires blocks[0] == 1, got {blocks[0]!r}")
        h1, h2, h3 = blocks
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]
        p_mults = [h for h in range(p, d0 + 1, p)]

        def add_g(t: Dict[str, Q], cf: Q) -> None:
            t[f"{li}V"] = t.get(f"{li}V", Q(0)) + cf
            for h in p_mults:
                t[f"{li}{h}"] = t.get(f"{li}{h}", Q(0)) - cf
            t[f"{lj}V"] = t.get(f"{lj}V", Q(0)) + cf

        b0: Dict[str, Q] = {"D": Q(1)}
        add_g(b0, Q(-1))
        out = [make_row(idx, nvar, b0, 0)]

        for a_mode in ("u2", "q"):
            for b_mode in ("q", "u1u3", "u1q"):
                t: Dict[str, Q] = {"D": Q(16), f"{lk}V": Q(-16)}
                add_g(t, Q(-8))
                cq = Q(0)
                if a_mode == "u2":
                    t[f"{lk}{h2}"] = t.get(f"{lk}{h2}", Q(0)) + 8
                else:
                    cq += 4
                if b_mode == "q":
                    cq += 4
                elif b_mode == "u1u3":
                    t[f"{lk}{h1}"] = t.get(f"{lk}{h1}", Q(0)) + 8
                    t[f"{lk}{h3}"] = t.get(f"{lk}{h3}", Q(0)) + 4
                else:
                    t[f"{lk}{h1}"] = t.get(f"{lk}{h1}", Q(0)) + 8
                    cq += 2
                add_mask_terms(t, li, d0, q_mask, Q(-8), cq)
                out.append(make_row(idx, nvar, t, 0))
        return out

    # 9. Elementary Coppersmith + Bezout (3-branch)
    if kind == "cop_elem":
        require(cfg["include_cop_elem"], "cop_elem split used when include_cop_elem is False")
        require(
            set(split) == {"type", "i", "j", "k", "p", "e_i", "j_mask", "k_mask"},
            f"Malformed cop_elem keys: {set(split)}",
        )
        i, j, k = check_perm(split["i"], split["j"], split["k"], "cop_elem")
        p = split["p"]
        require(type(p) is int and 2 <= p <= d0, f"Invalid cop_elem degree p={p!r}")
        e_i = check_mult_list(split["e_i"], p, d0, allow_zero_if_one=False, label="cop_elem e_i")
        j_mask, k_mask = split["j_mask"], split["k_mask"]
        require(type(j_mask) is int and 0 <= j_mask <= max_mask, f"Invalid cop_elem j_mask {j_mask!r}")
        require(type(k_mask) is int and 1 <= k_mask <= max_mask, f"Invalid cop_elem k_mask {k_mask!r}")
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]

        bdeg: Dict[str, Q] = {}
        add_mask_terms(bdeg, lj, d0, j_mask, Q(0), Q(1))
        add_mask_terms(bdeg, lk, d0, k_mask, Q(0), Q(1))
        add_sigma_terms(bdeg, lj, d0, Q(-1))

        b1: Dict[str, Q] = {"D": Q(1), f"{li}V": Q(-1)}
        for h in e_i:
            b1[f"{li}{h}"] = b1.get(f"{li}{h}", Q(0)) + 1
        add_mask_terms(b1, lj, d0, j_mask, Q(-1), Q(1))
        add_mask_terms(b1, lk, d0, k_mask, Q(-1), Q(0))
        add_sigma_terms(b1, lj, d0, Q(-1))

        b2: Dict[str, Q] = {"D": Q(1), f"{li}V": Q(-1)}
        for h in e_i:
            b2[f"{li}{h}"] = b2.get(f"{li}{h}", Q(0)) + (Q(1) - Q(h, p))
        add_mask_terms(b2, lj, d0, j_mask, Q(-1), Q(p + 1, p))
        add_mask_terms(b2, lk, d0, k_mask, Q(-1), Q(1, p))
        add_sigma_terms(b2, lj, d0, Q(-(p + 1), p))

        return [make_row(idx, nvar, bdeg, 0), make_row(idx, nvar, b1, 0), make_row(idx, nvar, b2, 0)]

    # 10. Tier 2 ONLY: 7-branch single-modulus Coppersmith + automorphism + 1D Salberger Thm. 1.2
    if kind == "cbp1":
        require(
            cfg["tier"] == "full" and cfg["include_cbp1"] is True,
            "cbp1 split is forbidden outside tier='full'",
        )
        require(
            set(split) == {"type", "mode", "i", "j", "k", "p", "e_i", "j_mask", "k_mask"},
            f"Malformed cbp1 keys: {set(split)}",
        )
        mode = split["mode"]
        require(mode in ("a", "b"), f"Invalid cbp1 mode {mode!r}")
        i, j, k = check_perm(split["i"], split["j"], split["k"], "cbp1")
        p = split["p"]
        require(type(p) is int and 2 <= p <= d0, f"Invalid cbp1 degree p={p!r}")
        e_i = check_mult_list(split["e_i"], p, d0, allow_zero_if_one=False, label="cbp1 e_i")
        j_mask, k_mask = split["j_mask"], split["k_mask"]
        require(type(j_mask) is int and 0 <= j_mask <= max_mask, f"Invalid cbp1 j_mask {j_mask!r}")
        require(type(k_mask) is int and 1 <= k_mask <= max_mask, f"Invalid cbp1 k_mask {k_mask!r}")
        li, lj, lk = LETTERS[i], LETTERS[j], LETTERS[k]

        def add_f_ux(t: Dict[str, Q], cf: Q, cux: Q) -> None:
            t[f"{li}V"] = t.get(f"{li}V", Q(0)) + cf
            for h in e_i:
                t[f"{li}{h}"] = t.get(f"{li}{h}", Q(0)) - cf + cux * Q(h, p)
            add_mask_terms(t, lj, d0, j_mask, cf, Q(0))
            add_mask_terms(t, lk, d0, k_mask, cf, Q(0))

        def add_ell(t: Dict[str, Q], c_idx: int, cf: Q) -> None:
            if c_idx == 1:
                for h in e_i:
                    t[f"{li}{h}"] = t.get(f"{li}{h}", Q(0)) + cf * Q(h, p)
            else:
                add_mask_terms(t, lj, d0, j_mask, Q(0), cf * Q(1, p))
                add_mask_terms(t, lk, d0, k_mask, Q(0), cf * Q(1, p))
                add_sigma_terms(t, lj, d0, -cf * Q(1, p))

        bdeg: Dict[str, Q] = {}
        add_mask_terms(bdeg, lj, d0, j_mask, Q(0), Q(1))
        add_mask_terms(bdeg, lk, d0, k_mask, Q(0), Q(1))
        add_sigma_terms(bdeg, lj, d0, Q(-1))
        out = [make_row(idx, nvar, bdeg, 0)]

        for c_idx in (1, 2):
            v1: Dict[str, Q] = {"D": Q(1)}
            add_f_ux(v1, Q(-1), Q(-1))
            add_ell(v1, c_idx, Q(1))
            add_sigma_terms(v1, lj, d0, Q(-1, p))
            add_mask_terms(v1, lj, d0, j_mask, Q(0), Q(1, p))
            out.append(make_row(idx, nvar, v1, 0))

            if mode == "a":
                v2: Dict[str, Q] = {"D": Q(1)}
                add_f_ux(v2, Q(-1), Q(-1))
                add_ell(v2, c_idx, Q(p - 1, p))
                out.append(make_row(idx, nvar, v2, 0))

            v3: Dict[str, Q] = {"D": Q(1)}
            add_f_ux(v3, Q(-1), Q(-1))
            if mode == "a":
                add_ell(v3, c_idx, Q(1))
                add_sigma_terms(v3, lk, d0, Q(-1, p))
                add_mask_terms(v3, lk, d0, k_mask, Q(0), Q(1, p))
            else:
                add_ell(v3, c_idx, Q(p - 1, p))
                add_sigma_terms(v3, lk, d0, Q(-(p - 1), p * p))
                add_mask_terms(v3, lk, d0, k_mask, Q(0), Q(p - 1, p * p))
            out.append(make_row(idx, nvar, v3, 0))
        return out

    # 11. Tier 2 ONLY: 4-branch large-coefficient Salberger (2023) Cor. 6.5 / Thm. 3.16 on F_i
    if kind == "salb_f":
        require(
            cfg["tier"] == "full" and cfg["include_salb_f"] is True,
            "salb_f split is forbidden outside tier='full'",
        )
        require(set(split) == {"type", "i", "d"}, f"Malformed salb_f keys: {set(split)}")
        i, d = split["i"], split["d"]
        require(type(i) is int and i in (0, 1, 2), f"Invalid salb_f letter {i!r}")
        require(type(d) is int and d in SALB_F_PARAMS and d <= d0, f"Invalid salb_f degree d={d!r}")
        c1, c2, c3, c4 = SALB_F_PARAMS[d]
        li = LETTERS[i]
        fi = ("A", "B", "C")[i]

        b0: Dict[str, Q] = {f"{li}V": Q(1), fi: Q(-1)}
        b1: Dict[str, Q] = {f"{li}{d}": Q(3), f"{li}V": Q(-1), fi: Q(-1)}
        b2: Dict[str, Q] = {f"{li}{d}": Q(4) - c1, f"{li}V": Q(-1), fi: Q(-1)}
        b3: Dict[str, Q] = {f"{li}{d}": Q(4) - c3, f"{li}V": Q(-1), fi: Q(-1)}
        for h in range(1, d0 + 1):
            if h != d:
                b2[f"{li}{h}"] = c2 * h
                b3[f"{li}{h}"] = c4 * h
        return [
            make_row(idx, nvar, b0, 0),
            make_row(idx, nvar, b1, 0),
            make_row(idx, nvar, b2, 0),
            make_row(idx, nvar, b3, 0),
        ]

    raise InvalidCertificate(f"Unsupported split type: {kind!r}")


def satisfies(row: Tuple[List[Q], Q], point: Sequence[Q]) -> bool:
    coeffs, rhs = row
    return sum(c * x for c, x in zip(coeffs, point)) <= rhs


def canonical_f_values(
    point: Sequence[Q], cfg: Dict[str, Any], idx: Dict[str, int]
) -> List[Q]:
    d0 = cfg["d0"]
    p_list = primes_up_to(d0)
    out: List[Q] = []
    for n, let in enumerate(LETTERS):
        fn = max(
            (sum(point[idx[f"{let}{h}"]] for h in range(p, d0 + 1, p)) for p in p_list),
            default=Q(0),
        )
        if cfg["include_salb_f"]:
            vn = point[idx[f"{let}V"]]
            for d, (c1, c2, c3, c4) in SALB_F_PARAMS.items():
                if d > d0:
                    continue
                u = point[idx[f"{let}{d}"]]
                s_ord = sum(h * point[idx[f"{let}{h}"]] for h in range(1, d0 + 1) if h != d)
                lb_d = min(
                    vn,
                    3 * u - vn,
                    (4 - c1) * u + c2 * s_ord - vn,
                    (4 - c3) * u + c4 * s_ord - vn,
                )
                if lb_d > fn:
                    fn = lb_d
        out.append(fn)
    return out


def verify_primal_disjunctions(
    point: Sequence[Q], cfg: Dict[str, Any], idx: Dict[str, int], nvar: int
) -> int:
    """Exhaustively verify primal witness against ALL active cuts and disjunctions of its tier."""
    d0 = cfg["d0"]
    alpha = parse_rational(cfg["alpha"])
    primes = primes_up_to(d0)
    checked = 0

    def check_split(sp: Dict[str, Any]) -> None:
        nonlocal checked
        brs = reconstruct_split_branches(sp, cfg, idx, nvar)
        require(any(satisfies(b, point) for b in brs), f"Primal violates {sp['type']}: {sp}")
        checked += 1

    # 1. All single-block Hua inequalities
    if cfg["include_hua"]:
        for i in range(3):
            for m in range(3, d0 + 1):
                moms = [6, 8] + ([16] if m >= 4 else []) + ([32] if m >= 5 else [])
                for mom in moms:
                    check_split({"type": "hua", "i": i, "m": m, "moment": mom})

    # Precompute active group masks and subset lists per letter
    active_gon: List[List[int]] = []
    active_tau: List[List[int]] = []
    active_div: List[List[int]] = []  # nonempty masks excluding group 1
    active_k1_e: List[List[List[int]]] = []
    active_mult_e: Dict[Tuple[int, int], List[List[int]]] = {}

    for l_idx, let in enumerate(LETTERS):
        act_g = [h for h in range(2, d0 + 1) if point[idx[f"{let}{h}"]] != 0]
        if point[idx[f"{let}r"]] != 0 or point[idx[f"W{let}"]] != 0:
            act_g.append(d0 + 1)
        g_masks = []
        d_masks = []
        for bits in range(1 << len(act_g)):
            mg = 1
            md = 0
            for bi, g in enumerate(act_g):
                if bits & (1 << bi):
                    mg |= 1 << (g - 1)
                    md |= 1 << (g - 1)
            g_masks.append(mg)
            if md != 0:
                d_masks.append(md)
        active_gon.append(g_masks)
        active_div.append(d_masks)

        act_t = [h for h in range(1, d0 + 1) if point[idx[f"{let}{h}"]] != 0]
        if point[idx[f"{let}r"]] != 0 or point[idx[f"W{let}"]] != 0:
            act_t.append(d0 + 1)
        t_masks = []
        for bits in range(1, 1 << len(act_t)):
            mt = 0
            for bi, g in enumerate(act_t):
                if bits & (1 << bi):
                    mt |= 1 << (g - 1)
            t_masks.append(mt)
        if not t_masks:
            t_masks = [1]
        active_tau.append(t_masks)

        items_k1 = [h for h in range(1, d0 + 1) if point[idx[f"{let}{h}"]] != 0]
        if point[idx[f"{let}r"]] != 0 or point[idx[f"W{let}"]] != 0:
            items_k1.append(0)
        e_k1 = [list(c) for r in range(1, len(items_k1) + 1) for c in combinations(items_k1, r)]
        active_k1_e.append(e_k1)
        active_mult_e[(l_idx, 1)] = e_k1

        for k_deg in range(2, d0 + 1):
            mults = [m for m in range(k_deg, d0 + 1, k_deg) if point[idx[f"{let}{m}"]] != 0]
            active_mult_e[(l_idx, k_deg)] = [
                list(c) for r in range(1, len(mults) + 1) for c in combinations(mults, r)
            ]

    # 2. GoN
    for ma, mb, mc in product(*active_gon):
        check_split({"type": "gon", "masks": [ma, mb, mc]})

    # 3. CL / stCL
    if cfg["include_cl"]:
        for tau in range(3):
            others = [l for l in range(3) if l != tau]
            l1, l2 = others[0], others[1]
            j_masks = list(active_tau[tau])
            if cfg["include_stcl"] or (tau == 0 and alpha < Q(1)):
                j_masks.append(0)
            for k_deg in range(1, d0 + 1):
                s1 = [[]] + active_mult_e[(l1, k_deg)]
                s2 = [[]] + active_mult_e[(l2, k_deg)]
                for e1 in s1:
                    for e2 in s2:
                        if not e1 and not e2:
                            continue
                        for jm in j_masks:
                            check_split({"type": "cl", "target": tau, "k": k_deg, "e1": e1, "e2": e2, "j_mask": jm})

    # 4. Safe prime-indexed coll_p
    if cfg["include_coll_p"]:
        for i in range(3):
            for j in range(3):
                if j == i:
                    continue
                k = 3 - i - j
                for p in primes:
                    check_split({"type": "coll_p", "i": i, "j": j, "k": k, "p": p})

    # 5. diffcl
    if cfg["include_diffcl"]:
        for tau in range(3):
            others = [l for l in range(3) if l != tau]
            l1, l2 = others[0], others[1]
            j_masks = [0] + active_div[tau]
            for h in range(1, d0 + 1):
                s1 = active_mult_e[(l1, h)]
                if not s1:
                    continue
                for ell in range(1, d0 + 1):
                    if ell == h:
                        continue
                    s2 = active_mult_e[(l2, ell)]
                    if not s2:
                        continue
                    for e1 in s1:
                        for e2 in s2:
                            for jm in j_masks:
                                check_split(
                                    {
                                        "type": "diffcl", "target": tau, "h": h, "ell": ell,
                                        "e1": e1, "e2": e2, "j_mask": jm, "thinned": cfg["include_stcl"],
                                    }
                                )

    # Precompute valid q_masks disjoint from multiples of p for each (i, p)
    qmasks_ip: Dict[Tuple[int, int], List[int]] = {}
    for i, let in enumerate(LETTERS):
        for p in primes:
            act = [
                h for h in range(2, d0 + 1)
                if h % p != 0 and point[idx[f"{let}{h}"]] != 0
            ]
            if point[idx[f"{let}r"]] != 0 or point[idx[f"W{let}"]] != 0:
                act.append(d0 + 1)
            ql = []
            for bits in range(1, 1 << len(act)):
                mk = 0
                for bi, g in enumerate(act):
                    if bits & (1 << bi):
                        mk |= 1 << (g - 1)
                ql.append(mk)
            qmasks_ip[(i, p)] = ql

    # 6. qcoll & st_qcoll
    if cfg["include_qcoll"] or cfg["include_st_qcoll"]:
        for i in range(3):
            for j in range(3):
                if j == i:
                    continue
                k = 3 - i - j
                for p in primes:
                    ql = [0] + qmasks_ip[(i, p)]
                    for m in range(1, d0 + 1):
                        ekl = active_mult_e[(k, m)]
                        if not ekl:
                            continue
                        for e_k in ekl:
                            for qm in ql:
                                for var in ("ac", "ap"):
                                    if cfg["include_qcoll"]:
                                        check_split(
                                            {
                                                "type": "qcoll", "variant": var,
                                                "i": i, "j": j, "k": k, "p": p,
                                                "q_mask": qm, "m": m, "e_k": e_k,
                                            }
                                        )
                                    if cfg["include_st_qcoll"]:
                                        check_split(
                                            {
                                                "type": "st_qcoll", "variant": var,
                                                "i": i, "j": j, "k": k, "p": p,
                                                "q_mask": qm, "m": m, "e_k": e_k,
                                            }
                                        )

    # 7. modcoll & modcoll3
    if cfg["include_modcoll"] or cfg["include_modcoll3"]:
        act_blks = [
            [h for h in range(1, d0 + 1) if point[idx[f"{let}{h}"]] != 0]
            for let in LETTERS
        ]
        for i in range(3):
            for j in range(3):
                if j == i:
                    continue
                k = 3 - i - j
                blks = act_blks[k]
                other_blks = [h for h in blks if h >= 2]
                for p in primes:
                    ql = qmasks_ip[(i, p)]
                    if not ql:
                        continue
                    for qm in ql:
                        if cfg["include_modcoll"]:
                            for h1 in blks:
                                check_split(
                                    {"type": "modcoll", "i": i, "j": j, "k": k, "p": p, "q_mask": qm, "blocks": [h1]}
                                )
                            for h1, h2 in combinations(blks, 2):
                                check_split(
                                    {"type": "modcoll", "i": i, "j": j, "k": k, "p": p, "q_mask": qm, "blocks": [h1, h2]}
                                )
                        if cfg["include_modcoll3"] and 1 in blks and len(other_blks) >= 2:
                            for h2, h3 in combinations(other_blks, 2):
                                for ha, hb in ((h2, h3), (h3, h2)):
                                    check_split(
                                        {"type": "modcoll3", "i": i, "j": j, "k": k, "p": p, "q_mask": qm, "blocks": [1, ha, hb]}
                                    )

    # 8. cop_elem & cbp1
    if cfg["include_cop_elem"] or cfg["include_cbp1"]:
        for i in range(3):
            for p in range(2, d0 + 1):
                ei_list = active_mult_e[(i, p)]
                if not ei_list:
                    continue
                for j in range(3):
                    if j == i:
                        continue
                    k = 3 - i - j
                    j_masks = [0] + active_div[j]
                    k_masks = active_div[k]
                    if not k_masks:
                        continue
                    for e_i in ei_list:
                        for jm in j_masks:
                            for km in k_masks:
                                if cfg["include_cop_elem"]:
                                    check_split(
                                        {
                                            "type": "cop_elem",
                                            "i": i, "j": j, "k": k, "p": p,
                                            "e_i": e_i, "j_mask": jm, "k_mask": km,
                                        }
                                    )
                                if cfg["include_cbp1"]:
                                    for mode in ("a", "b"):
                                        check_split(
                                            {
                                                "type": "cbp1", "mode": mode,
                                                "i": i, "j": j, "k": k, "p": p,
                                                "e_i": e_i, "j_mask": jm, "k_mask": km,
                                            }
                                        )

    # 9. salb_f (Tier 2 only)
    if cfg["include_salb_f"]:
        for i in range(3):
            for d in SALB_F_PARAMS:
                if d <= d0:
                    check_split({"type": "salb_f", "i": i, "d": d})

    return checked


def verify_certificate(cert: Any, require_primal: bool = False) -> Dict[str, Any]:
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 4000))
    require(isinstance(cert, dict), "Certificate must be a JSON object")
    require(cert.get("schema") == "abc-exceptional-frontier-v4", "Wrong schema")

    cfg = cert.get("config")
    require(isinstance(cfg, dict), "Missing config object")
    required_cfg = {
        "d0", "alpha", "lam", "tier", "symmetry", "exact_bc_shell",
        "include_l442", "include_cl", "include_stcl", "include_coll_p",
        "include_diffcl", "include_qcoll", "include_st_qcoll",
        "include_modcoll", "include_modcoll3", "include_hua",
        "include_cop_elem", "include_cbp1", "include_salb_f",
    }
    require(set(cfg) == required_cfg, f"Config keys mismatch: {set(cfg)}")
    d0 = cfg["d0"]
    require(type(d0) is int and d0 >= 4, f"Invalid d0: {d0!r}")
    alpha = parse_rational(cfg["alpha"])
    lam = parse_rational(cfg["lam"])
    require(Q(0) <= alpha <= Q(1), f"alpha out of [0, 1]: {alpha}")
    require(Q(0) < lam <= Q(1), f"lam out of (0, 1]: {lam}")

    tier = cfg["tier"]
    require(tier in ("elem", "full"), f"Invalid tier {tier!r}")
    sym = cfg["symmetry"]
    require(sym in ("none", "bc", "abc"), f"Invalid symmetry {sym!r}")
    require(type(cfg["exact_bc_shell"]) is bool, "Config exact_bc_shell must be bool")
    if sym == "abc":
        require(alpha == Q(1), "symmetry='abc' requires alpha=1")
        require(cfg["exact_bc_shell"] is False, "exact_bc_shell=True is incompatible with symmetry='abc'")

    elem_flags = (
        "include_l442", "include_cl", "include_stcl", "include_coll_p",
        "include_diffcl", "include_qcoll", "include_st_qcoll",
        "include_modcoll", "include_modcoll3", "include_hua", "include_cop_elem",
    )
    full_flags = ("include_cbp1", "include_salb_f")
    for bkey in elem_flags + full_flags:
        require(type(cfg[bkey]) is bool, f"Config {bkey} must be bool")
    for bkey in elem_flags:
        require(cfg[bkey] is True, f"Unsupported config flag {bkey}=False in v4 model")
    if tier == "elem":
        for bkey in full_flags:
            require(cfg[bkey] is False, f"Tier 'elem' strictly forbids {bkey}=True")
    else:
        for bkey in full_flags:
            require(cfg[bkey] is True, f"Tier 'full' requires {bkey}=True")

    names, idx = build_variable_layout(d0)
    nvar = len(names)
    require(cert.get("variables") == names, "Variable list does not match canonical layout")

    bound = parse_rational(cert.get("bound"))
    base_rows = reconstruct_base_rows(cfg, idx, nvar)
    require(
        cert.get("base_row_count") == len(base_rows),
        f"base_row_count mismatch: got {cert.get('base_row_count')}, expected {len(base_rows)}",
    )

    stats: Dict[str, Any] = {
        "d0": d0,
        "tier": tier,
        "alpha": str(alpha),
        "lam": str(lam),
        "symmetry": sym,
        "exact_bc_shell": cfg["exact_bc_shell"],
        "bound": str(bound),
        "base_rows": len(base_rows),
        "branches": 0,
        "hua_cuts": 0,
        "dual_leaves": 0,
        "farkas_leaves": 0,
        "max_depth": 0,
        "split_types": {},
        "max_leaf_l1": Q(0),
        "min_farkas_margin": None,
        "certificate_mode": "upper_bound_only",
        "primal_verified": False,
        "primal_disjunctions_checked": 0,
    }

    def check_node(node: Any, rows: List[Tuple[List[Q], Q]], depth: int) -> None:
        require(isinstance(node, dict), "Proof node must be an object")
        if depth > stats["max_depth"]:
            stats["max_depth"] = depth

        if set(node) == {"split", "children"}:
            branches = reconstruct_split_branches(node["split"], cfg, idx, nvar)
            children = node["children"]
            require(
                isinstance(children, list) and len(children) == len(branches),
                f"Split of type {node['split'].get('type')!r} requires {len(branches)} children, got {len(children) if isinstance(children, list) else type(children).__name__}",
            )
            st = node["split"]["type"]
            if st == "hua":
                stats["hua_cuts"] += 1
            else:
                stats["branches"] += 1
            stats["split_types"][st] = stats["split_types"].get(st, 0) + 1
            for ch, br in zip(children, branches):
                rows.append(br)
                check_node(ch, rows, depth + 1)
                rows.pop()
            return

        require(set(node) in ({"dual"}, {"farkas"}), f"Unknown node keys: {set(node)}")
        kind = next(iter(node))
        entries = node[kind]
        require(isinstance(entries, list), f"{kind} must be a list of [index, weight] pairs")
        total = [Q(0)] * nvar
        rhs = Q(0)
        l1 = Q(0)
        seen = set()
        for entry in entries:
            require(isinstance(entry, list) and len(entry) == 2, "Malformed multiplier entry")
            r_idx, w_raw = entry
            require(type(r_idx) is int and 0 <= r_idx < len(rows), f"Invalid row index {r_idx!r}")
            require(r_idx not in seen, f"Duplicate multiplier row index {r_idx}")
            seen.add(r_idx)
            w = parse_rational(w_raw)
            require(w >= 0, f"Negative multiplier {w}")
            l1 += w
            coeffs, r_rhs = rows[r_idx]
            rhs += w * r_rhs
            for j in range(nvar):
                if coeffs[j] != 0:
                    total[j] += w * coeffs[j]

        if l1 > stats["max_leaf_l1"]:
            stats["max_leaf_l1"] = l1

        if kind == "dual":
            d_pos = idx["D"]
            for j in range(nvar):
                req_val = Q(1) if j == d_pos else Q(0)
                require(
                    total[j] >= req_val,
                    f"Dual fails coordinate {names[j]}: {total[j]} < {req_val}",
                )
            require(rhs <= bound, f"Dual RHS {rhs} exceeds claimed bound {bound}")
            stats["dual_leaves"] += 1
        else:
            for j in range(nvar):
                require(total[j] >= 0, f"Farkas fails coordinate {names[j]}: {total[j]} < 0")
            require(rhs < 0, f"Farkas RHS {rhs} is not strictly negative")
            margin = -rhs
            if stats["min_farkas_margin"] is None or margin < stats["min_farkas_margin"]:
                stats["min_farkas_margin"] = margin
            stats["farkas_leaves"] += 1

    active_rows = list(base_rows)
    check_node(cert.get("tree"), active_rows, 0)

    if "primal" in cert:
        primal = cert["primal"]
        require(isinstance(primal, dict) and set(primal) <= set(names), "Malformed primal dict")
        point = [parse_rational(primal.get(nm, 0)) for nm in names]
        require(all(v >= 0 for v in point), "Primal has negative coordinate")
        require(point[idx["D"]] == bound, f"Primal D={point[idx['D']]} != bound {bound}")
        f_canon = canonical_f_values(point, cfg, idx)
        for l_idx, fnm in enumerate(("A", "B", "C")):
            require(
                point[idx[fnm]] == f_canon[l_idx],
                f"Primal {fnm}={point[idx[fnm]]} is not canonical F_canon={f_canon[l_idx]}",
            )
        for r_i, row in enumerate(base_rows):
            require(satisfies(row, point), f"Primal violates base row {r_i}")
        stats["primal_disjunctions_checked"] = verify_primal_disjunctions(point, cfg, idx, nvar)
        stats["primal_verified"] = True
        stats["certificate_mode"] = "exact_optimum"
    elif require_primal:
        raise InvalidCertificate("Exact-optimum certificate requires a verified primal witness")

    stats["max_leaf_l1"] = str(stats["max_leaf_l1"])
    if stats["min_farkas_margin"] is not None:
        stats["min_farkas_margin"] = str(stats["min_farkas_margin"])
    return stats


def verify_registry_binding(filename: str, cert: Dict[str, Any], stats: Dict[str, Any]) -> None:
    require(filename in EXPECTED_SUITE, f"Unexpected certificate not in theorem registry: {filename}")
    exp_d0, exp_tier, exp_a, exp_l, exp_sym, exp_shell, exp_b = EXPECTED_SUITE[filename]
    cfg = cert["config"]
    require(cfg["d0"] == exp_d0, f"{filename}: d0={cfg['d0']} != {exp_d0}")
    require(cfg["tier"] == exp_tier, f"{filename}: tier={cfg['tier']} != {exp_tier}")
    require(parse_rational(cfg["alpha"]) == Q(exp_a), f"{filename}: alpha mismatch")
    require(parse_rational(cfg["lam"]) == Q(exp_l), f"{filename}: lam mismatch")
    require(cfg["symmetry"] == exp_sym, f"{filename}: symmetry mismatch")
    require(cfg["exact_bc_shell"] is exp_shell, f"{filename}: exact_bc_shell mismatch")
    require(parse_rational(stats["bound"]) == Q(exp_b), f"{filename}: bound {stats['bound']} != {exp_b}")


def verify_summary_json(
    summary_path: Path,
    verified_stats: Dict[str, Dict[str, Any]],
    verified_primals: Dict[str, Dict[str, str]],
) -> int:
    require(summary_path.exists(), f"Missing consolidated summary file: {summary_path}")
    rows = json.loads(summary_path.read_text())
    require(isinstance(rows, list) and len(rows) == len(verified_stats), "Summary row count mismatch")
    seen = set()
    req_keys = (
        "file", "d0", "tier", "alpha", "lam", "symmetry", "exact_bc_shell",
        "our_bound", "branches", "hua_cuts", "dual_leaves", "farkas_leaves",
        "max_depth", "split_types", "primal",
    )
    for row in rows:
        require(isinstance(row, dict), "Summary row must be an object")
        for k in req_keys:
            require(k in row, f"Summary row missing required key {k!r}")
        fname = row["file"]
        require(fname in verified_stats and fname not in seen, f"Unexpected/duplicate summary entry {fname}")
        seen.add(fname)
        st = verified_stats[fname]
        require(row["d0"] == st["d0"], f"Summary d0 mismatch for {fname}")
        require(row["tier"] == st["tier"], f"Summary tier mismatch for {fname}")
        require(parse_rational(row["alpha"]) == Q(st["alpha"]), f"Summary alpha mismatch for {fname}")
        require(parse_rational(row["lam"]) == Q(st["lam"]), f"Summary lam mismatch for {fname}")
        require(row["symmetry"] == st["symmetry"], f"Summary symmetry mismatch for {fname}")
        require(row["exact_bc_shell"] is st["exact_bc_shell"], f"Summary exact_bc_shell mismatch for {fname}")
        require(parse_rational(row["our_bound"]) == Q(st["bound"]), f"Summary bound mismatch for {fname}")
        require(row["branches"] == st["branches"], f"Summary branches mismatch for {fname}")
        require(row["hua_cuts"] == st["hua_cuts"], f"Summary hua_cuts mismatch for {fname}")
        require(row["dual_leaves"] == st["dual_leaves"], f"Summary dual_leaves mismatch for {fname}")
        require(row["farkas_leaves"] == st["farkas_leaves"], f"Summary farkas_leaves mismatch for {fname}")
        require(row["max_depth"] == st["max_depth"], f"Summary max_depth mismatch for {fname}")
        require(row["split_types"] == st["split_types"], f"Summary split_types mismatch for {fname}")
        require(row["primal"] == verified_primals[fname], f"Summary primal mismatch for {fname}")
    return len(seen)


def run_corruption_self_test(
    elem_leaf_cert: Dict[str, Any],
    elem_branch_cert: Dict[str, Any],
    full_branch_cert: Optional[Dict[str, Any]] = None,
) -> int:
    """Verify positive controls and 34 reason-checked adversarial corruptions."""
    require("dual" in elem_leaf_cert["tree"], "elem_leaf_cert fixture must be a single dual leaf")
    require("children" in elem_branch_cert["tree"], "elem_branch_cert fixture must branch")
    require(elem_leaf_cert["config"]["tier"] == "elem", "elem_leaf_cert must be tier='elem'")

    d0_leaf = elem_leaf_cert["config"]["d0"]
    valid_leaf = copy.deepcopy(elem_leaf_cert["tree"])

    # Positive controls: valid splits from every elementary family grafted above valid dual leaves must PASS
    positive_splits = [
        ({"type": "hua", "i": 0, "m": 5, "moment": 32}, 1),
        ({"type": "cl", "target": 1, "k": 2, "e1": [2], "e2": [2], "j_mask": 0}, 2),
        ({"type": "cl", "target": 2, "k": 2, "e1": [2], "e2": [2], "j_mask": 1 << d0_leaf}, 2),
        ({"type": "coll_p", "i": 0, "j": 1, "k": 2, "p": 5}, 2),
        ({"type": "diffcl", "target": 2, "h": 1, "ell": 2, "e1": [1], "e2": [2], "j_mask": 0, "thinned": True}, 3),
        ({"type": "qcoll", "variant": "ap", "i": 0, "j": 1, "k": 2, "p": 2, "q_mask": 4, "m": 3, "e_k": [3]}, 3),
        ({"type": "st_qcoll", "variant": "ac", "i": 0, "j": 1, "k": 2, "p": 2, "q_mask": 4, "m": 3, "e_k": [3]}, 4),
        ({"type": "modcoll", "i": 0, "j": 1, "k": 2, "p": 5, "q_mask": 4, "blocks": [1, 3]}, 5),
        ({"type": "modcoll3", "i": 0, "j": 1, "k": 2, "p": 5, "q_mask": 4, "blocks": [1, 2, 3]}, 7),
        ({"type": "cop_elem", "i": 0, "j": 1, "k": 2, "p": 5, "e_i": [5], "j_mask": 0, "k_mask": 8}, 3),
    ]
    for valid_split, n_ch in positive_splits:
        control = copy.deepcopy(elem_leaf_cert)
        control["tree"] = {
            "split": valid_split,
            "children": [copy.deepcopy(valid_leaf) for _ in range(n_ch)],
        }
        verify_certificate(control, require_primal=True)

    # Adversarial corruption suite: (label, corrupted_cert, expected_error_substring)
    cases: List[Tuple[str, Dict[str, Any], str]] = []

    def graft_elem(sp: Dict[str, Any], n_ch: int) -> Dict[str, Any]:
        c = copy.deepcopy(elem_leaf_cert)
        c["tree"] = {"split": sp, "children": [copy.deepcopy(valid_leaf) for _ in range(n_ch)]}
        return c

    # 1. Dropped branch
    c = copy.deepcopy(elem_branch_cert)
    c["tree"]["children"] = c["tree"]["children"][:1]
    cases.append(("dropped_branch", c, "children, got 1"))

    # 2. Extra branch
    c = copy.deepcopy(elem_leaf_cert)
    c["tree"] = {
        "split": {"type": "coll_p", "i": 0, "j": 1, "k": 2, "p": 2},
        "children": [copy.deepcopy(valid_leaf)] * 3,
    }
    cases.append(("extra_branch", c, "requires 2 children, got 3"))

    # 3. Unknown split type
    cases.append(("unknown_split_type", graft_elem({"type": "magic"}, 2), "Unsupported split type"))

    # 4. Tier violation: cbp1 split inside tier='elem'
    cases.append((
        "cbp1_in_elem_tier",
        graft_elem({"type": "cbp1", "mode": "a", "i": 0, "j": 1, "k": 2, "p": 5, "e_i": [5], "j_mask": 0, "k_mask": 8}, 7),
        "cbp1 split is forbidden outside tier='full'",
    ))

    # 5. Tier violation: salb_f split inside tier='elem'
    cases.append((
        "salb_f_in_elem_tier",
        graft_elem({"type": "salb_f", "i": 0, "d": 5}, 4),
        "salb_f split is forbidden outside tier='full'",
    ))

    # 6. Tier violation: include_cbp1=True in tier='elem'
    c = copy.deepcopy(elem_leaf_cert)
    c["config"]["include_cbp1"] = True
    cases.append(("cbp1_flag_in_elem", c, "Tier 'elem' strictly forbids include_cbp1=True"))

    # 7. Tier violation: include_salb_f=True in tier='elem'
    c = copy.deepcopy(elem_leaf_cert)
    c["config"]["include_salb_f"] = True
    cases.append(("salb_f_flag_in_elem", c, "Tier 'elem' strictly forbids include_salb_f=True"))

    # 8. Invalid symmetry + exact_bc_shell combination
    c = copy.deepcopy(elem_leaf_cert)
    c["config"]["alpha"] = "1"
    c["config"]["symmetry"] = "abc"
    c["config"]["exact_bc_shell"] = True
    cases.append(("exact_bc_shell_with_abc", c, "incompatible with symmetry='abc'"))

    # 9. Symmetry 'abc' with alpha < 1
    c = copy.deepcopy(elem_leaf_cert)
    c["config"]["alpha"] = "1/2"
    c["config"]["symmetry"] = "abc"
    c["config"]["exact_bc_shell"] = False
    cases.append(("abc_sym_with_alpha_lt_1", c, "symmetry='abc' requires alpha=1"))

    # 10. modcoll3 with blocks[0] != 1 (CRITICAL SOUNDNESS GUARD!)
    cases.append((
        "modcoll3_h1_not_1",
        graft_elem({"type": "modcoll3", "i": 0, "j": 1, "k": 2, "p": 5, "q_mask": 4, "blocks": [2, 1, 3]}, 7),
        "modcoll3 strictly requires blocks[0] == 1",
    ))

    # 11. modcoll3 with duplicate blocks
    cases.append((
        "modcoll3_dup_blocks",
        graft_elem({"type": "modcoll3", "i": 0, "j": 1, "k": 2, "p": 5, "q_mask": 4, "blocks": [1, 2, 2]}, 7),
        "Invalid modcoll3 blocks",
    ))

    # 12. modcoll q_mask overlapping multiple of p
    cases.append((
        "modcoll_qmask_hits_p",
        graft_elem({"type": "modcoll", "i": 0, "j": 1, "k": 2, "p": 2, "q_mask": 2, "blocks": [1]}, 3),
        "overlaps p=2",
    ))

    # 13. modcoll empty q_mask
    cases.append((
        "modcoll_empty_qmask",
        graft_elem({"type": "modcoll", "i": 0, "j": 1, "k": 2, "p": 5, "q_mask": 0, "blocks": [1]}, 3),
        "Invalid q_mask",
    ))

    # 14. qcoll q_mask overlapping multiple of p
    cases.append((
        "qcoll_qmask_hits_p",
        graft_elem({"type": "qcoll", "variant": "ap", "i": 0, "j": 1, "k": 2, "p": 3, "q_mask": 32, "m": 2, "e_k": [2]}, 3),
        "overlaps p=3",
    ))

    # 15. qcoll invalid variant
    cases.append((
        "qcoll_bad_variant",
        graft_elem({"type": "qcoll", "variant": "xx", "i": 0, "j": 1, "k": 2, "p": 2, "q_mask": 4, "m": 2, "e_k": [2]}, 3),
        "Invalid qcoll variant",
    ))

    # 16. coll_p with composite p=4
    cases.append((
        "coll_p_nonprime",
        graft_elem({"type": "coll_p", "i": 0, "j": 1, "k": 2, "p": 4}, 2),
        "Invalid prime p=4",
    ))

    # 17. Hua invalid moment
    cases.append((
        "hua_bad_moment",
        graft_elem({"type": "hua", "i": 0, "m": 5, "moment": 12}, 1),
        "Invalid Hua moment",
    ))

    # 18. Hua L16 with m=3 (requires m >= 4)
    cases.append((
        "hua_l16_m3",
        graft_elem({"type": "hua", "i": 0, "m": 3, "moment": 16}, 1),
        "Hua L16 requires m >= 4",
    ))

    # 19. Hua L32 with m=4 (requires m >= 5)
    cases.append((
        "hua_l32_m4",
        graft_elem({"type": "hua", "i": 0, "m": 4, "moment": 32}, 1),
        "Hua L32 requires m >= 5",
    ))

    # 20. cop_elem empty k_mask
    cases.append((
        "cop_elem_empty_kmask",
        graft_elem({"type": "cop_elem", "i": 0, "j": 1, "k": 2, "p": 5, "e_i": [5], "j_mask": 4, "k_mask": 0}, 3),
        "Invalid cop_elem k_mask",
    ))

    # 21. diffcl with h == ell
    cases.append((
        "diffcl_h_eq_ell",
        graft_elem({"type": "diffcl", "target": 2, "h": 2, "ell": 2, "e1": [2], "e2": [2], "j_mask": 0, "thinned": True}, 2),
        "Invalid diffcl degrees",
    ))

    # 22. CL remainder group 0 with k=2
    cases.append((
        "cl_rem_with_k2",
        graft_elem({"type": "cl", "target": 1, "k": 2, "e1": [0], "e2": [2], "j_mask": 1}, 2),
        "Remainder group 0",
    ))

    # 23. CL out-of-range j_mask
    cases.append((
        "cl_out_of_range_jmask",
        graft_elem({"type": "cl", "target": 1, "k": 2, "e1": [2], "e2": [2], "j_mask": 1 << (d0_leaf + 1)}, 2),
        "Invalid CL j_mask",
    ))

    # 24. CL non-divisible multiplicity
    cases.append((
        "cl_nondivisible_mult",
        graft_elem({"type": "cl", "target": 2, "k": 3, "e1": [2], "e2": [3], "j_mask": 1}, 2),
        "Invalid multiplicity 2 for degree 3",
    ))

    # 25. CL k=0
    cases.append((
        "cl_k_zero",
        graft_elem({"type": "cl", "target": 1, "k": 0, "e1": [1], "e2": [1], "j_mask": 0}, 2),
        "Invalid CL degree",
    ))

    # 26. CL both e1 and e2 empty
    cases.append((
        "cl_empty_e1_e2",
        graft_elem({"type": "cl", "target": 1, "k": 2, "e1": [], "e2": [], "j_mask": 0}, 2),
        "At least one of CL e1, e2 must be nonempty",
    ))

    # 27. GoN mask missing group 1
    cases.append((
        "gon_missing_group1",
        graft_elem({"type": "gon", "masks": [2, 1, 1]}, 2),
        "Invalid GoN mask",
    ))

    # 28. Empty leaf dual
    c = copy.deepcopy(elem_branch_cert)
    node = c["tree"]
    while "children" in node:
        node = node["children"][0]
    node.clear()
    node["dual"] = []
    cases.append(("empty_leaf_dual", c, "Dual fails coordinate D"))

    # 29. Negative multiplier
    c = copy.deepcopy(elem_branch_cert)
    node = c["tree"]
    while "children" in node:
        node = node["children"][0]
    kind = next(iter(node))
    node[kind][0][1] = "-1/100"
    cases.append(("negative_multiplier", c, "Negative multiplier"))

    # 30. Out-of-range row index
    c = copy.deepcopy(elem_branch_cert)
    node = c["tree"]
    while "children" in node:
        node = node["children"][0]
    kind = next(iter(node))
    node[kind][0][0] = 999999
    cases.append(("invalid_row_index", c, "Invalid row index"))

    # 31. Tightened false bound
    c = copy.deepcopy(elem_branch_cert)
    c["bound"] = str(parse_rational(c["bound"]) - Q(1, 1000))
    cases.append(("tightened_false_bound", c, "exceeds claimed bound"))

    # 32. Inflated primal D
    c = copy.deepcopy(elem_branch_cert)
    c["primal"]["D"] = str(parse_rational(c["primal"]["D"]) + Q(1, 100))
    cases.append(("inflated_primal_D", c, "Primal D="))

    # 33. Float multiplier rejected
    c = copy.deepcopy(elem_branch_cert)
    node = c["tree"]
    while "children" in node:
        node = node["children"][0]
    kind = next(iter(node))
    node[kind][0][1] = 0.5
    cases.append(("float_multiplier", c, "Unsupported rational type"))

    # 34. Duplicate multiplier row index rejected
    c = copy.deepcopy(elem_branch_cert)
    node = c["tree"]
    while "children" in node:
        node = node["children"][0]
    kind = next(iter(node))
    node[kind].append(list(node[kind][0]))
    cases.append(("duplicate_row_index", c, "Duplicate multiplier row index"))

    # 35. Non-canonical inflated primal Fourier coordinate A
    c = copy.deepcopy(elem_leaf_cert)
    c["primal"]["A"] = str(parse_rational(c["primal"].get("A", "0")) + Q(1, 1000))
    cases.append(("non_canonical_primal_F", c, "is not canonical F_canon"))

    # 36. Tier 2 full-cert corruptions if available (invalid cbp1 mode & invalid salb_f degree)
    if full_branch_cert is not None:
        c = copy.deepcopy(full_branch_cert)
        c["tree"] = {
            "split": {"type": "cbp1", "mode": "z", "i": 0, "j": 1, "k": 2, "p": 5, "e_i": [5], "j_mask": 0, "k_mask": 8},
            "children": [{"dual": []}] * 7,
        }
        cases.append(("cbp1_bad_mode", c, "Invalid cbp1 mode"))

        c = copy.deepcopy(full_branch_cert)
        c["tree"] = {
            "split": {"type": "cbp1", "mode": "b", "i": 0, "j": 1, "k": 2, "p": 5, "e_i": [5], "j_mask": 0, "k_mask": 8},
            "children": [{"dual": []}] * 6,
        }
        cases.append(("cbp1_b_wrong_children", c, "requires 5 children, got 6"))

        c = copy.deepcopy(full_branch_cert)
        c["tree"] = {
            "split": {"type": "salb_f", "i": 0, "d": 3},
            "children": [{"dual": []}] * 4,
        }
        cases.append(("salb_f_bad_degree", c, "Invalid salb_f degree"))

    for label, damaged, expected_msg in cases:
        try:
            verify_certificate(damaged, require_primal=True)
        except InvalidCertificate as exc:
            require(
                expected_msg in str(exc),
                f"Self-test '{label}' failed for wrong reason: got {exc!r}, expected substring {expected_msg!r}",
            )
            continue
        raise InvalidCertificate(f"Self-test FAILED: corruption '{label}' was wrongly accepted!")
    return len(cases)


def verify_manifest(cert_dir: Path, expected_names: Sequence[str]) -> int:
    manifest = cert_dir / "MANIFEST.sha256"
    require(manifest.exists(), f"Required manifest missing: {manifest}")
    seen: set[str] = set()
    for raw_line in manifest.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        require(len(parts) == 2, f"Malformed manifest line: {raw_line!r}")
        expected_hex, rel_name = parts
        require(
            len(expected_hex) == 64 and all(ch in "0123456789abcdef" for ch in expected_hex),
            f"Bad SHA-256 hex: {expected_hex!r}",
        )
        require(
            "/" not in rel_name and "\\" not in rel_name and ".." not in rel_name,
            f"Out-of-directory manifest entry: {rel_name!r}",
        )
        require(rel_name not in seen, f"Duplicate manifest entry: {rel_name}")
        seen.add(rel_name)
        target = cert_dir / rel_name
        require(target.exists(), f"Manifest target missing: {target}")
        actual_hex = hashlib.sha256(target.read_bytes()).hexdigest()
        require(
            actual_hex == expected_hex,
            f"SHA-256 mismatch for {rel_name}: expected {expected_hex}, got {actual_hex}",
        )
    expected_set = set(expected_names)
    require(
        seen == expected_set,
        f"Manifest file set mismatch: missing={sorted(expected_set - seen)}, extra={sorted(seen - expected_set)}",
    )
    return len(seen)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="*", type=Path)
    parser.add_argument("--all", action="store_true", help="Verify full pinned suite in certificates/ and MANIFEST.sha256")
    parser.add_argument("--self-test", action="store_true", help="Run adversarial corruption rejection tests")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    cert_dir = repo_root / "certificates"
    suite_mode = args.all or not args.certificates
    paths: List[Path] = sorted(cert_dir.glob("*.json")) if suite_mode else list(args.certificates)
    require(len(paths) > 0, f"No certificates found in {cert_dir}")

    if suite_mode:
        require(len(EXPECTED_SUITE) > 0, "EXPECTED_SUITE registry is empty")
        actual_names = {p.name for p in paths}
        expected_names = set(EXPECTED_SUITE)
        require(
            actual_names == expected_names,
            f"Certificate directory mismatch: missing={sorted(expected_names - actual_names)}, extra={sorted(actual_names - expected_names)}",
        )

    elem_leaf_cert: Optional[Dict[str, Any]] = None
    elem_branch_cert: Optional[Dict[str, Any]] = None
    full_branch_cert: Optional[Dict[str, Any]] = None
    verified_stats: Dict[str, Dict[str, Any]] = {}
    verified_primals: Dict[str, Dict[str, str]] = {}

    for path in paths:
        cert = json.loads(path.read_text())
        stats = verify_certificate(cert, require_primal=suite_mode)
        if suite_mode:
            verify_registry_binding(path.name, cert, stats)
            verified_stats[path.name] = stats
            verified_primals[path.name] = cert["primal"]
        if cert["config"]["tier"] == "elem":
            if "dual" in cert["tree"] and elem_leaf_cert is None:
                elem_leaf_cert = cert
            if "children" in cert["tree"] and elem_branch_cert is None:
                elem_branch_cert = cert
        elif cert["config"]["tier"] == "full":
            if "children" in cert["tree"] and full_branch_cert is None:
                full_branch_cert = cert

        print(
            f"PASS {path.name:44s} | {stats['tier']:4s} | a={stats['alpha']:4s} l={stats['lam']:5s} "
            f"| D={stats['bound']:12s} | br={stats['branches']:5d} hua={stats['hua_cuts']:3d} "
            f"dual={stats['dual_leaves']:5d} fk={stats['farkas_leaves']:3d} d={stats['max_depth']:3d} "
            f"| primal={stats['primal_disjunctions_checked']}"
        )

    if suite_mode:
        n_man = verify_manifest(cert_dir, [p.name for p in paths])
        print(f"PASS MANIFEST.sha256: verified {n_man} exact SHA-256 certificate digests")
        summary_path = repo_root / "results" / "frontier_summary_v4.json"
        n_sum = verify_summary_json(summary_path, verified_stats, verified_primals)
        print(f"PASS {summary_path.name}: verified {n_sum} consolidated summary entries")

    if args.self_test:
        require(
            elem_leaf_cert is not None and elem_branch_cert is not None,
            "Self-test requires both a single-leaf and a branching tier='elem' certificate",
        )
        n_tests = run_corruption_self_test(elem_leaf_cert, elem_branch_cert, full_branch_cert)
        print(f"PASS corruption self-test: 10 positive controls + {n_tests}/{n_tests} adversarial corruptions rejected")


if __name__ == "__main__":
    main()
