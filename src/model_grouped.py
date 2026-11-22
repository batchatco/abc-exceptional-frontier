#!/usr/bin/env python3
"""Direct-d0 grouped linear/disjunctive model (v4) for exceptional abc triples.

Canonical specification for fixed cutoff d0 >= 4 (31 variables for d0 = 6) with
exact dyadic pinning of the (d0+1)-full tail block n_tail = prod_{v_p(n) >= d0+1} p^{v_p(n)}.

Supports two strictly separated v4 certification tiers (plus an uncertified BLT
baseline for comparison tables):

  - Tier 1 (`tier="elem"`, 100% purely elementary -- zero Bombieri-Pila, zero Salberger):
      * Base inequalities: radical budget, per-letter radical identities, exact dyadic
        size bounds sigma_n <= s_n, exact tail excess W_n >= d0 * n_r, prime-saving
        Fourier inequalities (p <= d0), pair bounds, asymmetric Fourier L^4-L^4-L^2
        (`L442`), exact symmetry-breaking rows, and optional exact dyadic shell bounds
        sigma_b >= 1, sigma_c >= 1 (`exact_bc_shell`, valid under symmetry in {'none','bc'}).
      * Single-block elementary Hua (1938) Weyl-sum moments (`hua`: outer-interpolated
        L^6, L^8 for m >= 3; L^16 for m >= 4; L^32 for m >= 5) separated lazily as
        1-branch valid linear cutting planes.
      * Disjunctions:
          - `gon`:      BLT Prop. 4.1 Geometry of Numbers (2-way)
          - `cl`:       Self-thinning Congruence-Lattice disjunction (`stCL`, 2-way)
          - `coll_p`:   Prime-indexed cross-letter collision using explicit M_{i,p} (2-way)
          - `diffcl`:   Multi-block self-thinning difference lattice (2- or 3-way)
          - `qcoll`:    Cofactor-divisor collision, variants `ac` and `ap` (3-way)
          - `st_qcoll`: Self-thinned cofactor-divisor collision when sigma_k > sigma_i (4-way)
          - `modcoll`:  1- or 2-block modular cofactor collision on (Z/QZ)^x (3- or 5-way)
          - `modcoll3`: 3-block modular cofactor collision on (Z/QZ)^x with h1 == 1 (7-way)
          - `cop_elem`: Elementary Minkowski + Bezout + roots mod Z_k (3-way)

  - Tier 2 (`tier="full"`, elementary Tier 1 + 1D plane-curve & 2D diagonal-surface bounds):
      * `cbp1`:   Single-modulus Coppersmith + Jonquieres automorphism + 1D Salberger
                  (2023, Thm. 1.2) plane-curve count, modes `a` and `b` (7-way)
      * `salb_f`: Large-coefficient Salberger (2023, Cor. 6.5 / Thm. 3.16) diagonal-surface
                  fourth-moment bound directly on F_i for d in {4, 5, 6} (4-way)
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
import math
from typing import Any, Dict, List, Optional, Sequence, Tuple

from exact_simplex import BareissTableau, frac_row_to_int


LETTERS = ("a", "b", "c")

# Exact verified rational parameters (c1, c2, c3, c4) for Salberger (2023) Cor. 6.5 / Thm. 3.16
# on F_i for d in {4, 5, 6}:
#   c1 >= 3/sqrt(d), c2 <= 1/(d*sqrt(d)),
#   c3 >= 3/(2*sqrt(d)) + 2/(d-1), c4 <= 1/(2*d*sqrt(d)).
SALB_F_PARAMS: Dict[int, Tuple[Fraction, Fraction, Fraction, Fraction]] = {
    4: (Fraction(3, 2), Fraction(1, 8), Fraction(17, 12), Fraction(1, 16)),
    5: (Fraction(161, 120), Fraction(4, 45), Fraction(281, 240), Fraction(2, 45)),
    6: (Fraction(49, 40), Fraction(1, 15), Fraction(81, 80), Fraction(1, 30)),
}

for _d, (_c1, _c2, _c3, _c4) in SALB_F_PARAMS.items():
    assert _d * (_c1 ** 2) >= 9
    assert (_d ** 3) * (_c2 ** 2) <= 1
    _r3 = _c3 - Fraction(2, _d - 1)
    assert _r3 > 0 and 4 * _d * (_r3 ** 2) >= 9
    assert 4 * (_d ** 3) * (_c4 ** 2) <= 1


def primes_up_to(n: int) -> List[int]:
    out = []
    for p in range(2, n + 1):
        if all(p % d != 0 for d in range(2, math.isqrt(p) + 1)):
            out.append(p)
    return out


@dataclass(frozen=True)
class ModelConfig:
    d0: int = 6
    alpha: Fraction = Fraction(1)
    lam: Fraction = Fraction(1)
    tier: str = "full"  # "blt", "elem", or "full"
    symmetry: str = "none"  # "none", "bc" (bV <= cV), or "abc" (aV <= bV <= cV)
    exact_bc_shell: bool = False
    include_l442: bool = True
    include_cl: bool = True
    include_stcl: bool = True
    include_coll_p: bool = True
    include_diffcl: bool = True
    include_qcoll: bool = True
    include_st_qcoll: bool = True
    include_modcoll: bool = True
    include_modcoll3: bool = True
    include_hua: bool = True
    include_cop_elem: bool = True
    include_cbp1: bool = False
    include_salb_f: bool = False

    def __post_init__(self) -> None:
        if self.d0 < 4:
            raise ValueError(f"d0 must be >= 4, got {self.d0}")
        if not (Fraction(0) <= self.alpha <= Fraction(1)):
            raise ValueError(f"alpha must be in [0, 1], got {self.alpha}")
        if not (Fraction(0) < self.lam <= Fraction(1)):
            raise ValueError(f"lam must be in (0, 1], got {self.lam}")
        if self.tier not in ("blt", "elem", "full"):
            raise ValueError(f"Invalid tier: {self.tier}")
        if self.symmetry not in ("none", "bc", "abc"):
            raise ValueError(f"Invalid symmetry: {self.symmetry}")
        if self.symmetry == "abc":
            if self.alpha != Fraction(1):
                raise ValueError("symmetry='abc' requires alpha = 1")
            if self.exact_bc_shell:
                raise ValueError("exact_bc_shell=True is incompatible with symmetry='abc'")
        if self.include_stcl and not self.include_cl:
            raise ValueError("include_stcl=True requires include_cl=True")
        if self.tier == "elem":
            if self.include_cbp1 or self.include_salb_f:
                raise ValueError("tier='elem' strictly forbids include_cbp1 and include_salb_f")
        if self.tier == "blt":
            if any(
                (
                    self.include_l442,
                    self.include_cl,
                    self.include_stcl,
                    self.include_coll_p,
                    self.include_diffcl,
                    self.include_qcoll,
                    self.include_st_qcoll,
                    self.include_modcoll,
                    self.include_modcoll3,
                    self.include_hua,
                    self.include_cop_elem,
                    self.include_cbp1,
                    self.include_salb_f,
                    self.exact_bc_shell,
                )
            ):
                raise ValueError("tier='blt' allows only pair + L^3 + GoN")

    @classmethod
    def elem(
        cls,
        alpha: Fraction,
        lam: Fraction,
        symmetry: str,
        d0: int = 6,
        exact_bc_shell: Optional[bool] = None,
    ) -> "ModelConfig":
        if exact_bc_shell is None:
            exact_bc_shell = symmetry in ("none", "bc")
        return cls(
            d0=d0,
            alpha=alpha,
            lam=lam,
            tier="elem",
            symmetry=symmetry,
            exact_bc_shell=exact_bc_shell,
            include_l442=True,
            include_cl=True,
            include_stcl=True,
            include_coll_p=True,
            include_diffcl=True,
            include_qcoll=True,
            include_st_qcoll=True,
            include_modcoll=True,
            include_modcoll3=True,
            include_hua=True,
            include_cop_elem=True,
            include_cbp1=False,
            include_salb_f=False,
        )

    @classmethod
    def full(
        cls,
        alpha: Fraction,
        lam: Fraction,
        symmetry: str,
        d0: int = 6,
        exact_bc_shell: Optional[bool] = None,
    ) -> "ModelConfig":
        if exact_bc_shell is None:
            exact_bc_shell = symmetry in ("none", "bc")
        return cls(
            d0=d0,
            alpha=alpha,
            lam=lam,
            tier="full",
            symmetry=symmetry,
            exact_bc_shell=exact_bc_shell,
            include_l442=True,
            include_cl=True,
            include_stcl=True,
            include_coll_p=True,
            include_diffcl=True,
            include_qcoll=True,
            include_st_qcoll=True,
            include_modcoll=True,
            include_modcoll3=True,
            include_hua=True,
            include_cop_elem=True,
            include_cbp1=True,
            include_salb_f=True,
        )

    @classmethod
    def blt(
        cls,
        alpha: Fraction,
        lam: Fraction,
        symmetry: str,
        d0: int = 6,
    ) -> "ModelConfig":
        return cls(
            d0=d0,
            alpha=alpha,
            lam=lam,
            tier="blt",
            symmetry=symmetry,
            exact_bc_shell=False,
            include_l442=False,
            include_cl=False,
            include_stcl=False,
            include_coll_p=False,
            include_diffcl=False,
            include_qcoll=False,
            include_st_qcoll=False,
            include_modcoll=False,
            include_modcoll3=False,
            include_hua=False,
            include_cop_elem=False,
            include_cbp1=False,
            include_salb_f=False,
        )

    def to_metadata(self) -> Dict[str, object]:
        return {
            "d0": self.d0,
            "alpha": str(self.alpha),
            "lam": str(self.lam),
            "tier": self.tier,
            "symmetry": self.symmetry,
            "exact_bc_shell": self.exact_bc_shell,
            "include_l442": self.include_l442,
            "include_cl": self.include_cl,
            "include_stcl": self.include_stcl,
            "include_coll_p": self.include_coll_p,
            "include_diffcl": self.include_diffcl,
            "include_qcoll": self.include_qcoll,
            "include_st_qcoll": self.include_st_qcoll,
            "include_modcoll": self.include_modcoll,
            "include_modcoll3": self.include_modcoll3,
            "include_hua": self.include_hua,
            "include_cop_elem": self.include_cop_elem,
            "include_cbp1": self.include_cbp1,
            "include_salb_f": self.include_salb_f,
        }


class GroupedModel:
    """Canonical variable layout, base/shell rows, lazy Hua cuts, and n-way disjunctions."""

    def __init__(self, cfg: ModelConfig) -> None:
        self.cfg = cfg
        self.d0 = cfg.d0
        self.g = cfg.d0 + 1  # groups per letter: 1..d0, r
        self.primes = primes_up_to(self.d0)
        self.names: List[str] = []
        for let in LETTERS:
            for i in range(1, self.d0 + 1):
                self.names.append(f"{let}{i}")
            self.names.append(f"{let}r")
        self.names.extend(["aV", "bV", "cV", "A", "B", "C", "D", "Wa", "Wb", "Wc"])
        self.idx: Dict[str, int] = {nm: k for k, nm in enumerate(self.names)}
        self.nvar = len(self.names)

        self.V = [self.idx["aV"], self.idx["bV"], self.idx["cV"]]
        self.F = [self.idx["A"], self.idx["B"], self.idx["C"]]
        self.D = self.idx["D"]
        self.W = [self.idx["Wa"], self.idx["Wb"], self.idx["Wc"]]

        self.base_rows = self._build_base_rows()
        self.shell_rows = self._build_shell_rows()
        self.all_base_rows = self.base_rows + self.shell_rows
        self.objective = [Fraction(0)] * self.nvar
        self.objective[self.D] = Fraction(1)

        # Static subset templates
        self.mult_subs = {
            k: self._nonempty_subsets(list(range(k, self.d0 + 1, k)))
            for k in range(2, self.d0 + 1)
        }
        self.hl_pairs = [
            (h, ell)
            for h in range(1, self.d0 + 1)
            for ell in range(1, self.d0 + 1)
            if h != ell
            and not ((h == 1 and ell in (4, 6)) or (ell == 1 and h in (4, 6)))
        ]
        self.salb_f_ds = tuple(d for d in (4, 5, 6) if d <= self.d0)

        # Precompute lazy single-block Hua cutting planes (exact int + sparse terms)
        self.lazy_hua_entries: List[Tuple[Dict[str, Any], List[int], int, int, str, List[Tuple[int, int]]]] = []
        if cfg.include_hua:
            for i in range(3):
                for m in range(3, self.d0 + 1):
                    moments = [6, 8]
                    if m >= 4:
                        moments.append(16)
                    if m >= 5:
                        moments.append(32)
                    for mom in moments:
                        sp = {"type": "hua", "i": i, "m": m, "moment": mom}
                        vec, rhs, nm = self.hua_branches_frac(sp)[0]
                        ic, ir, sk = frac_row_to_int(vec, rhs)
                        sparse = [(col, cf) for col, cf in enumerate(ic) if cf != 0]
                        self.lazy_hua_entries.append((sp, ic, ir, sk, nm, sparse))

    def blk(self, letter: int, mult: int) -> int:
        return letter * self.g + (mult - 1)

    def rem(self, letter: int) -> int:
        return letter * self.g + self.d0

    def _row(self, terms: Dict[int, Fraction | int], rhs: Fraction | int, name: str):
        v = [Fraction(0)] * self.nvar
        for k, val in terms.items():
            v[k] += Fraction(val)
        return (v, Fraction(rhs), name)

    def add_sigma(self, vec: List[Fraction], letter: int, coeff: Fraction) -> None:
        for h in range(1, self.d0 + 1):
            vec[self.blk(letter, h)] += coeff * h
        vec[self.rem(letter)] += coeff
        vec[self.W[letter]] += coeff

    def add_mask(self, vec: List[Fraction], letter: int, mask: int, cm: Fraction, cq: Fraction) -> None:
        for h in range(1, self.d0 + 1):
            if mask & (1 << (h - 1)):
                vec[self.blk(letter, h)] += cm + cq * h
        if mask & (1 << self.d0):
            vec[self.rem(letter)] += cm + cq
            vec[self.W[letter]] += cq

    def _build_base_rows(self) -> List[Tuple[List[Fraction], Fraction, str]]:
        rows: List[Tuple[List[Fraction], Fraction, str]] = []
        cfg = self.cfg
        sizes = [cfg.alpha, Fraction(1), Fraction(1)]

        # 0. Total radical budget
        rows.append(self._row({self.V[0]: 1, self.V[1]: 1, self.V[2]: 1}, cfg.lam, "rad_total"))

        # Per-letter anatomy
        for l_idx, let in enumerate(LETTERS):
            id_terms = {self.blk(l_idx, i): Fraction(1) for i in range(1, self.d0 + 1)}
            id_terms[self.rem(l_idx)] = Fraction(1)
            id_terms[self.V[l_idx]] = Fraction(-1)
            rows.append(self._row(id_terms, 0, f"rad_id_pos_{let}"))
            rows.append(self._row({k: -v for k, v in id_terms.items()}, 0, f"rad_id_neg_{let}"))

            sz_terms = {self.blk(l_idx, i): Fraction(i) for i in range(1, self.d0 + 1)}
            sz_terms[self.rem(l_idx)] = Fraction(1)
            sz_terms[self.W[l_idx]] = Fraction(1)
            rows.append(self._row(sz_terms, sizes[l_idx], f"size_{let}"))

            rows.append(
                self._row({self.rem(l_idx): self.d0, self.W[l_idx]: -1}, 0, f"tail_weight_{let}")
            )

            for p in self.primes:
                p_terms = {
                    self.blk(l_idx, i): Fraction(1)
                    for i in range(p, self.d0 + 1, p)
                }
                p_terms[self.F[l_idx]] = Fraction(-1)
                rows.append(self._row(p_terms, 0, f"fourier_p{p}_{let}"))

        # Pair bounds
        for i, j in ((0, 1), (0, 2), (1, 2)):
            rows.append(
                self._row(
                    {self.D: 1, self.V[i]: -1, self.V[j]: -1},
                    0,
                    f"pair_{LETTERS[i]}{LETTERS[j]}",
                )
            )

        # Fourier bounds: asymmetric L^4-L^4-L^2 (default) or legacy L^3 (BLT baseline)
        if cfg.include_l442:
            for i, j, k in ((0, 1, 2), (0, 2, 1), (1, 2, 0)):
                rows.append(
                    self._row(
                        {
                            self.D: 4,
                            self.F[i]: 1,
                            self.F[j]: 1,
                            self.V[i]: -3,
                            self.V[j]: -3,
                            self.V[k]: -2,
                        },
                        0,
                        f"fourier_L442_{LETTERS[i]}{LETTERS[j]}",
                    )
                )
        else:
            rows.append(
                self._row(
                    {
                        self.F[0]: 1,
                        self.F[1]: 1,
                        self.F[2]: 1,
                        self.D: 6,
                        self.V[0]: -4,
                        self.V[1]: -4,
                        self.V[2]: -4,
                    },
                    0,
                    "fourier_L3",
                )
            )

        # Exact symmetry-breaking rows
        if cfg.symmetry in ("bc", "abc"):
            rows.append(self._row({self.V[1]: 1, self.V[2]: -1}, 0, "sym_bV_le_cV"))
        if cfg.symmetry == "abc":
            rows.append(self._row({self.V[0]: 1, self.V[1]: -1}, 0, "sym_aV_le_bV"))

        return rows

    def _build_shell_rows(self) -> List[Tuple[List[Fraction], Fraction, str]]:
        """Exact dyadic shell inequalities sigma_b >= 1 and sigma_c >= 1 (RHS = -1)."""
        if not self.cfg.exact_bc_shell:
            return []
        cuts: List[Tuple[List[Fraction], Fraction, str]] = []
        for l_idx, let in ((1, "b"), (2, "c")):
            vec = [Fraction(0)] * self.nvar
            self.add_sigma(vec, l_idx, Fraction(-1))
            cuts.append((vec, Fraction(-1), f"shell_ge1_{let}"))
        return cuts

    def canonical_f_values(self, point: Sequence[Fraction]) -> List[Fraction]:
        """Exact canonical minimum Fourier savings F_n forced by prime rows (+ salb_f in full tier)."""
        out: List[Fraction] = []
        for n in range(3):
            fn = max(
                (sum(point[self.blk(n, h)] for h in range(p, self.d0 + 1, p)) for p in self.primes),
                default=Fraction(0),
            )
            if self.cfg.include_salb_f:
                vn = point[self.V[n]]
                for d in self.salb_f_ds:
                    c1, c2, c3, c4 = SALB_F_PARAMS[d]
                    u = point[self.blk(n, d)]
                    s_ord = sum(h * point[self.blk(n, h)] for h in range(1, self.d0 + 1) if h != d)
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

    # ------------------------------------------------------------------
    # Branch construction (1-way lazy Hua + n-way disjunctions)
    # ------------------------------------------------------------------

    def hua_branches_frac(self, split: Dict[str, Any]):
        """1-branch single-block elementary Hua (1938) Weyl-sum inequality."""
        i = int(split["i"])
        m = int(split["m"])
        mom = int(split["moment"])
        j, k = [l for l in range(3) if l != i]
        if mom == 6:
            if m < 3:
                raise ValueError(f"Hua L6 requires m >= 3, got {m}")
            terms = {
                self.D: 12, self.F[i]: 1, self.F[j]: 1, self.F[k]: 1,
                self.blk(i, m): 3, self.V[i]: -11, self.V[j]: -7, self.V[k]: -7,
            }
        elif mom == 8:
            if m < 3:
                raise ValueError(f"Hua L8 requires m >= 3, got {m}")
            terms = {
                self.D: 16, self.F[j]: 1, self.F[k]: 1,
                self.blk(i, m): 6, self.V[i]: -16, self.V[j]: -9, self.V[k]: -9,
            }
        elif mom == 16:
            if m < 4:
                raise ValueError(f"Hua L16 requires m >= 4, got {m}")
            terms = {
                self.D: 32, self.F[j]: 1, self.F[k]: 1,
                self.blk(i, m): 8, self.V[i]: -32, self.V[j]: -17, self.V[k]: -17,
            }
        elif mom == 32:
            if m < 5:
                raise ValueError(f"Hua L32 requires m >= 5, got {m}")
            terms = {
                self.D: 64, self.F[j]: 1, self.F[k]: 1,
                self.blk(i, m): 10, self.V[i]: -64, self.V[j]: -33, self.V[k]: -33,
            }
        else:
            raise ValueError(f"Unsupported Hua moment: {mom}")
        return [self._row(terms, 0, f"hua{mom}_{LETTERS[i]}_m{m}")]

    def gon_branches_frac(self, masks: Sequence[int]):
        b0 = [Fraction(0)] * self.nvar
        b1 = [Fraction(0)] * self.nvar
        b0[self.D] = b1[self.D] = Fraction(1)
        for v in self.V:
            b0[v] = b1[v] = Fraction(-1)
        for l_idx, mask in enumerate(masks):
            for i in range(1, self.d0 + 1):
                if mask & (1 << (i - 1)):
                    b0[self.blk(l_idx, i)] += 1
                    b1[self.blk(l_idx, i)] -= (i - 1)
            if mask & (1 << self.d0):
                b0[self.rem(l_idx)] += 1
                b1[self.W[l_idx]] -= 1
        tag = f"gon_{masks[0]}_{masks[1]}_{masks[2]}"
        return [(b0, Fraction(0), tag + "_b0"), (b1, Fraction(-1), tag + "_b1")]

    def cl_branches_frac(self, split: Dict[str, Any]):
        tau = int(split["target"])
        k = int(split["k"])
        e1 = list(split["e1"])
        e2 = list(split["e2"])
        j_mask = int(split["j_mask"])
        others = [l for l in range(3) if l != tau]
        l1, l2 = others[0], others[1]

        b0 = [Fraction(0)] * self.nvar
        b1 = [Fraction(0)] * self.nvar
        b0[self.D] = b1[self.D] = Fraction(1)
        b0[self.V[l1]] = b1[self.V[l1]] = Fraction(-1)
        b0[self.V[l2]] = b1[self.V[l2]] = Fraction(-1)

        for m in e1:
            if m == 0:
                b0[self.rem(l1)] += 1
                b1[self.rem(l1)] += 1 - Fraction(1, k)
                b1[self.W[l1]] -= Fraction(1, k)
            else:
                b0[self.blk(l1, m)] += 1
                b1[self.blk(l1, m)] += 1 - Fraction(m, k)
        for m in e2:
            if m == 0:
                b0[self.rem(l2)] += 1
                b1[self.rem(l2)] += 1 - Fraction(1, k)
                b1[self.W[l2]] -= Fraction(1, k)
            else:
                b0[self.blk(l2, m)] += 1
                b1[self.blk(l2, m)] += 1 - Fraction(m, k)

        for i in range(1, self.d0 + 1):
            if j_mask & (1 << (i - 1)):
                b0[self.blk(tau, i)] -= 1
                b1[self.blk(tau, i)] += i - 1
        if j_mask & (1 << self.d0):
            b0[self.rem(tau)] -= 1
            b1[self.W[tau]] += 1

        if self.cfg.include_stcl:
            self.add_sigma(b1, tau, Fraction(-1))
            rhs1 = Fraction(-1)
        else:
            rhs1 = -(Fraction(1) - self.cfg.alpha) if tau == 0 else Fraction(0)
        tag = f"cl_t{tau}_k{k}_j{j_mask}"
        return [(b0, Fraction(0), tag + "_b0"), (b1, rhs1, tag + "_b1")]

    def coll_p_branches_frac(self, split: Dict[str, Any]):
        """Safe prime-indexed collision using explicit M_{i,p} = sum_{p|h} i_h (decoupled from F_i)."""
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        p = int(split["p"])
        p_mults = [h for h in range(p, self.d0 + 1, p)]
        tag = f"collp_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{p}"

        b0 = [Fraction(0)] * self.nvar
        b0[self.D] = Fraction(1)
        b0[self.V[i]] = Fraction(-1)
        b0[self.V[j]] = Fraction(-1)
        for h in p_mults:
            b0[self.blk(i, h)] = Fraction(1)

        b1 = [Fraction(0)] * self.nvar
        b1[self.D] = Fraction(2)
        b1[self.V[i]] = Fraction(-1)
        b1[self.V[j]] = Fraction(-1)
        b1[self.V[k]] = Fraction(-2)
        for h in p_mults:
            b1[self.blk(i, h)] = Fraction(1)
        return [(b0, Fraction(0), tag + "_b0"), (b1, Fraction(0), tag + "_b1")]

    def diffcl_branches_frac(self, split: Dict[str, Any]):
        """Multi-block self-thinning difference congruence-lattice disjunction (2- or 3-way)."""
        tau = int(split["target"])
        h = int(split["h"])
        ell = int(split["ell"])
        e1 = list(split["e1"])
        e2 = list(split["e2"])
        j_mask = int(split["j_mask"])
        thinned = bool(split.get("thinned", True))
        others = [l for l in range(3) if l != tau]
        l1, l2 = others[0], others[1]

        g = math.gcd(h, ell)
        s = h // g
        d = ell // g

        def base_f() -> List[Fraction]:
            vec = [Fraction(0)] * self.nvar
            vec[self.D] = Fraction(1)
            vec[self.V[l1]] = Fraction(-1)
            vec[self.V[l2]] = Fraction(-1)
            for m in e1:
                if m == 0:
                    vec[self.rem(l1)] += 1
                else:
                    vec[self.blk(l1, m)] += 1
            for m in e2:
                if m == 0:
                    vec[self.rem(l2)] += 1
                else:
                    vec[self.blk(l2, m)] += 1
            self.add_mask(vec, tau, j_mask, Fraction(-1), Fraction(0))
            return vec

        def add_size(vec: List[Fraction], letter: int, el: Sequence[int], coeff: Fraction) -> None:
            for m in el:
                if m == 0:
                    vec[self.rem(letter)] += coeff
                    vec[self.W[letter]] += coeff
                else:
                    vec[self.blk(letter, m)] += coeff * m

        tag = f"diffcl_t{tau}_h{h}l{ell}_j{j_mask}"
        b0 = base_f()

        b1 = base_f()
        add_size(b1, l1, e1, Fraction(-1, 2 * g))
        add_size(b1, l2, e2, Fraction(-1, 2 * g))
        self.add_mask(b1, tau, j_mask, Fraction(0), Fraction(1, 2))
        if thinned:
            self.add_sigma(b1, tau, Fraction(-1, 2))
            rhs1 = Fraction(-1, 2)
        else:
            rhs1 = Fraction(0)

        out = [(b0, Fraction(0), tag + "_b0"), (b1, rhs1, tag + "_b1")]
        if s == 1 or d == 1:
            b2 = base_f()
            if s == 1:
                add_size(b2, l1, e1, Fraction(-1, g))
                add_size(b2, l2, e2, Fraction(-1, 2 * g))
            else:
                add_size(b2, l1, e1, Fraction(-1, 2 * g))
                add_size(b2, l2, e2, Fraction(-1, g))
            self.add_mask(b2, tau, j_mask, Fraction(0), Fraction(1))
            if thinned:
                self.add_sigma(b2, tau, Fraction(-1))
                rhs2 = Fraction(-1)
            else:
                rhs2 = Fraction(0)
            out.append((b2, rhs2, tag + "_b2"))
        return out

    def qcoll_branches_frac(self, split: Dict[str, Any]):
        """Cofactor-divisor collision disjunction (3-way), variants 'ac' and 'ap'."""
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        p = int(split["p"])
        q_mask = int(split["q_mask"])
        m = int(split["m"])
        e_k = list(split["e_k"])
        var = split["variant"]
        p_mults = [h for h in range(p, self.d0 + 1, p)]

        def add_rp(vec: List[Fraction], coeff: Fraction) -> None:
            vec[self.V[i]] += coeff
            for h in p_mults:
                vec[self.blk(i, h)] -= coeff

        def add_mk_u(vec: List[Fraction], cm: Fraction, cu: Fraction) -> None:
            for h in e_k:
                if h == 0:
                    vec[self.rem(k)] += cm + cu
                    vec[self.W[k]] += cu
                else:
                    vec[self.blk(k, h)] += cm + cu * Fraction(h, m)

        tag = f"qcoll_{var}_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{p}_q{q_mask}_m{m}"

        b0 = [Fraction(0)] * self.nvar
        b0[self.D] = Fraction(1)
        add_rp(b0, Fraction(-1))
        b0[self.V[j]] -= 1

        if var == "ac":
            b1 = [Fraction(0)] * self.nvar
            b1[self.D] = Fraction(2)
            add_rp(b1, Fraction(-1))
            b1[self.V[j]] -= 1
            self.add_mask(b1, i, q_mask, Fraction(-1), Fraction(1))
            b1[self.V[k]] -= 2
            add_mk_u(b1, Fraction(2), Fraction(-2))

            b2 = [Fraction(0)] * self.nvar
            b2[self.D] = Fraction(4)
            b2[self.V[i]] -= 3
            for h in p_mults:
                b2[self.blk(i, h)] += 1
            b2[self.V[j]] -= 2
            self.add_mask(b2, i, q_mask, Fraction(-1), Fraction(0))
            b2[self.V[k]] -= 3
            add_mk_u(b2, Fraction(3), Fraction(-1))
            return [(b0, Fraction(0), tag + "_b0"), (b1, Fraction(0), tag + "_b1"), (b2, Fraction(0), tag + "_b2")]

        if var == "ap":
            b1 = [Fraction(0)] * self.nvar
            b1[self.D] = Fraction(2)
            add_rp(b1, Fraction(-1))
            b1[self.V[j]] -= 1
            self.add_mask(b1, i, q_mask, Fraction(-1), Fraction(0))
            b1[self.V[k]] -= 2
            add_mk_u(b1, Fraction(1), Fraction(0))

            b2 = [Fraction(0)] * self.nvar
            b2[self.D] = Fraction(2)
            add_rp(b2, Fraction(-1))
            b2[self.V[j]] -= 1
            self.add_mask(b2, i, q_mask, Fraction(-1), Fraction(1))
            b2[self.V[k]] -= 2
            add_mk_u(b2, Fraction(1), Fraction(-1))
            return [(b0, Fraction(0), tag + "_b0"), (b1, Fraction(0), tag + "_b1"), (b2, Fraction(0), tag + "_b2")]

        raise ValueError(f"Unknown qcoll variant: {var}")

    def st_qcoll_branches_frac(self, split: Dict[str, Any]):
        """Self-thinned cofactor-divisor collision when sigma_k > sigma_i (4-way)."""
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        var = split["variant"]
        base_brs = self.qcoll_branches_frac(split)
        tag = f"st_qcoll_{var}_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{split['p']}_q{split['q_mask']}_m{split['m']}"

        b_deg = [Fraction(0)] * self.nvar
        self.add_sigma(b_deg, k, Fraction(1))
        self.add_sigma(b_deg, i, Fraction(-1))
        out = [(b_deg, Fraction(0), tag + "_bdeg")]

        for idx_b, (vec, rhs, _) in enumerate(base_brs):
            v_copy = list(vec)
            if (var == "ac" and idx_b == 1) or (var == "ap" and idx_b == 2):
                self.add_sigma(v_copy, k, Fraction(1))
                self.add_sigma(v_copy, i, Fraction(-1))
            out.append((v_copy, rhs, f"{tag}_b{idx_b}"))
        return out

    def modcoll_branches_frac(self, split: Dict[str, Any]):
        """1- or 2-block modular cofactor collision on (Z/QZ)^x (3- or 5-way)."""
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        p = int(split["p"])
        q_mask = int(split["q_mask"])
        blocks = [int(x) for x in split["blocks"]]
        p_mults = [h for h in range(p, self.d0 + 1, p)]

        def add_g(vec: List[Fraction], coeff: Fraction) -> None:
            vec[self.V[i]] += coeff
            for h in p_mults:
                vec[self.blk(i, h)] -= coeff
            vec[self.V[j]] += coeff

        tag = f"modcoll_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{p}_q{q_mask}_b{''.join(map(str, blocks))}"
        b0 = [Fraction(0)] * self.nvar
        b0[self.D] = Fraction(1)
        add_g(b0, Fraction(-1))
        out = [(b0, Fraction(0), tag + "_b0")]

        if len(blocks) == 1:
            h1 = blocks[0]
            for idx_b, use_q in enumerate((True, False), start=1):
                vec = [Fraction(0)] * self.nvar
                vec[self.D] = Fraction(2)
                vec[self.V[k]] = Fraction(-2)
                add_g(vec, Fraction(-1))
                self.add_mask(vec, i, q_mask, Fraction(-1), Fraction(1) if use_q else Fraction(0))
                if not use_q:
                    vec[self.blk(k, h1)] += Fraction(1)
                out.append((vec, Fraction(0), f"{tag}_b{idx_b}"))
        elif len(blocks) == 2:
            h1, h2 = blocks[0], blocks[1]
            idx_b = 1
            for u1_q in (True, False):
                for u2_q in (True, False):
                    vec = [Fraction(0)] * self.nvar
                    vec[self.D] = Fraction(4)
                    vec[self.V[k]] = Fraction(-4)
                    add_g(vec, Fraction(-2))
                    cq = Fraction((1 if u1_q else 0) + (1 if u2_q else 0))
                    self.add_mask(vec, i, q_mask, Fraction(-2), cq)
                    if not u1_q:
                        vec[self.blk(k, h1)] += Fraction(2)
                    if not u2_q:
                        vec[self.blk(k, h2)] += Fraction(2)
                    out.append((vec, Fraction(0), f"{tag}_b{idx_b}"))
                    idx_b += 1
        else:
            raise ValueError(f"modcoll requires 1 or 2 blocks, got {blocks}")
        return out

    def modcoll3_branches_frac(self, split: Dict[str, Any]):
        """3-block modular cofactor collision on (Z/QZ)^x with STRICT h1 == 1 (7-way)."""
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        p = int(split["p"])
        q_mask = int(split["q_mask"])
        h1, h2, h3 = [int(x) for x in split["blocks"]]
        if h1 != 1:
            raise ValueError(f"modcoll3 strictly requires blocks[0] == 1, got {h1}")
        p_mults = [h for h in range(p, self.d0 + 1, p)]

        def add_g(vec: List[Fraction], coeff: Fraction) -> None:
            vec[self.V[i]] += coeff
            for h in p_mults:
                vec[self.blk(i, h)] -= coeff
            vec[self.V[j]] += coeff

        tag = f"modcoll3_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{p}_q{q_mask}_b{h1}{h2}{h3}"
        b0 = [Fraction(0)] * self.nvar
        b0[self.D] = Fraction(1)
        add_g(b0, Fraction(-1))
        out = [(b0, Fraction(0), tag + "_b0")]

        idx_b = 1
        for a_mode in ("u2", "q"):
            for b_mode in ("q", "u1u3", "u1q"):
                vec = [Fraction(0)] * self.nvar
                vec[self.D] = Fraction(16)
                vec[self.V[k]] = Fraction(-16)
                add_g(vec, Fraction(-8))
                cq = Fraction(0)
                if a_mode == "u2":
                    vec[self.blk(k, h2)] += Fraction(8)
                else:
                    cq += Fraction(4)
                if b_mode == "q":
                    cq += Fraction(4)
                elif b_mode == "u1u3":
                    vec[self.blk(k, h1)] += Fraction(8)
                    vec[self.blk(k, h3)] += Fraction(4)
                else:
                    vec[self.blk(k, h1)] += Fraction(8)
                    cq += Fraction(2)
                self.add_mask(vec, i, q_mask, Fraction(-8), cq)
                out.append((vec, Fraction(0), f"{tag}_b{idx_b}"))
                idx_b += 1
        return out

    def cop_elem_branches_frac(self, split: Dict[str, Any]):
        """Elementary Minkowski + Bezout + roots mod Z_k disjunction (3-way, zero BP)."""
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        p = int(split["p"])
        e_i = list(split["e_i"])
        j_mask = int(split["j_mask"])
        k_mask = int(split["k_mask"])
        tag = f"copelem_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{p}_j{j_mask}_k{k_mask}"

        bdeg = [Fraction(0)] * self.nvar
        self.add_mask(bdeg, j, j_mask, Fraction(0), Fraction(1))
        self.add_mask(bdeg, k, k_mask, Fraction(0), Fraction(1))
        self.add_sigma(bdeg, j, Fraction(-1))

        b1 = [Fraction(0)] * self.nvar
        b1[self.D] = Fraction(1)
        b1[self.V[i]] -= Fraction(1)
        for h in e_i:
            b1[self.blk(i, h)] += Fraction(1)
        self.add_mask(b1, j, j_mask, Fraction(-1), Fraction(1))
        self.add_mask(b1, k, k_mask, Fraction(-1), Fraction(0))
        self.add_sigma(b1, j, Fraction(-1))

        b2 = [Fraction(0)] * self.nvar
        b2[self.D] = Fraction(1)
        b2[self.V[i]] -= Fraction(1)
        for h in e_i:
            b2[self.blk(i, h)] += Fraction(1) - Fraction(h, p)
        self.add_mask(b2, j, j_mask, Fraction(-1), Fraction(p + 1, p))
        self.add_mask(b2, k, k_mask, Fraction(-1), Fraction(1, p))
        self.add_sigma(b2, j, Fraction(-(p + 1), p))

        return [(bdeg, Fraction(0), tag + "_deg"), (b1, Fraction(0), tag + "_b1"), (b2, Fraction(0), tag + "_b2")]

    def cbp1_branches_frac(self, split: Dict[str, Any]):
        """Single-modulus Coppersmith + Jonquieres automorphism + 1D Salberger Thm. 1.2.

        mode='a' (7 branches): E_curve = max(s_0/p, ell/p, t_0/p)
        mode='b' (5 branches): E_curve = max(s_0/p, ((p-1)/p^2)*t_0 + ell/p) (subsumes ell/p)
        """
        i, j, k = int(split["i"]), int(split["j"]), int(split["k"])
        p = int(split["p"])
        e_i = list(split["e_i"])
        j_mask = int(split["j_mask"])
        k_mask = int(split["k_mask"])
        mode = split["mode"]
        if mode not in ("a", "b"):
            raise ValueError(f"Invalid cbp1 mode: {mode}")

        def add_f_ux(vec: List[Fraction], cf: Fraction, cux: Fraction) -> None:
            vec[self.V[i]] += cf
            for h in e_i:
                vec[self.blk(i, h)] += -cf + cux * Fraction(h, p)
            self.add_mask(vec, j, j_mask, cf, Fraction(0))
            self.add_mask(vec, k, k_mask, cf, Fraction(0))

        def add_ell(vec: List[Fraction], c_idx: int, coeff: Fraction) -> None:
            if c_idx == 1:
                for h in e_i:
                    vec[self.blk(i, h)] += coeff * Fraction(h, p)
            else:
                self.add_mask(vec, j, j_mask, Fraction(0), coeff * Fraction(1, p))
                self.add_mask(vec, k, k_mask, Fraction(0), coeff * Fraction(1, p))
                self.add_sigma(vec, j, -coeff * Fraction(1, p))

        tag = f"cbp1{mode}_{LETTERS[i]}{LETTERS[j]}{LETTERS[k]}_p{p}_j{j_mask}_k{k_mask}"
        out = []

        bj = [Fraction(0)] * self.nvar
        self.add_mask(bj, j, j_mask, Fraction(0), Fraction(1))
        self.add_mask(bj, k, k_mask, Fraction(0), Fraction(1))
        self.add_sigma(bj, j, Fraction(-1))
        out.append((bj, Fraction(0), tag + "_deg"))

        for c_idx in (1, 2):
            v1 = [Fraction(0)] * self.nvar
            v1[self.D] = Fraction(1)
            add_f_ux(v1, Fraction(-1), Fraction(-1))
            add_ell(v1, c_idx, Fraction(1))
            self.add_sigma(v1, j, Fraction(-1, p))
            self.add_mask(v1, j, j_mask, Fraction(0), Fraction(1, p))
            out.append((v1, Fraction(0), f"{tag}_c{c_idx}m1"))

            if mode == "a":
                v2 = [Fraction(0)] * self.nvar
                v2[self.D] = Fraction(1)
                add_f_ux(v2, Fraction(-1), Fraction(-1))
                add_ell(v2, c_idx, Fraction(p - 1, p))
                out.append((v2, Fraction(0), f"{tag}_c{c_idx}m2"))

            v3 = [Fraction(0)] * self.nvar
            v3[self.D] = Fraction(1)
            add_f_ux(v3, Fraction(-1), Fraction(-1))
            if mode == "a":
                add_ell(v3, c_idx, Fraction(1))
                self.add_sigma(v3, k, Fraction(-1, p))
                self.add_mask(v3, k, k_mask, Fraction(0), Fraction(1, p))
            else:
                add_ell(v3, c_idx, Fraction(p - 1, p))
                self.add_sigma(v3, k, Fraction(-(p - 1), p * p))
                self.add_mask(v3, k, k_mask, Fraction(0), Fraction(p - 1, p * p))
            out.append((v3, Fraction(0), f"{tag}_c{c_idx}m3"))

        return out

    def salb_f_branches_frac(self, split: Dict[str, Any]):
        """4-branch large-coefficient Salberger (2023) Cor. 6.5 / Thm. 3.16 directly on F_i."""
        i = int(split["i"])
        d = int(split["d"])
        c1, c2, c3, c4 = SALB_F_PARAMS[d]
        tag = f"salbf_d{d}_{LETTERS[i]}"

        def add_sord(vec: List[Fraction], coeff: Fraction) -> None:
            for h in range(1, self.d0 + 1):
                if h != d:
                    vec[self.blk(i, h)] += coeff * h

        b0 = [Fraction(0)] * self.nvar
        b0[self.V[i]] = Fraction(1)
        b0[self.F[i]] = Fraction(-1)

        b1 = [Fraction(0)] * self.nvar
        b1[self.blk(i, d)] = Fraction(3)
        b1[self.V[i]] = Fraction(-1)
        b1[self.F[i]] = Fraction(-1)

        b2 = [Fraction(0)] * self.nvar
        b2[self.blk(i, d)] = Fraction(4) - c1
        add_sord(b2, c2)
        b2[self.V[i]] = Fraction(-1)
        b2[self.F[i]] = Fraction(-1)

        b3 = [Fraction(0)] * self.nvar
        b3[self.blk(i, d)] = Fraction(4) - c3
        add_sord(b3, c4)
        b3[self.V[i]] = Fraction(-1)
        b3[self.F[i]] = Fraction(-1)

        return [
            (b0, Fraction(0), tag + "_b0"),
            (b1, Fraction(0), tag + "_b1"),
            (b2, Fraction(0), tag + "_b2"),
            (b3, Fraction(0), tag + "_b3"),
        ]

    def split_branches_frac(self, split: Dict[str, Any]):
        kind = split["type"]
        if kind == "hua":
            return self.hua_branches_frac(split)
        if kind == "gon":
            return self.gon_branches_frac(split["masks"])
        if kind == "cl":
            return self.cl_branches_frac(split)
        if kind == "coll_p":
            return self.coll_p_branches_frac(split)
        if kind == "diffcl":
            return self.diffcl_branches_frac(split)
        if kind == "qcoll":
            return self.qcoll_branches_frac(split)
        if kind == "st_qcoll":
            return self.st_qcoll_branches_frac(split)
        if kind == "modcoll":
            return self.modcoll_branches_frac(split)
        if kind == "modcoll3":
            return self.modcoll3_branches_frac(split)
        if kind == "cop_elem":
            return self.cop_elem_branches_frac(split)
        if kind == "cbp1":
            return self.cbp1_branches_frac(split)
        if kind == "salb_f":
            return self.salb_f_branches_frac(split)
        raise ValueError(f"Unknown split type: {kind}")

    def split_branches_int(self, split: Dict[str, Any]):
        out = []
        for c, r, nm in self.split_branches_frac(split):
            ic, ir, sk = frac_row_to_int(c, r)
            out.append((ic, ir, sk, nm))
        return out

    # ------------------------------------------------------------------
    # Lazy Hua separation & tightening
    # ------------------------------------------------------------------

    def find_most_violated_hua(
        self, nums: Sequence[int], det: int
    ) -> Tuple[Optional[Dict[str, Any]], Optional[Tuple[List[int], int, int, str]]]:
        """Return (split_dict, int_cut_tuple) for the most-violated single-block Hua row, or (None, None)."""
        if not self.lazy_hua_entries:
            return None, None
        best_lhs = 0
        best_d = 1
        best_item = None
        for sp, ic, ir, sk, nm, sparse in self.lazy_hua_entries:
            lhs = 0
            for col, cf in sparse:
                lhs += cf * nums[col]
            if lhs > 0:
                d_cf = ic[self.D]
                if best_item is None or lhs * best_d > best_lhs * d_cf:
                    best_lhs = lhs
                    best_d = d_cf
                    best_item = (sp, (ic, ir, sk, nm))
        if best_item is None:
            return None, None
        return best_item

    def tighten_lazy_hua(self, tab: BareissTableau) -> str:
        """Apply all violated lazy single-block Hua cuts in-place (for solve_exact_optimum / diving)."""
        if not self.lazy_hua_entries:
            return "optimal"
        while True:
            _, cut = self.find_most_violated_hua(tab.primal_numerators(), tab.det)
            if cut is None:
                return "optimal"
            st = tab.add_int_cut_and_resolve(*cut)
            if st != "optimal":
                return st

    # ------------------------------------------------------------------
    # Exact fast separation (pure-integer inner loops, zero float)
    # ------------------------------------------------------------------

    @staticmethod
    def _nonempty_subsets(items: Sequence[int]) -> List[List[int]]:
        out: List[List[int]] = []
        for r in range(1, len(items) + 1):
            for comb in combinations(items, r):
                out.append(list(comb))
        return out

    def find_top_violated_splits(
        self, nums: Sequence[int], det: int
    ) -> List[Tuple[Fraction, Dict[str, Any]]]:
        """Return the most-violated disjunction from each active family (sorted descending)."""
        cfg = self.cfg
        best_by_fam: Dict[str, Tuple[Fraction, Dict[str, Any]]] = {}

        def offer(fam: str, viol: Fraction, sp: Dict[str, Any]) -> None:
            if viol <= 0:
                return
            cur = best_by_fam.get(fam)
            if cur is None or viol > cur[0]:
                best_by_fam[fam] = (viol, sp)

        D_num = nums[self.D]
        V_nums = [nums[v] for v in self.V]
        F_nums = [nums[f] for f in self.F]
        L_num = V_nums[0] + V_nums[1] + V_nums[2]
        DL_num = D_num - L_num

        sigma_nums = [
            sum(h * nums[self.blk(l, h)] for h in range(1, self.d0 + 1))
            + nums[self.rem(l)]
            + nums[self.W[l]]
            for l in range(3)
        ]

        # Precompute per-letter active masks
        g_masses: List[List[int]] = []
        g_sizes: List[List[int]] = []
        active_tau: List[List[Tuple[int, int, int]]] = []
        active_gon: List[List[Tuple[int, int, int]]] = []
        div_lists_nonempty: List[List[Tuple[int, int, int]]] = []
        div_lists_with_empty: List[List[Tuple[int, int, int]]] = []

        for l_idx in range(3):
            g_mass = [nums[self.blk(l_idx, i)] for i in range(1, self.d0 + 1)] + [nums[self.rem(l_idx)]]
            g_size = [i * nums[self.blk(l_idx, i)] for i in range(1, self.d0 + 1)] + [
                nums[self.rem(l_idx)] + nums[self.W[l_idx]]
            ]
            g_exc = [(i - 1) * nums[self.blk(l_idx, i)] for i in range(1, self.d0 + 1)] + [
                nums[self.W[l_idx]]
            ]
            g_masses.append(g_mass)
            g_sizes.append(g_size)

            act_t = [g for g in range(self.g) if g_mass[g] != 0 or g_size[g] != 0]
            masks_t: List[Tuple[int, int, int]] = []
            for bits in range(1, 1 << len(act_t)):
                mk = 0
                ms = 0
                sz = 0
                for bi, g in enumerate(act_t):
                    if bits & (1 << bi):
                        mk |= 1 << g
                        ms += g_mass[g]
                        sz += g_size[g]
                masks_t.append((mk, ms, sz))
            active_tau.append(masks_t)

            act_g = [g for g in range(1, self.g) if g_mass[g] != 0 or g_exc[g] != 0]
            m0 = g_mass[0]
            masks_g: List[Tuple[int, int, int]] = []
            for bits in range(1 << len(act_g)):
                mk = 1
                ms = m0
                ex = 0
                for bi, g in enumerate(act_g):
                    if bits & (1 << bi):
                        mk |= 1 << g
                        ms += g_mass[g]
                        ex += g_exc[g]
                masks_g.append((mk, ms, ex))
            active_gon.append(masks_g)

            act_d = [g for g in range(1, self.g) if g_mass[g] != 0 or g_size[g] != 0]
            dl: List[Tuple[int, int, int]] = []
            for bits in range(1, 1 << len(act_d)):
                mk = 0
                ms = 0
                sz = 0
                for bi, g in enumerate(act_d):
                    if bits & (1 << bi):
                        mk |= 1 << g
                        ms += g_mass[g]
                        sz += g_size[g]
                dl.append((mk, ms, sz))
            div_lists_nonempty.append(dl)
            div_lists_with_empty.append([(0, 0, 0)] + dl)

        # 1. BLT Geometry of Numbers (GoN)
        ma_list, mb_list, mc_list = active_gon
        max_b_m = max(x[1] for x in mb_list)
        max_c_m = max(x[1] for x in mc_list)
        best_gon_v = 0
        best_gon_sp = None
        for mka, ma, ea in ma_list:
            if DL_num + ma + max_b_m + max_c_m <= 0:
                continue
            rem_e_a = DL_num - ea + det
            if rem_e_a <= 0:
                continue
            for mkb, mb, eb in mb_list:
                if DL_num + ma + mb + max_c_m <= 0:
                    continue
                rem_e_ab = rem_e_a - eb
                if rem_e_ab <= 0:
                    continue
                base_mab = DL_num + ma + mb
                for mkc, mc, ec in mc_list:
                    v0 = base_mab + mc
                    if v0 <= 0:
                        continue
                    v1 = rem_e_ab - ec
                    if v1 <= 0:
                        continue
                    vm = v0 if v0 < v1 else v1
                    if vm > best_gon_v:
                        best_gon_v = vm
                        best_gon_sp = {"type": "gon", "masks": [mka, mkb, mkc]}
        if best_gon_sp is not None:
            offer("gon", Fraction(best_gon_v, det), best_gon_sp)

        # 2. Congruence-Lattice & Self-Thinning Parallelogram (CL / stCL)
        if cfg.include_cl:
            stcl = cfg.include_stcl
            one_minus_a = Fraction(1) - cfg.alpha
            oma_n, oma_d = one_minus_a.numerator, one_minus_a.denominator
            cl_j_lists = {}
            for tau in range(3):
                jl = [(mk, mj, sj) for (mk, mj, sj) in active_tau[tau] if (mk & 1) == 0]
                if stcl or (tau == 0 and one_minus_a > 0):
                    jl.append((0, 0, 0))
                cl_j_lists[tau] = jl

            for k in range(2, self.d0 + 1):
                e_subs = self.mult_subs[k]
                for tau in range(3):
                    j_list = cl_j_lists[tau]
                    if not j_list:
                        continue
                    others = [l for l in range(3) if l != tau]
                    l1, l2 = others[0], others[1]
                    base = D_num - V_nums[l1] - V_nums[l2]
                    s1_list = [([], 0, 0)]
                    for e1 in e_subs:
                        m1 = sum(nums[self.blk(l1, m)] for m in e1)
                        if m1 != 0:
                            s1_list.append((e1, m1, sum(m * nums[self.blk(l1, m)] for m in e1)))
                    s2_list = [([], 0, 0)]
                    for e2 in e_subs:
                        m2 = sum(nums[self.blk(l2, m)] for m in e2)
                        if m2 != 0:
                            s2_list.append((e2, m2, sum(m * nums[self.blk(l2, m)] for m in e2)))
                    if len(s1_list) == 1 and len(s2_list) == 1:
                        continue
                    sig_shift = k * (det - sigma_nums[tau])
                    for e1, m1, s1 in s1_list:
                        for e2, m2, s2 in s2_list:
                            if not e1 and not e2:
                                continue
                            b0_pre = base + m1 + m2
                            s12 = s1 + s2
                            for mk, mj, sj in j_list:
                                v0 = b0_pre - mj
                                if v0 <= 0:
                                    continue
                                if stcl:
                                    v1_k = k * v0 - s12 + k * sj + sig_shift
                                    if v1_k <= 0:
                                        continue
                                    viol = min(Fraction(v0, det), Fraction(v1_k, k * det))
                                elif tau == 0 and oma_n > 0:
                                    v1_sc = oma_d * (k * v0 - s12 + k * sj) + k * oma_n * det
                                    if v1_sc <= 0:
                                        continue
                                    viol = min(Fraction(v0, det), Fraction(v1_sc, k * oma_d * det))
                                else:
                                    v1_k = k * v0 - s12 + k * sj
                                    if v1_k <= 0:
                                        continue
                                    viol = min(Fraction(v0, det), Fraction(v1_k, k * det))
                                offer(
                                    f"cl_k{k}",
                                    viol,
                                    {"type": "cl", "target": tau, "k": k, "e1": e1, "e2": e2, "j_mask": mk},
                                )

            # k == 1 (including e1 = [] or e2 = [] so separation matches exhaustive primal verification 100%)
            for tau in range(3):
                j_list = cl_j_lists[tau]
                if not j_list:
                    continue
                others = [l for l in range(3) if l != tau]
                l1, l2 = others[0], others[1]
                base = D_num - V_nums[l1] - V_nums[l2]
                sig_shift1 = det - sigma_nums[tau]
                subs = []
                for l_cur in (l1, l2):
                    m_base = nums[self.blk(l_cur, 1)]
                    items = [i for i in range(2, self.d0 + 1) if nums[self.blk(l_cur, i)] != 0]
                    if nums[self.rem(l_cur)] != 0 or nums[self.W[l_cur]] != 0:
                        items.append(0)
                    cur_s = [([], 0, 0), ([1], m_base, 0)]
                    for r in range(1, len(items) + 1):
                        for comb in combinations(items, r):
                            ms = m_base + sum(
                                nums[self.rem(l_cur)] if m == 0 else nums[self.blk(l_cur, m)]
                                for m in comb
                            )
                            ex = sum(
                                nums[self.W[l_cur]] if m == 0 else (m - 1) * nums[self.blk(l_cur, m)]
                                for m in comb
                            )
                            cur_s.append(([1] + list(comb), ms, ex))
                    subs.append(cur_s)
                min_mj = min(x[1] for x in j_list)
                max_ej = max(x[2] - x[1] for x in j_list)
                max_m2 = max(x[1] for x in subs[1])
                for e1, m1, ex1 in subs[0]:
                    if base + m1 + max_m2 - min_mj <= 0:
                        continue
                    for e2, m2, ex2 in subs[1]:
                        if not e1 and not e2:
                            continue
                        b0_pre = base + m1 + m2
                        if b0_pre - min_mj <= 0:
                            continue
                        b1_pre = base - ex1 - ex2
                        if stcl:
                            if b1_pre + max_ej + sig_shift1 <= 0:
                                continue
                        elif tau == 0 and oma_n > 0:
                            if oma_d * (b1_pre + max_ej) + oma_n * det <= 0:
                                continue
                        else:
                            if b1_pre + max_ej <= 0:
                                continue
                        for mk, mj, sj in j_list:
                            v0 = b0_pre - mj
                            if v0 <= 0:
                                continue
                            ej = sj - mj
                            if stcl:
                                v1 = b1_pre + ej + sig_shift1
                                if v1 <= 0:
                                    continue
                                viol = min(Fraction(v0, det), Fraction(v1, det))
                            elif tau == 0 and oma_n > 0:
                                v1_sc = oma_d * (b1_pre + ej) + oma_n * det
                                if v1_sc <= 0:
                                    continue
                                viol = min(Fraction(v0, det), Fraction(v1_sc, oma_d * det))
                            else:
                                v1 = b1_pre + ej
                                if v1 <= 0:
                                    continue
                                viol = min(Fraction(v0, det), Fraction(v1, det))
                            offer(
                                "cl_k1",
                                viol,
                                {"type": "cl", "target": tau, "k": 1, "e1": e1, "e2": e2, "j_mask": mk},
                            )

        # Shared precomputations for prime-indexed collision families
        need_pq = cfg.include_coll_p or cfg.include_qcoll or cfg.include_st_qcoll or cfg.include_modcoll or cfg.include_modcoll3
        mp_table: Dict[Tuple[int, int], int] = {}
        q_lists_all: Dict[Tuple[int, int], List[Tuple[int, int, int]]] = {}
        q_lists_pos: Dict[Tuple[int, int], List[Tuple[int, int, int]]] = {}
        if need_pq:
            for i in range(3):
                g_mass = g_masses[i]
                g_size = g_sizes[i]
                for p in self.primes:
                    mp = sum(nums[self.blk(i, h)] for h in range(p, self.d0 + 1, p))
                    mp_table[(i, p)] = mp
                    if mp == 0:
                        continue
                    act = [
                        g for g in range(1, self.g)
                        if (g == self.d0 or ((g + 1) % p != 0)) and (g_mass[g] != 0 or g_size[g] != 0)
                    ]
                    ql_all = [(0, 0, 0)]
                    ql_pos = []
                    for bits in range(1, 1 << len(act)):
                        mk = 0
                        ms = 0
                        sz = 0
                        for bi, g in enumerate(act):
                            if bits & (1 << bi):
                                mk |= 1 << g
                                ms += g_mass[g]
                                sz += g_size[g]
                        ql_all.append((mk, ms, sz))
                        if sz > ms:
                            ql_pos.append((mk, ms, sz))
                    q_lists_all[(i, p)] = ql_all
                    q_lists_pos[(i, p)] = ql_pos

        # 3. Safe prime-indexed cross-letter collision (coll_p)
        if cfg.include_coll_p:
            for i in range(3):
                for p in self.primes:
                    mp = mp_table[(i, p)]
                    if mp == 0:
                        continue
                    ri = V_nums[i] - mp
                    for j in range(3):
                        if j == i:
                            continue
                        k = 3 - i - j
                        v0 = D_num - ri - V_nums[j]
                        if v0 <= 0:
                            continue
                        v1_2 = 2 * D_num - 2 * V_nums[k] - ri - V_nums[j]
                        if v1_2 <= 0:
                            continue
                        viol = min(Fraction(v0, det), Fraction(v1_2, 2 * det))
                        offer("coll_p", viol, {"type": "coll_p", "i": i, "j": j, "k": k, "p": p})

        # Shared active (e, M, S) subsets per (letter, degree) for diffcl / qcoll / st_qcoll
        subs_by_lh: Dict[Tuple[int, int], List[Tuple[List[int], int, int]]] = {}
        if cfg.include_diffcl or cfg.include_qcoll or cfg.include_st_qcoll:
            for l_idx in range(3):
                m1_base = nums[self.blk(l_idx, 1)]
                items = [h for h in range(2, self.d0 + 1) if nums[self.blk(l_idx, h)] != 0]
                if nums[self.rem(l_idx)] != 0 or nums[self.W[l_idx]] != 0:
                    items.append(0)
                s_h1: List[Tuple[List[int], int, int]] = []
                if m1_base != 0:
                    s_h1.append(([1], m1_base, m1_base))
                for r in range(1, len(items) + 1):
                    for comb in combinations(items, r):
                        el = [1] + list(comb)
                        ms = m1_base + sum(
                            nums[self.rem(l_idx)] if h == 0 else nums[self.blk(l_idx, h)]
                            for h in comb
                        )
                        sz = m1_base + sum(
                            (nums[self.rem(l_idx)] + nums[self.W[l_idx]]) if h == 0 else h * nums[self.blk(l_idx, h)]
                            for h in comb
                        )
                        s_h1.append((el, ms, sz))
                subs_by_lh[(l_idx, 1)] = s_h1

                for h in range(2, self.d0 + 1):
                    cur: List[Tuple[List[int], int, int]] = []
                    for el in self.mult_subs[h]:
                        ms = sum(nums[self.blk(l_idx, m)] for m in el)
                        if ms != 0:
                            sz = sum(m * nums[self.blk(l_idx, m)] for m in el)
                            cur.append((el, ms, sz))
                    subs_by_lh[(l_idx, h)] = cur

        # 4. Multi-block self-thinning difference lattice (diffcl)
        if cfg.include_diffcl:
            thinned = cfg.include_stcl
            for tau in range(3):
                others = [l for l in range(3) if l != tau]
                l1, l2 = others[0], others[1]
                base = D_num - V_nums[l1] - V_nums[l2]
                jl = div_lists_with_empty[tau]
                min_mq = min(x[1] for x in jl)
                sig_shift = (det - sigma_nums[tau]) if thinned else 0
                for h, ell in self.hl_pairs:
                    s1_list = subs_by_lh[(l1, h)]
                    s2_list = subs_by_lh[(l2, ell)]
                    if not s1_list or not s2_list:
                        continue
                    g = math.gcd(h, ell)
                    s, d = h // g, ell // g
                    two_g = 2 * g
                    is_3way = (s == 1 or d == 1)
                    fam = "diffcl_3" if is_3way else "diffcl_2"
                    for e1, m1, S1 in s1_list:
                        for e2, m2, S2 in s2_list:
                            b0_pre = base + m1 + m2
                            if b0_pre - min_mq <= 0:
                                continue
                            S12 = S1 + S2
                            w_scaled = (2 * S1 + S2) if s == 1 else (S1 + 2 * S2)
                            for mk, mq, q in jl:
                                v0 = b0_pre - mq
                                if v0 <= 0:
                                    continue
                                v1_2g = two_g * v0 - S12 + g * (q + sig_shift)
                                if v1_2g <= 0:
                                    continue
                                if is_3way:
                                    v2_2g = two_g * v0 - w_scaled + two_g * (q + sig_shift)
                                    if v2_2g <= 0:
                                        continue
                                    viol = min(Fraction(v0, det), Fraction(v1_2g, two_g * det), Fraction(v2_2g, two_g * det))
                                else:
                                    viol = min(Fraction(v0, det), Fraction(v1_2g, two_g * det))
                                offer(
                                    fam,
                                    viol,
                                    {
                                        "type": "diffcl",
                                        "target": tau,
                                        "h": h,
                                        "ell": ell,
                                        "e1": e1,
                                        "e2": e2,
                                        "j_mask": mk,
                                        "thinned": thinned,
                                    },
                                )

        # 5. Cofactor-divisor collision (qcoll) and self-thinned variant (st_qcoll)
        if cfg.include_qcoll or cfg.include_st_qcoll:
            for i in range(3):
                for p in self.primes:
                    ql = q_lists_all.get((i, p))
                    if not ql:
                        continue
                    mp = mp_table[(i, p)]
                    rp = V_nums[i] - mp
                    for j in range(3):
                        if j == i:
                            continue
                        k = 3 - i - j
                        v0 = D_num - rp - V_nums[j]
                        if v0 <= 0:
                            continue
                        vk = V_nums[k]
                        b1_base = 2 * D_num - rp - V_nums[j] - 2 * vk
                        b2_ac_base = 4 * D_num - 3 * V_nums[i] + mp - 2 * V_nums[j] - 3 * vk
                        v_deg = sigma_nums[k] - sigma_nums[i]
                        do_st = cfg.include_st_qcoll and v_deg > 0

                        for m in range(1, self.d0 + 1):
                            ekl = subs_by_lh[(k, m)]
                            if not ekl:
                                continue
                            for e_k, mk_num, sk_num in ekl:
                                if cfg.include_qcoll:
                                    b1_ac_pre = m * (b1_base + 2 * mk_num) - 2 * sk_num
                                    b2_ac_pre = m * (b2_ac_base + 3 * mk_num) - sk_num
                                    b1_ap_pre = b1_base + mk_num
                                    b2_ap_pre = m * (b1_base + mk_num) - sk_num
                                    for qm, mq, sq in ql:
                                        v1_ac = b1_ac_pre + m * (sq - mq)
                                        if v1_ac > 0:
                                            v2_ac = b2_ac_pre - m * mq
                                            if v2_ac > 0:
                                                viol = min(
                                                    Fraction(v0, det),
                                                    Fraction(v1_ac, 2 * m * det),
                                                    Fraction(v2_ac, 4 * m * det),
                                                )
                                                offer(
                                                    "qcoll_ac",
                                                    viol,
                                                    {
                                                        "type": "qcoll", "variant": "ac",
                                                        "i": i, "j": j, "k": k, "p": p,
                                                        "q_mask": qm, "m": m, "e_k": e_k,
                                                    },
                                                )
                                        v1_ap = b1_ap_pre - mq
                                        if v1_ap > 0:
                                            v2_ap = b2_ap_pre + m * (sq - mq)
                                            if v2_ap > 0:
                                                viol = min(
                                                    Fraction(v0, det),
                                                    Fraction(v1_ap, 2 * det),
                                                    Fraction(v2_ap, 2 * m * det),
                                                )
                                                offer(
                                                    "qcoll_ap",
                                                    viol,
                                                    {
                                                        "type": "qcoll", "variant": "ap",
                                                        "i": i, "j": j, "k": k, "p": p,
                                                        "q_mask": qm, "m": m, "e_k": e_k,
                                                    },
                                                )
                                if do_st:
                                    b1_ac_pre = m * (b1_base + 2 * mk_num + v_deg) - 2 * sk_num
                                    b2_ac_pre = m * (b2_ac_base + 3 * mk_num) - sk_num
                                    b1_ap_pre = b1_base + mk_num
                                    b2_ap_pre = m * (b1_base + mk_num + v_deg) - sk_num
                                    for qm, mq, sq in ql:
                                        v1_ac = b1_ac_pre + m * (sq - mq)
                                        if v1_ac > 0:
                                            v2_ac = b2_ac_pre - m * mq
                                            if v2_ac > 0:
                                                viol = min(
                                                    Fraction(v_deg, det),
                                                    Fraction(v0, det),
                                                    Fraction(v1_ac, 2 * m * det),
                                                    Fraction(v2_ac, 4 * m * det),
                                                )
                                                offer(
                                                    "st_qcoll_ac",
                                                    viol,
                                                    {
                                                        "type": "st_qcoll", "variant": "ac",
                                                        "i": i, "j": j, "k": k, "p": p,
                                                        "q_mask": qm, "m": m, "e_k": e_k,
                                                    },
                                                )
                                        v1_ap = b1_ap_pre - mq
                                        if v1_ap > 0:
                                            v2_ap = b2_ap_pre + m * (sq - mq)
                                            if v2_ap > 0:
                                                viol = min(
                                                    Fraction(v_deg, det),
                                                    Fraction(v0, det),
                                                    Fraction(v1_ap, 2 * det),
                                                    Fraction(v2_ap, 2 * m * det),
                                                )
                                                offer(
                                                    "st_qcoll_ap",
                                                    viol,
                                                    {
                                                        "type": "st_qcoll", "variant": "ap",
                                                        "i": i, "j": j, "k": k, "p": p,
                                                        "q_mask": qm, "m": m, "e_k": e_k,
                                                    },
                                                )

        # 6. Modular cofactor collisions (modcoll 1/2-block and modcoll3 with h1 == 1)
        if cfg.include_modcoll or cfg.include_modcoll3:
            act_k_blocks = [
                [(h, nums[self.blk(k, h)]) for h in range(1, self.d0 + 1) if nums[self.blk(k, h)] != 0]
                for k in range(3)
            ]
            for i in range(3):
                for p in self.primes:
                    ql = q_lists_pos.get((i, p))
                    if not ql:
                        continue
                    rho = V_nums[i] - mp_table[(i, p)]
                    for j in range(3):
                        if j == i:
                            continue
                        k = 3 - i - j
                        g_num = rho + V_nums[j]
                        v0 = D_num - g_num
                        if v0 <= 0:
                            continue
                        blks = act_k_blocks[k]

                        if cfg.include_modcoll:
                            off_base = 2 * D_num - 2 * V_nums[k] - g_num
                            for h1, u1 in blks:
                                for qm, m_num, q_num in ql:
                                    H = u1 if u1 < q_num else q_num
                                    v_alt = off_base - m_num + H
                                    if v_alt > 0:
                                        viol = min(Fraction(v0, det), Fraction(v_alt, 2 * det))
                                        offer(
                                            "modcoll_1",
                                            viol,
                                            {"type": "modcoll", "i": i, "j": j, "k": k, "p": p, "q_mask": qm, "blocks": [h1]},
                                        )
                            for idx1 in range(len(blks)):
                                h1, u1 = blks[idx1]
                                u1_2 = 2 * u1
                                for idx2 in range(idx1 + 1, len(blks)):
                                    h2, u2 = blks[idx2]
                                    u2_2 = 2 * u2
                                    for qm, m_num, q_num in ql:
                                        H2 = (u1_2 if u1_2 < q_num else q_num) + (u2_2 if u2_2 < q_num else q_num)
                                        v_alt = 2 * (off_base - m_num) + H2
                                        if v_alt > 0:
                                            viol = min(Fraction(v0, det), Fraction(v_alt, 4 * det))
                                            offer(
                                                "modcoll_2",
                                                viol,
                                                {"type": "modcoll", "i": i, "j": j, "k": k, "p": p, "q_mask": qm, "blocks": [h1, h2]},
                                            )

                        if cfg.include_modcoll3:
                            u1 = nums[self.blk(k, 1)]
                            if u1 != 0:
                                other_blks = [(h, u) for (h, u) in blks if h >= 2]
                                if len(other_blks) >= 2:
                                    base16 = 16 * D_num - 16 * V_nums[k] - 8 * g_num
                                    for (h2, u2), (h3, u3) in combinations(other_blks, 2):
                                        for (ha, ua), (hb, ub) in (((h2, u2), (h3, u3)), ((h3, u3), (h2, u2))):
                                            for qm, m_num, q_num in ql:
                                                a_val = 8 * ua if 8 * ua < 4 * q_num else 4 * q_num
                                                b_val = min(4 * q_num, 8 * u1 + 4 * ub, 8 * u1 + 2 * q_num)
                                                v_alt16 = base16 - 8 * m_num + a_val + b_val
                                                if v_alt16 > 0:
                                                    viol = min(Fraction(v0, det), Fraction(v_alt16, 16 * det))
                                                    offer(
                                                        "modcoll_3",
                                                        viol,
                                                        {
                                                            "type": "modcoll3", "i": i, "j": j, "k": k,
                                                            "p": p, "q_mask": qm, "blocks": [1, ha, hb],
                                                        },
                                                    )

        # 7. Elementary Coppersmith (cop_elem) & CBP1 (pure-int inner loops, zero Fractions)
        if cfg.include_cop_elem or cfg.include_cbp1:
            for p in range(2, self.d0 + 1):
                pp = p * p
                pm1 = p - 1
                best_cop_v = 0
                best_cop_sp = None
                best_cbp_v = 0
                best_cbp_sp = None

                for i in range(3):
                    ei_cands = []
                    for el in self.mult_subs[p]:
                        mi = sum(nums[self.blk(i, h)] for h in el)
                        if mi != 0:
                            si = sum(h * nums[self.blk(i, h)] for h in el)
                            ei_cands.append((el, V_nums[i] - mi, si))
                    if not ei_cands:
                        continue
                    for j in range(3):
                        if j == i:
                            continue
                        k = 3 - i - j
                        dl_j = div_lists_with_empty[j]
                        dl_k = div_lists_nonempty[k]
                        if not dl_k:
                            continue
                        sig_j = sigma_nums[j]
                        sig_k = sigma_nums[k]
                        for e_i, ri_num, si in ei_cands:
                            base_d_ri = D_num - ri_num
                            for j_mk, mj_num, qj_num in dl_j:
                                s0 = sig_j - qj_num
                                c1_a = p * s0
                                d_ri_mj = base_d_ri - mj_num
                                qj_minus_sigj = qj_num - sig_j
                                for k_mk, mk_num, qk_num in dl_k:
                                    v_deg = qj_minus_sigj + qk_num
                                    if v_deg <= 0:
                                        continue
                                    ell1 = si if si < v_deg else v_deg
                                    d_minus_f = d_ri_mj - mk_num

                                    if cfg.include_cop_elem and c1_a < ell1:
                                        vm_p = p * (d_minus_f - s0) - (si - ell1)
                                        if vm_p > 0:
                                            vd_p = p * v_deg
                                            sc = vd_p if vd_p < vm_p else vm_p
                                            if sc > best_cop_v:
                                                best_cop_v = sc
                                                best_cop_sp = {
                                                    "type": "cop_elem",
                                                    "i": i, "j": j, "k": k, "p": p,
                                                    "e_i": e_i, "j_mask": j_mk, "k_mask": k_mk,
                                                }

                                    if cfg.include_cbp1:
                                        c1_max = c1_a if c1_a >= ell1 else ell1
                                        t0 = sig_k - qk_num
                                        c2_a = p * t0
                                        c2_b = pm1 * t0 + ell1
                                        e_a = c1_max if c1_max >= c2_a else c2_a
                                        e_b = c1_a if c1_a >= c2_b else c2_b
                                        if e_a <= e_b:
                                            mode = "a"
                                            e_c = e_a
                                        else:
                                            mode = "b"
                                            e_c = e_b
                                        vm_pp = pp * d_minus_f - p * (si - ell1) - e_c
                                        if vm_pp > 0:
                                            vd_pp = pp * v_deg
                                            sc = vd_pp if vd_pp < vm_pp else vm_pp
                                            if sc > best_cbp_v:
                                                best_cbp_v = sc
                                                best_cbp_sp = {
                                                    "type": "cbp1", "mode": mode,
                                                    "i": i, "j": j, "k": k, "p": p,
                                                    "e_i": e_i, "j_mask": j_mk, "k_mask": k_mk,
                                                }

                if best_cop_sp is not None:
                    offer(f"cop_elem_p{p}", Fraction(best_cop_v, p * det), best_cop_sp)
                if best_cbp_sp is not None:
                    offer(f"cbp1_p{p}", Fraction(best_cbp_v, pp * det), best_cbp_sp)

        # 8. Large-coefficient Salberger (2023) Cor. 6.5 / Thm. 3.16 directly on F_i (Tier 2 only)
        if cfg.include_salb_f:
            for d in self.salb_f_ds:
                c1, c2, c3, c4 = SALB_F_PARAMS[d]
                for i in range(3):
                    u = nums[self.blk(i, d)]
                    if u == 0:
                        continue
                    vi = V_nums[i]
                    fi = F_nums[i]
                    v0 = Fraction(vi - fi)
                    if v0 <= 0:
                        continue
                    v1 = Fraction(3 * u - vi - fi)
                    if v1 <= 0:
                        continue
                    sord = sum(h * nums[self.blk(i, h)] for h in range(1, self.d0 + 1) if h != d)
                    v2 = (Fraction(4) - c1) * u + c2 * sord - vi - fi
                    if v2 <= 0:
                        continue
                    v3 = (Fraction(4) - c3) * u + c4 * sord - vi - fi
                    if v3 <= 0:
                        continue
                    viol = min(v0, v1, v2, v3) / (4 * det)
                    offer(f"salbf_d{d}", viol, {"type": "salb_f", "i": i, "d": d})

        cands = list(best_by_fam.values())
        cands.sort(key=lambda pair: pair[0], reverse=True)
        return cands

    def find_most_violated_split(
        self, nums: Sequence[int], det: int
    ) -> Tuple[Optional[Dict[str, Any]], Fraction]:
        cands = self.find_top_violated_splits(nums, det)
        if not cands:
            return None, Fraction(0)
        return cands[0][1], cands[0][0]
