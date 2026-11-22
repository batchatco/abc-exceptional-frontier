#!/usr/bin/env python3
"""Exact-integer Bareiss simplex solver and Farkas/dual certificate extractor.

Zero floating-point arithmetic and zero third-party dependencies.
Maintains an exact integer Simplex tableau via Sylvester's determinant identity:
every entry tab[i][j] represents the exact rational number tab[i][j] / det
with det > 0.
"""

from __future__ import annotations

from fractions import Fraction
import math
from typing import Iterable, List, Sequence, Tuple


def frac_row_to_int(
    coeffs: Sequence[Fraction | int], rhs: Fraction | int
) -> Tuple[List[int], int, int]:
    """Scale rational inequality a^T x <= b to exact integers (k*a, k*b, k)."""
    f_coeffs = [Fraction(c) for c in coeffs]
    f_rhs = Fraction(rhs)
    k = f_rhs.denominator
    for c in f_coeffs:
        if c.denominator != 1:
            k = math.lcm(k, c.denominator)
    return [int(c * k) for c in f_coeffs], int(f_rhs * k), k


def sparse_weights(weights: Sequence[Fraction]) -> List[List[object]]:
    """Serialize nonzero rational multipliers as [[row_index, 'num/den'], ...]."""
    out: List[List[object]] = []
    for idx, w in enumerate(weights):
        if w != 0:
            out.append([idx, str(w)])
    return out


class BareissTableau:
    """Exact integer Simplex tableau for max c^T x s.t. A x <= b, x >= 0."""

    __slots__ = ("n_orig", "tab", "det", "basis", "row_scales", "row_names")

    def __init__(
        self,
        n_orig: int,
        tab: List[List[int]],
        det: int,
        basis: List[int],
        row_scales: List[int],
        row_names: List[str],
    ) -> None:
        self.n_orig = n_orig
        self.tab = tab
        self.det = det
        self.basis = basis
        self.row_scales = row_scales
        self.row_names = row_names

    def clone(self) -> "BareissTableau":
        return BareissTableau(
            self.n_orig,
            [row[:] for row in self.tab],
            self.det,
            self.basis[:],
            self.row_scales[:],
            self.row_names[:],
        )

    @property
    def n_tot(self) -> int:
        return len(self.tab[0]) - 1

    @property
    def m(self) -> int:
        return len(self.basis)

    def pivot(self, r: int, c: int) -> None:
        piv = self.tab[r][c]
        old_det = self.det
        if piv > 0:
            new_det = piv
            row_r = self.tab[r]
            for i, row_i in enumerate(self.tab):
                if i != r:
                    ic = row_i[c]
                    if ic != 0:
                        self.tab[i] = [
                            (piv * x - ic * y) // old_det for x, y in zip(row_i, row_r)
                        ]
                    else:
                        self.tab[i] = [(piv * x) // old_det for x in row_i]
        else:
            new_det = -piv
            row_r = [-y for y in self.tab[r]]
            self.tab[r] = row_r
            for i, row_i in enumerate(self.tab):
                if i != r:
                    ic = row_i[c]
                    if ic != 0:
                        self.tab[i] = [
                            (new_det * x - ic * y) // old_det
                            for x, y in zip(row_i, row_r)
                        ]
                    else:
                        self.tab[i] = [(new_det * x) // old_det for x in row_i]
        self.det = new_det
        self.basis[r] = c

    def primal_simplex(self, ncols: int | None = None) -> str:
        m = self.m
        if ncols is None:
            ncols = self.n_tot
        while True:
            obj = self.tab[-1]
            enter = -1
            for j in range(ncols):
                if obj[j] < 0:
                    enter = j
                    break
            if enter == -1:
                return "optimal"
            best_r = -1
            for i in range(m):
                aij = self.tab[i][enter]
                if aij > 0:
                    if best_r == -1:
                        best_r = i
                    else:
                        lhs = self.tab[i][-1] * self.tab[best_r][enter]
                        rhs = self.tab[best_r][-1] * aij
                        if lhs < rhs or (
                            lhs == rhs and self.basis[i] < self.basis[best_r]
                        ):
                            best_r = i
            if best_r == -1:
                return "unbounded"
            self.pivot(best_r, enter)

    def dual_simplex(self) -> str:
        m = self.m
        n_tot = self.n_tot
        it = 0
        while True:
            it += 1
            leave = -1
            if it <= 15:
                min_rhs = 0
                for i in range(m):
                    rhs = self.tab[i][-1]
                    if rhs < min_rhs:
                        min_rhs = rhs
                        leave = i
            else:
                # Strict Bland anti-cycling rule
                best_b = -1
                for i in range(m):
                    if self.tab[i][-1] < 0:
                        if leave == -1 or self.basis[i] < best_b:
                            leave = i
                            best_b = self.basis[i]
            if leave == -1:
                return "optimal"
            row_l = self.tab[leave]
            obj = self.tab[-1]
            enter = -1
            for j in range(n_tot):
                aij = row_l[j]
                if aij < 0:
                    if enter == -1:
                        enter = j
                    else:
                        lhs = obj[j] * (-row_l[enter])
                        rhs = obj[enter] * (-aij)
                        if lhs < rhs:
                            enter = j
            if enter == -1:
                return "infeasible"
            self.pivot(leave, enter)

    def add_int_cut_and_resolve(
        self, int_coeffs: Sequence[int], int_rhs: int, scale_k: int, name: str
    ) -> str:
        """Append scaled cut (int_coeffs/scale_k)^T x <= int_rhs/scale_k and re-optimize."""
        old_ntot = self.n_tot
        det = self.det
        for row in self.tab:
            row.insert(old_ntot, 0)

        new_row = [0] * (old_ntot + 2)
        for j in range(self.n_orig):
            new_row[j] = int_coeffs[j] * det
        new_row[old_ntot] = det
        new_row[-1] = int_rhs * det

        for r, bvar in enumerate(self.basis):
            if bvar < self.n_orig:
                cb = int_coeffs[bvar]
                if cb != 0:
                    row_r = self.tab[r]
                    for j in range(old_ntot + 2):
                        new_row[j] -= cb * row_r[j]

        self.tab.insert(self.m, new_row)
        self.basis.append(old_ntot)
        self.row_scales.append(scale_k)
        self.row_names.append(name)
        return self.dual_simplex()

    def add_frac_cut_and_resolve(
        self, coeffs: Sequence[Fraction | int], rhs: Fraction | int, name: str
    ) -> str:
        ic, ir, sk = frac_row_to_int(coeffs, rhs)
        return self.add_int_cut_and_resolve(ic, ir, sk, name)

    def primal_numerators(self) -> List[int]:
        """Fast exact numerator vector num_j such that x_j = num_j / self.det."""
        nums = [0] * self.n_orig
        for r, bvar in enumerate(self.basis):
            if bvar < self.n_orig:
                nums[bvar] = self.tab[r][-1]
        return nums

    def extract_exact_primal_dual(
        self, obj_scale: int = 1
    ) -> Tuple[Fraction, List[Fraction], List[Fraction]]:
        """Return (optimal_value, primal_x, dual_y) as exact Fractions."""
        det = self.det
        f0 = Fraction(0)
        x = [f0] * self.n_orig
        for r, bvar in enumerate(self.basis):
            if bvar < self.n_orig:
                x[bvar] = Fraction(self.tab[r][-1], det)
        y = [
            Fraction(
                self.tab[-1][self.n_orig + i] * self.row_scales[i],
                det * obj_scale,
            )
            for i in range(self.m)
        ]
        return Fraction(self.tab[-1][-1], det * obj_scale), x, y

    def extract_farkas_certificate(self) -> List[Fraction]:
        """Extract f >= 0 with f^T A >= 0, f^T b < 0 from an infeasible tableau."""
        det = self.det
        for i in range(self.m):
            row = self.tab[i]
            if row[-1] < 0 and all(row[j] >= 0 for j in range(self.n_tot)):
                return [
                    Fraction(row[self.n_orig + k] * self.row_scales[k], det)
                    for k in range(self.m)
                ]
        raise RuntimeError("Infeasible tableau missing non-negative Farkas row")


def build_initial_tableau(
    n_orig: int,
    rows: Iterable[Tuple[Sequence[Fraction | int], Fraction | int, str]],
    objective: Sequence[Fraction | int],
) -> Tuple[BareissTableau, int, str]:
    """Initialize exact integer tableau from rational rows A_i x <= b_i.

    Rows with b_i >= 0 are inserted directly and solved by primal simplex; any
    remaining rows with b_i < 0 are appended and resolved by dual simplex.
    Returns (tableau, obj_scale, status).
    """
    int_rows = [frac_row_to_int(c, r) + (nm,) for c, r, nm in rows]
    obj_ic, _, obj_k = frac_row_to_int(objective, 0)

    pos_rows = [(idx, row) for idx, row in enumerate(int_rows) if row[1] >= 0]
    neg_rows = [(idx, row) for idx, row in enumerate(int_rows) if row[1] < 0]

    # Require original row ordering to be preserved in slack columns when neg_rows is empty.
    if neg_rows:
        raise ValueError(
            "All base rows must have RHS >= 0 to preserve canonical row indexing; "
            f"negative RHS found at {[r[1][3] for r in neg_rows]}"
        )

    m = len(int_rows)
    tot = n_orig + m
    tab: List[List[int]] = []
    basis: List[int] = []
    scales: List[int] = []
    names: List[str] = []
    for i, (ic, ir, sk, nm) in enumerate(int_rows):
        row = [0] * (tot + 1)
        for j in range(n_orig):
            row[j] = ic[j]
        row[n_orig + i] = 1
        row[-1] = ir
        tab.append(row)
        basis.append(n_orig + i)
        scales.append(sk)
        names.append(nm)

    orow = [0] * (tot + 1)
    for j in range(n_orig):
        orow[j] = -obj_ic[j]
    tab.append(orow)

    bt = BareissTableau(n_orig, tab, 1, basis, scales, names)
    status = bt.primal_simplex(tot)
    return bt, obj_k, status
