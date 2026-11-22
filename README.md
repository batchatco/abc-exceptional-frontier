# `abc-exceptional-frontier`

[![Verify Certificates](https://github.com/batchatco/abc-exceptional-frontier/actions/workflows/verify.yml/badge.svg)](https://github.com/batchatco/abc-exceptional-frontier/actions/workflows/verify.yml)

Unconditional **two-tier** improvements on the exceptional set $N_\lambda(X)$ and imbalanced exceptional set $N_{\mathrm{rel}}(\alpha,\lambda;X)$ in the $abc$ conjecture, reaching $9/16$ purely elementarily and $4224/7637 \approx 0.55310$ via curve lifting and large-coefficient diagonal surfaces uniformly through $\lambda = 1$, certified directly at fixed cutoff $d_0 = 6$ by 23 exact rational dual/Farkas proof trees with zero floating-point arithmetic.

## Overview

For $0 \le \alpha \le 1$ and $0 < \lambda \le 1$, define
$$
N_\lambda(X) := \#\{(a,b,c) \in \mathbb{Z}_{>0}^3 : a+b=c,\; \gcd(a,b,c)=1,\; c \le X,\; \operatorname{rad}(abc) < c^\lambda\},
$$
$$
N_{\mathrm{rel}}(\alpha,\lambda;X) := \#\{(a,b,c) \in \mathbb{Z}_{>0}^3 : a+b=c,\; \gcd(a,b,c)=1,\; a < b,\; a \le c^\alpha,\; c \le X,\; \operatorname{rad}(abc) < c^\lambda\}.
$$

Working directly at fixed cutoff $d_0 = 6$ with exact dyadic tail pinning of $n_{\mathrm{tail}} := \prod_{v_p(n) \ge 7} p^{v_p(n)}$ and the empirical $L^4$ additive-energy coordinate $F_n := \max(0, 3 n_V - \log_X \|S_n\|_4^4)$, we separate all results into two strictly isolated, independently verified tiers in [paper/main.tex](paper/main.tex) ([paper/main.pdf](paper/main.pdf)):

1. **Tier 1 (Purely elementary — zero Bombieri–Pila, zero Salberger):** Combines asymmetric Fourier $L^4$–$L^4$–$L^2$ bounds (`L442`), single-block elementary Hua moments (`Hua`), self-thinning congruence and difference lattices (`stCL`, `diffCL`), prime-indexed and cofactor-divisor collisions (`coll_p`, `qcoll`, `st_qcoll`), 1-, 2-, and 3-block modular collisions on $(\mathbb{Z}/Q\mathbb{Z})^\times$ (`modcoll`, `modcoll3` with strict $h_1 = 1$), and elementary Minkowski–Bézout counting (`cop_elem`). Proves $N_\lambda(X) \ll_\varepsilon X^{9/16+\varepsilon}$ uniformly for $0 < \lambda \le 1$, extends the square-root plateau $N_{\mathrm{rel}}(\alpha,\lambda;X) \ll_\varepsilon X^{1/2+\varepsilon}$ through $\alpha = 97/206 \approx 0.47087$, proves $263/522 \approx 0.50383$ at $\alpha = 1/2$, and already attains the exact Tier 2 optimum at every tested $\alpha \le 4/5$ (reaching $686/1255 \approx 0.54661$ purely elementarily) and every tested sub-critical point $\lambda < 1$.
2. **Tier 2 (Full determinant-method frontier):** Adjoins two new determinant-method disjunctions built on Salberger (2023): single-modulus Coppersmith curve lifting via a Jonquières $\mathbb{Q}$-automorphism paired with Salberger's uniform plane-curve bound (`cbp1`), and a Brill–Gordan / Cauchy–Binet large-coefficient upgrade of Salberger's diagonal-surface fourth-moment estimate (`salb_f`, $d \in \{4,5,6\}$) feeding directly into $F_n$. Strictly improves the near-symmetric regime $\alpha > 4/5$ ($\lambda = 1$), giving $84209/152740 \approx 0.55132$ at $\alpha = 9/10$ and establishing, uniformly for all $0 < \lambda \le 1$,
$$
N_\lambda(X) \ll_\varepsilon X^{4224/7637 + \varepsilon} \qquad (4224/7637 = 0.553096\ldots).
$$

## Headline Results

### 1. Unrestricted $N_\lambda(X)$ ($0 < \lambda < 1$, and uniformly for $0 < \lambda \le 1$ in de Bruijn, Zeng, and Theorem 1.1)

| Bound / Reference | Analytic Inputs | Exact $\delta$ | Decimal | Certificate |
| :--- | :--- | ---: | ---: | :--- |
| de Bruijn (1962) | Radical pair count | $2/3$ | `0.66667` | — |
| BLT v1 (2024) | Anatomy + $L^3$ + GoN + Thue / det. method | $33/50$ | `0.66000` | — |
| R. Li (2025) | Refined BLT optimization | $56/85$ | `0.65882` | — |
| Bernert (2025) | Streamlined BLT analysis (sketched $8/13$) | $8/13$ | `0.61538` | — |
| BBLT v2 (2026, Thm. 1.3) | Full BBLT MILP (fixed $\lambda < 1$) | $3/5$ | `0.60000` | — |
| H. Li (2026, preprint) | Two-letter collision + Farkas | $59969/100033$ | `0.59949` | — |
| C. Zeng (Nov 2026, preprint) | Modulus locking | $11680007/20000012$ | `0.58400` | — |
| **Theorem 1.1(i) (Tier 1 Elem)** | **Purely elementary ($d_0 = 6$, zero curves)** | **$9/16$** | **`0.56250`** | `elem_unres_alpha1_lam1.json` |
| **Theorem 1.1(ii) (Tier 2 Full)** | **Tier 1 + `cbp1` + large-coeff. `salb_f`** | **$4224/7637$** | **`0.55310`** | `full_unres_alpha1_lam1.json` |

### 2. Imbalanced Frontier $N_{\mathrm{rel}}(\alpha,\lambda;X)$ uniformly for $0 < \lambda \le 1$ ($d_0 = 6$)

| $\alpha$ | de Bruijn | Base LP ($d_0=6$, uncert.) | **Tier 1 (Elem)** | **Tier 2 (Full)** | Best Decimal | Certificate(s) |
| ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| $0$ | $1/2$ | $1/2$ | **$1/2$** | — | `0.500000` | `elem_imbal_alpha_0_lam1.json` |
| $1/3$ | $2/3$ | $4/7$ | **$1/2$** | — | `0.500000` | `elem_imbal_alpha_1_3_lam1.json` |
| $2/5$ | $2/3$ | $4/7$ | **$1/2$** | — | `0.500000` | `elem_imbal_alpha_2_5_lam1.json` |
| $4/9$ | $2/3$ | $4/7$ | **$1/2$** | — | `0.500000` | `elem_imbal_alpha_4_9_lam1.json` |
| $15/32$ | $2/3$ | $4/7$ | **$1/2$** | — | `0.500000` | `elem_imbal_alpha_15_32_lam1.json` |
| $97/206$ | $2/3$ | $4/7$ | **$1/2$** | — | `0.500000` | `elem_imbal_alpha_97_206_lam1.json` |
| $1/2$ | $2/3$ | $4/7$ | **$263/522$** | — | `0.503831` | `elem_imbal_alpha_1_2_lam1.json` |
| $5/9$ | $2/3$ | $\ge 4/7$ | **$23/45$** | — | `0.511111` | `elem_imbal_alpha_5_9_lam1.json` |
| $2/3$ | $2/3$ | $36/61$ | **$34/63^\dagger$** | — | `0.539683` | `elem_imbal_alpha_2_3_lam1.json` |
| $3/4$ | $2/3$ | $29/49$ | **$137/251^\dagger$** | — | `0.545817` | `elem_imbal_alpha_3_4_lam1.json` |
| $4/5$ | $2/3$ | $29/49$ | **$686/1255^\dagger$** | — | `0.546614` | `elem_imbal_alpha_4_5_lam1.json` |
| $9/10$ | $2/3$ | $143/240$ | **$213/380^\dagger$** | **$84209/152740^\dagger$** | `0.551323` | `elem_imbal_alpha_9_10_lam1.json`, `full_imbal_alpha_9_10_lam1.json` |
| $1$ | $2/3$ | $3/5$ | **$9/16$** | **$4224/7637$** | `0.553097` | `elem_unres_alpha1_lam1.json`, `full_unres_alpha1_lam1.json` |

*Notes:* In the Tier 2 column, `—` indicates points where Tier 1 (purely elementary) already attains the exact Tier 2 optimum (verified against all `cbp1` and `salb_f` disjunctions). By monotonicity (Proposition 2.1), the single Tier 1 certificate at $\alpha = 97/206$ proves $N_{\mathrm{rel}}(\alpha,\lambda;X) \ll_\varepsilon X^{1/2+\varepsilon}$ uniformly for all $(\alpha,\lambda) \in [0, 97/206] \times (0, 1]$. Unmarked entries have zero-tail primal witnesses (hence are exact optima for every cutoff $d \ge 6$); entries marked $^\dagger$ carry nonzero tail weight at $d_0 = 6$.

### 3. Sub-Critical Frontier ($\lambda < 1$, $d_0 = 6$, Tier 1 Elementary = Tier 2 Full)

| $\alpha$ | $\lambda$ | BBLT Thm. 1.2 | Base LP ($d_0=6$, uncert.) | **Tier 1 = Tier 2** | Decimal | Certificate |
| ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| $1$ | $1/2$ | $29/80$ | $1/3$ | **$1/3^\dagger$** | `0.333333` | `elem_unres_alpha1_lam_1_2.json` |
| $1$ | $3/5$ | $21/50$ | $2/5$ | **$2/5^\dagger$** | `0.400000` | `elem_unres_alpha1_lam_3_5.json` |
| $1$ | $7/10$ | $191/400$ | $109/250$ | **$29/70^\dagger$** | `0.414286` | `elem_unres_alpha1_lam_7_10.json` |
| $1$ | $4/5$ | $107/200$ | $59/120$ | **$7/15^\dagger$** | `0.466667` | `elem_unres_alpha1_lam_4_5.json` |
| $1$ | $9/10$ | $237/400$ | $71/130$ | **$119/235^\dagger$** | `0.506383` | `elem_unres_alpha1_lam_9_10.json` |
| $1$ | $19/20$ | $497/800$ | $377/660$ | **$19/35^\dagger$** | `0.542857` | `elem_unres_alpha1_lam_19_20.json` |
| $1/2$ | $4/5$ | $107/200$ | $7/15$ | **$1759/4250$** | `0.413882` | `elem_imbal_alpha_1_2_lam_4_5.json` |
| $1/2$ | $9/10$ | $237/400$ | $47/90$ | **$145/306^\dagger$** | `0.473856` | `elem_imbal_alpha_1_2_lam_9_10.json` |

Every point in Table 3 is proved completely elementarily (Tier 1) and simultaneously attains the exact Tier 2 optimum. Entries marked $^\dagger$ carry nonzero tail weight at $d_0 = 6$ (at $\lambda \in \{1/2, 3/5\}$, $2\lambda/3$ is also sharp for all $d \ge 6$).

## Repository Layout

```text
abc-exceptional-frontier/
├── .github/workflows/verify.yml   # GitHub Actions CI (stdlib zero-float verification + audits)
├── LICENSE                        # MIT License
├── README.md
├── certificates/                  # 23 exact rational v4 certificates (21 Tier 1 + 2 Tier 2, 42 MiB) + MANIFEST.sha256
├── paper/
│   ├── Makefile                   # Containerized TeX Live build (podman)
│   ├── main.bib                   # Primary-source verified bibliography
│   ├── main.tex                   # Standalone LaTeX manuscript (two-tier v4)
│   └── main.pdf                   # Compiled PDF (18 pages, 0 warnings / 0 overfull boxes)
├── results/
│   ├── frontier_summary_v4.json   # Consolidated exact summary of all 23 certificates
│   └── summary_v4_*.json          # Per-batch solver outputs (elemA, elemB, elemC1, elemC2, fullA, fullB)
└── src/
    ├── verify_certificates.py     # Independent stdlib-only exact Fraction verifier (zero solver imports, zero floats)
    ├── audit_cl_and_lq_lemmas.py  # Empirical integer audit of CRT, 2D lattice, stCL, L442/Hua, modcoll3, Coppersmith/Jonquières & Brill–Gordan
    ├── exact_simplex.py           # Exact-integer Bareiss simplex & Farkas/dual extractor
    ├── model_grouped.py           # Direct fixed-d0 (3*d0 + 13)-variable two-tier model (Tier 1 elem & Tier 2 full)
    ├── branch_and_certify.py      # Exact rational n-way strong-branching B&B + lazy Hua cuts + proof-tree builder
    └── sweep_2d_frontier.py       # Reproducible batch generator for all 23 v4 certificates
```

## Quick Verification & Reproduction

### 1. Independently verify all 23 certificates (`47.0 s`, `403.8 MiB` cgroup peak RAM, Python 3 stdlib only, zero floats)
```bash
python3 src/verify_certificates.py --all --self-test
```
Verifies all 23 exact dual/Farkas proof trees (`80,967` branches, `216` single-block Hua cuts, `109,580` dual leaves, `168` Farkas leaves, max depth `122`), enforces strict Tier 1 / Tier 2 isolation, exhaustively checks all 23 canonical active-support primal witnesses, verifies the pinned 23-case theorem registry, verifies all 23 SHA-256 digests in `certificates/MANIFEST.sha256` and all 23 entries in `results/frontier_summary_v4.json`, and runs `10` positive controls plus `38/38` reason-checked adversarial corruption rejection tests.

### 2. Run the empirical integer audit of all analytic lemmas (`0.35 s`, `8.5 MiB` peak RAM)
```bash
python3 src/audit_cl_and_lq_lemmas.py
```

### 3. Rebuild the full 23-certificate suite from scratch (optional)
```bash
python3 src/sweep_2d_frontier.py elemA elemB elemC1 elemC2 fullA fullB manifest
```

### 4. Build the LaTeX paper (via containerized TeX Live)
```bash
make -C paper pdf
make -C paper clean
```

## AI-Assistance Disclosure

Large-language-model AI coding and mathematical research assistants were used extensively during this project to explore disjunction families, implement the solver and independent verifier, audit proof steps, and draft the manuscript. Every quantitative bound is backed by an exact rational proof tree verified with zero floating-point arithmetic by the standalone Python 3 standard-library checker (`src/verify_certificates.py`), and all external theorem citations were checked against primary sources.

