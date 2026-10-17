# Full proofs of items of ownwork.md §9: (H61) for case 2b, Theorem U, item 9, item 10, INV-A

This document contains the full proofs of the items that ownwork.md §9 states only in outline:
Theorem U (item 8, here §2), the polynomial parts of CERT, CJ and `aggregate` (item 9, §3) and
Lemma CH (item 10, §4). It also proves two of the assumptions listed there: (H61) for case 2b
(item 5, §1) and INV-A (item 4, §5).

It uses the cost model `docs/bounds/SPEC.md`, the per-module documents
`docs/bounds/{main,group,structure_cc_wl,soj,johnson_certs}.md` and `ownwork.md` in this directory.
Code line numbers refer to the files of this version.

---------------------------------------------------------------------------------------------

## 0. Summary

| item | result | constant | effect on the ω of ownwork.md §0 |
|---|---|---|---|
| 1. (H61) for case 2b | **proved as stated, for \|V\| ≥ 42** (case 2b gives \|V\| = \|pts\| ≥ 42, using CORRECTNESS.md Lemma 10.6, which cites CFSG). Every use of \|V\| ≥ 61 in soj.md is listed in §1.2; each holds for \|V\| ≥ 42. One constant needs an additional argument: Theorem A's d-ary coefficient `Y/16 + 1/2` follows from soj.md's crude power sums only for \|V\| ≥ 50; for 42 ≤ \|V\| ≤ 49 it follows from the midpoint estimate of the power sums (§1.5). (With the crude sums the coefficient for \|V\| ≥ 42 would be `Y/15 + 0.51`.) The per-call closed forms (i) hold for every n ≥ 2, Lemma T (ii) for every n, Theorem A and Theorem U (iii) for \|V\| ≥ 42, Theorem B (iv) for \|V\| ≥ 42 (regions at Y_V need only Y_V ≥ 4). | as stated | unchanged |
| 2. Theorem U, lower-order groups | **proved as stated, with a much smaller constant**: the nine lower-order groups, times 17, sum to at most `3.7·10⁻⁵·2^{U(y)}` for all m ≥ 90 (stated: 0.03). The dominant term is `≤ 1.7133·2^{U(y)}`, so `W_UPCC ≤ 1.714·(y+2)⁴ m^{7+2 log₂ y}`. Two counts in the lists of ownwork §8.3 are corrected (§2.6); the corrections do not affect the bound. | 0.03 holds (true value ≤ 3.7·10⁻⁵); 1.87 holds (1.714 suffices) | unchanged (`0.91 + U(y)`; `0.78 + U(y)` would also be valid) |
| 3. Item 9 (CERT, CJ, aggregate) | **proved as stated.** The polynomial (non-build, non-k!) parts are written out (§3.2–3.4). Per miss the M-proportional terms are `≤ 754346.97 M n⁶`, so two misses give `≤ 1508694 M n⁶ ≤ 1508700 M n⁶`; also `3514`, `44.8`, `131` hold. Two justifications in ownwork §8.8 are corrected (the non-M terms need `M ≥ 100n³`, not `M ≥ n`; the k!-list is `≤ 3.42 k! n²`, not `2.9 k! n²`); the conclusions stand. A sharper coefficient `970300` also holds (§3.5). | 1508700 holds | unchanged (`20.53 + 3lM + LKF + 6X`; `19.89 + …` would also be valid) |
| 4. Item 10 (Lemma CH) | **proved as stated**: `d ≤ 1.3m`, `κ ≤ 0.23m²` (in fact `≤ 0.19m²`), and every chosen object has height `≤ J + 2 < log₂m/δ + 2 ≤ m` (much less than the stated `≤ m`), so `A' ≤ 0.0095 m⁴ ≤ 0.8 m⁴`. Rests on soj.md Lemma P and (I8), i.e. on the inherited assumption 7 (coherence of WL outputs), like all of soj.md's run analysis. | as stated | unchanged |
| 5. INV-A (\|lifts\| ≤ k!) | **proved, under a weaker hypothesis than (A3)**: the number of lifts is the product over i < kA of the sizes of `levels[i].trans` (from the code), and this is `≤ k!/(k−kA)! ≤ k!` whenever every φ-image of `H.G.gens` maps A onto A (INV-A), using only johnson_certs.md Lemma B (proved from group.py, no completeness of Schreier–Sims needed). INV-A itself is proved from the code of certificates.py, action.py, main.py (`iso_window`) and group.py, assuming only HOM for `jd.Gw` (CORRECTNESS.md Lemmas 3.3, 4.4, 4.5). Neither completeness of Schreier–Sims nor correctness of the recursive solver calls is needed. Under completeness (CORRECTNESS.md Lemma 3.1) the count equals \|H^A\|. | k! | unchanged |

---------------------------------------------------------------------------------------------

## 1. (H61) for case 2b

### 1.1 What case 2b provides

`main.case_2b_structure` (main.py:905–957) is called with `Phi = a["Phi"]`, an orbit of `Fimg`
with `2·|Phi| > m` (main.py:793), so `|Phi| ≥ ⌊m/2⌋ + 1 ≥ 46` for m ≥ 90. The loop at
main.py:919–936 individualizes one point of `pts` per iteration while `H` is 2-transitive and not a
giant; CORRECTNESS.md Lemma 10.6 (citing CFSG: a non-giant is at most 5-transitive) bounds the
number of individualizations by 4. The uniprimitive branch calls `upcc_split_or_johnson(ccg, α, base,
…)` (main.py:957) with `ccg.vertices = pts` and `α = Fraction(2, 3)`. Hence, with `n := |V| = |pts|`:

* **(H42)** `n ≥ 46 − 4 = 42`, and `bound = (2/3)·n ≥ 28` (soj.py: `bound = alpha * nV`).
* **N1 ≥ 29.** Every bipartite call that passes its first `dominant_cell` test has
  `n1 > bound` (soj.md (I2)), and V1' is a cell with `|V1'| > bound`; so `N1 ≥ 29`.
* **n2 ≥ 7 at Phase 5.** At Phase 5, V1' is twin-free within its cell, so the `N1` sets
  `adjp[v]` are distinct (soj.md (I6)); they are d1-subsets of V2 with `2 ≤ d1 ≤ n2/2` (after the
  complement at soj.py:463–466; d1 ∉ {0,1} by (I6)), and Phase 5 is reached only if
  `len(H) ≠ comb(n2, d1)`, i.e. `N1 = |H| < C(n2, d1) ≤ C(n2, ⌊n2/2⌋)`. For `n2 ≤ 6` the right side
  is `≤ C(6,3) = 20 < 30 ≤ N1 + 1`. So `n2 ≥ 7`. (For the EDL caller `N1 ≥ 61` gives `n2 ≥ 8`.)
* `n1_orig = |V1_0| > bound ≥ 28`, so `n1_orig ≥ 29`.

### 1.2 Every place of soj.md that uses |V| ≥ 61 (or bound ≥ 40.67, N1 > 40.67, n2 ≥ 6)

| # | soj.md | what the argument uses | status for 42 ≤ \|V\| ≤ 60 |
|---|---|---|---|
| 1 | §0.3, definition of (H61) | – | replaced by (H42) |
| 2 | §1 `individualize_until`, reachability bullet: "never runs under (H61)" | `bound ≥ small_v1 = 6` | `bound ≥ 28`: holds |
| 3 | §1 `bipartite_split_or_johnson`, Phase 1: small_v1 return unreachable | `n1 > bound ≥ 6` | holds |
| 4 | §1 bipartite, "Closed forms": "Put n := \|V\| ≥ 61" | nothing: §1.3 re-derives both closed forms for every n ≥ 2 | holds |
| 5 | §1 bipartite, Closed forms: definition of Q and "n2 ≥ 6 holds at Phase 5" | `n2 ≥ 6` in the `1/n2` terms of Q | `n2 ≥ 7` (§1.1): holds |
| 6 | §2.A.1 (I2) | `n1_i > bound ≥ 40.67`, used as `6 < bound` and "\|V\| ≥ 10" | holds |
| 7 | §2.A.1 (I5) | `n1_orig ≥ 41`, used only as `n1_orig ≥ 6` (as (I5) states) | `n1_orig ≥ 29`: holds |
| 8 | §2.A.1 (I8), `J < Y/δ` | choice levels have `n2 ≥ 6` | `n2 ≥ 7`: holds (`J ≤ 1 + log_{3/2}(n2_0/7) < Y/δ`) |
| 9 | §2.A.2 Theorem A, "Closed form. Combine": `Q_i ≤ (13Y + 102)(n2_i² + n)` "for n ≥ 61" | true for n ≥ 5 (§1.5) | holds |
| 10 | Theorem A, closed form, [d-ary part]: coefficient `Y/16 + 1/2` | with `Σ n2_i⁴ ≤ (n/3)⁵`, `Σ n2_i² ≤ (n/3)³` it needs n ≥ 50 | holds by the midpoint estimate (§1.5) |
| 11 | §2.B Theorem B, statement: "m ≥ \|V\| ≥ 61" | `Y_V ≥ 4` (region R1), `Y_V ≥ e` (passing to m), `Y ≥ 5.93` at `Y = log₂ m` | holds (§1.6) |
| 12 | §2.A.3, EDL: \|C\| > (2/3)m ≥ 61 | EDL caller only | not case 2b |
| 13 | §3 "Could not prove", item 2: (H61) assumed | – | proved in this section |

No other statement of soj.md depends on |V|: Lemma P, Lemma AR, Lemma R, Lemma Σ, the reachability
facts (I1), (I3), (I4), (I6)–(I8), §2.A.4 (key sizes), §2.C (outputs) and the per-function bounds of
§1 are proved there without a size hypothesis (each against the hypotheses it states; the lemmas of
CORRECTNESS.md §9 and the results of HBD that (I7) cites have no size hypothesis).

### 1.3 (i) The closed forms of one bipartite call, re-derived for every n ≥ 2

**Substitutions** (valid at every bipartite call of a run, every n = |V|; soj.md references):
`n1, N1, Ntot ≤ n` (all inside `V ∖ {x}`); `n2 < n/3` (I3); `Σ2 ≤ 2U2 < 2n/3` and `U2 < n/3`
(Lemma P, `U2 ≤ n − 1 − |V1_0| < n/3`); `d1 ≤ n2/2 < n/6`; `D ≤ N1 + 2 ≤ n + 1`;
`s* ≤ ⌈d1/2⌉ ≤ n/12 + 1`; every `⌈lg x⌉` with x ≤ n is ≤ L := ⌈lg n⌉, `⌈lg D⌉ ≤ L + 1`;
`F(u) ≤ 12(n/3)² + 68(n/3)`; `σ(pt) ≤ Σ2`. In P8 only, `N1·n2 ≤ (n − n2)·n2 ≤ (2n/3)(n/3) = 2n²/9`
(from `N1 + n2 ≤ n − 1`, the points of V2 having disjoint non-empty underlying sets outside V1_0,
and `n2 < n/3`; `(n − z)z` is increasing for z ≤ n/2). Callee symbols, TCK and the T-terms are
removed (they are the callee list and Q). Phase bounds as in soj.md §1:

| phase | substituted bound (callee symbols removed) |
|---|---|
| P0 | `nL + (19/3)n + 117 + 22M + 4Mn` |
| P1 | `30` |
| P2 | `2n² + 99n + 106 + 34M + 4Mn` |
| P3 | `nL + 3n + 5` |
| P3' | `2n² + 38.5n + 112` |
| P4 | `(38/3)n² + (169/3)n + 38` |
| PJ | `(29/6)n² + 40n + 94 + 18M + 4Mn` |
| PH | `(4/3)n² + 23n + 64 + 27M + 2Mn` |
| P5 (non-T) | `(n²/6)L + (16/3)n² + nL + 108.92n + L + 223` |
| P6 | `20n² + 179n + 331` |
| P7 (own, non-T) | `(4/3)n² + (70/3)n + 130d + 460` |
| P8 | `110.95n² + (4/3)nL + 237n + 220 + 34M + 4Mn` |
| SC | `20n² + (8/3)nL + (607/3)n + 543` |
| CO | `50n² + 0.67nL + 222n + 1247 + 24M` |

*No-choice call:* `1397 + P0 + P1 + P2 + max(P3', P3 + P4 + max(PJ, PH, P5 + P6))`. The termwise
maximum of the inner alternatives (`P3+P4+P5+P6 = (n²/6)L + 38n² + 2nL + 347.25n + L + 597`,
`P3+P4+PJ = 17.5n² + nL + 99.34n + 137 + 18M + 4Mn`, `P3+P4+PH = 14n² + nL + 82.34n + 107 + 27M + 2Mn`,
`P3'`) plus the common part gives

    B_nc ≤ 2247 + 452.59n + 40n² + (n²/6 + 3n + 1)L + 83M + 12Mn
         ≤ 2287 + 454n + 41n² + (n²/6 + 3n + 2)L + 85M + 12Mn          (soj.md's form, every n ≥ 2).

*Choice call:* `1397 + P0 + P1 + P2 + P3 + P4 + P5 + P7 + P8 + max(SC, CO)`:

    B_c ≤ 3843 + 130d + 755.92n + 182.28n² + (n²/6 + 7n + 1)L + 114M + 12Mn
        ≤ 3902 + 130d + 758n + 185n² + (n²/6 + 8n + 2)L + 114M + 12Mn   (soj.md's form, every n ≥ 2).

(Without the refinement `N1·n2 ≤ 2n²/9` the n²-coefficient is `185.17 > 185`; with it, `182.28`.)
Neither closed form uses n ≥ 61.

**Q** (soj.md §1, bipartite, Closed forms), re-derived; it uses only `n2 ≥ 6` at Phase 5. The T-terms per call are:
TCK `≤ (12d+33)n2²T + (4d+11)T + 38n2³ + 38n2² + 31n2 + 101` (soj.md §1 twin_classes_kary, exact
form); P5: `11(d+3)·N1·C(d1,d) + (12d + 50 + D)T` with `N1·C(d1,d) ≤ n·(n2/2)^d/d! ≤ nT/2`; DL:
`2(T/n2)(28n2² + 72n2 + 123 + d) + (T/n2)(36 + 10d + 2dσ_pt)`, `σ_pt ≤ 2n/3`. With `T ≥ n2²` and
`n2 ≥ 6`: `(38n2³ + 38n2² + 31n2 + 101)/T ≤ 38n2 + 46`, `(246 + 2d)/n2 ≤ 41 + d/3`,
`(36 + 10d + 2dσ_pt)/n2 ≤ 6 + 1.67d + (2d/9)n`, `94n2 ≤ 15.67n2²`. Sum/T:
`≤ (12d + 48.67)n2² + (5.73d + 17.5)n + 18d + 299 ≤ (13d + 76)n2² + (6d + 33)n + 15d + 250 = Q`,
the excess `3d + 49` of the constant being covered by the slack `(d + 27.3)n2² ≥ 36d + 983` of the
n2²-coefficient.

### 1.4 (ii) Lemma T for every n

soj.md's proof (§1, bipartite, Lemma T) uses only Lemma AR(ii) (`C(n2, t) ≤ N1 < n`, `2t < d1 ≤ n2/2`), the
inequality `4^t < (n2/t)^t ≤ C(n2,t) < 2^Y`, hence `t < Y/2`, and `t^{2t} < (Y/2)^{2t} ≤ (Y/2)^Y`,
which needs `Y/2 > t ≥ 1` (automatic when t ≥ 1). So (i) `T ≤ n2²·n^{1 + log₂ Y}` and (iii)
`d < Y + 2` hold for every n; (ii) uses the R1 argument, valid for `Y ≥ 4`. **Lemma T holds as
stated for |V| ≥ 42.**

### 1.5 (iii) Theorem A and Theorem U for |V| ≥ 42

*Q_i.* With `d_i < Y + 2`: `Q_i ≤ (13Y + 102)n2_i² + (6Y + 45)n + 15Y + 280 ≤ (13Y + 102)(n2_i² + n)`
iff `15Y + 280 ≤ (7Y + 57)n`, true for n ≥ 5.

*The d-ary part.* `Σ_i T_i Q_i ≤ (13Y + 102)·n^{1 + log₂ Y}·Σ_i n2_i²(n2_i² + n)` over the calls that
reach Phase 5; their `n2_i` are distinct integers in `[7, K]`, `K := ⌈n/3⌉ − 1 < n/3` (soj.md (I8)).
* soj.md uses `Σ n2_i⁴ ≤ (n/3)⁵`, `Σ n2_i² ≤ (n/3)³`, giving the coefficient
  `(13Y + 102)(1/243 + 1/(27n))`. At `Y = log₂ n` this is `≤ Y/16 + 1/2` exactly for n ≥ 50
  (n = 49: 0.85240 > 0.85092; n = 50: 0.85159 ≤ 0.85274; n = 61: 0.84578 ≤ 0.87067), so for
  42 ≤ n ≤ 49 the stated constant does not follow from soj.md's argument.
* **Midpoint estimate.** For a convex f, `f(j) ≤ ∫_{j−1/2}^{j+1/2} f` (Hermite–Hadamard), so
  `Σ_{j=1}^{K} j⁴ ≤ (K + 1/2)⁵/5 ≤ (n/3)⁵(1 + 3/(2n))⁵/5` and `Σ_{j≤K} j² ≤ (n/3)³(1 + 3/(2n))³/3`.
  For n ≥ 42: `(1 + 1/28)⁵/5 ≤ 0.23837`, `(1 + 1/28)³/3 ≤ 0.37035`, and
  `Σ_i T_iQ_i ≤ (13Y + 102)(0.23837/243 + 0.37035/(27·42))·n^{6 + log₂ Y} ≤ (0.0170Y + 0.1334)·n^{6+log₂Y}
  ≤ (Y/16 + 1/2)·n^{6 + log₂ Y}`. (The bracket decreases in n.)
* **So Theorem A holds as stated for |V| ≥ 42.** With soj.md's crude sums one gets the corrected
  coefficient `(13Y + 102)·51/(243·42) ≤ Y/15 + 0.51` for n ≥ 42.

The other parts of Theorem A use only the per-call closed forms (§1.3, every n), the call count
`L + 1 ≤ n2_0 < n/3` and `J < Y/δ` (§1.2 row 8), `d < Y + 2`, `130d ≤ 130Y + 260`: valid for n ≥ 42.

*Theorem U.* ownwork.md §8.3 bounds the run at `n = |V| ≤ m` by expressions that are non-decreasing in
`n` and in `Y = log₂ n` and evaluates them at `n = m ≥ 90`. All facts used for a run on
`42 ≤ |V| ≤ m` are valid (rows 2–11, Lemma K-run and U-SO, which use only `|V| ≤ m`). Evaluating at
`|V| = m ≥ 90 > 61` makes every simplification of soj.md that used n ≥ 61 valid; in particular the
uncollapsed d-ary sum `(13Y + 102)(1/243 + 1/(27n))n^{6+log₂Y}` is non-decreasing in n and at n = m
is `≤ (0.0589y + 0.462)m^{6 + log₂ y} ≤ (y/16 + 1/2)m^{6 + log₂ y}`. **Theorem U holds for every run of
case 2b**; §2 gives the complete proof with explicit constants.

### 1.6 (iv) Theorem B for |V| ≥ 42

The steps of soj.md §2.B, one by one, with `Y_V := log₂|V| ≥ log₂ 42 = 5.39`:
* **(★)** lists the choice points (x: n candidates; the tie of `select_min`: `≤ Lc ≤ n²/4`; DL
  prefixes `≤ n2_j^{d_j−1}` together with the coherent point; the half split `< n/3`). The thin-cycle
  exit (soj.md §2.B, after (★)) makes the run `x, y` with `n(n−1)` sequences, `log₂ ≤ 2Y_V`, which is below the
  right side of (★) in case 2b (`≥ 3Y_V − 2`). None of these uses n ≥ 61.
* **Lemma R**: `C(n2,t) ≥ (n2/t)^t ≥ 2^Y = n > N1`; every n.
* **R3** (`n2 < 2Y + 4`) and **R2** (`2Y + 4 ≤ n2 < Y²`): every n (R2 is empty for `Y ≤ 3.24`).
* **R1** (`n2 ≥ Y²`): `μ ≤ Z/2` uses `2Y/Z + 1 ≤ Y/log₂Y + 1 ≤ Y`, true for **`Y_V ≥ 4`**, i.e.
  `|V| ≥ 16`; `#R1 < Y/δ` uses `n2 ≥ 6` (row 8). So the region bounds hold at `Y_V` — not only the
  final simplification needs a size condition, but the extra condition `|V| ≥ 16` is satisfied.
* **Passing to m**: every term of R is non-decreasing for `Y ≥ e` (soj.md §2.B, proof of Theorem B, "Passing to m"), and
  `Y_V ≥ 5.39 > e`.
* **Final simplification** at `Y = log₂ m ≥ 6.49`: `log₂(Y/log₂Y + 1) ≤ log₂ Y` (Y ≥ 4),
  `ln(Y/log₂ Y) ≤ ln2·log₂ Y` (Y ≥ 2), `(log₂Y − 1)/δ + 1 ≤ log₂Y/δ` (δ < 1),
  `log₂(2Y + 4) ≤ log₂ Y + 1.42` iff `4/Y ≤ 2^{1.42} − 2 = 0.6759` iff `Y ≥ 5.918`. Coefficients
  (ℓ := log₂ Y): `Yℓ²: 2ln2/δ + 2/δ = 5.789 ≤ 5.8`; `Yℓ: 2ln2 + 1/δ + 3 = 6.096 ≤ 6.1`;
  `Y: 2 + 2 (log₂(Y/ℓ + 1)·2Y/ℓ) + 4.26 = 8.26`, plus `2` for `[2Y]_2b`: `10.26 ≤ 10.3`;
  `ℓ²: 2/δ = 3.42 ≤ 3.5`; `ℓ: 6`; constant `8.52 ≤ 9`.

**Theorem B holds as stated for m ≥ |V| ≥ 42.** Note: the `10.3Y` of the simplified R already
contains the case-2b tie term `[2Y]_2b`; the "`+ 2y`" of case 2b in PROOF.md §10 counts it a second
time, which is harmless (the WL-path coefficient is `8.26 ≤ 8.3`).

### 1.7 Remarks

* The arguments above use |V| only through `bound ≥ 6`, `n1_orig ≥ 6`, `n2 ≥ 6` at Phase 5,
  `Y_V ≥ 4` and the d-ary coefficient. `n2 ≥ 6` follows from `N1 ≥ 19` (`C(5,2) = 10 < 20 = C(6,3)`),
  i.e. from `|V| ≥ 27`; the midpoint coefficient at n = 27 is `0.265 ≤ 0.797`. So soj.md's run
  analysis holds for every `|V| ≥ 27`. Case 2b needs this only through the lower bound `|pts| ≥ 42`,
  which rests on CFSG (CORRECTNESS.md Lemma 10.6).
* **Effect on ω: unchanged.**

---------------------------------------------------------------------------------------------

## 2. Theorem U with every group bounded explicitly

### 2.1 Setting

One run of `upcc_split_or_johnson` on `V` (`42 ≤ n := |V| ≤ m` in case 2b, `n = |C| > 2m/3` in the
EDL paths), base on `M = m ≥ 90` points, `y = log₂ m ≥ y₀ := log₂ 90 = 6.491853`, `Y = log₂ n ≤ y`,
`L := ⌈lg n⌉ ≤ Y + 1`, `δ = log₂(3/2) = 0.5849625`, `1/δ = 1.709512`. Facts used (soj.md, ownwork.md):
the run is upcc → B_0 → … → B_L with `< n/3` bipartite calls; `J < Y/δ` choice levels (§1.2 row 8);
`d_j < Y + 2`, `n2_j < n/3`, `T_j = n2_j^{d_j} ≤ Tm := (n/3)²n^{1+log₂Y}` (Lemma T); keys of
soj-size `≤ 85m` and height `≤ 13m` (Lemma K-run), so every structure operation costs `≤ SO = 2048m⁴`
(U-SO). Every bound below is a sum of terms with non-negative coefficients, each non-decreasing in
`n` and `Y`; so the run's own work is at most the value at `n = m`, `Y = y`, `L = y + 1`,
`J = y/δ`, which is what is written. The string factor 17 (ownwork §1.3) multiplies everything.
In case 2b too `m = |Γ| ≥ 90` (a Johnson node); only `|V|` can be as small as 42, and §1 shows that
every fact used here holds for such runs, so no separate range `m ≥ 42` is needed.
`2^{U(y)} = (y+2)⁴ m^{7 + 2log₂y}`; at m = 90: `(y₀+2)⁴ = 5200.08`, `2^{U(y₀)} = 8.7753·10²⁷`
(`log₂ = 92.8255`).

### 2.2 Lemma Mono (the ratios decrease)

For `y ≥ y₀` (`1/(y ln2) ≤ 0.22224`, `2log₂y ≥ 5.3973`, `log₂ y ≥ 2.6986`, `1/ln 2 = 1.4427`):
* **(M1)** `f = c·∏_i (y + a_i)^{e_i}·m^b` with `a_i ≥ 0`, constant `b ≤ 7`, `E := Σe_i ≤ 37`:
  `g := log₂(f/2^U) = const + Σ e_i log₂(y + a_i) + (b − 7 − 2log₂y)·y − 4log₂(y+2)`,
  `g' ≤ E/(y ln2) + b − 7 − 2log₂ y − 2/ln2 ≤ 0.22224E + b − 15.2827 < 0`.
* **(M2)** `f = c·∏(y + a_i)^{e_i}·m^{b + log₂ y}` with `b ≤ 6`, `E ≤ 23`:
  `g' ≤ 0.22224E + b − 7 − log₂ y − 1/ln2 ≤ 0.22224E + b − 11.141 < 0`.
* **(M3)** `f = (y/δ)·Tm·(y+2)^{y+2}·B(y)` with `Tm = m^{3 + log₂y}/9`,
  `B(y) = 14(y+2)(y+1) + 11(y+2) + 476 = 14y² + 53y + 526`:
  `f/2^U = (y/δ)·B(y)·(y+2)^{y−2}/(9 m^{4 + log₂ y})`, and
  `g' = 1/(y ln2) + B'/(B ln2) + log₂(1 + 2/y) + ((y−2)/(y+2) − 1)/ln2 − 4 ≤ 0.2223 + 0.4445 + 0.3880 − 4 < 0`
  (`B'/B ≤ 2/y` because `2B − yB' = 53y + 1052 > 0`).

So for every term of these forms the ratio to `2^{U(y)}` is largest at m = 90, and a sum of such
terms has its ratio bounded by the sum of the ratios at m = 90.

### 2.3 The groups (derivations)

**G1a, d-ary part of Theorem A** (soj.md Theorem A, [d-ary part]; §1.5): `(y/16 + 1/2)·m^{6 + log₂ y}`. Form (M2), b = 6.

**G1b, the rest of Theorem A without callees** (soj.md Theorem A, lines [no-choice levels],
[choice levels], [upcc itself]; for the line [thin-cycle exit], `16n² + 2n⌈lg n⌉ + 94n + 82 + 12M`,
the larger `TC` of ownwork §3.4 without its choose and refine, `16n² + 2n⌈lg n⌉ + 97n + 100 + 13M`):

    G1b = 14m³ + (m³/18 + m² + m)(y+1) + 152m² + 763m + 4m³ + 29m²
          + (y/δ)·[4162 + 130y + 758m + 185m² + (m²/6 + 8m + 2)(y+1) + 114m + 12m²]
          + 765 + 354m + 54m² + 9m²y + 10m(y+1) + 34m + 4m² + 16m² + 2m(y+1) + 97m + 100 + 13m.

All terms are (M1) with b ≤ 3, E ≤ 2.

**G2, structure operations.** Calls in a run: upcc `individualize` and `refine`
(soj.py:297, 299), `≤ g_t ≤ (n−1)/2` `split_by_blocks` of tied key classes, the thin-cycle `refine`;
per bipartite call `cell_of` and the Phase-2 `refine` (soj.py:432, 438); one terminal of ≤ 2
(`split_by_blocks`, or `with_johnson`, or `mark` + `refine`); per choice level `≤ d_j − 1` marks
(P7), `key_of_vertex` and `refine` (P8), and ≤ 2 in `coherent` (mark + refine, or one
`split_by_blocks`). Total `N_SO ≤ 5 + n/2 + 2n/3 + J(Y + 5)`, each `≤ SO`; plus `C_JC = 9` once:

    G2 = (5 + 7m/6 + (y/δ)(y + 5))·2048m⁴ + 9          (≤ 2.64m·2048m⁴ ≤ 4m·SO).

(M1), b ≤ 5, E ≤ 2.

**G3, chooser.** `Ck(σ) = 53 + σ` (soj-size σ ≥ the structure_cc_wl.md size), `Cc ≤ 104`. In upcc:
checks of sizes 8, 11, 12, 9 (`≤ 252`). In one bipartite call together with its `coherent` or
`_split_by_coloring_of_v2` member, the checks are those of soj.py:414 ("bsoj"), "bsoj-dom",
"bsoj-d1", "bsoj-complete", "bsoj-twin-blocks", "bsoj-dary" (size `13 + D ≤ 14 + n`), "bsoj-twk",
"bsoj-twk-pick", `≤ d` checks "dl" of design_lemma, "bsoj-wl-dom2", "bsoj-wl-dom1", "bsoj-c1c2",
"bsoj-sub2clique", "bsoj-cohout", ≤ 7 checks of `coherent` (incl. two `select_min` checks) or
"split-v2": at most `25 + d` checks, all of size ≤ 18 except "bsoj-dary". (The checks inside
`refine_structures` and `classical_wl` are in their bounds.) Chooses: x, the tie or the thin-cycle y,
per choice level the DL prefix and the coherent point, the half split: `≤ 4 + 2J`. With `d ≤ y + 2`:

    G3 = 252 + 104(4 + 2y/δ) + (m/3)·(1917 + 71y + m).

(M1), b ≤ 2.

**G4, hashing and canon callbacks.** `C_key = 14`, `C_hk(σ) = 5 + 169σ` (canon ≤ 169σ on set-free
objects, group.md §6), `C_Fix = 5`. upcc (soj.md U(n)): `(n + n²)C_key + (n + n²/2)C_hk(1) +
(n²/4)(C_hk(3) + C_Fix) = 230.25n² + 188n`. Per choice level: `_split_by_coloring_of_v2`
`n2·C_hk(1) ≤ 58n`; `coherent` `2n(C_key + C_hk(1) + C_Fix) = 386n` (two `select_min` over ≤ n
candidates, or one and the `X.key` colouring of C1); P8 `Ntot·C_hk(K) ≤ n(5 + 169·85m)` (vcol):

    G4 = 230.25m² + 188m + (y/δ)(14365m² + 449m).

(M1), b ≤ 2.

**G5, cc callees** (Table U of ownwork with structure_cc_wl.md §5, int colours, `r, r' ≤ N²`).
upcc: `C_diag(n) = 7 + 3n`. Per kind-'b' level: `C_CC(Ntot) + Ntot²(C_c + C_col) + 4C_indc +
2C_clq + 2C_disc + C_comp + C_odc + n2·C_od` with `C_c = 40 + 10d ≤ 60 + 10Y`, `C_col = 45`:

    per level ≤ 158n⁴ + 2n³L + 388n³ + 60n²L + 10n²Y + 1554n² + 376n + 1276,
    G5 = 7 + 3m + (y/δ)·[158m⁴ + 2m³(y+1) + 388m³ + 60m²(y+1) + 10m²y + 1554m² + 376m + 1276].

(M1), b ≤ 4, E ≤ 2.

**G6, wl callees, except the dominant term.** Per choice level j (soj.md §2.A.2 callee list):
* `refine_structures(n2_j, d_j) ≤ 131 + N^k k^k(14kλ(N) + 11k + 476) + (4k² + 54k + 286)N^{2k+1}λ(N)`
  (structure_cc_wl.md), `N = n2_j`, `k = d_j`, `N^k ≤ Tm`, `k^k ≤ (Y+2)^{Y+2}`, `λ(N) ≤ Y + 1`.
  The first part summed over the levels is
  **G6a** `= (y/δ)·[131 + Tm·(y+2)^{y+2}·(14(y+2)(y+1) + 11(y+2) + 476)]`, form (M3) plus (M1);
  the second part is the dominant term (§2.4).
* DL callees `2(T/n2)(C_pvc + C_ppc) + 2T·n2·C_c` with `C_pvc = 49 + 41n2 + 10dn2`, `C_ppc = 41 + d`,
  `C_c = 40 + 10d`, `n2 ≥ 6`: `≤ T[112 + 20.34d + (80 + 20d)n2]`; plus `C_pvc` once:
  **G6b** `= (y/δ)·[Tm·(153 + 20.34y + (120 + 20y)m/3) + 49 + 41m/3 + 10(y+2)m/3]`, form (M2), b ≤ 4.
* kind 'b': `classical_wl(Ntot)` without its callbacks (structure_cc_wl.md closed form without
  `N²·C_cb`; the callbacks are in G4, G5 and the own instructions), with `ν ≤ 3·85m + 3`,
  `η ≤ 2·13m + 2` (vcol returns `("v1"/"v2", …, canon(key))`, Lemma C), `canon(ν+2) ≤ 169(ν+2)`;
  `C_ppc(d) ≤ 43 + y`; `C_KS = 27` per Phase-5 call (≤ 9n in all):
  **G6c** `= (y/δ)·[(48(y+1) + 382)m⁵ + (255m + 5)m⁴ + 12(26m+4)(255m+5)m²(y+1) + (1785m+101)m²
  + (43095m + 845)m² + 38m + 229 + 43 + y] + 9m`, form (M1), b ≤ 5.

### 2.4 The dominant term

Second part of `refine_structures`, summed over the `J < y/δ` levels, at n = m:
`(y/δ)·(4(y+2)² + 54(y+2) + 286)·(y+1)·Tm²·(m/3)`, `Tm²·(m/3) = m^{7 + 2log₂y}/243`. With
`y(y+1) ≤ (y+2)²` and `4 + 54/(y+2) + 286/(y+2)² ≤ 14.32512` for `y ≥ y₀`:

    D6 ≤ 14.32512/(243δ) · (y+2)⁴ m^{7+2log₂y} = 0.100778·2^{U(y)},   17·D6 ≤ 1.71322·2^{U(y)}.

(Evaluated exactly at m = 90, `17·D6 = 1.1555·2^{U}`.)

### 2.5 Values at m = 90 and the conclusion

| group | form | value at m = 90 (before ×17) | `17·value/2^{U(y₀)}` |
|---|---|---|---|
| G1a | (M2) | 9.0414·10¹⁶ | 1.76·10⁻¹⁰ |
| G1b | (M1) | 3.4956·10⁷ | 6.8·10⁻²⁰ |
| G2 | (M1) | 3.1917·10¹³ | 6.2·10⁻¹⁴ |
| G3 | (M1) | 7.7014·10⁴ | 1.5·10⁻²² |
| G4 | (M1) | 1.2936·10⁹ | 2.6·10⁻¹⁸ |
| G5 | (M1) | 1.1849·10¹¹ | 2.3·10⁻¹⁶ |
| G6a | (M3)+(M1) | 1.9091·10²² | 3.70·10⁻⁵ |
| G6b | (M2) | 1.3137·10¹⁵ | 2.6·10⁻¹² |
| G6c | (M1) | 5.0052·10¹⁴ | 9.7·10⁻¹³ |
| sum | | | ≤ 3.70·10⁻⁵ |

(A direct bound for G6a: with `(y−2)log₂(y+2) − y log₂ y = y log₂(1 + 2/y) − 2log₂(y+2) ≤ 2/ln2 − 2log₂(y+2)`
one gets `G6a/2^U ≤ (y/δ)·B(y)·e²/(9(y+2)²m⁴)`, which at m = 90 is `≤ 2.82·10⁻⁶`, times 17
`≤ 4.8·10⁻⁵`.)

By Lemma Mono each ratio is non-increasing in m, so for all m ≥ 90:

    17·(G1a + G1b + G2 + G3 + G4 + G5 + G6a + G6b + G6c) ≤ 3.7·10⁻⁵·2^{U(y)}   (≤ 0.03·2^{U(y)} as stated),
    W_UPCC ≤ (1.71322 + 0.00004)·2^{U(y)} ≤ 1.714·(y+2)⁴ m^{7 + 2log₂ y} ≤ 1.87·(y+2)⁴ m^{7 + 2log₂ y}.

This holds for every run of case 2b (§1) and of the EDL callers.

### 2.6 Corrections to the lists of ownwork §8.3 (no effect)

* Group 2: per choice level the count is `≤ d_j + 3 < y + 5` (ownwork: `d_j + 5 ≤ y + 6`, but
  `d_j + 5 < y + 7` only); in total `N_SO ≤ 2.64m`, within the stated `4m`.
* Group 3: "checks ≤ 395 + D_i" per bipartite call is right for calls without a choice (the maximum
  over those paths is `389 + D`), but a choice level also makes the checks of P8 and of `coherent`
  (about 860 more) and `d` checks "dl"; G3 above includes them.
* `(n + n²)C_key` is in ownwork's group 5; here it is in G4.

**Effect on ω: unchanged** (`0.91 + U(y)`; `log₂ 1.714 = 0.78` would also be valid).

---------------------------------------------------------------------------------------------

## 3. Item 9: polynomial parts of CERT, CJ and aggregate (ownwork §8.8)

### 3.1 Ranges and units

Johnson node: `90 ≤ m ≤ n`, `k ≤ m/10 ≤ n/10`, `⌈lg n⌉ ≤ n/10` (n ≥ 90), `⌈lg k⌉ ≤ k`, every group of
degree ≤ n + m ≤ 2n has `≤ 3n` generators (`r̂ ≤ 3n`, F1), `J + 1 ≤ n + 1` (johnson_certs.md §3.16),
`λ ≤ k!` (INV-A, §5). Units of ownwork Table U: `B1 = 4096n⁵`, `B2 = 65536n⁵`,
`C_φ = 14n² + 164n + 517`, `PG(k, ≤3n) ≤ 1876k⁵ + 669nk² + 24nk + 240n + 2k + 113` (Init0 plus F2),
`ORD_k ≤ 17 + 1876k⁵ + 1338k³` (`order` of a degree-k group: a build not done in `__init__` has
≤ 6 generators, `Build(k, 6) ≤ 1876k⁵ + 1338k²`; otherwise `17 + 149`).
Collapse to `n⁶`: a monomial `n^a`, a ≤ 6, is `≤ 90^{a−6}n⁶` (F5, v₀ = 90).

### 3.2 CERT (one uncached `certificate`, johnson_certs.md §3.16 with the external callees substituted)

*Builds.* SW: `intersect_image` B1, `image_is_sym` B1, `preimage` 4B2, `order` B1, `subgroup`
B2 + B1 → `5B2 + 4B1`; each of the `≤ J + 1` KL calls that are not cache hits (johnson_certs.md
§3.15): `PermGroup(n+m)` B2, `levels` B2, `level_group` 2B2, `order` B2, `coset_reps_prefix` B2,
`PermGroup(n, r_K)` B1 → `6B2 + B1`; each of the `≤ J + 1` RC calls: `generated_subcoset` B1,
`subgroup` B2 + B1 → `B2 + 2B1`; `pointwise_stabilizer` 2B1. Total
`(7n + 12)B2 + (3n + 9)B1 ≤ (11n + 16)B2 + (4n + 10)B1` (ownwork uses the right side).

*k!-terms* (per round, ≤ n + 1 rounds): own `k!(2n + 2k² + 60k + 161)` (johnson_certs.md), KL's
`coset_reps_prefix` `k!(k+1)(6n+75)`, RC's `k!(Inv + Act + Mul) = k!(24n + 70)`, `PermGroup(k, k!)`
`k!(8k + 80 + 223k²)`, `generated_subcoset` pieces `1736k!n³`. Besides `1736k!n³` the bracket is
`225k² + 143k + 6nk + 32n + 386 ≤ 2.85n² + 46.3n + 386 ≤ 3.42n² ≤ 0.038n³`, so
**CERT_k! ≤ 1737(n+1)k!n³** (ownwork writes "≤ 2.9k!n² ≤ 0.04k!n³"; the first number is too small,
the second and the conclusion hold).

*Polynomial part* (everything else):

    own   (n+1)[n⌈lg n⌉ + 69n + 3n(2n + 37k + 95) + 119k + 957] + 3n(111k + 230) + 3k⌈lg k⌉ + 18k + 20n + 14m + 850
    E1    SW externals:  1238n³ + 291n² + 3013n + 36m + 9412
          (subgroup 1238n³; intersect_image(4) 24n² + 774n + 1875; image_is_sym 24n² + 243n + 315;
           preimage(8) 243n² + 1996n + 6840; sym_gens ×2 ≤ 36m + 382)
    E2    IOA, IG:  (n+3)·[2·PG(k, 3n) + ORD_k]
    E3    KL externals of the non-hit calls:  (n+1)(120n² + 752n + 270)
    E4    AFF orbits:  (n+1)·800n²
    E5    RC externals:  (n+1)(1238n³ + 1876k⁵ + 2k + 113)
    E6    pointwise_stabilizer: 450n²;   E7  r_K·phi: 3n·C_φ;   E9  CE orders: (n+2)·ORD_k.

With the substitutions of §3.1:

    CERT_poly ≤ 0.0938n⁶ + 0.22512n⁵ + 1254.06n⁴ + 3506.83n³ + 3816.43n² + 9485.1n + 12365 ≤ 0.25600·n⁶.

(`n⁶`: `5628 + 1876 + 1876 = 9380` times `10⁻⁵` from `k⁵ ≤ n⁵/10⁵` in E2, E5, E9; `n⁴`:
`1238 + 13.38 + 1.338 + 1.338`; collapse `0.0938 + 0.22512/90 + 1254.06/8100 + 3506.83/90³ + … =
0.255993`.)

### 3.3 CJ (`conjugate`, johnson_certs.md §3.14)

*Builds:* `subgroup` B2 + B1, `Σ_i PermGroup(n, r_{N,i}) + PermGroup(n, r_K)` (≤ n + 2 groups) →
`B2 + (n + 3)B1`. *k!-terms:* `(n+1)k!(15k + 67)` own, `2Λ·Mul`, `Σ_i PermGroup(k, λ_i)`'s
`Λ(8k + 80 + 223k²)`, `Λ ≤ (n+1)k!`: `≤ (n+1)k!(223k² + 23k + 6n + 169) ≤ 2.35(n+1)k!n² ≤ 2.4(n+1)k!n²`
(ownwork omits `8k + 80`; the bound holds).

*Polynomial part:*

    own   560 + 2k⌈lg k⌉ + 27k + 25n + 3n(37k + 19n + 132) + (n+1)(50n + 245)
    ext   Inv 10n + 29;  2(r_H + R_N + r_K)·Mul ≤ 2(3n² + 9n)(3n + 11);  10(n+3);  subgroup 1238n³;
          IOA PG(k, 3n);  phi C_φ;  (n+2)(24n² + 240n) [PermGroup(n,·) Init0 parts];
          (n+1)(113 + 2k + 1876k⁵) [PermGroup(k, λ_i) non-k! parts];  (n+2)·ORD_k [CE].

    CJ_poly ≤ 0.03752n⁶ + 0.07504n⁵ + 1.338n⁴ + 1289.37n³ + 542.72n² + 1951.1n + 1641 ≤ 0.04030·n⁶.

### 3.4 aggregate, one miss (main.md §aggregate)

`F ≤ 3nM` (each `K(A)` has ≤ 1.5n generators), `r_F ≤ 1.5m`, `φ ≤ m`, `+64` for the string key (C6):

    A ≤ M·(CERT + CJ) + M(Inv + Ident) + F(Isid + 2C_φ) + PermGroup(m, F) + M(157 + 9k) + (47 + 2n)F
        + M²(65 + F(85 + 34k + Mul)) + [non-M terms],

`M(Inv + Ident) = M(12n + 62)`; `F(Isid + 2C_φ) ≤ M(84n³ + 993n² + 3219n)`; `PermGroup(m, F) ≤ B1 +
247Fn² ≤ B1 + 741Mn³` (U-PG); `(47 + 2n)F ≤ M(6n² + 141n)`. The M-proportional part outside
CERT + CJ is

    AGG_M_extra = 825n³ + 999n² + 3372.9n + 219 ≤ 0.001148·n⁶.

Non-M terms: first generic phi `B2 + 60n² + 359n + 529`, `PermGroup(m,F)`'s `B1`, `is_giant_on(m, r_F)
≤ m + 19 + 2B1 + 1.5m(8m + 80)`, `orbits ≤ 400n²`, `r_F·restrict_to ≤ 1.5m(37m + 67)`,
`LocalCertificates (n + 31)`, own `705 + 4λn + 86m + 2m⌈lg m⌉ + (22m + 8)r_F + 64`: at λ = 1,
`≤ 77825n⁵`. Since `M ≥ C(10k, k) ≥ 10^k ≥ 10^{X+2} ≥ 100n³`, this is `≤ 77825/(100·90⁴)·Mn⁶ ≤
1.2·10⁻⁵ Mn⁶` (ownwork justifies "≤ 0.01Mn⁶" by `M ≥ n`, which is not enough: it would need
`n ≥ 2790`; `M ≥ 100n³` suffices).

BFS: `M²(65 + F(96 + 34k + 3n)) ≤ 65M² + M³·3n(96 + 6.4n) ≤ 65M² + 22.4n²M³` (n ≥ 90).

### 3.5 The coefficients

Per miss, the M-proportional terms are (with ownwork's build count)

    M·[(11n + 17)B2 + (5n + 13)B1] + M·(CERT_poly + CJ_poly + AGG_M_extra) + M·k!-terms
    ≤ (741376 + 1167360/90 + 0.25600 + 0.04030 + 0.00115)·Mn⁶ + …  = 754346.97·Mn⁶ + M·k!-terms,

so `≤ 754347 Mn⁶` as stated. Two misses (λ = 1; F6 for λ ≥ 1):

    A_x + A_y ≤ λ·(1508694 Mn⁶ + 3514 Mk!n⁴ + 44.8 n²M³ + 131 M²)

(`2·754346.97 + 2·1.2·10⁻⁵ ≤ 1508694`; `2·(1737 + 2.4/n)(1 + 1/n) ≤ 3512.7 ≤ 3514`; `2·22.4 = 44.8`;
`2·65 = 130 ≤ 131`). **The stated `1508700 Mn⁶ + 3514 Mk!n⁴ + 44.8n²M³ + 131M²` is proved.**

A second, independent way: the polynomial parts are absorbed by the difference between ownwork's
build count and the true one, `(n+1)(4B2 + B1) = 266240(n+1)n⁵`. With the true count
`(7n + 13)B2 + (4n + 12)B1` per miss one gets `485148.45 + 0.30` per miss, so
`A_x + A_y ≤ λ(970300 Mn⁶ + 3514 Mk!n⁴ + 44.8n²M³ + 131M²)` also holds.

**Effect on ω: unchanged** (`ω_agg ≤ 20.53 + 3lM + LKF + 6X`; with 970300 it would be `19.89 + …`).

---------------------------------------------------------------------------------------------

## 4. Item 10: Lemma CH (choice parameters of the procs with choices)

The procs are `proc2` of N6b-EDL (main.py:611–614), the proc of case 2b (main.py:737–739 →
`case_2b_structure`) and the proc of case 3 (main.py:1018–1033). The bounds hold for every run
(the x-run and every replay run: a completed replay consumes the whole trace, so it has the same
number of choice events, and its chosen objects obey the same structural bounds). J denotes the
number of choice levels of the upcc run, `J < Y/δ ≤ y/δ` (soj.md (I8), which rests on WL coherence);
for `90 ≤ m ≤ 129`, `y/δ < 12`, so `J ≤ 11`.

### 4.1 d (choice events)

`chooser.choose` calls (in soj.py, design.py, main.py, structure.py):
* `extended_design_lemma`: the DL prefix (soj.py:270), once; its `select_min` has distinct int
  keys (EDL's `cc.key` is the identity on distinct colours): no choice.
* upcc run: x (soj.py:294); either the thin-cycle y (soj.py:363) or the `select_min` tie
  (soj.py:147, only with tied keys, i.e. case 2b) followed by the bipartite chain: per choice level the
  DL prefix and at most one coherent point (soj.py:729, 746, 768), and at most one half-split point
  (soj.py:488). `individualize_until` and `_individualize_v2` are not reached (soj.md (I7)).
  At most `3 + 2J` events.
* `case_2b_structure`: one choose per iteration of the loop at main.py:919–936; each iteration has
  `np_ ≥ 3` and removes one point, so `≤ |Phi| − 2 ≤ m − 2` (4 under CFSG); then either the
  disconnected branch (one `select_min` tie, then return) or the upcc run.
* `hypergraph_structure`, `case_3`'s proc before EDL: no choose.

So `d ≤ 4 + 2J` (N6b-EDL, case 3) and `d ≤ m + 1 + 2J` (case 2b). For `m ≤ 129`: `d ≤ m + 23 ≤ 1.3m`
(m ≥ 77); for `m ≥ 130`: `1 + 2J < 1 + 3.42y ≤ 0.3m` (true at m = 130, and `0.3m − 3.42log₂m` is
increasing for m ≥ 17). **`d ≤ 1.3m`.**

### 4.2 κ (size of `tuple(chosen)`, relevant only when no `Fixed` was chosen)

Sizes in soj.md's convention (a string costs 1 + its length; this dominates the structure_cc_wl.md
size used by main.md). Chosen objects:
* ints (case-2b points, x, y): size 1, at most `m − 2 + 2`;
* the EDL prefix candidate `(tuple of ℓ ≤ k−1 ints, "a"/"b")`: `1 + (1 + ℓ) + 2 ≤ k + 3`;
* per choice level, the DL candidate `(tuple(V2[i] for i in tup), kind)`: `≤ 4 + Σ_{p∈tup}σ(p) ≤ 4 + Σ2`
  (distinct points), and the coherent point `σ(p) ≤ Σ2`; the half-split point `≤ Σ2`.
* `Σ2 ≤ 2U2 − n2 < 2U2 < 2|V|/3 ≤ 2m/3`: soj.md Lemma P (every point is an int or a frozenset of
  ≥ 2 points with disjoint underlying sets, so `σ(p) ≤ 2u(p) − 1`), and `U2 ≤ U2_0 ≤ |V| − 1 − |V1_0|
  < |V|/3`, because the underlying sets of every later V2 lie inside those of V2_0.

Case 2b has no EDL prefix and the EDL paths have no case-2b points, so

    κ ≤ 1 + max(m, k + 4) + J(4 + 4m/3) + 2m/3 ≤ 3 + (5/3)m + (y/δ)(4 + 4m/3).

At m = 90: `≤ 153 + 11.098·124 = 1529.2 ≤ 0.189m²`; `κ/m²` is decreasing in m. **`κ ≤ 0.23m²`.**

### 4.3 Heights of chosen objects

New points are created only at the contraction of `coherent` (soj.py:756:
`W2 = [frozenset(v2_of(w) for w in blk) for blk in B]`); every other step passes sub-lists of the
current V2 (soj.py:530, 608, 677; `coherent` B2 and C2). A contraction raises the maximal height of a
point by 1, and it happens at most once per `coherent` call, i.e. at most once per kind-'b' choice
level. Points of V2_0 are ints (height 0). Hence every point has height `≤ J`, a DL candidate
`(tuple of points, str)` has height `≤ J + 2`, the EDL candidate height 2, ints 0. So every chosen
object has height `≤ J + 2 < y/δ + 2` (`≤ 13` for m ≤ 129), far below the stated `≤ m`.
`apply_obj` preserves sizes and heights (it maps ints to ints elementwise), so all keys in
`_covered` obey the same bounds.

### 4.4 A'

`A_key ≤ Σ_o (130 + 15h(o))|o| ≤ (160 + 15J)κ` (structure_cc_wl.md `apply_obj`), so

    A' = 53 + 22d + 4κ + A_key ≤ 53 + 28.6m + (164 + 25.65y)·κ ≤ 53 + 28.6m + (164 + 25.65y)(3 + (5/3)m + (y/δ)(4 + 4m/3)),

`≤ 6.2·10⁵ ≤ 0.0095m⁴` at m = 90, decreasing relative to `m⁴`. **`A' ≤ 0.8m⁴` (in fact `≤ 0.01m⁴`).**
Lemma CH is proved as stated (with the inherited assumption 7 through Lemma P and (I8)).
**Effect on ω: unchanged.**

---------------------------------------------------------------------------------------------

## 5. INV-A: |lifts| ≤ k!

`LocalCertificates.kernel_and_lifts(H, A_sorted)` (certificates.py:209–230) builds
`comb = PermGroup(n + m, H.combined_gens, forced_prefix=[n + a for a in A_sorted], …)`, sets `kA` to
the number of leading levels with base point in `Aset = n + A`, and appends one lift per element of
`comb.coset_reps_prefix(kA)`.

**(a) The count (unconditional, group.py).** `coset_reps_prefix(kA)` (group.py:424–440) sets
`k = min(kA, len(levels)) = kA` (the while loop at certificates.py:220 keeps `kA ≤ len(levels)`) and
yields from `rec(kA − 1, id)`, which iterates over `levels[i].trans.values()` and recurses to i − 1,
yielding at i = −1. So exactly `∏_{i<kA} |levels[i].trans|` representatives, and
`|lifts| = ∏_{i<kA} |levels[i].trans|`.

**(b) The bound (needs INV-A, not Schreier–Sims completeness).** johnson_certs.md Lemma B is proved
from the code of `_build`: (a) the base points are distinct; (b) level generators and transversal
values lie in the group generated by the generator list `gl` used in the build and fix the earlier
base points; (c) the keys of `trans_i` lie in the orbit of `b_i` under the level generators. Let
**INV-A'**: every element of `gl` maps `X = n + A` onto itself. Then the orbit of `b_i ∈ X` under
`levels[i].gens` lies in `X ∖ {b_0, …, b_{i−1}}` (a permutation fixing `b_l` maps no other point to
`b_l`), so `|trans_i| ≤ k − i` for `i < kA`, and `|lifts| ≤ k!/(k − kA)! ≤ k!` (`kA ≤ k` by (a)).
`gl ⊆ H.combined_gens` (PermGroup keeps distinct non-identity elements of the passed list, and
pruning keeps a sub-list, group.py:46–75, 197), and `H.combined_gens[i] = H.G.gens[i] + (n + p_i[v])_v`
with `p_i = H.phi_gens[i]` (action.py:169), which maps `n + A` onto itself iff `p_i(A) = A`.
So INV-A' follows from **INV-A**: every element of `H.phi_gens` maps A onto A.
Without INV-A, `X = n + range(m)` is always invariant (each `p_i` is a permutation of range(m)),
which gives `|lifts| ≤ m!/(m−k)!` (johnson_certs.md §1.7).

**(c) INV-A from HOM.** Assume **HOM** for `Gw = jd.Gw`: `G.gens[j] ↦ phi_gens[j]` extends to a
homomorphism `φ: G → Sym(Γ)`, and `Gw.phi(g) = φ(g)` for every `g ∈ G` (CORRECTNESS.md Lemma 3.3 at
main.py:290 and main.py:343, with Lemmas 4.4 and 4.5 and the remark after Lemma 4.4 for the fast
`phi_fn`). Then every `GroupWithAction` made by `Gw.subgroup` has `phi_gens = φ(gens)` and
`⟨combined_gens⟩ = {(g, φ(g))}`; in particular an element of `⟨combined_gens⟩` that fixes a set of
points `n + B` pointwise (resp. setwise) has a φ-image fixing B pointwise (setwise). The callers of
`kernel_and_lifts` are `affected` and `recompute` (certificates.py:198, 273), both called only in
`certificate` with `H_0 = setwise_stabilizer(A)` or `H_i = recompute(H_{i−1}, …)` (certificates.py:297,
311, 328). Induction on i:
* `H_0` (certificates.py:175–185): its generators are a sub-list of `lifted + K.gens` of `preimage`
  (action.py:278–290, 292–296). `K = Gw.kernel()` has generators `g[:n]` with g a level generator of
  `comb_gamma` below the prefix levels of the moved Γ-points; such g fixes those points (Lemma B(b))
  and the unmoved ones, so `φ(K.gens) = id`. `lifted = Gw.lift(h)`: `lift` (action.py:248–268) returns
  `g[:n]` for a product g of transversal values of `comb_gamma` whose Γ-part is `n + h` (the final
  check at action.py:265–268), so `φ(lift(h)) = h`. Here `h ∈ intersect_image(...)`, i.e. a
  non-identity element of `sym_gens(sorted(A), m) + sym_gens(Γ∖A, m)` (a transposition and a cycle
  inside A, resp. inside Γ∖A, perm.py:144–152) or a product of such elements and inverses
  (`even_subgroup_gens`, group.py:498–519). All of them map A onto A.
* `H_i`: `recompute` (certificates.py:271–287) returns `Gw.subgroup(Hgroup.gens + [rep])` with
  `(Hgroup, rep) = generated_subcoset(n, pieces)` (group.py:480–495), whose generators are a sub-list
  of `∪_j C_j.group.gens ∪ {s_j s_1^{-1}}` and `rep = s_1`, `s_j = C_j.rep·σ_j`. Here `σ_j = r[:n]` with
  `r ∈ ⟨comb.gens⟩` (Lemma B(b) for the transversal values); by INV-A for `H_{i−1}` the elements of
  `comb.gens` preserve `n + A`, so `φ(σ_j)` preserves A. `C_j = iso_window(N, x, x2, window, tower)`
  (main.py:371–389) is `Coset(N, id)`, `None`, or `lifter.lift_coset(C)` (action.py:138–144), whose
  group is `lift_group(C.group)` with generators a sub-list of `[lifter.lift(h)] + kernel().gens`
  (action.py:119–136) and whose representative is `lifter.lift(C.rep)`; `lifter.lift` and `kernel`
  return products of transversal values, resp. level generators, of `N.prefix_group(window)`, which has
  the generators of N (action.py:79–117, group.py:252–260); the cache path of `lift_group` (action.py:121–123) returns a group built in the same way by the same lifter. So all of them lie in `⟨N.gens⟩`,
  whatever the recursive call returned. `N.gens = [g[:n] for g in K.gens]`, `K = comb.level_group(kA)`
  (certificates.py:222–223): level-kA generators fix the moved points of `n + A` (they are
  `b_0, …, b_{kA−1}`, created first, group.py:88–90; later base points come from `rest_order`, which
  excludes the prefix, group.py:92) and the unmoved ones, so `φ(N.gens)` fixes A pointwise. Hence every
  generator of `H_i` has a φ-image mapping A onto A, and `H_i.phi_gens = φ(H_i.G.gens)`.

So INV-A, and with (b) `|lifts| ≤ k!`, holds in every returning run, assuming only HOM. Neither
completeness of Schreier–Sims nor correctness of the recursive `iso` calls is used.

**(d) Under (A3) the count is |H^A|.** With CORRECTNESS.md Lemma 3.1 (complete chains), `|trans_i|
= |comb^{(i)} : comb^{(i+1)}|`, so `∏_{i<kA}|trans_i| = |comb : comb^{(kA)}|`; `comb^{(kA)}` is the
pointwise stabilizer of `b_0, …, b_{kA−1}`, i.e. of `n + A` (the other points of `n + A` are fixed by
`comb`); under HOM `comb ≅ H` by projection, and `comb/comb^{(kA)}` is the image of `comb` on `n + A`,
i.e. `H^A = φ(H)|_A`. So `|lifts| = |H^A| ≤ |Sym(A)| = k!`.

**Exactly what is assumed:** HOM for `jd.Gw` (part of CORRECTNESS.md's correctness proof, through
Lemmas 3.3, 4.4, 4.5 and the theorems they cite). Not assumed: completeness of Schreier–Sims
(needed only for the equality in (d)), correctness of the solver. The same count bounds the lifts
used later by `conjugate` (it transports each lift, keeping their number) and `compare`, and
the counts `Q_A ≤ 2M(n+1)k!`, `Q_cmp ≤ 4M²(n+1)k!`.
**Effect on ω: unchanged.**
