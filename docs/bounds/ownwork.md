# Own work of every node type, with all callee symbols substituted: W(node) ≤ λ^e · 2^ω

Inputs: the five per-module documents in this directory (`main.md`, `group.md`,
`structure_cc_wl.md`, `soj.md`, `johnson_certs.md`) and the cost model of `SPEC.md`. Line numbers
of `main.py`, `johnson.py`, `soj.py` refer to the files of this version.

---------------------------------------------------------------------------------------------

## 0. Summary

Notation: `X = log2 n`, `y = log2 m`, `ls = log2 s`, `LKF = log2(k!)`, `lM = log2 M`,
`U(y) := (7 + 2 log2 y)·y + 4 log2(y+2)` (exponent of one Split-or-Johnson run),
`R_t := (y+1)(4t² + 55t + 287)·m^{2t+1}` (the t-ary WL refinement on Γ).
Every bound is `W ≤ λ^e · 2^ω`; the "simple ω" column is a closed form valid on the whole
admissible range (§1.1); the code functions of §10 return the sharper log-sum forms, which are ≤
the simple ones.

| node / part | e | simple ω (range) | sharp form (W/λ^e ≤ …), section |
|---|---|---|---|
| `W_iso(n)`: wrapper of one `Solver.iso` call (+ `_one_iso`) | 1 | `8.11 + 2X` (n ≥ 2) | `276 n²`, §5.1 |
| `W_iw(n, L ≤ n)`: own work of one `iso_window` | 1 | `14.37 + 5X` (n ≥ 2) | `21038 n^5`; `20481 n^5` for n ≥ 90, §5.2 |
| `P_cr(n)`: chain-rule node incl. the wrappers of its ≤ n orbit calls | 1 | `14.50 + 6X` | `23138 n^6`, §5.3 |
| N1 brute force (`|G| ≤ 5040`) | 1 | `18.48 + 5X` | `14164 n^5 + 1123944 n² + 921385 n + 4894264`, §6.1 |
| N3 giant | 1 | `14.03 + 5X` | `16634 n^5`, §6.2 |
| N4 strong Luks, `A(n) + q·B(n)` | 1 | `16.79 + 7X + log2(1+q)` | `A = 1600 n^7 + 444310 n^5`, `B = 1790 n³`, §7.1 |
| N5 Cameron, `A(n) + I·B(n)`, `I ≤ s_c!` | 1 | `17.01 + 7X + log2(1+I)` | `A = 1600 n^7 + 518132 n^5`, `B = 1898 n³`, §7.2 |
| J0: Johnson entry (`max(D_hint, D_J)` + `johnson_case`) | 0 | `14.83 + 5X` (n ≥ 90) | `29070 n^5`, §8.1 |
| one run of `upcc_split_or_johnson` (|V| ≤ m, base on m points) | 0 | `0.91 + U(y)` | `1.87 (y+2)^4 m^{7 + 2 log2 y}`, §8.3 |
| one run of `extended_design_lemma` (arity k) | 0 | `log2[17(280+42k) m^{k+1} + 3485 m^5 + 73100 m^4 + 1.87·2^{U(y)}]` | §8.4 |
| N6b primitive, pullback branch (s = 1 proved) | 1 | `22.51 + 5X` | `5948600 n^5`, §8.6 |
| N6b primitive, EDL branch | **2** | `4 ls + 2 + max(5.09 + log2(y+1) + log2(4t²+55t+287) + (2t+1)y, 1.91 + U(y), 5.09 + log2(2n + 53t + 335) + (t+1)y, 22.70 + 5X)` | §8.7 |
| N6c: `A_x + A_y` (two `aggregate` misses) | 1 | `20.53 + 3 lM + LKF + 6X` | `1508700 M n^6 + 3514 M k! n^4 + 44.8 n² M³ + 131 M²`, §8.8 |
| N6c: the `Q_A ≤ 2M(n+1)k!` wrappers `Q_A·W_iw(n)` | 1 | `15.34 + lM + LKF + 6X` | `41421 M k! n^6`, §8.9 |
| N6c case 1, `H_1` (s = 1 proved) | 1 | `22.52 + lM + 5X` | `5989168 n^5 + 20604 n³ M`, §8.10 |
| N6c case 2a, `H_2a` (s = 1 proved; incl. `top_action` and its 5 wrappers) | 1 | `24.12 + lM + 5X` | `18105170 n^5 + 33218 n³ M`, §8.11 |
| N6c case 2b, `H_2b` | 1 | `4 ls + 1.59 + max(1.91 + U(y), 22.70 + 5X, 19.64 + lM + 5X)` | §8.12 |
| N6c case 3, `W_c3` (own work incl. the `Γ ≤ 4M²` compares) | 1 | `14.53 + 2 lM + 2 LKF + 6X` | `16569 M² n^6 + 7025 M² k! n^4 + 0.32 M (k!)² n²`, §8.13 |
| N6c case 3, the `Q_cmp ≤ 4M²(n+1)k!` wrappers (letters λ+2) | 1 | `16.34 + 2 lM + LKF + 6X` | `82839 M² k! n^6`, §8.13 |
| N6c case 3, branch `17·W_br[P_3, f_a, 0]` (with the k-ary WL) | 1 | `4 ls + 2 + max(5.09 + log2(y+1) + log2(4k²+56k+288) + (2k+1)y, 1.91 + U(y), 22.71 + 5X, 19.64 + lM + 5X)` | §8.13 |
| branch template residual `Π = W_br − (s+1)P − s·W_rec` | – | four variants (conventions of the per-module documents) | §8.5 |
| N6c total | 1 | `log2(29070 n^5 + 672 n + (A_x+A_y)/λ + Q_A·W_iw/λ + H_case/λ)` | §8.14 |

**Is the own work linear in λ?** Yes for every node type **except N6b with the EDL branch**, where
the best bound proved here is quadratic: `W ≤ λ²·2^ω` (e = 2). The source is
`hypergraph_structure` line 549, `sorted(set(s), key=canon)`: the `⌈d log2 d⌉ ≤ n⌈log2 n⌉`
comparisons of canonical images of letters cost up to `(height + 1)·size ≤ 2λ·3λ = 6λ²` each
(structure_cc_wl.md Lemma S3 with Lemma C), not `3λ` as main.md K10 assumes; for nested letters
`((…(ℓ0, b1), …), bj)` of size λ = 2j + 1, which `LocalCertificates.compare` produces, the cost is
really Θ(λ²) per comparison in the model (§2, C1). Everywhere else letters are only hashed or
tested for equality, which is linear in λ.

**Further results** (details in §2, §3):
* main.md K10 also undercounts the sort of `case_3`'s `proc` (line 1025): 18(k+4) per comparison,
  not 3(k+4) (C7).
* With `h* ≤ f_a + s(γ_n + 1)` the `_covered` terms of `branch` are `s³` and `s⁴` (not `s²`, `s³`);
  the template has a term `(1+2κ)(3n+1)·s⁴` (C3). Hence the factor `s⁴` (4 log2 s) in the branch nodes.
* For the procs of N6b-pullback, case 1 and case 2a, `proc` makes no `choose` call, so `d = 0` and
  `s = 1` exactly (Lemma R of main.md); these nodes run `proc` at most twice.
* Bounds read off the code (§3): `iroot` costs `21⌊bitlen(N)/s⌋ + 62`; `_cameron_candidates` is
  `≤ 4L³√N + 2L³ + 64L² + 97L + |ts|(L²+L)` (L = log2 N, N ≥ 9); `_thin_cycle_structure` is
  `≤ 16n² + 2n⌈log2 n⌉ + 97n + 204 + 13M + C_ref`, at least soj.md's bound for it; a upcc run that
  takes the thin-cycle exit costs at most soj.md's `U(n)` plus this bound; the integer threshold
  tests cost only their instructions, and the comparisons they decide are exact for every m.
* `recognize_cameron` is charged by johnson_certs.md for up to `LS(N−1)/8` heavy bodies, each with a
  `GroupWithAction.kernel` (three Schreier–Sims builds of degree ≤ 1.25N): `RCAM ≤ 1600 N^7` (N ≥ 9).
  This is the `n^7` of N4/N5; it is crude (johnson_certs.md §7.4), but proved.
* String hashing conventions differ between the per-module documents; the per-character reading is
  used here, with a factor 17 on all structure/wl/cc/soj-dependent parts (§1.3).
* Conditional facts inherited from the per-module documents (marked where used, §9): INV-A (`|lifts| ≤ k!`), the
  correctness of group.py (`I ≤ q`, `I ≤ s_c!`), (H61) `|V| ≥ 61` in case 2b, determinism of `proc`.

---------------------------------------------------------------------------------------------

## 1. Setting, conventions, facts used throughout

### 1.1 Parameters and admissible ranges

* A **node** is one execution of `Solver._solve(G, x, y, tower)`; `n = G.n ≥ 2`, `X = log2 n`,
  `r = len(G.gens)`. All bounds count the operations of the node outside nested `Solver.iso` calls
  (main.md §3), with every callee symbol replaced by a closed form.
* **Letter size** `λ ≥ 1` (main.md §1.1). A bound `a0 + a1λ + … + a_eλ^e` with `a_i ≥ 0` is
  `≤ λ^e (a0 + … + a_e)` for `λ ≥ 1` (**F6**); all closed forms below are therefore evaluated at λ = 1
  and multiplied by `λ^e`.
* **Johnson nodes:** `m = |Γ|` with `90 ≤ m ≤ n` (the Johnson case is entered only for
  `m ≥ ℓ(n) = 10 k_paper(n) ≥ 90`, main.md §1.1), `y = log2 m ≥ 6.49`.
  `t = jd.t` with `b = C(m,t) ≤ n` blocks; `t ≤ (m−1)/2` (recognize_johnson only returns `k ≥ 2t+1`,
  the hint has t = 2), hence `C(m,t) ≥ 2^t` and `t ≤ X`.
  `k = k_paper(n) = max(9, ⌊X⌋ + 3) ≤ m/10`, `M = C(m,k)`. Then `M ≥ C(90, 9) > 2^{39}` and
  `M ≥ C(10k, k) ≥ 10^k ≥ 10^{X+2} > n`.
* `s ≥ 1`: the number of complete choice sequences of a branch (main.md Lemma R), free.
  `q`: coset representatives of N4 (`q ≤ |Gbar|`); `I ≤ s_c!` (N5), `2 ≤ s_c ≤ log2 m`.
* Generator counts: every existing `PermGroup` of degree N has `≤ γ_N` generators (group.md Lemma G).

### 1.2 Facts

* **(F1)** `γ_N = max(6, λ_N)`, `λ_N ≤ ⌈3N/2⌉ − 1 ≤ 1.5N` (group.md Lemma C(b), CST). Hence
  `γ_N ≤ 6N` (N ≥ 1), `≤ 3N` (N ≥ 2), `≤ 1.5N` (N ≥ 4). In particular `r ≤ 3n`, and in a Johnson node
  every group of degree ≤ n + m has ≤ 3n generators.
* **(F2)** `Build(N, ρ) ≤ 1876 N^5 + 223 ρ N²` for N ≥ 1. Proof: group.md Lemma B (B = N, F ≤ N)
  gives `(3/2)λN^4 + 28λN³ + (437/2)λN² + 381λN + 138λ + (25/2)λ²N(N+1) + (133/2)N³ + 29N² + (501/2)N
  + 323 + ρ(3N² + 61N + 159)`; with `λ = λ_N ≤ 1.5N` every monomial is `≤ N^5` (resp. `ρN²`) times its
  coefficient, and the coefficients sum to `2.25 + 42 + 327.75 + 571.5 + 207 + 56.25 + 66.5 + 29 + 250.5
  + 323 = 1875.75` and `3 + 61 + 159 = 223`.
* **(F3) Units.** `B1 := 2^12 n^5`, `B2 := 2^16 n^5`. For n ≥ 2:
  `Build(N ≤ n, ρ ≤ 12n) ≤ 1876n^5 + 2676n³ ≤ 2545 n^5 = B1 − 1551 n^5` and
  `Build(N ≤ 2n, ρ ≤ 12n) ≤ 60032 n^5 + 10704 n³ ≤ 62708 n^5 = B2 − 2828 n^5`.
  The slack absorbs every constant-size `Init0` remainder below (`113 + 4n + 2F ≤ 1551 n^5`).
* **(F4) Logarithms.** `(ln N)^j/N` is maximal at `N = e^j`. Hence `log2 N ≤ 1.07√N`,
  `(log2 N)² ≤ 1.13 N` (N ≥ 1); for N ≥ 9: `(log2 N)² ≤ 1.117N`, `(log2 N)³ ≤ 4.04N`,
  `(log2 N)^4 ≤ 20.4N`, `log_3 N ≤ N/4`; for x ≥ 90: `log2 x ≤ 0.073x`, `⌈log2(2x+1)⌉ ≤ 0.1x`.
* **(F5) Monomial rule.** For `v ≥ v0 > 0` and `a ≤ A`: `v^a ≤ v0^{a−A} v^A`. All "collapses" below
  (`Σ c_j n^{a_j} ≤ C n^A`) apply it with `v0 = 2` (general nodes) or `v0 = 90` (Johnson nodes); the
  constant `C` is the stated coefficient sum.

### 1.3 String-hashing convention (factor 17)

SPEC charges hashing/comparing "one per element touched" and is silent on strings. main.md counts a
literal string of ≤ 8 characters as one element inside tuples (but its K3 charges string *keys* per
character), structure_cc_wl.md treats strings as atoms (its §1.1), soj.md and johnson_certs.md charge
`1 + length`. The per-character reading is used here. Every string that the code of structure/wl/cc/soj/
design/main hashes or compares (tags, invariant labels, root cell keys, `"x"/"y"`, `"agg"`, kinds
`"a"/"b"`, case names) is a literal of ≤ 16 characters (over all these modules, excluding `STATS`/`stats`
keys, which SPEC charges at ≤ 64, docstrings and exception texts; the longest is `"bsoj-twin-blocks"`). So
under per-character charging every touch costs ≤ 17 times the atom charge, and **every bound of
structure_cc_wl.md and main.md is at most multiplied by 17** (instructions are unchanged). The
factor 17 is applied to every part of a Johnson node that involves `proc`, `branch`, structure/wl/cc callees or
the soj run, and to `aggregate`'s and `case_3`'s string keys as explicit additive terms. Nodes N1–N5,
`W_iso`, `W_iw`, `P_cr` and J0 touch no strings outside per-character-charged K3 keys and stats, and
group.md / johnson_certs.md need no factor.

### 1.4 Inherited assumptions (all from the per-module documents; see §9)

(A1) returning runs under `Params.paper()`: every `fallback` raises, so code after it is not charged;
(A3) correctness of group.py/action.py, used only for counting (`I ≤ q`, `I ≤ s_c!`);
(A5) determinism of `proc` (main.md Lemma R, s-counts); INV-A (johnson_certs.md §1.7: `|lifts| ≤ k!`;
unconditionally replace `k!` by `m!/(m−k)!` in the certificate, compare, Q_A, Q_cmp terms); (H61)
`|V| ≥ 61` for the upcc call of case 2b (assumed in soj.md §0.3 and §3, item 2).

---------------------------------------------------------------------------------------------

## 2. Check of main.md §3 against `main.py` (completeness), and corrections

The profile numbers of main.md are those of `opcount.generate()` for every `main.*` and `graph.*`
code object of this version (`babai_gi/_opprofiles.py`). The threshold tests of lines 601, 793, 800
(`2*len(Cx) > m`, `2*len(orb) > m`, `2*len(S) >= m`) are integer comparisons, equivalent to the
comparisons with `m/2` (§3.5). The functions `iso`, `_one_iso`, `_solve`, `brute_force`,
`iso_window`, `chain_rule`, `strong_luks`, `cameron_reduction`, `johnson_case`, `trivial_case`,
`hypergraph_*`, `primitive_johnson`, `branch`, `_covered`, `imprimitive_johnson`, `aggregate`,
`case_2a`, `top_action`, `case_2b_structure`, `case_3`, `_chain_search` are compared with main.md
statement by statement. Covered by main.md (and used below unchanged):

* `iso`: `tuple(x)`, `tuple(y)`, `Tower.trivial`, both `len` tests, the `all(is_string_automorphism …)`
  generator, `Counter(x) != Counter(y)` (K13: `(12+16λ)n + 6`), `x == y`, `x != y`, `G.aut_cache.get(x)`
  and `G.aut_cache[x] = A` keyed by the string (`4λn + 6`), the two stats updates (K11), `Coset`.
* `_solve`: up to three `G.order()` calls, two `factorial(n)`, `getattr`, the two `agg_cache`
  operations with key `"hint_jd"` (K3 charges string keys per character), the f-string stats (192),
  `top_blocks`, both `minimal_block_system`, both `induced_action`, `tower.extend`, `coarse.sort()`,
  `recognize_johnson`, `recognize_cameron`, `enumeration_cap`, `johnson_phi` per generator,
  `GroupWithAction`, `JohnsonData` with `[list(b) for b in blocks]`.
* `chain_rule`: `G.stage_cache.get(x)` and the store keyed by the string (`4λn + 6`); `brute_force`:
  the `aut_cache` operations; `aggregate`: the cache key `("agg", s, k)` (`2(2λn + 13)` on a miss,
  `C_agg_hit ≤ 4λn + 47` on a hit, the hit being proved in main.md); `case_3`: `stats["cert_classes"] =`
  (64), the `buckets`, `class_of`, `classes` operations; all `Coset(...)` constructions on early returns.

Additions / corrections (all are taken into account in §5–§8):

* **(C1) `sorted(…, key=canon)` of letters (line 549) is quadratic in λ.** main.md K10 charges a
  comparison of two canonical encodings at their size `≤ 3z`. For `<` CPython compares the first
  differing pair twice (`==`, then `<`), recursively; the bound is structure_cc_wl.md **Lemma S3**:
  `x < y` costs `≤ (min height + 1)·min size`. A letter of size λ has height `≤ λ − 1`; by
  structure_cc_wl.md **Lemma C** its image has size `≤ 3λ` and height `≤ 2λ − 1`, so one comparison
  costs `≤ 2λ·3λ = 6λ²`. The bound is attained up to a constant: the letters produced by
  `colored_string` at compare depth j are `((…(ℓ0, b1), b2)…, bj)` (λ = 2j + 1); two of them differing
  only in ℓ0 cost `Σ_{i ≤ j} Θ(j − i) = Θ(λ²)`. Hence in `hypergraph_structure` the term `3λn⌈log2 n⌉`
  of main.md becomes **`6λ² n⌈log2 n⌉`** (d ≤ n distinct letters), and `W_hs`, `P_edl` and node N6b-EDL
  are quadratic in λ. No other code sorts or `<`-compares letters (everywhere else letters are only
  hashed or compared with `==`/`!=`, which cost `≤ size`, structure_cc_wl.md Lemma S2), so all other
  nodes stay linear in λ.
* **(C2)** The 14 instructions of `_one_iso` (main.md "own work 14", attributed to no node) are added
  to `W_iso`.
* **(C3) The `_covered` terms of `branch` are `s³` and `s⁴`.** In main.md's `Σ_j C_cov` the generator
  count is `h_j ≤ h* = f_a + S(r̄ + 1)`, which grows with S ≤ s. So `S²·20000·h*·A'` contains
  `20000·A'·(γ_n+1)·s³` and `S³(1+2κ)(20000 + h*)` contains `(1+2κ)(γ_n+1)·s⁴`. §8.5 writes the template
  as a polynomial `c0 + c1 s + … + c4 s⁴` with explicit coefficients.
* **(C4) Generator counts.** `γ_N` (F1) is used for every existing group. For constructors the build
  term uses the *passed* generator count: `PermGroup(n, H_gens)` in `branch` gets `f_a = len(known
  non-identity auts) ≤ F ≤ M·γ_n` generators, `PermGroup(m, F_gens-images)` in `aggregate` gets F, so
  their `Build` has `ρ = f_a` resp. F (group.md Lemma B uses `ρ = len(gl)` at the call). (group.md's
  table writes `Build(n, ρ_H)` for `GroupWithAction.subgroup`; here `Build(n, L)` with the passed L is
  charged.)
* **(C5) Caches used.** `GroupWithAction.lift` in the run loop of `branch` (line 662) and of
  `cameron_reduction` (line 483) is charged at group.md's *steady* bound `9m² + 3nm + 108m + 3n + 581`:
  the same object has executed `preimage` before (lines 640, 476), which calls `kernel()`; `kernel()`
  calls `comb_gamma()` (caching `_comb_gamma`) and `_gamma_levels()` (building `H_Γ` via `H.levels`)
  unless `_kernel` is already set, which happens only after such a call; none of these caches is ever
  reset. `Gw.phi` (lines 690, 787, 1011, `certificate`, `top_action`) is charged at
  `max(fast, generic steady) ≤ 14n² + 164n + 517` per call plus one first-call surplus
  `B2 + 60n² + 359n + 529` per node (the fast `phi_fn` of `JohnsonData` may be `None`).
  Every other callee is charged at its first-call bound.
* **(C6) Strings:** factor 17 as in §1.3; explicit extras: `+64` per `aggregate` call
  (`("agg", s, k)`: ≤ 4 string touches), `+34` per compare iteration and per test set of `case_3`
  (`name0 == "x"`, `(name, A)` keys), `+17` in `imprimitive_johnson` (case-name comparisons).
* **(C7)** `case_3.proc` line 1025, `sorted(set(raw), key=canon)`: raw values `("c", ci, label)` have
  height 2, images height ≤ 5 and size ≤ 3(k+4): one comparison `≤ 18(k+4)` (Lemma S3), not `3(k+4)`.
* **(C8) `top_action`:** the loops of lines 851 and the `phi_fn` checks of `Fw` run over
  `Fgroup.gens` (`f' ≤ γ_n`), only line 850 runs over all `f = len(F_gens) ≤ F`; main.md's `f` in
  `(r1 + 2f)·C[phi]` can be replaced by `f'` (this is done in §8.11).
* **(C9)** N6a (`t = 1` primitive) is unreachable (main.md §6.6) and not bounded here.

Nothing else is missing: every operation of a node outside nested `Solver.iso` calls is either in
main.md's bounds or in the list above.

---------------------------------------------------------------------------------------------

## 3. Bounds read off the code: `iroot`, `_cameron_candidates`, the thin-cycle exit, integer thresholds

This section gives the bounds of `johnson.iroot` and `johnson._cameron_candidates` (johnson_certs.md
refers to §3.1 and §3.2 for them) and the closed form of `johnson.recognize_cameron` used in §7. It
also derives from the code the counts of `soj.upcc_split_or_johnson` and `soj._thin_cycle_structure`
that §8.3 and ownwork_gaps.md §2 use, and checks the integer threshold tests (§3.5); each of these
counts is at least the corresponding bound of soj.md.

Method: `opcount.profile` (PROOF.md Lemma 1.1, whose hypotheses `tests/test_attribution.py` checks:
`outside + Σ_loops [cycle·(I + E) + entry·E]`), and, for `johnson.iroot` and the code objects of
soj.py, the region profile of soj.md (Lemma 1.1'). `tests/test_soj_regions.py` checks the
hypotheses (R1)–(R6) of Lemma 1.1' on these code objects and freezes their region numbers (the
table of soj.md §4.2); every region number quoted in this section is from that table. Where the two
profiles give different counts the larger one is taken. Built-ins in the conventions of the
per-module document of the function's module.

### 3.1 `johnson.iroot(N, s)`

* Profile: outside 14; While@154 (cycle 21, entry 5). Region (`tests/test_soj_regions.py`):
  outside' 19, cycle' 21.
* Iterations: `lo = 0`, `hi = 2^{b+1}`, `b = ⌊bitlen(N)/s⌋`. While `hi − lo = 2^j > 1`, `lo + hi =
  2lo + 2^j` is even, so `mid = lo + 2^{j−1}` and the new difference is `2^{j−1}`. Exactly `I = b + 1`
  iterations, one entry.
* Built-ins: `bit_length` 1; `mid ** s`, the shifts and comparisons are int instructions (SPEC: cost 1).
* **Bound:** `14 + 21(I + 1) + 5 + 1 = 21⌊bitlen(N)/s⌋ + 62 ≤ 21(log2 N + 1)/s + 62`.

### 3.2 `johnson._cameron_candidates(N, ts)` (root computed by `iroot`)

* Profile: outside 20; For@131 (32, 0); While@138 (40, 13); While@141 (11, 6). johnson_certs.md
  (`johnson._cameron_candidates`) analyses the passes and the two while loops: "per pass total
  ≤ 2 + |ts| + a(2c + 2ab + 18b + 6a + 86 + |ts|)", a = log2 c, b = √(2c), at most L = log2 N passes.
* N < 9: ≤ 20. For N ≥ 9: For@131 runs over `range(2, bitlen(N))`, `σ = bitlen(N) − 2 = ⌊L⌋ − 1`
  iterations (s = 2, …, ⌊L⌋), one entry: `32(σ + 1)` instructions, `bit_length` 1, range `σ + 1`, one
  `iroot(N, s)` per s.
* A pass needs `c ≥ 3` and `c^s = N`; for each s at most one c, so the candidate set has the
  properties that johnson_certs.md uses (c^s = N, c ≥ 3, the same t-loop), and johnson_certs.md's
  analysis of `recognize_cameron` (`K_c ≤ LS/2`, `Σ_cand s^j ≤ L·S^j`, the heavy bodies) applies as
  it stands.
* Fixed part: `21 + 33(σ + 1) + Σ_{s=2}^{⌊L⌋}(21⌊(⌊L⌋+1)/s⌋ + 62) ≤ 54 + 95σ + 21(L+1)(H_{⌊L⌋} − 1)
  ≤ 95L − 41 + 21(L+1) ln L`.
* Passes: johnson_certs.md's sum `L·[2 + L√N + 0.71L²N^{1/4} + 12.73L N^{1/4} + 1.5L² + 43L] +
  |ts|(L + L²/2)`.
* With `N^{1/4} ≤ √N/√3` (N ≥ 9) and `ln L ≤ L − 1`:
  `CC ≤ (0.41L³ + 8.35L²)√N + 1.5L³ + 64L² + 97L − 62 + |ts|(L + L²/2)`, and with `8.35L² ≤ 2.65L³`
  (L ≥ 3.16): **`CC(N, ts) ≤ 4L³√N + 2L³ + 64L² + 97L + |ts|(L² + L)`** (N ≥ 9). The solver passes
  `ts = None` (main.py:320), so the last term vanishes.

### 3.3 `johnson.recognize_cameron` and its closed form

Profile numbers as in johnson_certs.md. Its bound RCAM is johnson_certs.md's, with CC the bound of
§3.2. Closed form used in §7 (N ≥ 9; N < 9: 82): with `L = log2 N`, `S ≤ log_3 N ≤ min(L/1.585, N/4)`,
`LS ≤ 0.631L² ≤ 0.713N`, `r, r_N ≤ 1.5N` (F1: `Gbar`, `Nk` are groups of degree N ≥ 9; `Nact` of degree
`c ≤ √N` has ≤ 3c generators, so `RJ(c, r_N)` is RJ of an existing group):
* heavy bodies: `LS(N−1)/8 ≤ 0.0892 N²`; per body `GWA.__init__(N,S,r) ≤ 12N² + 96N + 147`,
  `GWA.kernel(N,S,r)` with three builds of degree `≤ N + S ≤ 1.25N`, each `≤ 1876·1.25^5 N^5 +
  223·12N·1.5625N² ≤ 5774 N^5`, plus `≤ 50.6N² + 462.3N + 1051`; `induced_action(N, r_N; √N) ≤ 1876N^{2.5}
  + 334.5N² + 54N^{1.5} + 196N + 18√N + 168`; `max(Ord, RJ)(√N) ≤ 2·4096 N^{2.5} + 35000 N²` (§4, U-RJ).
  Per body `≤ 17175.4 N^5 + 12543.75 N³ + 10068 N^{2.5} + 35397.1 N² + 54N^{1.5} + 754.3N + 18√N + 1366
  ≤ 17420.5 N^5` (F5 with v0 = 9), all bodies `≤ 1554 N^7`.
* the rest: `LS·[…] ≤ 0.713N·(5.85N^4 + 1.07N^{3.5} + 99.5N³ + 70.71N^{2.5} + 584N² + 3N^{1.5} + 87N +
  233)`, `CC`, `ORB ≤ 67.5N³ + 124N² + 22N + 127`, 75: together `≤ 0.26 N^7` (F5 with v0 = 9).
* **U-RC:** `RCAM(N) ≤ 1600 N^7 + 82` (all N ≥ 2).

### 3.4 `soj.upcc_split_or_johnson` (thin-cycle exit) and `soj._thin_cycle_structure`

soj.md bounds both functions for this code (soj.md §1, `upcc_split_or_johnson` and
`_thin_cycle_structure`; Theorem A, lines [upcc itself] and [thin-cycle exit]). This subsection
re-derives the counts from the code; the bound used in §8.3 and in ownwork_gaps.md §2 is soj.md's
`U(n)` for upcc and the bound TC below for `_thin_cycle_structure`, which is at least soj.md's.

**upcc.** opcount: outside 269; For@309 (68, 0); ListComp@317 (7, 9). Region (the profile soj.md's
own bound U(n) uses, `tests/test_soj_regions.py`): outside' 302; loop 309 cycle' 82; loop 317 cycle'
7. Loop 309 has `≤ g_k + 1 ≤ n` passes, loop 317 runs at most once (it is on the `return` path),
with `q + 1 ≤ n` passes, q = number of tied colour classes of valency 1. The thin-cycle test adds
the built-in `len(blocks[0])`, ≤ 1 per tied class (`g_t ≤ n/2`). soj.md's `U(n) ≤ 761 + 354n + …`
counts all of these. A run that takes the thin-cycle exit ends with one call
`_thin_cycle_structure` and makes no bipartite call, which only shortens the run:
`W_UPCC ≤ U(n) + TC` for such a run.

**`_thin_cycle_structure(cc, x, cands, base, chooser, depth)`.** n = |V| = `len(cc.vertices)`,
`q = len(cands) ≤ n − 1`, M = `base.m`.
* Profile: outside 58; For@367 (17, 0) over `cc.vertices` (n iterations, 1 entry); ListComp@369
  (12, 9) over `cc.vertices`, entered once per u (n entries, n² iterations); For@372 (31, 0) over
  `range(1, n)` (n − 1 iterations, 1 entry); `<lambda@379>` total 8. Instructions:
  `58 + 17(n+1) + 12(n² + n) + 9n + 31n = 12n² + 69n + 75`; region profile (outside' 61; 23, 12, 31;
  `tests/test_soj_regions.py`): `12n² + 66n + 84`. Take `12n² + 69n + 84`.
* Built-ins (soj.md conventions, int keys η = 4, int comparisons 2): `sorted(cands)` `≤ 2n⌈lg n⌉ + 2n +
  1`; `pos[x]`, `pos[y]` 8; `nxt = {}` 1; per u: `pos[u]` 4, the store `nxt[u] = …` 4, per v `pos[v]` 4
  (`row[·] == c` is an instruction): `n(8 + 4n)`; `place = {x: 0}` 5; `len` 1, the range n; per j:
  `len(nxt[u])` with its lookup 5, `nxt[u][0]` 4, `u in place` 4, `place[u] = j` 4: `17(n − 1)`.
* Callees: `chooser.choose` (`Cc ≤ 104`, structure_cc_wl.md: Recording 33, Replay 104) and
  `base.refine(lambda, ("upcc-cycle", depth))`: `C_ref` with `σ_f = 1` (an int or None), `σ_tag = 13`,
  plus the callback, called M times (soj.md §0.1), `8 + 1 + 4 = 13` each.
* **Bound:** `TC ≤ 16n² + 2n⌈log2 n⌉ + 97n + 204 + 13M + C_ref`. This is at least soj.md's bound
  `16n² + 2n⌈lg n⌉ + 94n + 82 + 12M + Cc(q) + C_ref` (with `Cc ≤ 104`), and without its choose and
  refine, `16n² + 2n⌈log2 n⌉ + 97n + 100 + 13M`, at least soj.md's line [thin-cycle exit] of
  Theorem A. **Choice:** one `choose` among `q ≤ n − 1` candidates (y). Key growth:
  `σ(tag) + σ(f) + 3 = 17 ≤ 19`, within soj.md §2.A.4.

### 3.5 `soj._split_by_coloring_of_v2` and the other integer thresholds

* `_split_by_coloring_of_v2`: opcount ListComp@657 (24, 8), region 24 (`tests/test_soj_regions.py`);
  the built-ins of the comprehension are a lookup and a `len`. soj.md's bound
  `SC ≤ 543 + 103n2 + …` uses these numbers.
* `reduce_part2_by_color` (`2·max_twin_class ≤ n1 + 2`), `bipartite_split_or_johnson` (`2·d1 > n2`,
  `2·len(cl) > n2`), `coherent_split_or_johnson` (`2·dk > n1`, `0 < 2·dg < n2`), `main.primitive_johnson`
  (`2·len(Cx) > m`), `main.aggregate` (`2·len(orb) > m`, `2·len(S) ≥ m`): their profiles are those of
  the per-module documents, and int arithmetic costs only its instruction, so the bounds of those
  documents apply.
* Semantics: each integer test is equivalent to the corresponding comparison over the rationals
  (e.g. `2·len(Cx) > m ⟺ len(Cx) > m/2`), so the tests are exact for every m, and soj.md's
  reachability arguments, made over the rationals, hold for every m (soj.md §0.1, "Thresholds").

### 3.6 Profile numbers used in §3 (`opcount.generate()`, as in `babai_gi/_opprofiles.py`)

```python
PROFILES_NEW = {
    'johnson.iroot': (14, [(154, 21, 5)]),
    'johnson._cameron_candidates': (20, [(131, 32, 0), (138, 40, 13), (141, 11, 6)]),
    'soj.upcc_split_or_johnson': (269, [(298, 13, 9), (306, 27, 0), (309, 68, 0), (317, 7, 9), (318, 12, 12),
                                        (331, 23, 0), (335, 32, 0), (349, 15, 8), (350, 17, 9)]),
    'soj._thin_cycle_structure': (58, [(367, 17, 0), (369, 12, 9), (372, 31, 0)]),
    'soj._split_by_coloring_of_v2': (126, [(654, 13, 0), (657, 24, 8), (662, 17, 2), (667, 6, 8), (668, 10, 8)]),
}
NESTED_NEW = {'soj._thin_cycle_structure.<lambda@379>': (8, 0)}
```

---------------------------------------------------------------------------------------------

## 4. Table U: closed forms of the callees

All for n ≥ 2. "deg ≤ n" means every group handled has degree ≤ n (so its build is ≤ B1 by F3; an
existing group has ≤ 6·degree generators, F1); "deg ≤ 2n" allows the combined groups of degree
`n + m ≤ 2n` (build ≤ B2); `ρ` (generators of the group of a `GroupWithAction`) ≤ 3n, `λ_{n+m} ≤ 3n`.
Each line: cited bound → crude form; the crude form follows by inserting these maxima and applying F5
with v0 = 2 (coefficient sums shown where not immediate).

**perm, Coset, Tower** (group.md §3, §5, §7):
* `Ident(N) = 2N+33`, `Isid = 3N+39`, `Mul = 3N+11`, `Inv = 10N+29`, `Act(L) = 11L+30`, `Par = 55N+43`,
  `Coset(N) = N+10`, `from_cycles(N,c,T) = 3N+28c+14T+31`, `sym_gens(N,L) = 6N+15L+191`,
  `alt_gens(N,L) = 6N+16L+229`, `even_subgroup_gens(L,D) = 185+10D+282L+130LD`.
* `is_string_automorphism(x, g)`: group.md `12L+22` with int letters; each of its ≤ L letter
  comparisons costs ≤ λ more: **`ISA ≤ 12n + 22 + λn`**.
* `Tower.trivial 39`, `is_trivial 6`, `top_blocks ≤ 40n+66`, `extend ≤ 92+24n+K(n+22)`,
  `restrict(·, L) ≤ 94 + K(32L+88)`, K = number of levels. **K ≤ n − 2 for every tower of the
  recursion**: `extend` is called only with a partition having fewer blocks than the top
  (main.py:305–307) and ≥ 2 blocks (a maximal block system), `restrict` keeps a level only if its block
  count is ≥ 2 and strictly below the previous one (tower.py:106–113), and towers are otherwise passed
  unchanged; so the block counts strictly decrease from n and stay ≥ 2.

**group** (group.md §4, §8):
* **U-PG** `PermGroup.__init__(N, r passed)` incl. any build (`113 + 2N + 2F + r(8N+80) + Build(N, ρ ≤ r)`):
  deg ≤ n: `≤ B1 + r(8n+80)` (r ≤ 12n), `≤ B1 + 247 r n²` (any r: `223n² + 8n + 80 ≤ 247n²`);
  deg ≤ 2n: `≤ B2 + r(16n+80)` (r ≤ 12n), `≤ B2 + 920 r n²` (any r).
* **U-Ord** `order`, `levels` of an existing group: `17 + β ≤ B1` (deg ≤ n), `≤ B2` (deg ≤ 2n);
  `level_group ≤ 2B + 48n² + 268n + 168`; `is_trivial 6`, `known_order_or_none 10`.
* `orbits ≤ 24Nρ + 85N + 51 ≤ 400n²` (deg ≤ 2n, ρ ≤ 6n); `minimal_block_system ≤ 238N³ + 87ρN³
  ≤ 380n^4` (deg ≤ n, ρ ≤ 3n); `induced_action ≤ B1 + 350n²` (`168 + 28n + 3n(36n+124)`);
  `point_stabilizer`, `pointwise_stabilizer ≤ 2B1 + 450n²`.
* `coset_reps_prefix(N ≤ 2n, k; E elements) ≤ B + 92 + 4n + E(k'+1)(6n+75)`, `k' ≤ min(k, levels)`;
  `elements(N; E) ≤ B1(N) + 96 + 2N + E(N+1)(3N+75)` (B1(N) = 4096 N^5).
* **U-GS** `generated_subcoset(N ≤ n; L pieces)`: with `Σρ_i ≤ 6nL`, `R ≤ (6n+1)L`:
  `≤ 1876n^5 + 210 + 12n + L(1338n³ + 271n² + 497n + 117) ≤ B1 + 1736 L n³`.

**action** (group.md §5):
* `window_lifter` (miss) `≤ 248 + 28n + n⌈lg n⌉ + 6n(42n+182) + Build ≤ B1 + 875n²`;
  `WindowLifter.lift` (first) `≤ B1 + 540n²`; `lift_group ≤ 3B1 + 1414n³` (ρ, ρ_H ≤ 6n, ρ_K ≤ 1.5n:
  `1273 + 776.5n + 72n² + 6n(9n² + 102n + 443) + 3·Build`); `lift_coset ≤ 4B1 + 1700n³`;
  `restrict_string(w) = 21w + 35`.
* `GWA.__init__(n', m', ρ) = 147 + ρ(2n' + 24m' + 64) [+ ρ·C[phi_fn]] ≤ 78n² + 192n + 147`;
  `comb_gamma ≤ B2 + 48n² + 246n + 155`; `_gamma_levels ≤ B2 + 48n² + 265n + 360`;
  `kernel ≤ 3B2 + 643n³`; `image_order`, `image_is_sym ≤ B1 + 24n² + 243n + 315` (steady `≤ 202 + m`);
  `lift ≤ B2 + 60n² + 357n + 704` (steady `≤ 12n² + 111n + 581`);
  `intersect_image(L) ≤ B1 + 24n² + 254n + 743 + L(283 + 130n)`;
  `preimage(L ≤ 9n) ≤ 4B2 + 147n² + 1044n + 1384 + L(12n² + 119n + 682)`;
  `subgroup(L ≤ 12n) ≤ B2 + B1 + 1238n³` (`36n³ + 633n² + 3311n + 461` without phi_fn, `≤ 913n³` with);
  `phi`: first generic call `≤ B2 + 60n² + 359n + 529`, every call otherwise (generic steady
  `12n² + 113n + 406` or fast `61 + PF`, `PF ≤ m(2t+51) + 50`): **`C_φ := 14n² + 164n + 517`** (§2 C5).

**johnson, certificates** (johnson_certs.md §5):
* `JP ≤ 10n² + 45nX + 149n + 168`, `JD ≤ 6n²X + 166n² + 18nX + 338n + 271` (t ≤ X, nb ≤ n, r ≤ 3n),
  `omega_of(a) ≤ nb(t + a + 19) + 8n + 33`, `restrict_to(L) = 37L + 67`, `is_primitive 12`,
  `is_giant_on(k, g) ≤ k + 19 + PG(k, g) + Ord(k)`, `LocalCertificates.__init__ = n + 31`.
* **U-RJ** `recognize_johnson(N, r ≤ 3N) ≤ B1(N) + 35000 N^4` (N ≥ 2). From johnson_certs.md's RJ with
  `L ≤ 1.07√N`, `L² ≤ 1.13N`, `ℓ ≤ L + 1`, `k' ≤ √(3N)`, `orbits_on(N(N−1), r) ≤ 74 + 103N² + 34rN²`,
  `PG(k', r) + Ord(k') ≤ 58492 N^{2.5} + 2007N² + 6995N^{1.5} + 240N + 3.47√N + 130` (F2 at degree k'):
  `RJ − B1 ≤ 13.56N^4 + 62905.1N³ + 2149.07N^{2.5} + 8073N² + 295.3N^{1.5} + 160.7N + 355.3√N + 434
  ≤ 34375 N^4` (F5, v0 = 2).
* **U-RC** `recognize_cameron ≤ 1600 N^7 + 82` (§3.3).

**structure, wl, cc, canon** (structure_cc_wl.md §5, group.md §6), all ×17 when used (§1.3):
* `canon(σ-node set-free object) ≤ 165σ + 4·#Fixed ≤ 169σ`; `_hk(σ) ≤ 5 + 169σ`;
  `Chooser.check(s) = 53 + s`, `choose ≤ 104`, `RecordingChooser.__init__ = 8`, `Fixed.__init__ + 1 = 5`,
  `JohnsonCell + 1 = 9`, `KStructure.__init__ = 27`, `KStructure.color(2) = 45`,
  `prefix_vertex_coloring = 49 + 41N + 10kN`, `prefix_pair_coloring = 41 + l`, `<c@67> = 40 + 10k`.
* `enumerate_runs ≤ 12 + R(123 + 21d)`, `R ≤ s` runs; `apply_obj(o) ≤ (130 + 15h(o))|o|`.
* `refine_structures(N, k) ≤ 131 + N^k k^k (14k⌈lg N⌉ + 11k + 476) + (4k² + 54k + 286) N^{2k+1} ⌈lg N⌉`.
  On Γ with `2 ≤ k ≤ m` (so `k^k ≤ m^k`): **`≤ R_k := (y+1)(4k² + 55k + 287) m^{2k+1}`**
  (`m^{2k}(14k(y+1) + 11k + 476) ≤ (y+1)m^{2k+1}(0.156k + 0.016k + 0.71)` for m ≥ 90; 131 absorbed).
* cc (int colours, γ = 1, colour counts `r, r' ≤ N²`, callbacks excluded): `ClassicalCC.__init__ ≤
  150 + 51N + 187N² + 12N²⌈lg N⌉`; `induced ≤ 177 + 52N + 205N² + 12N²⌈lg N⌉`; `is_clique ≤ 68 + 6N +
  12N²`; `disconnected_off_diagonal_colors ≤ 85 + 12N² + 38N³ + N²(168 + 137N + 79N² + N⌈lg N⌉)`;
  `components ≤ 38N³ + 33N² + 57N + 73`; `off_diagonal_colors ≤ 39 + 12N² + 3N`; `out_degree ≤ 39 + 13N`;
  `is_uniprimitive ≤ 135 + 24N² + N²(86 + 77N + 51N²) + 38N³`; `canonical_keys ≤ 207 + 61N + 321N² + 72N³
  + N^4(1887 + 1777N + (630N + 600)⌈lg N⌉)`; `key = 14`, `set_keys = 4`, `diagonal_colors = 7 + 3N`.

**Lemma K-run (key sizes inside the procs of a Johnson node).** In every `proc` run of `primitive_johnson`,
`case 1/2a/2b/3`, every `Structure` has keys of soj-size `≤ 85m` and height `≤ 13m`.
*Proof.* Every proc starts from its own root (keys `"all"`, `"twins"`, `"rest"`, `"Phi"`, `"S"`,
`("orb", len)`, `"fixed"`: σ ≤ 8, height ≤ 1). Construction steps: ≤ m individualizations in the
while loop of `case_2b_structure`; ≤ k ≤ m individualizations and one refine in
`extended_design_lemma` (k = X.k); one `split_by_blocks` in the disc branches; a upcc run makes
`≤ 3 + g_t + (L+1) + Σ_j (d_j + 3) + 2 ≤ 5 + 5|V|/6 + (Y/δ)(Y + 5)` steps (soj.md §2.A.4; the thin-cycle
exit adds one refine and skips the bipartite chain). With |V| ≤ m, Y ≤ y and `6 + 1.71y² + 8.55y ≤ 2m`
(m ≥ 90), there are `r ≤ 4m` steps. By structure_cc_wl.md Lemma K each step adds
`≤ σ(tag) + σ(f) + 3 ≤ 15 + 3 + 3 = 21` nodes (soj.md §2.A.4: tags σ ≤ 15, values σ ≤ 3) and ≤ 3 to the
height, after `+6` and `+2` for the root: keys `≤ 8 + 6 + 84m ≤ 85m`, height `≤ 3 + 12m ≤ 13m`. ∎

**U-SO (one structure operation in a Johnson node).** With M = m ≥ 90 points, keys ≤ 85m, height
≤ 13m, Johnson cell ≤ m, tags σ ≤ 15, values σ ≤ 3 (height ≤ 1), `⌈lg(2m+1)⌉ ≤ 0.1m` (F4) and
`canon ≤ 169σ`, each of `refine`, `individualize`, `mark`, `with_johnson`, `Structure.__init__` (≤ 2m+1
cells), `split_by_blocks` (incl. its `Structure.__init__`), `cell_of`, `key_of_vertex`, `aut_gens`,
`align` (with its parity/odd-automorphism part) costs **`≤ SO := 2048 m^4`** (callbacks excluded):
* refine: `291 + 225m + 3m² + 507m + 169m(85m+21) + m·0.1m·(1.5m + 41 + 3(85.24m)(26.13m))`
  `≤ 668.2m^4 + 0.196m³ + 14409m² + 732m + 291 ≤ 670m^4`; individualize, mark, with_johnson likewise ≤ 670m^4;
* `Structure.__init__` with `L0 ≤ 2m + 1`, input keys ≤ 85m + 18, height ≤ 13m + 1:
  `L0⌈lg L0⌉·3(85.23m)(26.08m) ≤ 0.2012m²·6668.4m² = 1341.7m^4`, rest `≤ 4.3m^4`: ≤ 1346m^4; SBB ≤ 1347m^4;
* align: `2m⌈lg m⌉·3κ(2η+3) ≤ 0.2m²·255m·26.04m = 1328m^4`, plus `2m·169κ + 17κm + J(38+6t) + odd ≤
  30642m² + 1500m + 1500`: ≤ 1332m^4; aut_gens `≤ 240.2m² + 525m + 501`.
*Dependence on the key size.* For keys of soj-size ≤ K and height ≤ H on m points the same
computation gives `refine ≤ 291 + 732m + 3m² + 169m(K + 21) + m⌈lg(2m+1)⌉(1.5m + 41 + 3(K + 21)(2H + 12))`;
`Structure.__init__`, `split_by_blocks` and `align` have the same shape (`L0⌈lg L0⌉·3κ(2η+5)`,
`2m⌈lg m⌉·3κ(2η+3)`). So every structure operation is `O(m² log m · K·H + mK)`, and K enters the node
bounds only through SO; Lemma K-run (K ≤ 85m, H ≤ 13m) turns this into `2048m^4`.

---------------------------------------------------------------------------------------------

## 5. The wrapper, `iso_window`, and the chain-rule node

### 5.1 `W_iso(n)` — one `Solver.iso` call (n ≥ 2)

main.md §3.1: `W_iso ≤ 508 + 22r + 36λn + r·C[ISA](n,λ) + C[Tower.trivial] + C[identity](n) +
C[Coset](n)`; plus 14 for `_one_iso` (C2). With `r ≤ 3n` (F1), `ISA ≤ 12n + 22 + λn`, 39, `2n + 33`,
`n + 10`:

    W_iso ≤ 522 + 44r + 36λn + λrn + 39 + 2n + 33 + n + 10
          ≤ 604 + 135n + 36λn + 36n² + 3λn²  ≤  λ(604 + 171n + 39n²)  ≤  276 λ n²     (F5, n ≥ 2: 151 + 85.5 + 39).

**ω_iso = log2 276 + 2X ≤ 8.11 + 2X.** Nested calls: main.md §3.1 (one node and one `iso(G,x,x)` if
x ≠ y; one node if x = y and the cache misses).

### 5.2 `W_iw(N, L)` — one `Solver.iso_window` call on a group of degree N, window L ≤ N

main.md §2 `iso_window`; every group involved has degree ≤ N (Table U with N for n):
`80 + L⌈lg L⌉ + (2+λ)L` + `window_lifter ≤ B1(N) + 875N²` + `2·restrict_string = 42L + 70` + `is_trivial 6`
+ `Ident 2N+33` + `Coset N+10` + `Tower.trivial 39` + `Tower.restrict ≤ 94 + 32NL + 88N` (K ≤ N) +
`lift_coset ≤ 4B1(N) + 1700N³`. With L ≤ N, `L⌈lg L⌉ ≤ N²`:

    W_iw(N, L) ≤ 5·B1(N) + 1700N³ + 908N² + (135 + λ)N + 332
               ≤ λ(20480N^5 + 1700N³ + 908N² + 136N + 332) ≤ 21038 λ N^5  (N ≥ 2),  ≤ 20481 λ N^5 (N ≥ 90).

(N ≥ 2: `20480 + 425 + 113.5 + 8.5 + 10.4`.) The bound is increasing in L, so it holds for every window
of a group of degree N. **ω_iw = log2 21038 + 5X ≤ 14.37 + 5X.**

### 5.3 `P_cr(n)` — a chain-rule node, with the wrappers of its orbit calls

`P_cr := D_cr + W_cr + Σ_i W_iso(n_i)` (the ≤ ω ≤ n nested calls `iso(Hr_i, …)` on orbits of size
`n_i ≥ 2` — a call is made only if `Hr_i` is non-trivial — with `Σ n_i = n`; chain_rule does the
restriction work itself, so there is no `W_iw`).
* `D_cr ≤ 500 + Ord(n,r) + orbits ≤ 500 + B1 + 400n²` (main.md §2 `_solve`).
* `W_cr` (main.md §2): `303 + 132ω + 2ω⌈lg ω⌉ + (1+5λ)n + (ω+1)Ident(n) + Coset(n) ≤ 4n² + (169+5λ)n + 346`,
  and per orbit: `window_lifter ≤ B1 + 875n²`, `WindowLifter.lift ≤ B1 + 540n²`, `lift_group ≤ 3B1 +
  1414n³`, `2 restrict_string = 42n_i + 70`, `is_trivial 6`, `restrict ≤ 94 + 32n·n_i + 88n`,
  `Inv + Act + Mul = 24n + 70`. Over ω ≤ n orbits: `≤ 5n·B1 + 1414n^4 + 1415n³ + 144n² + 282n`.
  (The stage cache only removes terms; all are charged.)
* `Σ_i W_iso(n_i) ≤ 276λ Σ n_i² ≤ 276λn²`.

      P_cr ≤ (5n+1)B1 + 1414n^4 + 1415n³ + (548 + 276λ)n² + (451 + 5λ)n + 846 ≤ 23138 λ n^6     (n ≥ 2).

(`20480 + 2048 + 353.5 + 176.9 + 51.5 + 14.3 + 13.2`.) **ω_cr = 14.50 + 6X.** Nested: ≤ n calls as main.md
N2.

---------------------------------------------------------------------------------------------

## 6. N1 and N3

### 6.1 N1 — brute force, `g = |G| ≤ 5040`

main.md §3.2 N1: `W ≤ 706 + 5λn + g + 2C_cs + Ord(n,r) + PermGroup(n, g) + Ident(n) + 2Coset(n)` with
`C_cs ≤ 4783 + (2044+λ)n + 12n⌈lg n⌉ + 444g + (85+2λ)gn + levels(n,r) + Ident(n)` (main.md
`_chain_search`, no forced prefix, g ≤ 5040). Substitutions: `levels, Ord ≤ B1`;
`PermGroup(n, ≤ g gens) ≤ 113 + 2n + g(8n+80) + 1876n^5 + 223gn²` (F2 directly: g may exceed 12n);
`Ident = 2n+33`, `Coset = n+10`; g = 5040:

    W_bf ≤ 3B1 + 1876n^5 + 1123920n² + 24n⌈lg n⌉ + (901218 + 20167λ)n + 4894264
         ≤ λ(14164 n^5 + 1123944 n² + 921385 n + 4894264) ≤ 365190 λ n^5            (n ≥ 2).

**ω_bf = log2(14164n^5 + 1123944n² + 921385n + 4894264) ≤ 18.48 + 5X.** Nested calls: none.

### 6.2 N3 — giant (`G ≥ Alt(Ω)`, `trivial_case` with `is_sym` given)

main.md §3.2 N3; substitutions: `3Ord ≤ 3B1`, `orbits ≤ 400n²`, `is_trivial 6`,
`GWA.__init__(n,n,r)` with `phi_fn = lambda g: g` (3 instructions per call, r calls)
`≤ 147 + 3n(26n + 64) + 9n = 78n² + 201n + 147`, `Σ_l sym_gens(n_l, n) ≤ d(6n + 191) + 15n ≤ 6n² + 206n`,
`PermGroup(n, ≤ 4n) ≤ B1 + 32n² + 320n`, `even_subgroup_gens(≤ 2n, n) ≤ 260n² + 574n + 185`,
`Par 55n+43`, `from_cycles(n,1,2) = 3n + 87`, `Mul 3n+11`, `Coset n+10`, `4r ≤ 12n`:

    W_giant ≤ 4B1 + 776n² + (1566 + 26λ)n + 1692 + 4λ ≤ 16634 λ n^5                    (n ≥ 2).

**ω_giant = 14.03 + 5X.** Nested calls: none.

---------------------------------------------------------------------------------------------

## 7. N4 and N5

### 7.1 N4 — strong Luks: `W ≤ λ(A(n) + q·B(n))`

Common dispatch part (main.md `_solve`, `D_e0`): `631 + 101n + 3n⌈lg n⌉ + 3Ord + orbits + is_trivial +
top_blocks + 2·MBS + induced_action(≤ n) + extend + induced_action(m) + Ord(m) + 33`
`≤ 6B1 + 760n^4 + 1104n² + 187n + 828` (Table U; `extend ≤ n² + 46n + 92` with K ≤ n).

main.md §3.2 N4 (all three entry paths charged at once): `W ≤ D_e0 + 503 + (41+n)I + (2+λn)S +
RJ(m,r) + RC(m,r) + GWA.__init__(n,m,r) + kernel + comb_gamma + _gamma_levels +
coset_reps_prefix(n+m, k; I) + I(Inv + Act) + S·Mul + generated_subcoset(n, S) + Coset(n)`, `S ≤ I ≤ q`
(main.md: `I ≤ |G : N| = |Gbar| = q` by (A3)), m = number of blocks ≤ n, `fallback` not executed (A1).
* q-independent: `GWA.__init__ ≤ 78n² + 192n + 147`, `kernel ≤ 3B2 + 643n³`, `comb_gamma ≤ B2 + 48n² + 246n
  + 155`, `_gamma_levels ≤ B2 + 48n² + 265n + 360`, the one-time part of `coset_reps_prefix ≤ B2 + 92 + 4n`
  and of `generated_subcoset ≤ B1`, `Coset ≤ n + 10`, `RJ ≤ B1 + 35000n^4` (U-RJ, degree m ≤ n),
  `RC ≤ 1600n^7 + 82` (U-RC).
* per coset representative (I of them; successes S ≤ I): `41 + n` and `2 + λn` (main.md), one element of
  `coset_reps_prefix` `≤ (m+1)(6n+75)` (`k' ≤ k = _gamma_levels() ≤ m`), `Inv(n) + Act(n) = 21n + 59`,
  `Mul(n) = 3n + 11`, one piece of `generated_subcoset` `≤ 1736n³` (U-GS).

      A(n) ≤ 7B1 + 6B2 + 760n^4 + 643n³ + 1278n² + 895n + 2095 + (B1 + 35000n^4) + (1600n^7 + 82)
           = 1600 n^7 + 425984 n^5 + 35760 n^4 + 643 n³ + 1278 n² + 895 n + 2177 ≤ 1600 n^7 + 444310 n^5,
      B(n) ≤ 1736 n³ + 6n² + (106 + λ)n + 188 ≤ 1790 λ n³                                   (n ≥ 2).

**ω_luks = log2(1600n^7 + 444310n^5 + 1790·q·n³) ≤ 16.79 + 7X + log2(1 + q).** On the first entry path
(`small_quotient`, no recognition) RJ and RC are not executed: `A ≤ 421888 n^5 + 760n^4 + …
≤ 2^{18.70} n^5`. q: `q < m^{1+⌊log2 m⌋}` (first path), `q < m^{2+⌊log2 m⌋}` or `m < 25, q ≤ 24!`
(second), `q ≤ (ℓ(n)−1)!` (third) — main.md §3.2. Nested: ≤ q calls on the kernel (degree n).

### 7.2 N5 — Cameron reduction: `W ≤ λ(A(n) + I·B(n))`, `I ≤ s_c! ≤ ⌊log2 m⌋!`

main.md §3.2 N5; substitutions (Table U): `GWA.__init__(n,m,r) ≤ 78n² + 192n + 147`;
`PermGroup(m, ν ≤ 1.5n) ≤ B1 + 12n² + 120n` (`ν = len(N_gens) ≤ γ_m`); `Ord(m, ν) ≤ B1`;
`preimage(L = ν ≤ 1.5n) ≤ 4B2 + 18n³ + 325.5n² + 2067n + 1384`; `GWA.__init__(m, s_c, r_b) ≤ 147 +
3n(2n + 24X + 64) ≤ 78n² + 192n + 147`; `comb_gamma`, `_gamma_levels` (degree `m + s_c ≤ 2n`) as in 7.1;
one-time `coset_reps_prefix ≤ B2 + 92 + 4n`, `generated_subcoset ≤ B1`; `Coset`; RJ, RC as in 7.1.
Per representative: `53 + m`, `2 + λn`, one element `≤ (s_c + 1)(6n + 75) ≤ 6n² + 81n + 75`,
`Gw0.lift` at the steady bound `≤ 12n² + 111n + 581` (C5: `preimage` was executed before on `Gw0`),
`Inv + Act = 21n + 59`, `Mul = 3n + 11`, one piece `≤ 1736n³`:

      A(n) ≤ 9B1 + 7B2 + 760n^4 + 18n³ + 1694n² + 3274n + 3703 + (B1 + 35000n^4) + (1600n^7 + 82)
           ≤ 1600 n^7 + 518132 n^5,
      B(n) ≤ 1736 n³ + 18n² + (217 + λ)n + 781 ≤ 1898 λ n³                                   (n ≥ 2).

**ω_cam = log2(1600n^7 + 518132n^5 + 1898·I·n³) ≤ 17.01 + 7X + log2(1 + I).** Nested: ≤ I calls on
`NG = φ^{-1}(Nbar)` (degree n).

---------------------------------------------------------------------------------------------

## 8. N6 — the Johnson case

Throughout: `90 ≤ m ≤ n` (so all collapses use F5 with v0 = 90), `X ≤ 0.073n`, `t ≤ X`, `b ≤ n`,
`k ≤ m/10 ≤ n/10`, `M ≥ n`, `r, r̄ ≤ 3n` (F1), `f_a ≤ F ≤ M·γ_n ≤ 3nM`. Abbreviation for the
`Structure.__init__` of a root (structure_cc_wl.md, `193 + 77L0 + 6m + mλ(m) + L0·J + L0·Cc(κ_in+2) +
L0λ(L0)(4 + 1.5m + 3(κ_in+2)(2η_in+5))` with root keys `κ_in ≤ 8`, `η_in ≤ 1`, no Johnson cell,
`Cc(10) ≤ 1690`):

    SR(m, L0) := 193 + 1767 L0 + 6m + m⌈lg m⌉ + L0⌈lg L0⌉(214 + 1.5m).

### 8.1 J0 — the entry part (`_solve` dispatch up to `johnson_case`, plus `johnson_case`)

main.md N6: `J0 = max(D_hint, D_J) + 30 + is_primitive (12)`. Substitutions (Table U, r ≤ 3n, b ≤ n,
t ≤ X): `3 Ord ≤ 3B1`, `orbits ≤ 400n²`, `is_trivial 6`, `GWA.__init__ ≤ 78n² + 192n + 147`,
`JohnsonData.__init__ ≤ JD`, `r·johnson_phi ≤ 3n·JP`, `RJ(b ≤ n) ≤ B1 + 35000n^4`, `8r + 9n ≤ 33n`,
`D_e0 ≤ 6B1 + 760n^4 + 1104n² + 187n + 828` (§7.1):

    D_hint ≤ 3B1 + 6n²X + 644n² + 18nX + 537n + 1360,
    D_J    ≤ 7B1 + 35760n^4 + 30n³ + 141n²X + 1795n² + 18nX + 1254n + 1630.

`D_hint ≤ D_J`, and with `X ≤ 0.073n`: `J0 ≤ (28672 + 397.4 + 0.01)n^5 + 42 ≤ 29070 n^5`.
No letter is touched (e = 0). **ω_J0 = log2 29070 + 5X ≤ 14.83 + 5X.** Nested calls: none.

### 8.2 Choice parameters of the branch nodes, and procs without choices

`branch` (main.md Lemma R) depends on `d` (choice events of the x-run), `s = ∏ c_j`, `κ` (size of
the key `tuple(chosen)`; it matters only if `prune`, i.e. no `Fixed` was chosen, main.py:651) and
`A' := 53 + 22d + 4κ + A_key` (the per-image cost of line 698 in `_covered`).

**Lemma NC (no choice ⇒ s = 1).** The procs of N6b-pullback (`proc@604`), case 1 (`proc@721`) and
case 2a (`proc@821`) call no `choose` (they call `largest_twin`/`aggregate`, one `check`, set
operations and `Structure(...)`: main.py:604–609, 721–733, 821–825). So `d = 0`, `s = ∏_∅ = 1`, `κ = 1`
(empty tuple), `A_key = 0`, `A' = 57`, and by Lemma R(a) `enumerate_runs` executes `proc` at most once:
`proc` runs ≤ 2 times, the run loop has ≤ 1 iteration, `_covered` is called ≤ 1 time. ∎

**Lemma CH (procs with choices: N6b-EDL, case 2b, case 3).** `d ≤ 1.3m`, `κ ≤ 0.23m²`, `A' ≤ 0.8m^4`.
*Proof.* The `choose` calls of one x-run are: in a upcc run (soj.md §2.B table, plus the
`_thin_cycle_structure` choice of §3.4) `x`, the tie of `select_min` (a `Fixed`), per choice level
the DL prefix and one coherent point, the terminal half split, the thin-cycle `y`: `≤ 4 + 2J` with
`J < Y/δ ≤ y/δ`; in `extended_design_lemma` one more (the DL prefix, design.py); in
`case_2b_structure` `≤ φ ≤ m` (main.py:929) plus one `select_min` tie. Each proc makes at most one upcc
run and either one EDL or one `case_2b_structure`, so `d ≤ m + 5 + 2J`. For `90 ≤ m < 130`,
`⌊y/δ⌋ = 11` and `d ≤ m + 27 ≤ 1.3m`; for `m ≥ 130`, `5 + 2y/δ ≤ 5 + 3.42y ≤ 0.3m`. So `d ≤ 1.3m`. Sizes of chosen objects (only relevant without `Fixed`):
vertices and coherent/terminal points are ints or V2-points, `σ(p) ≤ Σ2 < 2|V|/3 ≤ 2m/3` (soj.md:
`Σ2 ≤ 2U2 < 2n/3`); a DL prefix is a tuple of distinct points, size `≤ 4 + Σ2 ≤ 4 + 2m/3` (soj.md DL:
candidates have size ≤ 4 + ℓ*σ_pt, and distinct entries sum to ≤ Σ2); in EDL the prefix has size
`≤ 3 + k`. Hence `κ ≤ 1 + m + 3 + 2m/3 + 1.71y(4 + 4m/3) + (3 + k) ≤ 0.23m²` (at m = 90 the left side is
≤ 1640 ≤ 1863, and the ratio decreases in m). Heights of chosen objects are ≤ m (nesting depth of
points ≤ number of contraction levels + 1), so `A_key ≤ (130 + 15m)κ` (Table U, `apply_obj`) and
`A' ≤ 53 + 28.6m + 0.92m² + (130 + 15m)·0.23m² ≤ 0.05 m^4 ≤ 0.8m^4`. ∎

### 8.3 Theorem U — one run of `upcc_split_or_johnson` (|V| ≤ m, base on M = m points)

**Statement.** Under (H61), with `y = log2 m ≥ 6.49` and the string factor 17:

    W_UPCC ≤ 1.87 · (y+2)^4 · m^{7 + 2 log2 y} = 2^{0.903 + U(y)},     U(y) = (7 + 2 log2 y)y + 4 log2(y+2).

This keeps soj.md's form n^{O(log log n)}; no letter is involved (e = 0).

*Proof.* Start from soj.md Theorem A (§2.A.2) at `n := |V| ≤ m`, `Y = log2 n ≤ y`, `M = m`; it covers
both kinds of run, including the thin-cycle exit (§3.4). Every term below is increasing in `n` and
`Y`, so it suffices to take `|V| = m`. Group the terms of one run (soj.md lists the callee symbols):
1. *soj's own terms (Theorem A without callees), with the line [thin-cycle exit] replaced by the
   larger TC of §3.4 without its choose and refine:* `(Y/16 + 1/2)n^{6+log2 Y} + O(n³ log n + Y n² M)`,
   plus `16n² + 2n⌈lg n⌉ + 97n + 100 + 13M`.
2. *Structure operations* (`refine`, `mark`, `individualize`, `split_by_blocks`, `with_johnson`,
   `cell_of`; soj.md's callee list): ≤ 4 per bipartite call (`cell_of`, the Phase-2 refine, a terminal of
   ≤ 2), `3 + |V|/2` in upcc itself (individualize, refine, ≤ g_t ≤ |V|/2 `split_by_blocks` of tied classes,
   the thin-cycle refine), ≤ `d_j + 5` per choice level: `≤ 3 + 1.84m + 1.71y(y+6) ≤ 4m` operations, each
   `≤ SO = 2048m^4` (U-SO; keys ≤ 85m by Lemma K-run): `≤ 8192 m^5`.
3. *Chooser:* `≤ n/3` bipartite calls with checks `≤ 395 + D_i`, `d_j ≤ Y + 2` checks `Ck(6) = 59` per
   choice level, upcc's `Ck(8,9,11,12) ≤ 252`; `≤ n + 3` chooses at `104`.
4. *Hashing/canon callbacks:* `(n + n²/2)C_hk(1) + (n²/4)(C_hk(3) + C_Fix)` and, per choice level,
   `Ntot·C_hk(K ≤ 85m) ≤ n(5 + 169·85m)`: `≤ 220n² + 174n + (Y/δ)(14370nm + 444n)`.
5. *cc callees:* `C_key(n + n²)`, `C_diag(n)`, and per choice level (kind 'b') `C_CC(n) + n²(C_c + C_col)
   + 4C_indc + 2C_clq + 2C_disc + C_comp + C_odc + n·C_od` (Table U; `C_c ≤ 60 + 10Y`, `C_col = 45`):
   `O((Y/δ)·n^4)`.
6. *wl callees per choice level* (`< Y/δ` levels; `n2_j < n/3`, `d_j < Y + 2`, Lemma T:
   `T_j = n2_j^{d_j} ≤ Tm := (n/3)² n^{1+log2 Y}`): `refine_structures(n2_j, d_j)` (Table U form)
   `≤ 131 + Tm·(Y+2)^{Y+2}(14(Y+2)(Y+1) + 11(Y+2) + 476) + (4(Y+2)² + 54(Y+2) + 286)·Tm²·(n/3)·(Y+1)`;
   the prefix colourings `2T/n2·(C_pvc + C_ppc) + 2T·n2·C_c ≤ 2Tm(n/3)(50 + 12(Y+2))`; `classical_wl(n)`
   with callbacks (structure_cc_wl.md, colour bound ν = 256M, η = 27M): `≤ (48⌈lg n⌉ + 382)n^5 +
   (ν+2)n^4 + 12(η+2)(ν+2)n²⌈lg n⌉ + … = O(m^5 log m)`.

*The dominant term* is the second part of `refine_structures` in group 6. Since `Tm²·(n/3) =
n^{7+2 log2 Y}/243`, `Y(Y+1) ≤ (Y+2)²` and `4(Y+2)² + 54(Y+2) + 286 ≤ 14.33(Y+2)²` (Y + 2 ≥ 8.49), its
sum over the levels is `≤ (Y/δ)(Y+1)·14.33(Y+2)²·n^{7+2log2 Y}/243 ≤ 0.10081·(Y+2)^4 n^{7+2 log2 Y}`;
times 17: `≤ 1.714·2^{U(y)}`.
*All other terms* are `≤ poly(y)·m^a` with `a ≤ max(6 + log2 y, 4.5 + 2 log2 y, 6)`: for the first part
of `refine_structures` use `(Y+2)^{Y+2} ≤ n^{log2 Y + 1.5}` (equivalently `(Y+2)log2(Y+2) ≤ Y(log2 Y + 1.5)`,
true for Y ≥ 6.49 since `(Y+2)log2(1+2/Y) ≤ 3.78` and `2 log2 Y + 3.78 ≤ 1.5Y`); every other group is
polynomial of degree ≤ 6 in m times a polynomial in y. Against `2^{U(y)} ≥ 5196·m^{7+2log2 y}` each is
smaller by a factor `≥ m^{2.5}/poly(y)`, and this ratio decreases in m (y > 2.9). At m = 90 the largest,
the first part of `refine_structures`, is `17·1.71y·(1/9)(14·8.49·7.49 + 93.4 + 476)/(5196·90^{2.5}) ≤
8·10^{-5}` of `2^{U(y)}`; each of the fewer than 30 groups is ≤ 10^{-3}, so together `≤ 0.03·2^{U(y)}`.
Total `≤ (1.714 + 0.03)·2^{U(y)} ≤ 1.87·2^{U(y)}`. ∎

(The exact substituted sum is at most `1.156·2^{U(y)}` on the whole range, maximal at m = 90; it tends
to `0.48·2^{U(y)}`.)

### 8.4 One run of `extended_design_lemma` (arity k = X.k, m points)

soj.md §2.A.3: `W_EDL ≤ E(m,k) + DL(m,k) + W_UPCC(|C|)` (soj.md counts DL inside E and again; both are kept here).
* `DL(m,k)` (soj.md closed form, σ_pt = 1; `C_pvc = 49 + 41m + 10km`, `C_ppc = 41 + k`, `C_c = 40 + 10k`,
  `Ck(6) = 59`, `Cc = 104`): `2m^{k−1}((68+10k)m² + (113+10k)m + 213 + 2k) + m^{k−1}(36+12k) + 10km +
  43m + 171k + 613 ≤ (140 + 21k)·m^{k+1}` (coefficients: `136 + 20k + (226+20k)/90 + (462+16k)/8100 + … ≤
  138.7 + 20.3k`).
* `E − DL` (soj.md own bound with callees): `(k+1)` structure operations (k−1 individualize, refine,
  SBB) `≤ (k+2)·SO`; `Ck(10) + Ck(12) + Ck(9) ≤ 195`; `C_ppc`; `C_CC(m) + m²(40+10k)`; `C_disc(m)`;
  `select_min` `≤ 88 + 54m + m(14 + 174 + 5)` + `Ck(9)`; `C_comp(m)`; the listcomp `19.5m + 15`; `C_up(m)`;
  one choose 104. With `(k+2)·2048m^4 ≤ 204.8m^5 + 4096m^4` (k ≤ m/10) and the cc bounds of Table U
  (`C_disc + C_up ≤ 130m^4 + O(m³ log m)`): `E − DL ≤ 205m^5 + 4300m^4`.
* `W_UPCC(|C|)`: `|C| > 2m/3 ≥ 61` (soj.md H61 for this caller), Theorem U.

    W_EDL ≤ 17·[(280 + 42k)m^{k+1} + 205m^5 + 4300m^4] + 1.87·2^{U(y)}.

**ω_edl(y, k) = log2(17(280+42k)m^{k+1} + 3485 m^5 + 73100 m^4 + 1.87·2^{U(y)})** (e = 0). Choice count: soj.md
(`log2 s_EDL ≤ (k−2)log2 m + max(log2 m, log2 s_UPCC(m))`).

### 8.5 The branch template `W_br[P, f_a, W_rec]`, with every callee substituted

main.md's template with C3 (the `_covered` sums with `h* = f_a + s·g`, `g := γ_n + 1 ≤ 3n + 1`) and these
substitutions (Table U; `a_x = len(aut_gens) ≤ 4m ≤ 4n` by structure_cc_wl.md "G ≤ 4K", hence
`2a_x ≤ 8n`; steady `lift` and `C_φ` by C5):
`align ≤ SO`, `aut_gens ≤ SO`, `lift ≤ 12n² + 111n + 581`, `Inv 10n+29`, `Act 11n+30`, `Isid 3n+39`,
`intersect_image(L ≤ 4n) ≤ B1 + 544n² + 1386n + 743`, `PermGroup(m, 2a_x) ≤ B1 + 128n² + 640n`,
`order ≤ B1`, `preimage(L ≤ 8n) ≤ 4B2 + 96n³ + 1099n² + 6500n + 1384`, `image_is_sym ≤ B1 + 24n² + 243n +
315`, `PermGroup(n, f_a) ≤ B1 + 247f_a n²` (only if f_a > 0), `Ident 2n+33`, `enumerate_runs ≤ 12 +
s(123 + 21d)`, `s·Mul`, `generated_subcoset(n, s+1) ≤ B1 + 1736(s+1)n³`, `2 Coset`, the first generic
`phi` `≤ B2 + 60n² + 359n + 529`, `RecordingChooser 8`. Then

    W_br[P, f_a, W_rec] = (s+1)·P + s·W_rec + Π,      Π = c0 + c1 s + c2 s² + c3 s³ + c4 s⁴,

    c0 = 5B1 + 5B2 + SO + 1832n³ + 1855n² + (9132 + λ)n + 3512 + 22d + f_a(3n + 50) + [B1 + 247 f_a n²]_{f_a>0}
    c1 = SO + 1736n³ + 12n² + 138n + 1259 + 22d + 2κ + f_a(14n² + 167n + 570)
    c2 = g(14n² + 167n + 570) + 960041 + 2κ + 20000·f_a·A'
    c3 = 20000·g·A' + (1 + 2κ)(20000 + f_a)
    c4 = (1 + 2κ)·g

(`c1`: the per-run terms `431 + d + 2κ + r̄ + align + lift + Inv + Act`, `_covered`'s `54 + 14h* +
h*(Isid + C_φ)` with `14 + 3n + 39 + C_φ = 14n² + 167n + 570`, `enumerate_runs`, `Mul`, a second
`1736n³`; `c2..c4` from `S²(960041 + 2κ + 20000h*A') + S³(1+2κ)(20000 + h*)` with `S ≤ s`.) All
coefficients are non-negative, so for `s ≥ 1`, `Π ≤ s^4·Σc_j`. Substituting `SO = 2048m^4 ≤ 2048n^4`,
the parameters of §8.2, `f_a ≤ 3nM` and collapsing at n ≥ 90 (λ = 1, F6):

| variant | `Π/λ ≤` | coefficient check |
|---|---|---|
| primitive, no choices (`f_a = 0`, s = 1) | `348207 n^5` | `348160 + 4096/90 + 3610/8100 + … = 348206.0` |
| imprimitive, no choices (s = 1) | `352303 n^5 + 1212 n³ M` | `+B1`; `f_a(261n² + 170n + 1140623) ≤ M(783 + 5.7 + 422.5)n³` |
| primitive, choices | `s^4 · 396384 n^5` | `348160 + 48000 (c3: 20000·3n·0.8m^4) + 223.3 + 0.5 + …` |
| imprimitive, choices | `s^4 (400480 n^5 + 48001 M n^5)` | `+B1`; `c2: 20000 f_a A' ≤ 48000 M n^5`, rest `≤ 0.1 M n^5` |

In the nodes the string factor 17 multiplies `W_br` (structures, keys and `_covered` tuples are
hashed). Nested calls: `≤ s` calls `iso(G1, x, y^{σ^{-1}})` (`W_rec = 0`), or those of `W_rec`.

### 8.6 N6b, pullback branch (`2|Cx| > m`; s = 1 by Lemma NC)

`W ≤ J0 + 17·(381 + 36m + W_tw + W_br[P_pull, 0, 0])`, `W_br = 2P_pull + Π` (primitive, no choices),
`P_pull ≤ 115 + 59m + W_tw + SR(m, 2)` (`check(3) = 56`),
`W_tw ≤ 72 + 85m + 78m² + 38m³ + ½m²·n(74 + 35X + λ) ≤ λ(1.28n^4 + 75.5n³ + 78n² + 85n + 72)`.
So `17·(381 + 36m + 3W_tw + 2(115 + 59m + SR(m,2))) ≤ 17·0.08·λn^5` and

    W ≤ λ(29070 + 17·(348207 + 0.08)) n^5 ≤ 5948600 λ n^5.

**ω_pull = 22.51 + 5X.** Nested calls: ≤ 1 call `iso(G1, x, y^{σ^{-1}})`, degree n.

### 8.7 N6b, EDL branch — quadratic in λ (e = 2)

`P_edl ≤ 31 + 5m + W_hs + SR(m,1) + W_EDL(m,t)/17`, and with C1:

    W_hs ≤ 243 + m + (47 + 4λ)n + (n+1)⌈lg(n+1)⌉ + 6λ²n⌈lg n⌉ + (11t + 53 + 2λ + 2n)m^t + 165λn + 83 + n + R_t

(`n·canon(λ) ≤ 165λn`: letters are set-free; `KStructure 27`; `check(D+2) ≤ 56 + n`; `refine_structures(m,t)
≤ R_t`). Every coefficient is a polynomial in λ of degree ≤ 2, so W ≤ λ²·(value at λ = 1) (F6).

    W/λ² ≤ J0 + 17·(381 + 36m + W_tw) + 17·2s·P_edl + 17·s^4·396384 n^5
        ≤ 34s·R_t + 34s(2n + 11t + 55)m^t + 34s(280 + 42t)m^{t+1} + 3.74s·2^{U(y)}
          + 6738528 s^4 n^5 + 8602 s n^5 + 29071 n^5

(`17·2s` for the ≤ s+1 ≤ 2s proc runs; `8602 = 34·(205 + 4300/90 + 0.05)` collects EDL's `205m^5 +
4300m^4` and the small terms of `P_edl`; `29071` collects J0 and `17(381 + 36m + W_tw)`; t ≥ 2,
`C(m,t) ≤ n`.)

**ω_pj_edl** = the base-2 log of this sum (§10); simple form
`4 ls + 2 + max(5.09 + log2(y+1) + log2(4t² + 55t + 287) + (2t+1)y, 1.91 + U(y), 5.09 + log2(2n + 53t + 335)
+ (t+1)y, 22.70 + 5X)`. Nested calls: `≤ s` calls `iso(G1, x, y^{σ^{-1}})` (≤ 1 if x ≠ y succeeds).

*Smallest e.* e = 2 is needed for this bound: the `6λ²n⌈lg n⌉` term is attained up to a constant
(C1), and nothing else in the node compensates it for large λ (all other terms are O(λ)). With
letters of bounded nesting depth h (height ≤ h), Lemma S3 gives `(h+1)·3λ` per comparison and the node
is linear in λ with the factor `6` replaced by `3(h+1)`.

### 8.8 N6c — `A_x + A_y`: the two `aggregate` misses (Q_A wrappers excluded)

main.md's miss bound with `F ≤ 3nM`, `r_F ≤ γ_m ≤ 1.5m`, `φ ≤ m`, `+64` for the string key (C6), and:
* `CERT := C[certificate](n,m,k)` (johnson_certs.md §3.16 with ext substituted): the builds are KL's
  `PermGroup(n+m)` init, `levels`, `level_group`, `order`, `coset_reps_prefix` (`6B2`) and
  `PermGroup(n, r_K)` (`B1`) for the `≤ J + 1 ≤ n+1` KL calls that are not cache hits (johnson_certs.md
  §3.15), RC's `subgroup` and `generated_subcoset` (`B2 + 2B1`) per iteration, SW's (`5B2 + 4B1`) and
  `pointwise_stabilizer` (`2B1`): `≤ (7n+12)B2 + (3n+9)B1 ≤ (11n+16)B2 + (4n+10)B1` (the latter used
  below); the k!-terms (INV-A) `≤ 1737(n+1)k!n³` (U-GS pieces `1736k!n³`, plus `k!(Inv+Act+Mul)`,
  KL's `k!(n + k² + 30k + 58)`, `coset_reps_prefix`'s `k!(k+1)(6n+75)`, `223k!k²` of `PermGroup(k, k!)`,
  all `≤ 2.9k!n² ≤ 0.04k!n³`); the remaining own and callee terms are `O(n^4 + n·k^5)`.
* `CJ := C[conjugate]` (§3.14): builds `subgroup` (`B2 + B1`), `Σ_i PermGroup(n, r_{N,i}) + PermGroup(n, r_K)`
  (`(n+2)B1`): `≤ B2 + (n+3)B1`; k!-terms `(n+1)k!(15k + 67 + 2(3n+11) + 223k²) ≤ 2.4(n+1)k!n²`.
* `M·(Inv + Ident)`, `F(Isid + 2C_φ) ≤ M(84n³ + 993n² + 3219n)`, the first generic phi, `LocalCertificates
  (n+31)`, `PermGroup(m, F) ≤ B1 + 741Mn³`, `orbits ≤ 400n²`, `r_F·restrict_to ≤ 1.5m(37m + 67)`,
  `is_giant_on(m, r_F) ≤ m + 19 + 2B1 + 1.5m(8m + 80)`.
* The BFS: `M²(65 + F(85 + 34k + Mul)) ≤ 65M² + M³·3n(96 + 6.4n) ≤ 65M² + 22.4n²M³` (34k ≤ 3.4n;
  `3n(96 + 6.4n) ≤ 22.4n²` iff n ≥ 90).

Per miss, `M·(CERT + CJ)` has the builds `M((11n+17)B2 + (5n+13)B1) = M(741376n + 1167360)n^5`; all
`M`-proportional terms collapse into `754347 M n^6`, all non-`M` terms (`≤ 3B1 + B2 + O(n²)`) into
`≤ 0.01 M n^6` (M ≥ n). Two misses (λ = 1):

    A_x + A_y ≤ λ(1508700 M n^6 + 3514 M k! n^4 + 44.8 n² M³ + 131 M²)

(`2·1737(1 + 1/90) + 2·2.4/90 ≤ 3514`; the exact substituted sum has M n^6-coefficient ≤ 1508694 at
n = 90, ownwork_gaps.md §3.5). **ω_agg ≤ 20.53 + 3 lM + LKF + 6X** (e = 1: the cache key hashes the string, `2(2λn+13)`).
Hits (`proc` of cases 1, 2a, 2b): `4λn + 47` each, inside the procs' bounds. Nested calls: the `Q_A`
certificate calls (8.9).

### 8.9 N6c — the `Q_A` wrappers

`Q_A ≤ 2M(n+1)k!` iso_window calls (johnson_certs.md §4; INV-A), windows `W_new ⊆ Ω`, groups of
degree n: `Q_A·W_iw(n) ≤ 2M(n+1)k!·20481λn^5 ≤ 41421 λ M k! n^6` (n ≥ 90).
**ω_QA = 15.34 + lM + LKF + 6X.** Nested: one `iso` per wrapper (window ≤ n points).

### 8.10 N6c case 1 (s = 1 by Lemma NC)

`H_1 = 17·W_br[P_1, f_a, 0] = 17(2P_1 + Π)` (imprimitive, no choices), `P_1 ≤ 163 + 4λn + 54m + 3m²
+ (58 + m) + SR(m, m+1)` (`check(m+5) = 58 + m`); with `⌈lg(m+1)⌉ ≤ 0.1n`,
`SR(m, m+1) ≤ 0.5n³ + 1800n + 200`, so `17·2P_1 ≤ 0.003·λn^5`:

    H_1 ≤ λ(5989168 n^5 + 20604 n³ M)        (17·352303 = 5989151; 17·1212 = 20604).

**ω_case1 = log2(5989168n^5 + 20604n³M) ≤ 22.52 + lM + 5X.** Nested: ≤ 1 call `iso(G1, ·)`.

### 8.11 N6c case 2a (s = 1; `top_action` with its five wrappers)

`H_2a = 227 + W_br[P_2a, f_a, 11 + W_ta]` (main.md), times 17 (generously also on `W_ta`), with
`P_2a ≤ 115 + 4λn + 23m + 56 + SR(m, 2)` and, by C8 (`r1 ≤ 3n`, `f' ≤ γ_n ≤ 3n`, `f ≤ 3nM`, w ≤ n):

    W_ta ≤ 636 + 8m + 54n + 32f + n⌈lg n⌉ + (19+λ)n + 4n² + Σ_ta + 5·W_iw(n),
    Σ_ta ≤ (B2 + B1 + 1238n³) [subgroup] + 10 + 12n(37n + 67) [(2r1 + 2f')·restrict_to] + 9n·C_φ [(r1+2f')·phi]
           + 2(78n² + 192n + 147) + 60n [lambda@845] + (3B2 + 643n³) [kernel] + (n(X + n + 19) + 8n + 33) [omega_of]
           + f(3n+39) + (B1 + 247fn²) + (22n + 229) [alt_gens] + 5(B2 + 60n² + 357n + 704) [lifts]
           + 4(113 + 2n) + 2(B1 + 24n² + 243n + 315) + 3(3n + 87) + 3(24n + 70) + (B1 + 4·1736n³) + (2n + 33) + (n + 10).

Builds `9B2 + 5B1 = 610304n^5`, wrappers `5·20481n^5`; f-terms `≤ M(741n³ + 9n² + 213n)`. With
`s = 1`, `W_br = 2P_2a + 11 + W_ta + Π`:

    H_2a ≤ 17·[(352302 + 712706.3 + 0.1)n^5 + (1212 + 741.2)n³M] λ ≤ λ(18105170 n^5 + 33218 n³ M).

**ω_case2a ≤ 24.12 + lM + 5X.** Nested: ≤ 5 calls (`top_action`: ≤ 4 on `Ω(Φ)`, 1 on the rest).

### 8.12 N6c case 2b

`H_2b = 17·W_br[P_2b, f_a, 0]`, `P_2b ≤ 62 + 4λn + W_2b`, `W_2b ≤ 526 + 206m + 105m² + 4m³ + m²⌈lg m⌉ + 7r_F +
m·γ_m(2m² + 7m + 20) + Σ_2b` with `r_F, γ_m ≤ 1.5m` and

    Σ_2b ≤ 112 + 59m + SR(m,2) + 1.5m(37m+67) + (B1(m) + 1.5m(8m+80)) + m·[4B1(m) + SO + 135m³ + 679m² + 463m + 231]
           + 2C_CC(m) + canonical_keys(m) + C_disc(m) + 247m² + 254 + C_comp(m) + SO + 4 + W_UPCC(m)/17,

(per while-iteration: `orbitals`, `order`, `point_stabilizer` (2 builds), `PermGroup(p_j − 1, r_v)`,
`individualize`, `choose`, `r_v·restrict_to`; `select_min ≤ 247m² + 254`; the terminal `split_by_blocks`
`≤ SO`; `set_keys 4`; the upcc run under H61). So `W_2b − W_UPCC/17 ≤ 16384m^6 + O(m^5 log m)`, and
`17·2s·(W_2b − W_UPCC/17) ≤ 0.01·s·2^{U(y)}` (`2^{U(y)} ≥ 5196 m^{12.39}`), while `17·2s(62 + 4λn) ≤ 161λs n^5`
goes to the `n^5` term (n may exceed every power of m). Hence

    H_2b ≤ λ(3.75 s·2^{U(y)} + 6808321 s^4 n^5 + 816017 s^4 M n^5)

(the `≤ s+1 ≤ 2s` runs of `proc` give `2s·W_UPCC ≤ 3.74 s·2^{U(y)}`; `17·400480 + 161 = 6808321`;
`17·48001 = 816017`).
**ω_case2b ≤ 4 ls + 1.59 + max(1.91 + U(y), 22.70 + 5X, 19.64 + lM + 5X).** Nested: ≤ s calls `iso(G1, ·)`.

### 8.13 N6c case 3

**Own work `W_c3`** (main.md, `Γ ≤ 4M²`, plus the string extras `34(Γ + 2M)` of C6):
* `CMP := C[compare]` (johnson_certs.md §3.18, callees substituted, `ℓ ≤ n+1`, `Λ ≤ (n+1)k!`):
  `(n+1)B1` (the `≤ ℓ` `generated_subcoset`) `+ (n+1)k!(1736n³ + 54n + 164)` (pieces, `Λ(27n + 83)`,
  `Λ·Mul`, `Λ'(Inv + Act + Mul)`) `+ 503 + 40m + 111n + 2n(t + k + 19) + (n+1)(n⌈lg n⌉ + 2n + 102)` `+`
  `image_is_sym` steady `202 + m`, `parity(m) 55m + 43`, steady `lift`, `Coset`.
* `OL := C[ordered_label](k) ≤ 4096k^5 + k!(3k² + 101k + 120) + 37k + 194` (`elements(k; k!) ≤ B1(k) + 96 +
  2k + k!(k+1)(3k+75)`).
* per test set (2M): `Ident + C_φ + Inv(m) + k!·OL`; once: `image_order` (B1 + …), the first `lift`
  (B2 + …), the first generic phi (B2 + …).

      W_c3 ≤ λ(16569 M² n^6 + 7025 M² k! n^4 + 0.32 M (k!)² n²)

(`4M²(n+1)B1 ≤ 16566 M²n^6`; `4M²(n+1)k!(1736n³ + …) ≤ 7021.2 M²k!n^4`, `2Mk!·4096k^5 ≤ 0.09 M²k!n^4` as
`M ≥ n`, `k ≤ n/10`; `2M(k!)²(3k² + 101k + 120) ≤ 0.32M(k!)²n²`). **ω_c3own ≤ 14.53 + 2lM + 2LKF + 6X.**

**The compare wrappers.** `Q_cmp ≤ 4M²(n+1)k!` iso_window calls with letters `λ+2 ≤ 3λ`;
`W_iw(n, λ+2) ≤ λ·20481n^5` (the λ-term of W_iw is `(135+λ')n`), so `Q_cmp·W_iw ≤ 82839 λ M² k! n^6`.
**ω_c3Q = 16.34 + 2lM + LKF + 6X.**

**The branch** `17·W_br[P_3, f_a, 0]` (imprimitive, choices) with C7:

    P_3 ≤ 226 + λn + 33m + m⌈lg m⌉ + (9k + 82)m^k + 18k(k+4)m^k⌈lg m⌉ + (k+5)m^{2k} + 169(k+4)m^k
          + 84 + m^k + R_k + SR(m, 2) + W_EDL(m,k)/17

(`D3 ≤ m^k`, sort `≤ 18(k+4)·D3⌈lg D3⌉`, `canon(k+4) ≤ 169(k+4)`, `check(D3+3) ≤ 56 + m^k`, `KStructure 27`).
`(k+5)m^{2k}` and all `m^k`, `m^{k+1}` terms are `≤ (y+1)(k+1)m^{2k+1}`, so
`P_3 ≤ (y+1)(4k² + 56k + 288)m^{2k+1} + 254m^5 + λn + W_UPCC/17`. Then

    17·W_br ≤ λ[34s(y+1)(4k² + 56k + 288)m^{2k+1} + 3.74s·2^{U(y)} + 8670 s n^5 + 6808160 s^4 n^5 + 816017 s^4 M n^5].

**ω_c3br ≤ 4 ls + 2 + max(5.09 + log2(y+1) + log2(4k² + 56k + 288) + (2k+1)y, 1.91 + U(y), 22.71 + 5X,
19.64 + lM + 5X).** Nested: `Q_cmp` wrapper calls and ≤ s calls `iso(G1, ·)`.

`H_3 = W_c3 + Q_cmp·W_iw + 17·W_br`; **ω_case3** = log-sum of the three (§10).

### 8.14 N6c total

    W(N6c) ≤ J0 + 653 + λn + m + 17 + (A_x + A_y) + Q_A·W_iw(n) + H_case
           ≤ λ·[29070 n^5 + 672 n + (A_x+A_y)/λ + Q_A W_iw/λ + H_case/λ],

e = 1, with `H_case` from 8.10–8.13 (`A_y = 0` if `y = x`; `672n ≥ 653 + n + m + 17`). Which term leads
depends on (n, m, k, s): `44.8n²M³` (aggregate), `82839M²k!n^6` (case-3 wrappers), the k-ary WL
`(y+1)(4k²+56k+288)m^{2k+1}` of case 3 (it beats `M³` e.g. at m = 90, k = 9: `19y = 123.3 > 3 lM = 118.1`),
the soj run `2^{U(y)}`, or the `s^4` terms; `omega_N6c` takes the log-sum.

---------------------------------------------------------------------------------------------

## 9. What is conditional, sketched, or not proved

**Inherited assumptions** (each is stated and used as in the cited document):
1. **(A1) Returning runs** under `Params.paper()`: every `fallback` is unreachable (main.md §1.4, soj.md
   (I7), johnson_certs.md §3.16 "Fallback"); code after a `fallback` is not charged. Used in N4 (no
   `fallback` of `strong_luks`), case 2b (line 939), soj (individualize_until, `_individualize_v2`).
2. **(A3) Correctness of group.py / action.py**, used only for counts: `I ≤ q` (N4), `I ≤ s_c!` (N5),
   `G^φ` a giant in `setwise_stabilizer`, group orders handed to Schreier–Sims.
3. **(A5) Determinism of `proc`** (main.md Lemma R): the bound `s` on runs and the `≤ s+1` executions
   of `proc`. Lemma NC (s = 1) also rests on Lemma R.
4. **INV-A** (johnson_certs.md §1.7, `|lifts| ≤ k!`): used in `CERT`, `CJ`, `CMP`, `Q_A`, `Q_cmp`.
   Unconditionally replace `k!` by `m!/(m−k)!` in exactly these terms, i.e. `LKF` by
   `log2(m!/(m−k)!) ≤ k·log2 m` in ω_agg, ω_QA, ω_c3own, ω_c3Q. INV-W (J ≤ n/3) is not used (J ≤ n is used instead).
5. **(H61)** `|V| ≥ 61` for the upcc call of case 2b (assumed in soj.md §3, item 2); for the EDL callers it
   is proved (m ≥ 90). Without it soj.md's run analysis (and Theorem U) does not apply to case 2b.
6. **CST** `λ_N ≤ ⌈3N/2⌉ − 1` (Cameron–Solomon–Turull), via group.md Lemma C(b); all generator counts.
7. **Coherence of WL outputs** (soj.md §3, item 3, which takes it from CORRECTNESS.md §7): used by
   soj's reachability and choice lemmas, hence by Theorem U and Lemma CH.

**Proved here but only in outline** (complete proofs, with the sums written out term by term, are in
`ownwork_gaps.md` §2–§4; the stated constants are those sums rounded up — some with very little
slack, e.g. 1508694 → 1508700):
8. Theorem U: the dominant group is bounded in full; the ~30 lower-order groups are bounded by order
   of magnitude (`poly(y)·m^a`, a ≤ max(6 + log2 y, 4.5 + 2 log2 y)) with the constant 0.03 for their sum;
   their individual constants (e.g. the counts of chooser checks and canon callbacks per bipartite
   level) are generous readings of soj.md's callee lists, not re-derived line by line.
9. The polynomial (non-build, non-k!) parts of `CERT`, `CJ` and of `aggregate` (§8.8), whose
   contribution to the leading coefficient is < 1 (out of 1508700).
10. Lemma CH's object sizes rely on soj.md's `Σ2 < 2|V|/3` and the DL candidate size `≤ 4 + ℓ*σ_pt`;
    the height bound `≤ m` of chosen objects is a crude reading (nesting depth ≤ contraction levels + 1).

**Modelling choices:**
11. Strings are charged per character (factor 17, §1.3). Under main.md's atom convention for
    tuple-embedded strings the Johnson bounds only decrease.
12. For `johnson.iroot` and the code objects of soj.py in §3 the opcount profile is cross-checked
    with the region profile of soj.md (Lemma 1.1', `tests/test_soj_regions.py`); where they differ
    the larger count is used.

**Not bounded:** N6a (unreachable, main.md §6.6); the forced-prefix variant of `_chain_search` (only
`string_isomorphism` with a user group); `graph.py` (not a node).

---------------------------------------------------------------------------------------------

## 10. Code: `omega_<type>` functions (upper bounds on log2(W / λ^e)) with a self-test

The functions return the sharp log-sum forms of §5–§8 (the "sharp form" column of §0); `_selftest()`
checks, on admissible points (n = 2^14, 2^20, 2^40, 2^64, m = 10k, t = 2, s ∈ {1, 2^10}), that each sharp
value is at most the simple ω of the summary table, and prints the values. Saved as a file and run
with `python`, the block prints a table and "self-test passed".

```python
"""Upper bounds on log2(W / lam^e) for the node types of babai_gi (ownwork.md).

All arguments are logs base 2 except t and k (integers):
  X = log2 n, y = log2 m, lq = log2 q, lI = log2 I, lM = log2 M (M = binom(m, k)),
  ls = log2 s.  Each function bounds log2(W / lam^e) with e = 1, except omega_pj_edl (e = 2);
  omega_J0, omega_upcc and omega_edl bound lambda-free quantities (e = 0 is also valid for them).
Admissible ranges: n >= 2 (X >= 1) for omega_iso .. omega_cameron; Johnson nodes:
90 <= m <= n, binom(m, t) <= n, k = max(9, floor(X) + 3) <= m/10, s >= 1.
"""
from math import log2, lgamma, log, inf

def _lse(*terms):
    """log2(sum 2^t) for the given exponents (base-2 log-sum-exp)."""
    t = [x for x in terms if x != -inf]
    mx = max(t)
    return mx + log2(sum(2.0 ** (x - mx) for x in t))

def _l(c):
    return log2(c)

def log2fact(k):
    return lgamma(k + 1) / log(2)

def U_exp(y):
    """log2 of the closed form of one run of upcc_split_or_johnson, without its constant."""
    return (7 + 2 * log2(y)) * y + 4 * log2(y + 2)

# ------------------------------------------------------------------ wrappers (n >= 2)
def omega_iso(X):                     # W_iso <= 276 lam n^2
    return _l(276) + 2 * X

def omega_iw(X):                      # W_iw(n, <= n) <= 21038 lam n^5
    return _l(21038) + 5 * X

def omega_cr(X):                      # P_cr <= 23138 lam n^6 (incl. the wrappers of the <= n orbit calls)
    return _l(23138) + 6 * X

# ------------------------------------------------------------------ N1, N3 (n >= 2)
def omega_bf(X):                      # 14164 n^5 + 1123944 n^2 + 921385 n + 4894264  (<= 2^18.48 n^5)
    return _lse(_l(14164) + 5 * X, _l(1123944) + 2 * X, _l(921385) + X, _l(4894264))

def omega_giant(X):                   # 16634 n^5
    return _l(16634) + 5 * X

# ------------------------------------------------------------------ N4, N5 (n >= 2)
def omega_luks(X, lq):                # A(n) + q B(n),  A = 1600 n^7 + 444310 n^5,  B = 1790 n^3
    return _lse(_l(1600) + 7 * X, _l(444310) + 5 * X, _l(1790) + lq + 3 * X)

def omega_cameron(X, lI):             # 1600 n^7 + 518132 n^5 + 1898 I n^3,  I <= s_c!
    return _lse(_l(1600) + 7 * X, _l(518132) + 5 * X, _l(1898) + lI + 3 * X)

# ------------------------------------------------------------------ Johnson (n >= m >= 90)
def omega_J0(X):                      # J0 <= 29070 n^5
    return _l(29070) + 5 * X

def omega_upcc(y):                    # one run of upcc on |V| <= m points, base on m points
    return _l(1.87) + U_exp(y)

def omega_edl(y, k):                  # one run of extended_design_lemma (X.k = k) on m points
    m5 = 5 * y
    return _lse(_l(17 * (280 + 42 * k)) + (k + 1) * y, _l(17 * 205) + m5, _l(17 * 4300) + 4 * y,
                _l(1.87) + U_exp(y))

def omega_pj_pullback(X):             # N6b, 2|Cx| > m: s = 1;  W <= 5948600 lam n^5
    return _l(5948600) + 5 * X

def omega_pj_edl(X, y, t, ls):        # N6b, EDL branch, t >= 2:  W <= lam^2 * 2^omega
    RT = log2(y + 1) + _l(4 * t * t + 55 * t + 287) + (2 * t + 1) * y
    return _lse(_l(34) + ls + RT,
                _l(3.74) + ls + U_exp(y),
                _l(34 * (280 + 42 * t)) + ls + (t + 1) * y,
                _l(34) + ls + log2(2 * 2 ** X + 11 * t + 55) + t * y,
                _l(6738528) + 4 * ls + 5 * X, _l(8602) + ls + 5 * X, _l(29071) + 5 * X)

def omega_agg(X, k, lM):              # A_x + A_y (two aggregate misses), Q_A wrappers excluded
    lkf = log2fact(k)
    return _lse(_l(1508700) + lM + 6 * X, _l(3514) + lM + lkf + 4 * X,
                _l(44.8) + 3 * lM + 2 * X, _l(131) + 2 * lM)

def omega_QA(X, k, lM):               # Q_A * W_iw(n),  Q_A <= 2M(n+1)k!
    return _l(41421) + lM + log2fact(k) + 6 * X

def omega_branch_rest(X, lM, ls, imprimitive, choices):
    """Pi = c0 + c1 s + ... + c4 s^4 of the branch template (Section 8.5), i.e. W_br minus
    (s+1)P and s W_rec; values in the conventions of the per-module documents (x17 is applied
    by the callers)."""
    if not choices:                   # d = 0, hence s = 1
        if imprimitive:
            return _lse(_l(352303) + 5 * X, _l(1212) + lM + 3 * X)
        return _l(348207) + 5 * X
    if imprimitive:
        return 4 * ls + _lse(_l(400480) + 5 * X, _l(48001) + lM + 5 * X)
    return 4 * ls + _l(396384) + 5 * X

def omega_case1(X, lM):               # H_1 (s = 1)
    return _lse(_l(5989168) + 5 * X, _l(20604) + lM + 3 * X)

def omega_case2a(X, lM):              # H_2a (s = 1) incl. top_action and its 5 iso_window wrappers
    return _lse(_l(18105170) + 5 * X, _l(33218) + lM + 3 * X)

def omega_case2b(X, y, lM, ls):       # H_2b
    return _lse(_l(3.75) + ls + U_exp(y), _l(6808321) + 4 * ls + 5 * X,
                _l(816017) + 4 * ls + lM + 5 * X)

def omega_case3_own(X, k, lM):        # W_c3 (+ string extras): own work of case_3 incl. the compares
    lkf = log2fact(k)
    return _lse(_l(16569) + 2 * lM + 6 * X, _l(7025) + 2 * lM + lkf + 4 * X, _l(0.32) + lM + 2 * lkf + 2 * X)

def omega_case3_Qcmp(X, k, lM):       # Q_cmp * W_iw(n) at letter size lam + 2,  Q_cmp <= 4M^2(n+1)k!
    return _l(82839) + 2 * lM + log2fact(k) + 6 * X

def omega_case3_branch(X, y, k, lM, ls):   # 17 * W_br[P_3, f_a, 0]
    RK = log2(y + 1) + _l(4 * k * k + 56 * k + 288) + (2 * k + 1) * y
    return _lse(_l(34) + ls + RK, _l(3.74) + ls + U_exp(y), _l(34 * 255) + ls + 5 * X,
                _l(6808160) + 4 * ls + 5 * X, _l(816017) + 4 * ls + lM + 5 * X)

def omega_case3(X, y, k, lM, ls):
    return _lse(omega_case3_own(X, k, lM), omega_case3_Qcmp(X, k, lM), omega_case3_branch(X, y, k, lM, ls))

def omega_N6c(X, y, k, lM, ls, case):
    """total own work of an imprimitive Johnson node: J0 + 670 + n + m + A_x + A_y + Q_A W_iw + H_case."""
    h = {'1': lambda: omega_case1(X, lM), '2a': lambda: omega_case2a(X, lM),
         '2b': lambda: omega_case2b(X, y, lM, ls), '3': lambda: omega_case3(X, y, k, lM, ls)}[case]()
    return _lse(omega_J0(X), _l(672) + X, omega_agg(X, k, lM), omega_QA(X, k, lM), h)

def _selftest():
    """Sharp forms <= the simple forms of the summary table, on admissible points; prints a table."""
    from math import comb
    names = ("iso", "iw", "cr", "bf", "giant", "luks", "cam", "J0", "upcc", "edl", "pull", "pj_edl",
             "agg", "QA", "case1", "case2a", "case2b", "case3", "N6c(1)", "N6c(2a)", "N6c(2b)", "N6c(3)")
    print("    X      y   k   ls  " + " ".join(f"{s:>8s}" for s in names))
    for n_exp in (14, 20, 40, 64):
        X = float(n_exp); n = 2 ** n_exp
        k = max(9, int(X) + 3); m = max(90, 10 * k); y = log2(m); t = 2
        assert m <= n and comb(m, t) <= n and k <= m / 10
        lM = log2(comb(m, k)); LKF = log2fact(k); U = U_exp(y)
        lq = 2 * X; lI = log2fact(int(y))
        for ls in (0.0, 10.0):
            sharp = [omega_iso(X), omega_iw(X), omega_cr(X), omega_bf(X), omega_giant(X),
                     omega_luks(X, lq), omega_cameron(X, lI), omega_J0(X), omega_upcc(y), omega_edl(y, k),
                     omega_pj_pullback(X), omega_pj_edl(X, y, t, ls), omega_agg(X, k, lM), omega_QA(X, k, lM),
                     omega_case1(X, lM), omega_case2a(X, lM), omega_case2b(X, y, lM, ls),
                     omega_case3(X, y, k, lM, ls)] + [omega_N6c(X, y, k, lM, ls, c) for c in ("1", "2a", "2b", "3")]
            simple = {0: 8.11 + 2 * X, 1: 14.37 + 5 * X, 2: 14.50 + 6 * X, 3: 18.48 + 5 * X, 4: 14.03 + 5 * X,
                      5: 16.79 + 7 * X + log2(1 + 2 ** lq), 6: 17.01 + 7 * X + log2(1 + 2 ** lI),
                      7: 14.83 + 5 * X, 8: 0.91 + U, 10: 22.51 + 5 * X,
                      11: 4 * ls + 2 + max(5.09 + log2(y + 1) + log2(4 * t * t + 55 * t + 287) + (2 * t + 1) * y,
                                           1.91 + U, 5.09 + log2(2 * n + 53 * t + 335) + (t + 1) * y, 22.70 + 5 * X),
                      12: 20.53 + 3 * lM + LKF + 6 * X, 13: 15.34 + lM + LKF + 6 * X,
                      14: 22.52 + lM + 5 * X, 15: 24.12 + lM + 5 * X,
                      16: 4 * ls + 1.59 + max(1.91 + U, 22.70 + 5 * X, 19.64 + lM + 5 * X)}
            c3 = _lse(14.53 + 2 * lM + 2 * LKF + 6 * X, 16.34 + 2 * lM + LKF + 6 * X,
                      4 * ls + 2 + max(5.09 + log2(y + 1) + log2(4 * k * k + 56 * k + 288) + (2 * k + 1) * y,
                                       1.91 + U, 22.71 + 5 * X, 19.64 + lM + 5 * X))
            simple[17] = c3
            for i, v in simple.items():
                assert sharp[i] <= v + 1e-9, (names[i], n_exp, ls, sharp[i], v)
            assert all(v == v and v < inf for v in sharp)
            print(f"{X:5.0f} {y:6.2f} {k:3d} {ls:4.0f}  " + " ".join(f"{v:8.1f}" for v in sharp))
    print("self-test passed")

if __name__ == "__main__":
    _selftest()
```
