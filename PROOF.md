# Running time of `babai_gi`: at most `2^{U(log₂ n)}` operations

This document proves an explicit upper bound on the number of **operations** (Part I)
executed by `string_isomorphism(G, x, y)` and by `graph_isomorphism`, for the default
parameters `Params.paper()` and every input:

**Theorem A (String Isomorphism).** For every permutation group `G ≤ Sym(Ω)`, `|Ω| = n`,
given by generators, and all strings `x, y : Ω → ℤ`, `string_isomorphism(G, x, y)` executes
at most `2^{U(log₂ n)}` operations, where

    U(X) = b* X³ + X ρ(X) + 2 X² + E(X) + 10,
    b*   = (S₂ + δ) / (3 δ²) = 2.6593095...,   δ = log₂(3/2),   S₂ = 1/2 + π²/6,

`ρ(w) = 5 w log₂²w + 3 w log₂ w + 12 w`, and `E(X) = ∫₀^X e(u) du` with
`e(u) = 3u²/log₂²(u + 4) + 11u + 60`. Written out, for `n ≥ 2` (`X ≥ 1`),

    U(X) = b* X³ + 5X² log₂²X + 3X² log₂X + 39X²/2 + 60X + 3I(X) + 10,
    I(X) = ∫₀^X u² / log₂²(u + 4) du = (1 + o(1)) X³ / (3 log₂²X),

and `U(0) = 10` for `n = 1`. By Lemma 4.2, `3I(X) ≤ X³/log₂²(X + 4) + 1.17 X³/log₂³(X + 4)`, so in
closed form the operation count is at most

    2^10 · 2^{b* X³ + X³/log₂²(X+4) + 1.17 X³/log₂³(X+4) + 5X² log₂²X + 3X² log₂X + 39X²/2 + 60X}.

The second-order term of `U` is `3I(X) = (1 + o(1)) X³/log₂²X`; it exceeds `5X² log₂²X` only for
`X > 2^{19.34}`. (For other hashable letters add the cost of `canon.normalize_letters`, §13.1.)

**Theorem B (Graph Isomorphism).** For graphs on `v ≥ 2` vertices given by edge lists of
length at most `L`, `graph_isomorphism` executes at most `288L + 2^{U_GI(log₂ v)}` operations,

    U_GI(V) = F(2V − 1, V, 2V − 1) + (2V − 1) ρ(V) + 2(2V − 1)² + E(2V − 1) + 10
            = (2A + 3B) V³ + 10V² log₂²V + 6V² log₂V + (54 − A − 5B/2) V² − 5V log₂²V
              − 3V log₂V + (78 + B/2) V − 42.5 + 3I(2V − 1)
            ≤ (2A + 3B) V³ + 10V² log₂²V + 6V² log₂V + (54 − A − 5B/2) V² − 5V log₂²V
              − 3V log₂V + (78 + B/2) V − 42.5 + Z³/log₂²(Z + 4) + 1.17 Z³/log₂³(Z + 4)
            = (2A + 3B) V³ + (8 + o(1)) V³/log₂²V,         Z = 2V − 1,
    2A + 3B = (4S₂ + 7δ)/(6δ²) = 6.1733746...   (§4, §13.2, Lemma 13.3).

**The form `a · 2^{b log^c n}`.** `U(X) − b* X³ → ∞`, so the exponent `c = 3` and the
infimum `b*` of the admissible `b` are determined by the bound, `b*` is not attained (no
finite `a` works at `b = b*`), and for each `b > b*` the smallest `a` with
`2^{U(log₂ n)} ≤ a · 2^{b log₂³ n}` for every `n ≥ 1` is

    a(b) = 2^{M(b)},     M(b) = max_{n ≥ 1} (U(log₂ n) − b log₂³ n),

for which §13.3 proves lower and upper bounds that differ by at most `max(10⁻⁶ M(b), 0.02)`.
§13.4 explains in which sense `c = 3` and `b*` are optimal: they are the
values of the recursion that this proof bounds, and that recursion attains them.

Every step is a proof from the code (Parts I and III) or from the cited papers; the
numerical inequalities between explicit functions are verified with exact interval
arithmetic by `babai_gi/timebound.py` (`python -m babai_gi.timebound`).

**Code version.** Line numbers refer to the files of this version of the repository.

---

# Part I. The cost model

## 1. Operations

One **operation** is

* the execution of one CPython 3.13 bytecode instruction of the package
  (`dis.get_instructions`); an instruction counts one also when it handles a number of items
  fixed by the program text (building or unpacking a 3-tuple, one step of `zip` or
  `enumerate`);
* an arithmetic operation or comparison of `int` or `Fraction` values of any size (group
  orders are large integers): the instruction that performs it (unit-cost arithmetic);
* a dictionary or set lookup, insertion or deletion: one, plus the cost of hashing the key
  and of one `==` comparison; hashing or comparing a tuple or frozenset costs one per element
  it touches, recursively;
* a built-in whose work grows with its data costs one per element it touches, in addition to
  its call instruction: container constructors from an iterable, `sorted`
  (`L⌈log₂ L⌉` comparisons, each costing the comparison of its keys, plus `2L + 1`; a `key=`
  function is called `L` times), `sum`, `max`, `min`, `any`, `all`, `map`, `zip`,
  `enumerate`, `range` iteration, `x in list`, `list.index`, `list.count`, list repetition,
  slicing, `list.extend`, `list.pop(0)`, set and frozenset algebra and comparison (per
  element of both operands), equality and ordering of tuples and lists, `str`/`repr`,
  `itertools` generators (per element produced, times the length of the produced tuple),
  `math.factorial(L)` and `math.comb` (`L` multiplications), `str.join`, iteration over
  `.items()/.keys()/.values()`.

Not counted: the text of exception messages on error exits, and the work of the diagnostic
counters `Solver.stats` and `soj.STATS` beyond their `+= 1` instructions and one hash of the
key (at most 64).

The **letter size** `λ` of a string is the largest size of its letters (`size(a) = 1` for an
`int`, `bool`, `None` or short constant string, `1 + Σ size(e)` for a tuple or frozenset).
`string_isomorphism` and the graph functions first replace the letters by integers
(`canon.normalize_letters`), so for them `λ = 1`; inside the recursion only
`LocalCertificates.compare` builds new letters, `(ℓ, 0/1)`, of size `λ + 2`.

## 2. Lemma 1.1 (instruction profiles)

`babai_gi/opcount.py` computes for every function `f` a profile: `outside`, the number of
its instructions outside every loop, and for every loop `(line, kind, cycle, entry)`.

**Lemma 1.1.** One call of `f` executes at most

    outside + Σ_loops [ cycle · (iterations + entries) + entry · entries ]

of its own instructions, where `iterations` and `entries` are the total numbers of
iterations and entries of that loop during the call (an inner loop is entered once per
iteration of the enclosing loop).

*Proof.* `opcount.profile` attributes each instruction to the innermost loop (`for`,
`while`, inlined comprehension, `yield from`) whose source span contains its position, and
places three kinds of instructions by their offset instead, because CPython 3.13 gives them
positions outside the loop they belong to: `FOR_ITER` (it runs once per iteration plus once
per entry) goes to its loop together with its `EXTENDED_ARG` prefixes; a backward jump
belongs to the loop that owns its target (skipping `EXTENDED_ARG`); and an instruction inside
the cycle of a loop but attributed to an enclosing level (an exception-handler entry, which
has no position) goes to that loop. Between two executions of an instruction at offset `o`
control passes from an offset `≥ o` to an offset `≤ o`, which within one code object happens
only through a backward jump `j` with `target(j) ≤ o ≤ j` (exception handlers of the package
lie after the code they protect, and a generator resumes after its `YIELD_VALUE`). So an
instruction outside every backward-jump range runs at most once per call; an instruction in
the range of a loop's own jumps but not in an inner loop's runs at most once per execution
of the loop's head plus once per entry; and the head (`FOR_ITER`, the `while` test, `SEND`)
runs once per iteration plus once per entry. Nested code objects (lambdas, generator
expressions, inner functions) are separate profiles; `opcount` reports their loops too. ∎

`tests/test_opcount.py` checks the profiles against `sys.monitoring` counts on functions
with every loop shape used in the package (`for`, nested loops, `while`, comprehensions,
generators, `yield from`, `try` in loops, `break`/`continue`, a loop body longer than 255
code units), including the three placements by offset described in the proof.
`tests/test_attribution.py` checks the facts the proof uses on every code object of the
package: every backward jump belongs to a loop; every instruction in the range of a
backward jump of a loop `J` is attributed to `J` or to a loop nested in `J`; every
exception handler lies after the code it protects; and every lambda has no backward jump
and every generator expression one loop head, its `FOR_ITER`. The six code objects where
one of these fails (an exception exit jump of `canon.normalize_letters`, handler stubs in
`main._chain_search`, and four nested code objects that contain loops) are listed in the test
and bounded by hand in `docs/bounds/` (group.md Lemma R, main.md Lemma P, johnson_certs.md
§1.3).

## 3. Per-function bounds

For every function of the package the documents in `docs/bounds/` prove an explicit bound on
the operations of one call, by Lemma 1.1, an iteration bound with proof for every loop, the
built-in charges of §1 and the callees' bounds (`docs/bounds/SPEC.md` is the specification
they follow). Calls of `Solver.iso` made by a function are not part of its bound; they are
listed as the function's *solver calls*. Part III combines these bounds into the own work of
each node of the recursion.

---

# Part II. The recursion

Logarithms are to base 2. For a call on `Ω` with `|Ω| = n` we write `X = log n`.
`δ = log(3/2)`. CORRECTNESS.md proves that under `Params.paper()` no `fallback` and no
invariant check is reached (its Theorem B); all statements below are about such runs.

## 4. Constants and auxiliary functions

    S₂ = 1/2 + π²/6,   β = S₂/δ = 3.6667890...,
    B = 1/(2δ) = 0.8547556...,   A = (β − 1/2)/(3δ) = 1.8045539...,   C = 2,
    b* = A + B = (S₂ + δ)/(3δ²) = 2.6593095...

so that `2Bδ = 1` and `(3A + B)δ = β`. For `w ≥ 1` let `ℓ = log w` and

    ρ(w) = 5wℓ² + 3wℓ + 12w,     φ(w) = w ρ(w);

`ρ` and `φ` are nondecreasing and convex on `[1, ∞)` (their second derivatives are sums of
nonnegative terms), and `φ'` is nondecreasing. For `u ≥ 0` let

    e(u) = 3u²/log²(u + 4) + 11u + 60,     E(X) = ∫₀^X e(u) du.

**Lemma 4.1.** `e` is nondecreasing and `e ≥ 60` on `[0, ∞)`; hence `E` is convex, and
`E(X) − E(X') ≥ (X − X') e(X')` and `E(X) − E(X') ≥ X − X'` for `X ≥ X' ≥ 0`.

*Proof.* With `l = log(u + 4)`, `d/du [u²/l²] = (2u/l²)(1 − u/((u + 4) l ln 2))`, and
`(u + 4) l ln 2 = (u + 4) ln(u + 4) ≥ u` because `ln(u + 4) ≥ ln 4 > 1`. ∎

**Lemma 4.2.** Let `I(X) = ∫₀^X u²/log²(u + 4) du`, so that `E(X) = 3I(X) + 11X²/2 + 60X`, and
`L = log(X + 4)`. For all `X ≥ 0`,

    X³/(3L²)  ≤  I(X)  ≤  X³/(3L²) + 1.17 X³/(3L³).

*Proof.* Let `G_α(X) = (X³/3)(L⁻² + αL⁻³)`; `G_α(0) = 0 = I(0)`. With `dL/dX = 1/((X + 4) ln 2)`,
`t = X + 4` and `q = X/t`,

    G_α'(X) − X²/L² = (X²/L³) · [α(1 − q/ln t) − 2q/(3 ln 2)].

For `α = 0` the bracket is `≤ 0`, so `G_0' ≤ I'` and `G_0 ≤ I`. For `α = 1.17` the bracket is
`≥ 0` iff (multiplying by `(3 ln 2/2) t ln t > 0`)

    h(t) = (κ − 1) t ln t + 4 ln t − κ t + 4κ ≥ 0,     κ = (3 ln 2/2) · 1.17 = 1.2165…,

for `t ≥ 4`. `h = P − N` with `P = (κ − 1) t ln t + 4 ln t + 4κ` and `N = κt` nondecreasing, and
`timebound.check_I_bound` verifies `P(u) − N(v) ≥ 0` on a partition of `[4, 512]` with exact
interval arithmetic; for `t ≥ 512`, `h(t) ≥ t((κ − 1) ln t − κ) ≥ 0` because
`(κ − 1) ln 512 ≥ κ` (also checked). So `G_α' ≥ I'` and `I ≤ G_α`. ∎

(The bracket is `≥ 0` for every `X` iff `α ≥ sup_t (2/(3 ln 2))(t − 4) ln t/(t ln t − t + 4)`
`= 1.16684…` (at `t ≈ 88`), so `1.17` is the best two-decimal constant of this form; as
`X → ∞` the constant needed tends to `2/(3 ln 2) = 0.9618…`, the coefficient of the expansion
`I(X) = X³/(3L²) + (2/(3 ln 2)) X³/(3L³) + O(X³/L⁴)`. For `X ≥ 84` the upper bound exceeds
`I(X)` by less than 1%.)

The remainder of the Split-or-Johnson choice count (`docs/bounds/soj.md`, Theorem B) is

    R(Y) = 5.8 Y log²Y + 6.1 Y log Y + 10.3 Y + 3.5 log²Y + 6 log Y + 9,

nondecreasing for `Y ≥ 1`.

## 5. Sections and the section degree

A group `S` is a *section* of `H` if `S ≅ K/L` for subgroups `L ⊴ K ≤ H`. For a permutation
group `H` let

    μ(H) = max({4} ∪ {μ ≥ 5 : Alt(μ) is a section of H}).

**Lemma 5.1.**
(a) A section of a section of `H` is a section of `H`; so `μ(H') ≤ μ(H)` if `H'` is a
    subgroup or a homomorphic image of `H` (for example the group induced by `H` on an
    invariant set or on a system of blocks).
(b) If `H` embeds in `Sym(r)` then `μ(H) ≤ max(4, r)`.
(c) If `N ⊴ H`, every nonabelian simple section of `H` is a section of `N` or of `H/N`.
    Hence `μ(H₁ × H₂) ≤ max(μ(H₁), μ(H₂))` for subdirect products, and
    `μ(H) ≤ max(4, s, c)` for `H ≤ Sym(s) wr Sym(c)`.
(d) If `H` contains a subgroup isomorphic to `Alt(m)`, `m ≥ 5`, then `μ(H) ≥ m`.

*Proof.* (a) If `L' ⊴ K' ≤ K/L`, their preimages `L ≤ L'' ⊴ K'' ≤ K` satisfy
`K''/L'' ≅ K'/L'`. (b) `|Alt(μ)| = μ!/2` divides `|H|`, which divides `r!`, and
`μ!/2 > r!` for `μ ≥ r + 1 ≥ 5`. (c) Let `S = K/L` be simple nonabelian. `(K ∩ N)L/L` is
normal in `K/L`, so either `(K ∩ N)L = K` and `K/L ≅ (K ∩ N)/(K ∩ N ∩ L)` is a section of
`N`, or `K ∩ N ≤ L` and `K/L` is a quotient of `K/(K ∩ N) ≅ KN/N ≤ H/N`. For a subdirect
product take `N = H ∩ (H₁ × 1)`, whose quotient embeds in `H₂`; for the wreath product
`N = H ∩ Sym(s)^c`, then the product case and (b) for `H/N ≤ Sym(c)`. (d) A subgroup is a
section. ∎

## 6. Towers, levels and the potential

A *tower* for `G` (`tower.py`) is a sequence `P₁ < … < P_k` of `G`-invariant partitions of
`Ω`, strictly coarsening, each with at least two blocks; `P₀` is the partition into points
and `P_{k+1} = {Ω}`. For `G` transitive and a level `i ∈ {1, …, k+1}` let `Bl` be a block
of `P_i` and

* `r_i` = the number of `P_{i−1}`-blocks in `Bl` (the same for all blocks, `G` being
  transitive on `P_i`), so `∏ r_i = n`;
* `H_i` = the permutation group induced by the setwise stabiliser `G_{Bl}` on these `r_i`
  blocks (the same up to isomorphism for all `Bl`); `H_{k+1}` is the action of `G` on the
  blocks of `P_k` (*the top action*);
* `z_i = log r_i`, `w_i = log min(r_i, μ(H_i))`, `X_i = z₁ + … + z_i` (so `X_{k+1} = X`).

So `1 ≤ z_i ≤ X_i` and `min(z_i, 2) ≤ w_i ≤ z_i`. Put

    F(z, w, Y) = z (A w² + B w (Y − (z − w)/2)),
    T(z, w, Y) = F(z, w, Y) + z ρ(w) + C z²,
    Φ(G, T)    = Σ_{i=1}^{k+1} T(z_i, w_i, X_i) + E(X).

The *level part* `Λ(G, T) = Φ(G, T) − E(X)`. If `G` is transitive, `ext(T)` is the tower
that `_solve` uses after its extension step (`main.py:297-308`): `T` itself if the top
action is primitive, otherwise `T` followed by the partition `coarse` (CORRECTNESS.md,
Lemma 5.3); `Φ_ext(G, T) = Φ(G, ext(T))`.

**Lemma 6.1 (the function F).** On `{0 < w, 0 < z ≤ Y}`:
`∂F/∂z = w(A w + B(Y − z) + B w/2) > 0`, `∂F/∂w = z(2Aw + B(Y − z/2) + Bw) > 0`,
`∂F/∂Y = B z w > 0`; and for `z₁ + z₂ = z`,

    F(z₁, w, Y) + F(z₂, w, Y − z₁) = F(z, w, Y).                                   (6.1)

Moreover `F(q, q, Y) = A q³ + B q² Y`, and for `z₁, z₂ > 0`, `s = z₁ + z₂`,

    F(z₁, z₁, Y) + F(z₂, z₂, Y − z₁) = F(s, s, Y) − z₁ z₂ (3A s + 2B Y + B z₂).    (6.2)

*Proof.* Direct computation. For (6.1) both sides equal
`A z w² + B w z Y − (B/2) w z² + (B/2) z w²` after `z² = z₁² + z₂² + 2z₁z₂`. For (6.2):
`A(z₁³ + z₂³) + B(z₁² Y + z₂²(Y − z₁))` against `A s³ + B s² Y`. ∎

`T` is nondecreasing in each argument on this region, since `ρ` is nondecreasing.

**Lemma 6.2 (monotonicity).**
(a) If `H ≤ G` is transitive, `Φ(H, T) ≤ Φ(G, T)`.
(b) If `H ≤ G` and `O` is an orbit of `H`, then every level of the restricted tower `T|O`
    (`Tower.restrict`, which drops trivial and repeated levels) is the restriction of a level
    `i` of `T` with `r'_i ≤ r_i`, `μ(H'_i) ≤ μ(H_i)`, `X'_i ≤ X_i`, distinct levels of `T|O`
    coming from distinct levels of `T`; hence `Λ(H^O, T|O) ≤ Λ(G, T)` level by level.
(c) `Φ_ext(G, T) ≤ Φ(G, T)`. More precisely, the extension replaces the top level
    `(z, w, X)` by two levels `(z_c, w_c, X)` and `(z_s, w_s, X − z_c)` with `z_c + z_s = z`,
    `w_c, w_s ≤ w`, and `T(z_c, w_c, X) + T(z_s, w_s, X − z_c) ≤ T(z, w, X) − 2C z_c z_s`.

*Proof.* (a) `H_{Bl} ≤ G_{Bl}`, so the induced groups are subgroups; Lemma 5.1(a). (b) If
`Bl` is a block of `P_i` meeting `O`, an element of `H` mapping `Bl ∩ O` into itself maps `Bl`
to `Bl` (it maps `Bl` to a block meeting `O` in `Bl ∩ O`), so the setwise stabiliser of
`Bl ∩ O` in `H^O` is `(H_{Bl})^O`, which acts on the `P_{i−1}`-blocks meeting `Bl ∩ O`: an
invariant subset of the blocks counted by `r_i`, so the group is a homomorphic image of a
subgroup of `H_i`. A dropped level contributes ratio 1. Each term of `Φ` is nondecreasing in
`z_i, w_i, X_i` (Lemma 6.1, `z_i ≤ X_i` holds in both towers), so we may decrease the
arguments one at a time. (c) The new top action is a quotient of the old top action, the new
lower level is the action of a block stabiliser on the old top blocks inside it, a
restriction of a subgroup (Lemma 5.1(a)); the ratios multiply to `r_{k+1}`. By (6.1) and
monotonicity in `w`, `F(z_c, w_c, X) + F(z_s, w_s, X − z_c) ≤ F(z, w, X)`;
`z_c ρ(w_c) + z_s ρ(w_s) ≤ z ρ(w)`; `C(z_c² + z_s²) = C z² − 2C z_c z_s`. ∎

## 7. Calls, passes and leaves

A *call* is an execution of `Solver.iso`, a *node* an execution of `Solver._solve`. For a
state `ν = (G, T)` and `λ ≥ 1` let

    B_λ(ν) = sup ops(_solve(G, x, y, T)),

over strings `x, y` of letter size `≤ λ` and over all states of the caches that satisfy
CORRECTNESS.md (P1). `Solver.iso(G, x, y, T)` (`main.py:219-256`) runs, after the checks of
its first lines, `_solve(G, x, y, T)` (through `_one_iso`) and, if that succeeds and `x ≠ y`,
`iso(G, x, x, T)`, which returns `G.aut_cache[x]` if present and otherwise runs
`_solve(G, x, x, T)` and stores the result; for `x = y` it runs at most one `_solve`. Call
the execution of `_solve(G, x, y)` the *y-pass* and that of `_solve(G, x, x)` the *x-pass*.

**Lemma 7.1 (leaves of a call).** Let `H` be a group of degree `n'` with a tower `T'`, and
consider one call `iso(H, x, y, T')`. Define the *leaves* of the call as the groups on
which a nested `iso` call is made by the chain of `chain_rule` nodes starting at this call,
and whose own node is not a `chain_rule` node: either `|L| ≤ 5040` (brute force) or `L`
transitive. Then
(a) every leaf is `L = (H_L)^{O_L}` for a subgroup `H_L ≤ H` and an `H_L`-orbit `O_L`, with
    the tower `T'|O_L`; the sets `O_L` are pairwise disjoint;
(b) each leaf receives exactly one `iso` call (one y-pass and at most one x-pass, or one
    x-pass);
(c) `ops(iso(H, x, y, T')) ≤ P_iso(n') + 2 Σ_{L transitive, |L| > 5040} B_λ(L, T'|O_L)`,
    where `P_iso(n') = 2n'(P_cr(n') + W_iso(n') + W_bf(n'))` with the bounds `P_cr`
    (one chain-rule node, including the restriction work and the wrappers of its nested
    calls), `W_iso` and `W_bf` (brute force) of Part III.

*Proof.* If `H` is transitive or `|H| ≤ 5040`, `H` is the only leaf and (c) is the wrapper
plus a y-pass and an x-pass. Otherwise `_solve(H, x, y)` is a chain rule over the orbits of
`H` (`main.py:391-434`). (a) Window `i` of a chain rule on a group `K` is an orbit `Δ_i` of
`K`, and the nested call is on `cur^{Δ_i}` with `cur ≤ K` (the stage group); by induction
along the chain the groups are restrictions of subgroups of `H` to orbits, and the orbits of
a chain-rule node partition its domain. (b) Consider the y-pass of a chain-rule node on `K`
with `x ≠ y`. For each window it calls `iso(cur^{Δ_i}, x_i, y_i)` and, on success, appends
`(lifter, group)` to `K.stage_cache[x]`, where `group` is the lift of the automorphism group
returned by that call; inside that call, if `x_i ≠ y_i`, `iso` computed `Aut(x_i)` and stored
it in `cur^{Δ_i}.aut_cache[x_i]` (or returned at its first line, which costs only the
wrapper). The y-pass returns `None` as soon as one window fails, and then `iso(K, …)` returns
`None` without an x-pass. If it succeeds, the x-pass `_solve(K, x, x)` takes the same branch
(the order of `K` and its orbits do not depend on the strings), reads every
`(lifter, group)` from `K.stage_cache[x]` (`main.py:411-412`), so its window groups are the
same objects, and each nested `iso(cur^{Δ_i}, x_i, x_i)` is answered from `aut_cache` or at
its first line. So the x-pass of a chain-rule node makes no nested `_solve` call, and every
leaf is reached exactly once through the y-passes (or, where `x_i = y_i`, through one cold
x-pass, whose chain-rule descendants are again x-passes reaching each leaf once).
(c) A chain-rule tree with `≤ n'` leaves (disjoint nonempty domains) has at most `n' − 1`
internal nodes, each with at most two passes; a leaf with `|L| ≤ 5040` costs at most
`W_iso + 2W_bf`; a transitive leaf at most `W_iso + A + B ≤ W_iso + 2B_λ`. ∎

**Lemma 7.2 (windows).** Let `ν = (G, T)` be a transitive state after its extension step, so
`Φ_ext(ν) = Φ(ν)`, and let `L` range over states with pairwise disjoint domains `O_L ⊆ Ω`.
For each `L` put `X_L = log |O_L|` and define its *drop*

    D(L) = Λ(ν) − Λ(L) + E(X) − E(X_L) − (X − X_L),

where `Λ(L)` is the level part of `L` with its extended tower. Then

    Σ_L 2^{Φ_ext(L)} ≤ 2^{Φ(ν) − min_L D(L)}.

*Proof.* `Φ_ext(L) = Λ(L) + E(X_L) = Φ(ν) − D(L) + X_L − X`, and `Σ_L 2^{X_L − X} =
Σ_L |O_L|/n ≤ 1`. ∎

By Lemma 4.1, `E(X) − E(X_L) − (X − X_L)` is nonnegative and nonincreasing in `X_L`, so a
bound `X_L ≤ X − s` gives `D(L) ≥ Λ(ν) − Λ(L) + E(X) − E(X − s) − s`.

## 8. The induction

**Theorem 8.1.** For every transitive state `ν = (G, T)` and every `λ ≥ 1`,
`B_λ(ν) ≤ λ² · 2^{Φ_ext(ν)}`.

(The exponent 2 of `λ`: the own work of a node is at most `λ^e 2^{ω}` with `e = 1`, except
for the Extended Design Lemma branch of a primitive Johnson node, where `hypergraph_structure`
sorts the letters with `key=canon` and one comparison of canonical images costs up to `6λ²`
(`docs/bounds/ownwork.md` §8.7); `e = 2` covers all nodes since `λ ≥ 1`.)

The proof is by induction on CORRECTNESS.md's measure `(n, |G|, [x ≠ y])`: every nested
call is on a state with a smaller measure (CORRECTNESS.md §14; for the calls used below:
the kernel `N` of a nontrivial block action, `NG = φ⁻¹(N̄)` of index `|P| ≥ 2`, `G₁ =
φ⁻¹(Aut(S) ∩ φ(G))` with `Aut(S) ∩ φ(G) < φ(G)` (CORRECTNESS.md §12), `N ≤ G_A < G` in
the certificates, `K ≤ G₁`, `Aut_top ≤ G₁`, and restrictions to proper windows). After the
extension step the node is one of the types of §9, which also lists its nested calls. For a
node `ν` let

    W_tot(ν) = W(ν) + Σ_{nested calls c} P_iso(n_c),

`W(ν)` its own work (Part III). By Lemma 7.1 and the induction hypothesis,

    B_λ(ν) ≤ W_tot(ν) + Σ_c 2 λ_c² Σ_{L leaf of c} 2^{Φ_ext(L)},                   (8.1)

`λ_c ≤ λ + 2`, so `λ_c² ≤ 9λ²`, for the calls of `compare`, and `λ_c = λ` for all others. The
calls of a node are grouped into `g ≤ 3` groups; group `j` has `N_j` calls, letter factor
`κ_j ∈ {1, 9}`,
and every leaf of every call of the group has drop at least `D_j`, so that by Lemma 7.2

    Σ_{L leaf of c} 2^{Φ_ext(L)} ≤ 2^{Φ_ext(ν) − D_j}.

Then `B_λ(ν) ≤ λ² 2^{Φ_ext(ν)}` follows from

    W_tot(ν) ≤ λ² 2^{Φ_ext(ν) − 1}     and      D_j ≥ log N_j + log κ_j + 2 + log g  (all j).   (8.2)

We call `D_j` the *drop* of group `j`. §9 bounds the drops, §10 the multiplicities `N_j`,
§11 verifies the second half of (8.2), and Part III the first half.

## 9. The node types and their drops

Fix a transitive node `ν = (G, T)` with `|G| > 5040`, after the extension step, so its top
action `Ḡ` (on the `m_b` blocks of the top partition) is primitive. Let `(z, w, X)` be its
top level and `p = X − z` (the lower mass, `p = log` of the block size). Every leaf `L` of a
nested call is the restriction of a subgroup of `G` to a subset of `Ω` (Lemma 7.1), so by
Lemma 6.2(b),(c) its levels other than those coming from the top level of `T` are bounded
by the lower levels of `ν`. A *leaf bound* bounds the terms `T'(L)` of the remaining (at most
two, after the leaf's own extension) levels of `L` and gives `X_L ≤ X − s`; then

    D(L) ≥ T(z, w, X) − T'(L) + E(X) − E(X − s) − s.                               (9.1)

### 9.1 Brute force, giants

`|G| ≤ 5040` (brute force) and `|G| ≥ n!/2` (`trivial_case`) make no nested calls; only
(8.2a) is needed.

### 9.2 Strong Luks reduction (`strong_luks`, `main.py:436-460`)

Entered when `|Ḡ| < m_b^{1 + ⌊log m_b⌋}` (small quotient), when `Ḡ` is not recognised
(then `m_b ≥ 25` and `|Ḡ| < m_b^{2+⌊log m_b⌋}`, or `m_b < 25` and `|Ḡ| ≤ m_b!`; the
fallback for `m_b ≥ 25` above the cap is unreachable, CORRECTNESS.md Theorem B), or when
`Ḡ` is a Johnson group on `Γ` with `|Γ| = m_Γ < ℓ(n)` (then `|Ḡ| ≤ m_Γ!`). One group of
`N ≤ |Ḡ|` calls `iso(N, x, y^{σ⁻¹})` on the kernel `N` of the action on the blocks. `N`
fixes every block, so every leaf lies inside one block: its tower is the restriction of the
lower levels, `T'(L) = 0`, `X_L ≤ p = X − z`, and

    D_Luks = T(z, w, X) + E(X) − E(X − z) − z.

### 9.3 Cameron groups (`cameron_reduction`, `main.py:462-495`)

`Ḡ` is recognised as a Cameron group `(A_k^{(t)})^s ≤ Ḡ ≤ S_k^{(t)} wr S_s` on
`m_b = c^s` points, `c = binom(k, t)`, `s ≥ 2` (Babai Def. 3.2.2; `johnson.recognize_cameron`
verifies the product structure: the coordinates, the kernel `N̄` of the action on them, and
that `N̄` acts on the fibres of a coordinate as a Johnson group). One group of
`N ≤ |Ḡ : N̄| = |P|` calls `iso(NG, ·)`, `P ≤ Sym(s)` the group induced on the coordinates.

**Lemma 9.1.** (a) `s ≤ k`, `c ≥ 10`, and `log |P| ≤ log s! ≤ z`. (b) Every leaf `L` of a
call on `NG` has `T'(L) ≤ T(z, w, X) − min(2C(z − 1), (3/4) C z²)`.

*Proof.* (a) The reduction is entered only if `|Ḡ| ≥ m_b^{1+⌊log m_b⌋} > 2^{log² m_b}`
(`main.py:312-315`) and `|Ḡ| ≤ (k!)^s s!`, with `log m_b = s log c` and `c ≥ k`. So
`s² log² c < s log k! + log s! ≤ s k log k + s log s`, i.e. `s log² k < k log k + log s`.
If `s > k` this gives `s log k (log k − 1) < log s < s`, so `log k < 1.62` and `k ≤ 3`; for
`k = 3`, `2.51 s < 4.76 + log s` forces `s ≤ 2 < k`. So `s ≤ k`. For `t = 1`, `c = k` and
`2 log² k < log k! + 1` fails for `k ≤ 9`, so `c = k ≥ 10`; for `t ≥ 2`, `c ≥ binom(5, 2)`.
Finally `log s! ≤ s log s ≤ s log k ≤ s log c = z`. (b) `NG` acts on the top blocks as
`N̄ ≤ ∏_i Sym(Δ_i)` and preserves each coordinate. Let `H ≤ NG` be the subgroup of which
`L` is the restriction and `𝒯` the set of top blocks met by `O_L`, an `H`-orbit. The
coordinate maps `π_i : 𝒯 → Δ_i` are `H`-equivariant. If the top action of `L` is
primitive, each `π_i` is constant or injective on `𝒯`, so `|𝒯| ≤ c` and
`T'(L) ≤ T(z, w, X) − C(z² − (z/s)²) ≤ T(z, w, X) − (3/4)Cz²` (monotonicity, `w_L ≤ w`,
`X_L ≤ X`). If it is imprimitive, the leaf's `_solve` splits it into two levels with
`z₁ + z₂ ≤ z`, `z₁, z₂ ≥ 1`, and Lemma 6.2(c) gives `C(z² − z₁² − z₂²) ≥ 2C(z − 1)`. If
`|𝒯| = 1` the top level vanishes. ∎

So `D_Cam ≥ min(2C(z − 1), (3/4)Cz²)` with `z = log m_b ≥ log 100`.

### 9.4 The Johnson case

Here `Ḡ` is a Johnson group `S^{(t)}(Γ) ≥ Ḡ ≥ A^{(t)}(Γ)` acting on the `binom(m, t)`
standard blocks, `m = |Γ| ≥ ℓ(n) = 10k`, `k = k_paper(n) = max(9, ⌊X⌋ + 3)`, `t ≤ m/2`
(`johnson.py`), so `y := log m ≥ log 90`, `z = log binom(m, t)`, and by Lemma 5.1(b),(d)
`μ(Ḡ) = m` and `w = y`. For `t ≥ 2`, `z ≥ log binom(m, 2) ≥ 2y − 1.017`. The node is
*primitive* (`p = 0`, then `t ≥ 2`: a primitive `t = 1` group is a giant, §9.1) or
*imprimitive* (`p ≥ 1`).

`φ : G → Sym(Γ)` is the giant representation. A *structure* `S` on `Γ` (`structure.py`)
has cells with keys; a *class* is the union of the cells with one key; a Johnson cell
`J` carries `J(m', t')`, `t' ≥ 2`, `m' ≥ 2t' + 1`, and `Aut(S)` acts on it through
`Sym(m')`. `branch` (`main.py:620-687`) computes `S` for `x` and for every choice
sequence for `y` and calls, for each aligned run, `iso(G₁, x, y₁)` with
`G₁ = φ⁻¹(Aut(S_x) ∩ φ(G))` (or `top_action` in case 2a).

**Lemma 9.2 (Babai Lemma 5.2.1, Prop. 5.2.3).** Colour each `t`-subset `T` of `Γ` by
`(|T ∩ Δ_j|)_j` for a partition of `Γ` into classes `Δ_j`. Every colour class other than the
classes `binom(Δ_j, t)` has at most `(2/3) binom(m, t)` elements (`t ≤ m/2`), and
`|binom(Δ_j, t)| ≤ (|Δ_j|/m)^t binom(m, t)`. Every orbit of `Aut(S)` on `binom(Γ, t)` lies
in one colour class. (Cited; the last sentence because `Aut(S)` preserves every class.)

**Kinds of structures.** By CORRECTNESS.md §12 (including the case-2b exit for tied colours of valency 1,
CORRECTNESS.md §9.2.1) every structure passed to the recursion is of one of the kinds

* **C**: every class has at most `(2/3)m` points;
* **E**: one class `Δ` with `|Δ| > (2/3)m` consists of `c ≥ 2` cells of size `s ≥ 2`; the
  other classes have fewer than `m/3` points;
* **J**: one class is a Johnson cell `J` with `|J| > (2/3)m`; the other classes have fewer
  than `m/3` points;
* **P** (primitive `t ≥ 2` only, the twin pullback): `{C₀, Γ∖C₀}`, `|C₀| > m/2`, and `x` is
  constant on `binom(C₀, t)`;
* **A** (case 2a): `{Φ, Γ∖Φ}`, `|Φ| > m/2`, handled by `top_action`.

In kinds C, E, J, `μ(Aut(S)) ≤ (2/3)m` (Lemma 5.1(c): a class of `c` cells of size `s`
contributes `max(4, s, c) ≤` its size, a Johnson cell `m' ≤ 1/2 + √(2m + 1/4) < (2/3)m`
since `binom(m', 2) ≤ |J| ≤ m`), and in kind E even `≤ m/2` on `Δ`.

**Lemma 9.3 (leaf bounds of the branch).** Let `L` be a leaf of a call `iso(G₁, x, y₁)`,
`𝒯` the set of top blocks met by `O_L` (an orbit of a subgroup of `Aut(S) ∩ φ(G)`), and
`(z_L, w_L)` the data of the top level of `L` (before its own extension). Then
`X_L ≤ X − (z − z_L)` and, with `ω_J(y) = y/2 + 0.61 ≥ log(1/2 + √(2m + 1/4))`:

* (C) if `𝒯` lies in a colour class of size `≤ (2/3) binom(m, t)`: `z_L ≤ z − δ`,
  `w_L ≤ y − δ`;
* (E, `t = 1`, `𝒯 ⊆ Δ`): either `z_L ≤ y − 1`, or the top action of `L` is imprimitive and
  its extension has two levels `z₁, z₂ ≥ 1` with `z₁ + z₂ = z_L ≤ y`, `w_i ≤ z_i`;
* (E, `t ≥ 2`, `𝒯 ⊆ binom(Δ, t)`): `z_L ≤ z`, `w_L ≤ y − 1`;
* (J, `𝒯 ⊆ binom(J, t)`): `z_L ≤ z`, `w_L ≤ ω_J(y)`;
* (P): `𝒯 ⊆ binom(C₀, t)` gives no leaf (the string is constant there, so the nested call
  returns at its first line); otherwise `z_L ≤ z − δ`, `w_L ≤ y`;

and every `𝒯` of kinds C, E, J not covered by the second to fourth items is in the first.

*Proof.* `|O_L| ≤ |𝒯| 2^p` gives `X_L ≤ X − (z − z_L)`. `w_L ≤ log μ` of the group induced
on `𝒯`, a section of `Aut(S)` (Lemma 5.1(a)). (C): Lemma 9.2 and `μ(Aut(S)) ≤ (2/3)m`.
(E, `t = 1`): `Aut(S)` permutes the cells of `Δ`, so the sets `cell ∩ 𝒯` form an invariant
partition of `𝒯` with parts of equal size; if there is one part, `|𝒯| ≤ s ≤ m/2`; if the
parts are points, `|𝒯| ≤ c ≤ m/2`; otherwise it is a block system and the top action is
imprimitive, and `_solve` of `L` splits it (Lemma 6.2(c)). (E, `t ≥ 2`) and (J): `μ ≤ m/2`
on `Δ`, `μ ≤ m'` on `J`. (P): `Aut(S) = Sym(C₀) × Sym(Γ∖C₀)` and Lemma 9.2. The other
classes of kinds E and J have fewer than `m/3 ≤ (2/3)m` points, so their `t`-sets fall
under (C) by Lemma 9.2. ∎

**The drops.** Write `σ(X, y)` for the bound of §10 on the log of the number of runs. By
Lemma 9.3, (9.1) and Lemma 6.1 the branch has the following drops, in which `t = 1`
(`z = y`) is the worst case of kinds C and E/J with `t ≥ 2` reduce to the primitive `t = 2`
case (Lemma 11.5):

    D_C  = F(y, y, X) − F(y − δ, y − δ, X − δ) + φ(y) − φ(y − δ) + C(2yδ − δ²) + E(X) − E(X − δ) − δ,
    D_E  = (y − 1)(3Ay + 2BX + B) + φ(y) − φ(y − 1) − φ(1) + 2C(y − 1)               (t = 1, split),
    D_E2 = F(z, y, X) − F(z, y − 1, X) + z(ρ(y) − ρ(y − 1))                           (t ≥ 2),
    D_J  = F(y, y, X) − F(y, ω, X) + y(ρ(y) − ρ(ω)),   ω = ω_J(y)                     (t = 1),
    D_P  ≥ C(2zδ − δ²),

and kind A (§9.5) and the E-subcase `z_L ≤ y − 1` have drops `≥ D_C`.

*Derivation.* (C) The leaf's top terms are at most `T(y − δ, y − δ, X − δ)` (`z_L ≤ y − δ`,
`w_L ≤ y − δ`, `X_L ≤ X − δ`; for a split use (6.1)); `T(y, y, X) − T(y − δ, y − δ, X − δ)`
gives the first four terms and `X_L ≤ X − δ` the last two. For `t ≥ 2` the same bound with `z`
in place of the first `y` is larger (Lemma 11.5). (E, split) With `s = z₁ + z₂ = z_L`,
`u = y − s`, `Y = X − u`, (6.2) gives
`T(y,y,X) − T'(L) ≥ A(y³ − s³) + B(y²X − s²(X − u)) + z₁z₂(3As + 2B(X − u) + Bz₂)
+ φ(y) − φ(z₁) − φ(z₂) + C(y² − z₁² − z₂²)`, using `z_iρ(w_i) ≤ φ(z_i)`. Since `z₂ ≥ 1`,
`z₁z₂ B z₂ ≥ B z₁z₂`; the remaining dependence on the split,
`z₁z₂(3As + 2B(X − u) + B) − φ(z₁) − φ(z₂) − C(z₁² + z₂²)`, is concave in `z₁` (φ convex),
so it is smallest at `z₁ ∈ {1, s − 1}`. With that choice the bound `h(s)` (plus
`E(X) − E(X − u) − u`) has derivative
`−(3A + B)(s − 1)² − 2B(X − u)(s − 1) − φ'(s − 1) − 2C(s − 1) + 1 − e(X − u) ≤ 0` in `s`
(`u = y − s`), so it is smallest at `s = y`, `u = 0`, which is `D_E`. (E, `z_L ≤ y − 1`)
This is the C-bound with `δ` replaced by 1, and every term of `D_C` is nondecreasing in the
shrink `δ` (for `C(2yδ − δ²)` because `δ ≤ y`, for the `E` terms because `e ≥ 1`).
(E, `t ≥ 2`; J) Only `w` decreases: `F(z, y, X) − F(z, w_L, X) + z(ρ(y) − ρ(w_L))`, with
`w_L ≤ y − 1`, resp. `w_L ≤ ω` and `z = y` for `t = 1`. (P) Only the `C`-term is used. ∎

### 9.5 Case 2a and `top_action` (`main.py:815-902`)

`proc` makes no choice (`s = 1`). For each aligned run `top_action` makes at most five
`iso_window` calls: at most four on `Ω(Φ)` with the group `K = ker(G₁ → Sym(Φ))`, which fixes
every standard block `B_T`, `T ⊆ Φ`, so every leaf lies in one block (drop `≥ D_Luks`-type,
`≥ T(z, y, X)`); and one on `Ω ∖ Ω(Φ)` with `Aut_top`, whose orbits on `binom(Γ, t)` lie in
colour classes `|T ∩ Φ| = j < t` of size `≤ (2/3) binom(m, t)` (Lemma 9.2; for `t = 1`,
`|Γ∖Φ| < m/2`), so the leaves satisfy (C) with `w_L ≤ y` and the drop is
`≥ C(2zδ − δ²)`.

### 9.6 Local certificates and their comparison

`aggregate` (`main.py:744-812`) computes the certificates of all `M = binom(m, k)` test sets
`A` of `x` (and of `y`); one certificate makes at most `n · k!` calls `iso_window(N, x, x', W)`
(`certificates.py:271-339`: at most `n` iterations, `W` grows strictly; at most `k!` lifts per
iteration), where `N = ker(H → Sym(A))` for the current `H ≤ G_A ≤ G` with `H^A ⊇ Alt(A)`,
and `W = W_new` consists of points affected by `H` (`W_old` points are affected by the
smaller current group too). In case 3, `case_3` makes at most `4M²` calls of `compare`,
each with at most `(n + 1) k!` calls `iso_window(it.N, x_A, y', W_new)` on the same windows
and groups as a certificate trajectory, with letters of size `λ + 2`
(`certificates.py:347-402`).

**Lemma 9.4 (Affected Orbit Lemma, Babai Cor. 8.3.7; cited).** If `φ_A : H → Sym(A)` is a
giant representation, `|A| = k ≥ 5`, every orbit of `ker φ_A` contained in an affected
`H`-orbit has length at most `n/k`.

**Lemma 9.5 (drop of a shrinking window).** Let `H ≤ G` and let every leaf `L` of a call on
a group `≤ H` satisfy `|O_L| ≤ 2^{X − ℓ}`, `0 ≤ ℓ ≤ w`. Then
`T'(L) ≤ T(z, w, X) − (B/2) w² ℓ`.

*Proof.* Let `z_L ≤ z` and `p_L ≤ p` be the top ratio and lower mass of `L`, `u = z − z_L`,
`v = p − p_L`, `u + v ≥ ℓ`. Writing `F(z, w, z + p) = A w² z + B w z p + (B/2) w z (z + w)`,
`F(z, w, X) − F(z_L, w, X_L) ≥ A w² u + B w z_L v`. If `z_L ≥ w`, this is `≥ B w² ℓ`; if
`w/2 ≤ z_L < w`, `≥ (B/2) w² ℓ`; if `z_L < w/2`, `u ≥ w/2` and it is
`≥ A w³/2 ≥ (B/2) w² ℓ` (`A ≥ B`, `ℓ ≤ w`). A split top (Lemma 6.2(c)) and `w_L ≤ w` only
decrease `T'(L)`. ∎

With Lemma 9.4, `ℓ = log k` and `w = y` (`log k < y`), the certificate calls and the
comparison calls have the drop

    D_cert = (B/2) y² log k + E(X) − E(X − log k) − log k.

## 10. The multiplicities

* **Luks** (§9.2): `log N < z(1 + z)` (small quotient), `< z(2 + z)` (unrecognised,
  `m_b ≥ 25`), `≤ log m_b!` (`m_b < 25`), `≤ log m_Γ!` (small `Γ`, `6 ≤ m_Γ ≤ 10k − 1`;
  `m_Γ ≥ 6` because a Johnson group on fewer points is a small quotient).
* **Cameron**: `log N ≤ z` (Lemma 9.1).
* **Certificates**: `N ≤ 2M(n + 1)k! ≤ 2^{k y + X + 2}` (`M k! ≤ m^k`).
* **Comparisons**: `N ≤ 4M²(n + 1)k! ≤ 2^{2ky − log k! + X + 3}`, letter factor 9.
* **Branch**: `N ≤ 2^{σ(X, y)}` runs, one call each (five in case 2a, where `s = 1`), with

      σ(X, y) = (k − 2) y + β y² + R(y)  ≤  (X + 1) y + β y² + R(y)     (X ≥ 6).

  *Proof.* The number of runs is the product of the candidate counts of the choices of one
  run of `proc` (`docs/bounds/main.md`, Lemma R). Case 3: the Extended Design Lemma on the
  `k`-ary structure, `log s ≤ (k − 2) y + max(y, β y² + R(y))` (`docs/bounds/soj.md`,
  "Choice count of `extended_design_lemma`" with Theorem B). Case 2b: at most four
  individualised points, then the orbital configuration: a tie in `select_min` among at most
  `m` colours, or `upcc_split_or_johnson` with `log s ≤ β y² + R(y) + 2y` (Theorem B with the
  case-2b tie term; `|pts| ≥ m/2 − 4 ≥ 41` and the hypothesis `|V| ≥ 61` of Theorem B is
  used there only through `bound ≥ 6`, `n1_orig ≥ 6` and the final simplification at
  `Y = log m ≥ log 90`), or the cycle structure (two choices); in all cases
  `log s ≤ 6y + β y² + R(y) ≤ σ` since `k − 2 ≥ 7`. Primitive `t ≥ 2`: the Extended Design
  Lemma on the `t`-ary hypergraph, `(t − 2) y + max(y, βy² + R(y)) ≤ σ` because
  `t ≤ X ≤ ⌊X⌋ + 1`. Pullback, case 1, case 2a: no choice. ∎

## 11. Verification of the inequalities (8.2b)

The groups of calls and the required inequalities (with `log g + 2 ≤ 4`) are:

| node | group | requirement |
|---|---|---|
| Luks | `N` calls | `D_Luks ≥ log N + 2` |
| Cameron | `N` calls | `D_Cam ≥ log N + 2` |
| Johnson, imprimitive | certificates | `D_cert ≥ k y + X + 2 + 4` |
| | comparisons | `D_cert ≥ 2ky − log k! + X + 3 + 4 + log 9` |
| | branch | `D_kind ≥ σ(X, y) + 4` for the kinds C, E, J; `≥ log 5 + 4` for P, A |
| Johnson, primitive | branch | `D_kind ≥ σ(X, y) + 4` |

`timebound.py` checks each reduced inequality below as `P − N ≥ 0` with `P`, `N`
nondecreasing on the domain: on `[a, b]` the value `P(a) − N(b)` is a lower bound, computed
with exact interval arithmetic and bisected until positive, up to `y = 2^{10}`, resp.
`X = 2^{12}`; beyond that by Lemma 11.2. All logarithms of rationals are enclosed by
convergent series with remainder bounds (`interval.py`), and `π²` by Machin's formula.

**Lemma 11.2 (dominance).** If `f(x) ≥ Σ_i c_i x^{p_i} log^{q_i} x` for `x ≥ x₁ ≥ 4`, the
term `d` with the lexicographically largest `(p, q)` has `c_d > 0`, all other `(p_i, q_i)` are
smaller, and `q_i − q_d ≤ (p_d − p_i) ln x₁` whenever `p_i < p_d`, then every ratio
`r_i = x^{p_i − p_d} log^{q_i − q_d} x` is nonincreasing on `[x₁, ∞)`, and
`f(x) ≥ x^{p_d} log^{q_d} x · (c_d + Σ_{c_i < 0} c_i r_i(x₁))`, which is `≥ 0` if the
bracket is.

*Proof.* `(d/dx) ln r_i = ((p_i − p_d) + (q_i − q_d)/ln x)/x ≤ 0` under the hypotheses. ∎

**Lemma 11.3 (kind C).** For `X ≥ y + 1`, `y ≥ log 90`:
`D_C − σ(X, y) − 4 ≥ [φ(y) − φ(y − δ) − R(y) − C₁ y − q₁] + [E(X) − E(X − δ) − δ − δX/2 − q₂]`
with `C₁ = 1 + δ(β + 1/2) − 2Cδ = 1.0975653...` and any `q₁ + q₂ ≥ 4 + Cδ² − b*δ³ =
4.1520665...`.

*Proof.* `F(q, q, Y) = Aq³ + Bq²Y` gives
`F(y, y, X) − F(y − δ, y − δ, X − δ) = A(3y²δ − 3yδ² + δ³) + B(y²δ + 2yδX − 2yδ² − δ²X + δ³)`.
With `2Bδ = 1`, `(3A + B)δ = β`, `σ ≤ (X + 1)y + βy² + R(y)`, the terms `yX` and `βy²` cancel,
`−(3A + 2B)δ² = −δ(β + 1/2)`, and `Bδ² X = δX/2`. ∎

(Q1) `φ(y) − φ(y − δ) ≥ R(y) + C₁ y + 2.1` for `y ≥ log 90` and (Q2)
`δ e(X − δ) ≥ δ + δX/2 + 2.1` for `X ≥ log 90 + 1` (Lemma 4.1) are checked; `2.1 + 2.1 ≥
4.153`.

**Lemma 11.4 (kind E, `t = 1`).** `D_E − σ(X, y) − 4` is increasing in `X` (its
`X`-coefficient is `2B(y − 1) − y > 0`), and at `X = y + 1` it is at least
`(3A + 2B − 1 − β) y² + (−3A + B + 2C − 2) y − 3B − 2C + φ'(y − 1) − ρ(1) − R(y) − 4`, using
`φ(y) − φ(y − 1) ≥ φ'(y − 1)`. (Q3) checks that this is `≥ 0` for `y ≥ log 90`.

**Lemma 11.5 (`t ≥ 2`).** (a) `D_C` with `z` in place of the first argument is
nondecreasing in `z` (its `z`-derivative is
`A(y² − (y − δ)²) + Bδ(X − z) + (B/2)(y² − (y − δ)²) + ρ(y) − ρ(y − δ) + 2Cδ ≥ 0`), so kind C
with `t ≥ 2` follows from Lemma 11.3 (`X ≥ z ≥ 2y − 1.017 ≥ y + 1`). (b) For kind E and J
with `t ≥ 2`, `D_E2 ≤ D` (`ω ≤ y − 1`) and
`D_E2 − σ − 4 ≥ z[(A + B/2)(2y − 1) + B(X − z/2)] + z(ρ(y) − ρ(y − 1)) − (X + 1)y − βy² − R(y) − 4`,
which is increasing in `X` (coefficient `Bz − y > 0`) and, at `X = z`, in `z` (derivative
`(A + B/2)(2y − 1) + Bz + ρ(y) − ρ(y − 1) − y > 0`). (Q4) checks it at
`X = z ∈ [2y − 1.017, 2y − 1]` (the increasing parts at `z = 2y − 1.017`, the decreasing part
`−(z + 1)y` at `z = 2y − 1`).

**Lemma 11.6 (kind J, `t = 1`).** `D_J − σ − 4` has `X`-coefficient `By(y − ω) − y > 0`;
(Q5) checks it at `X = y + 1` with `ω = y/2 + 0.61` (`ρ(y) − ρ(ω)` is nondecreasing since
`ρ'` is and `ω' = 1/2`).

**Lemma 11.7 (certificates and comparisons).** Minimising over `y`,
`(B/2) y² log k − k y ≥ −k²/(2B log k)` and `(B/2) y² log k − 2k y ≥ −2k²/(B log k)`. So it
suffices that, with `l_k = log k`, (Q6) `l_k e(X − l_k) ≥ k²/(2B l_k) + X + l_k + 6` and
(Q7) `l_k e(X − l_k) ≥ 2k²/(B l_k) − log k! + X + l_k + 7 + log 9` for `X ≥ log 90 + 1`
(`E(X) − E(X − l_k) ≥ l_k e(X − l_k)`); `k = ⌊X⌋ + 3` is constant between integers. For the
tail, `k ∈ [X + 2, X + 3]`, `log k! ≥ k log k − k/ln 2`, `log(X − l_k + 4) ≤ log X + 4/(X ln 2)`
and `1/(l + ε)² ≥ 1/l² − 2ε/l³` give a monomial lower bound with leading term
`(3 − 2/B) X²/log X > 0`.

**Lemma 11.8 (Luks).** `T(z, w, X) ≥ 2z² + (A + B/2 + ρ(1)) z` for `X ≥ z ≥ 1`, `w ≥ 1`
(`F(z, w, X) ≥ z(A + B/2) w²` because `X ≥ z`). This is `≥ z(1 + z) + 2` and
`≥ z(2 + z) + 2` for `z ≥ log 25`, so the small-quotient and unrecognised cases with
`m_b ≥ 25` hold (`E(X) − E(X − z) − z ≥ 0`). (Q9) checks `2z² + (A + B/2 + ρ(1))z ≥
log m! + 4` for `2 ≤ m ≤ 24`, `z = log m`.

**Lemma 11.9 (small `Γ`).** `D_Luks − log m_Γ! − 2 ≥ 0` for `6 ≤ m_Γ ≤ 10k − 1`. The
left side is increasing in `z` (for fixed `X`) and in `X`, so it suffices to take `z = g =
log m_Γ` and the smallest `X` with `X ≥ g` and `10k(X) − 1 ≥ m_Γ`. (Q8) checks
`T(g, g, X) + g e(X − g) − g − log m_Γ! − 4 ≥ 0` there, for every `m_Γ ≤ 4096` and on blocks
of consecutive values up to `2^{17}` (with Robbins' upper bound for `log m!`); for
`m_Γ > 2^{17}`, `T ≥ B g² X ≥ B g² (m_Γ/10 − 3)` and `log m_Γ! ≤ m_Γ g` give
`m_Γ g (Bg/10 − 1) − 3Bg² − g − 4 ≥ 0.45 g⁴ − 3Bg² − g − 4 > 0`.

**Cameron.** `min(2C(z − 1), (3/4)Cz²) ≥ z + 2` for `z ≥ 2`.

**Kinds P and A.** `C(2zδ − δ²) ≥ 2(2 · 12 · δ − δ²) > 26 > log 5 + 4` (`z ≥ 2y − 1.017 ≥
12`, resp. `≥ y ≥ log 90` for case 2a, where the drop of the `Ω(Φ)` calls is
`≥ T(z, y, X)`).

## 12. Part III: the own work, and condition (8.2a)

`docs/bounds/ownwork.md` substitutes the per-function bounds of `docs/bounds/` into the own
work of every node type. Its starting point is `docs/bounds/main.md` §3, which lists for each
node type the operations executed outside nested `Solver.iso` calls; ownwork.md §2 checks that
list against the code statement by statement and adds the items it missed (C1–C9). Its
summary table (§0) gives `W(node) ≤ λ^e 2^ω`; the bounds used here are:

* `W_iso(n) ≤ 276 n²`, `P_cr(n) ≤ 23138 n⁶`, brute force `≤ 14164n⁵ + 1123944n² + 921385n +
  4894264`, hence `P_iso(n) = 2n(P_cr + W_iso + W_bf) ≤ 13954342 n⁷ ≤ 2^{7X + 23.74}`;
* strong Luks `≤ λ(1600n⁷ + 444310n⁵ + 1790 q n³)`, Cameron `≤ λ(1600n⁷ + 518132n⁵ + 1898 I n³)`;
* the Johnson nodes: the terms of ownwork.md §8.6–§8.14 (entry, `aggregate`, the certificate
  wrappers, cases 1, 2a, 2b, 3, the comparison wrappers, the branch template with its `s⁴`
  term from `_covered`, and the Extended Design Lemma / Split-or-Johnson runs).

**Condition (8.2a).** `W_tot(ν) = W(ν) + Σ_c P_iso(n_c) ≤ λ² 2^{Φ(ν) − 1}` is checked by
`timebound.check_own_work`:

* **(W1)** Brute force and giants have no nested calls and `log(W/λ) ≤ 22.73 + 5X`; strong Luks
  has `log(W_tot/λ) ≤ log q + 23.79 + 7X` and Cameron `≤ log I + 23.79 + 7X`. Since
  `Φ ≥ T(z, w, X) + E(X)`, `T ≥ log q + 2` (Lemma 11.8, (Q9)) resp. `T ≥ 2z² ≥ log I + 1`
  (Lemma 9.1), and `E(X) ≥ 5.5X² + 60X ≥ 7X + 24.79` for `X ≥ 1`, the condition holds. For a
  Johnson quotient on `m_Γ < ℓ(n)` points, **(W4)** checks
  `T(g, g, X) + 5.5X² + 60X ≥ log m_Γ! + 23.79 + 7X + 1` at the smallest admissible `X`, as in
  Lemma 11.9 (exactly up to `m_Γ = 4096`, on blocks up to `2^{17}`; beyond, `T ≥ Bg²X`).
* **(W2)** Imprimitive Johnson node. Every term of ownwork.md §8.14, and `P_iso` times the
  number of nested calls, is bounded with `log M ≤ ky ≤ Xy + 3y`, `log k! ≤ (X + 3) log(X + 3)`,
  `log s ≤ σ ≤ Xy + y + βy² + R(y)`, `t ≤ X`, by a combination with nonnegative coefficients of
  `Xy, y², R(y), y log y, y, log(y + 2), X, (X + 3)log(X + 3), 1`; a log-sum of `r` terms by the
  coefficientwise maximum plus `log r`. The result is

      log(W_tot/λ²) + 1 ≤ 5Xy + 14.67y² + 4R(y) + 2y log y + 9y + 4 log(y + 2) + 8X
                          + 2(X + 3)log(X + 3) + 33.91.

  Against `Φ ≥ T(y, y, X) + E(X) = Ay³ + By²X + yρ(y) + 2y² + E(X)` (`z ≥ y`): the `Xy` terms
  compare as `5 ≤ B log 90 = 5.549`, and the `y`-terms and the `X`-terms are checked
  separately (each `≥ 0`).
* **(W3)** Primitive Johnson node, the same way:
  `log(W_tot/λ²) + 1 ≤ 4Xy + 14.67y² + 4R(y) + 2y log y + 8y + 4 log(y + 2) + 7X + 28.06`,
  against `Φ ≥ T(X, y, X) + E(X)` with `X ≥ 2y − 1.017`. The difference is nondecreasing in `X`
  (checked: `Ay² + B(2y − 1.017)y + 60 ≥ 4y + 7`), and it is checked at `X = 2y − 1.017`.

**What Part III takes from the per-module documents.** The bounds rest on (ownwork.md §9): returning runs
(no fallback is reached; CORRECTNESS.md Theorem B); the correctness of the group algorithms,
used for the counts `I ≤ q` and `I ≤ s_c!` (CORRECTNESS.md §3); the determinism of `proc`
(main.md Lemma R; CORRECTNESS.md §6); the Cameron–Solomon–Turull bound on the number of
generators kept by Schreier–Sims (cited, group.md Lemma G); and the coherence of the WL
outputs (CORRECTNESS.md §7). The items that ownwork.md §9 gives only in outline are proved in
`docs/bounds/ownwork_gaps.md`, with no change of any bound used above: soj.md's run analysis
and Theorems A, B hold for `|V| ≥ 42`, which covers case 2b (`|pts| ≥ 42`); the lower-order
groups of the Split-or-Johnson run sum to at most `3.7·10⁻⁵ · 2^{U(y)}` (`0.03` is used); the
polynomial parts of the certificate and `aggregate` bounds give the stated coefficients; the
chosen objects of a run have height at most `log m/δ + 2`; and `|lifts| ≤ k!` follows from the
code, assuming only that `φ` is a homomorphism (CORRECTNESS.md Lemmas 3.3, 4.4, 4.5).

## 13. The bounds

### 13.1 String Isomorphism (Theorem A)

`string_isomorphism(G, x, y)` normalises the letters (`canon.normalize_letters`; for integer
letters at most `180 + 452n + 16n⌈log 2n⌉` operations, group.md §8; for other letters the bound
of group.md, linear in the total size of the letters up to a logarithmic factor) and calls
`iso(G, x', y', trivial tower)` with integer letters, `λ = 1`. For `n = 1` the call returns at
its first line: at most `180 + 452 + 16 + 276 ≤ 2^{10}` operations. For `n ≥ 2`, Lemma 7.1 and
Theorem 8.1 give

    ops ≤ W_norm(n) + P_iso(n) + 2 Σ_L 2^{Φ_ext(L)},

the leaves `L` being transitive constituents of subgroups of `G` with the trivial tower, which
has one level with `z_L = X_L` and `w_L ≤ X_L`; so `Φ_ext(L) ≤ T(X_L, X_L, X_L) + E(X_L)` and, by
Lemma 7.2 with the monotonicity of `T`, `Σ_L 2^{Φ_ext(L)} ≤ 2^{T(X, X, X) + E(X)}`. Here
`T(X, X, X) = (A + B)X³ + Xρ(X) + 2X²` and `W_norm + P_iso ≤ 2^{7X + 24.8} ≤ 2^{E(X)}`. Hence

    ops ≤ 2^{U(X)},   U(X) = b* X³ + X ρ(X) + 2X² + E(X) + U₀,   U₀ = 10.

### 13.2 Graph Isomorphism (Theorem B)

`graph_isomorphism(edges1, v, edges2, v)` (without vertex colours) builds `G = S^{(2)}(V)`
on `N = binom(v, 2)` points (`GraphInstance`), the two 0/1 strings, and calls `iso` once
(main.md, `graph.graph_isomorphism`): its own work, with the callees of `GraphInstance`
substituted (johnson_certs.md, group.md tables), is at most

    1890 + 288L + 863N + 16N⌈log 2N⌉ + 218v + 10v² ≤ 288L + (1031 + 16V) v²   (v ≥ 2),

`L` the length of the longer edge list, `V = log v`. For `v ≥ 3` the root state is transitive
with one level, `z = X = log N ≤ 2V − 1` and `w = log min(N, μ(Sym(v))) ≤ V` (`μ(Sym(v)) = v`
for `v ≥ 5`, `μ = 4` and `min(N, 4) ≤ v` for `v = 3, 4`). With `W_iso(N) ≤ 276N²` and
Theorem 8.1,

    ops ≤ 288L + (1031 + 16V)v² + 69v⁴ + 2^{T(X, V, X) + E(X) + 1} ≤ 288L + 2^{U_GI(V)},
    U_GI(V) = T(2V − 1, V, 2V − 1) + E(2V − 1) + U₀,

because `T(z, w, z)` and `E` are nondecreasing in `z` and the polynomial terms are at most
`2^{E(2V − 1)}`; for `v = 2` the call returns at its first line. The leading term of `U_GI` is
`F(2V, V, 2V) = (2A + 3B) V³`.

### 13.3 The constants `a(b)`

For `b > b*` the smallest `a` with `2^{U(log₂ n)} ≤ a · 2^{b log₂³ n}` for every integer `n ≥ 1` is

    a(b) = 2^{M(b)},     M(b) = max_{n ≥ 1} f(log₂ n),     f(x) = U(x) − b x³,

and for graphs (`b > 2A + 3B`) the same with `U_GI` and `v ≥ 2` in place of `U` and `n ≥ 1`.
The maximum exists by Lemma 13.1. `timebound.log2_a_bracket` computes exact rationals
`lo ≤ M(b) ≤ hi` by Lemmas 13.1–13.4; the table lists them.

**Lemma 13.1 (tail).** For each `b` of the table there is `x₁ ≥ 16` with `f(x) ≤ 0` for all
`x ≥ x₁`; since `f(0) = U(0) = 10 > 0` (resp. `lo > 0` for graphs), the maximum is attained at
some `n < 2^{x₁}`.

*Proof.* Strings: `E(x) ≤ x e(x) ≤ 3x³/log²x + 11x² + 60x` (Lemma 4.1 and `log(x + 4) ≥ log x`),
so `bx³ − U(x) ≥ (b − b*)x³ − 3x³/log²x − 5x² log²x − 3x² log x − 25x² − 60x − 10`. Graphs: by
Lemma 13.3 `U_GI(x) ≤ (2A + 3B)x³ + Zρ(x) + 2Z² + E(Z) + 10` with `Z = 2x − 1 ≤ 2x`, and
`Zρ(x) ≤ 10x² log²x + 6x² log x + 24x²`, `2Z² ≤ 8x²`,
`E(Z) ≤ Z e(Z) ≤ 24x³/log²x + 44x² + 120x`. In both cases Lemma 11.2 applies to the right-hand
side from `x₁`, the first power of 2 from 16 on for which its bracket is nonnegative
(`timebound._excess_tail`, `_tail_start`). ∎

**Lemma 13.2.** `e` is convex on `[0, ∞)`. Hence for `0 ≤ p < q`,

    (q − p) e((p + q)/2)  ≤  ∫_p^q e  ≤  (q − p)(e(p) + e(q))/2.

*Proof.* `e(u) = 3 (ln 2)² h(u) + 11u + 60` with `h(u) = u²/ℓ²`, `ℓ = ln(u + 4)`. With `s = u + 4`,
`h' = 2u/ℓ² − 2u²/(sℓ³)` and

    h'' = 2/ℓ² − 8u/(sℓ³) + 2u²/(s²ℓ³) + 6u²/(s²ℓ⁴) = 2Q/(s²ℓ⁴),   Q = s²ℓ² − (4us − u²)ℓ + 3u².

As a quadratic in `ℓ`, `Q` has discriminant `u²((4s − u)² − 12s²)`, which is `≤ 0` iff
`3u + 16 = 4s − u ≤ 2√3 s`, i.e. `u ≥ (16 − 8√3)/(2√3 − 3) = 8/√3`. For `0 ≤ u ≤ 8/√3`:
`8/√3 ≤ 4.62` (`64/3 ≤ 4.62²`); `(u + 4) ln(u + 4) − 4u` has derivative `ln(u + 4) − 3 < 0` for
`u < e³ − 4`, and `ln 8.62 ≤ 3`, so on `[0, 4.62]` it is at least `8.62 ln 8.62 − 18.48 > 0`;
hence `sℓ ≥ 4u` and `Q = sℓ(sℓ − 4u) + u²ℓ + 3u² ≥ 0`. The three numerical facts are checked
by `timebound.check_e_convex`. The two inequalities are those of Hermite–Hadamard for a convex
function. ∎

**Lemma 13.3 (decomposition).** Strings, `x ≥ 0`: `f = P − N` with

    P(x) = x ρ(max(x, 1)) + 2x² + E(x) + 10,     N(x) = (b − b*) x³.

Graphs, `x = log₂ v ≥ 1`, `Z = 2x − 1`: since
`F(Z, x, Z) = Z(Ax² + Bx(Z + x)/2) = (2A + 3B)x³ − (A + 5B/2)x² + Bx/2`, `f = P − N` with

    P(x) = Bx/2 + Z ρ(x) + 2Z² + E(Z) + 10,     N(x) = (b − 2A − 3B) x³ + (A + 5B/2) x².

`P`, `N`, `P'` and `N'` are nondecreasing (for strings `P'` jumps up at `x = 1`, from
`ρ(1) + 4 + e(1) = 16 + e(1)` to `φ'(1) + 4 + e(1)`, `φ'(1) = 3/ln 2 + 24`).

*Proof.* The identity for `F` is expanded with `Z = 2x − 1`. `P' = φ'(x) + 4x + e(x)` for
strings at `x ≥ 1` (`12 + 4x + e(x)` below 1), and
`P' = B/2 + 2ρ(x) + Zρ'(x) + 8Z + 2e(Z)` for graphs with
`ρ'(w) = 5ℓ² + (10/ln 2 + 3)ℓ + 3/ln 2 + 12 ≥ 0` (`ℓ = log w ≥ 0`): sums and products of
nonnegative nondecreasing functions (§4, Lemma 4.1). `N' = 3(b − b*)x²`, resp.
`3(b − 2A − 3B)x² + 2(A + 5B/2)x`, with positive coefficients. ∎

**Lemma 13.4 (the bracket).** Let `g₀ < g₁ < …` be the grid `g_{j+1} = max(g_j + 1/64, g_j(1 + 1/500))`
(rounded up to a dyadic), from `g₀ = 0` (strings) resp. `1` (graphs) to beyond the `x₁` of
Lemma 13.1, and let `E_lo`, `E_hi` be the sums of the midpoint resp. trapezoid terms of
Lemma 13.2 over the grid of `Z`, extended to a point off the grid by one more term (for graphs
`E(1)` is bracketed by 64 cells of `[0, 1]`). By Lemma 13.2, `E_lo ≤ E ≤ E_hi`. Write `P_lo`,
`P_hi` for `P` with `E_lo`, `E_hi` and outward-rounded interval arithmetic.

(i) For every integer `n` and an enclosure `[X⁻, X⁺] ∋ log₂ n`,
`P_lo(X⁻) − N(X⁺) ≤ f(log₂ n) ≤ P_hi(X⁺) − N(X⁻)`. `lo` is the largest lower value over the
integers the program evaluates: `n = 1` (resp. 2), the integers next to `2^x` at the best grid
point and at refined points, and those of the enumerated cells in (ii). So `lo ≤ M(b)`.

(ii) Every cell `[s, t]` of the grid below `x₁` is either discarded, enumerated, or split at
`m = (s + t)/2`. It is discarded when one of

    P_hi(t) − N(s),        P_hi(m) − N(m) + ((t − s)/2) · max(P'(t) − N'(s), N'(t) − P'(s), 0)

is at most `lo + τ`; both bound `f` on `[s, t]`, the first because `P` and `N` are
nondecreasing, the second by the mean value theorem (`f` is continuous and piecewise `C¹`, and
`|f'| ≤ max(P'(t) − N'(s), N'(t) − P'(s))` on the cell because `P'` and `N'` are
nondecreasing). It is enumerated when `t ≤ 40` and `2^t − 2^s ≤ 48` (tested in floating point; the test
only selects the method): `f` is evaluated by (i) at every integer of a range `[n⁻, n⁺]` with
`log₂(n⁻ − 1) < s` (or `n⁻` the smallest admissible `n`) and `log₂(n⁺ + 1) > t`, checked
with the enclosures of `log₂`, so the range contains every `n` with `log₂ n ∈ [s, t]`. A cell narrower
than `max(2^{−30}, s·2^{−24})` is not split further and its bound is kept. Then
`M(b) ≤ hi = max(lo + τ, the upper values of the enumerated integers, the kept bounds)`,
because every `n < 2^{x₁}` lies in a cell and `lo` only increases during the search.

The tolerance is `τ = max(1/100, 10⁻⁷ lo, 2(E_hi − E_lo) at the best grid point)`. ∎

| `b` (strings, in `log₂³ n`) | `log₂ a(b)` at least | at most | maximum at `n = 2^x`, `x ≈` |
|---|---|---|---|
| 2.7 | 155 970 392 421.99 | 155 970 477 301.66 | 22556.1 |
| 2.8 | 3 911 362 588.91 | 3 911 363 421.26 | 4364.03 |
| 3 | 264 827 869.68 | 264 827 901.73 | 1342.89 |
| 3.5 | 14 301 246.21 | 14 301 247.96 | 385.61 |
| 4 | 2 829 660.40 | 2 829 660.69 | 196.272 |
| 5 | 348 962.92 | 348 962.96 | 83.8771 |
| 6 | 80 514.17 | 80 514.19 | 46.9898 |
| 8 | 9 308.72 | 9 308.74 | 20.4455 |
| 10 | 1 861.37 | 1 861.39 | 10.9099 |
| 20 | 102.60 | 102.62 | 2 |

| `b` (graphs, in `log₂³ v`) | `log₂ a(b)` at least | at most | maximum at `v = 2^x`, `x ≈` |
|---|---|---|---|
| 6.5 | 7 288 683 439.03 | 7 288 688 534.01 | 4164.91 |
| 7 | 363 889 425.19 | 363 889 556.84 | 1127.5 |
| 8 | 25 844 867.93 | 25 844 873.66 | 365.177 |
| 10 | 1 803 033.05 | 1 803 033.34 | 121.425 |
| 15 | 55 162.20 | 55 162.22 | 30.7797 |
| 20 | 5 723.67 | 5 723.69 | 13.1126 |
| 30 | 310.66 | 310.68 | 3.80735 |

(`python -m babai_gi.timebound --table`; the bounds are exact rationals, printed rounded down
resp. up to two decimals.)

So, for example, `string_isomorphism` on `n` points executes at most
`2^{2829660.69} · 2^{4 log₂³ n}` and at most `2^{1861.39} · 2^{10 log₂³ n}` operations for every `n`,
and by the lower bounds no constant smaller than `2^{2829660.40}` resp. `2^{1861.37}` makes these
statements follow from Theorem A. The constants are large because of the term
`X ρ(X) ≈ 5X² log²X` of `U`, the sum of the remainders `R(y)` of the Split-or-Johnson
choice counts along a chain of colourings: at the maxima of the table (`X ≤ 22557`) it is at
least 9 times the term `3I(X) ≈ X³/log²X` of `E`. As `b` decreases to `b*` the maximum moves to
`X → ∞`, `3I(X)` takes over (from `X ≈ 2^{19.34}`), and `a(b) → ∞`.

### 13.4 In which sense `c = 3` and `b*` are the smallest values

The proof bounds the operations by a function `Ψ` of the state that satisfies the
inequalities of §8 for the multiplicities of §10 and the progress of §9. These inequalities
alone force `c = 3` and `b ≥ b*`:

**Proposition 13.4.** Let `Ψ(X, y)` be any function such that
`Ψ(X, y) ≥ σ₀(X, y) + Ψ(X − δ, y − δ)` for `log 90 ≤ y ≤ X − 1`, where
`σ₀(X, y) = (X − 1) y + β y²` is a lower bound for the multiplicity bound `σ` of §10 (the
only inequality of the proof for the step "kind C, `t = 1`": a colouring with classes of
`(2/3)m` points shrinks `|Γ|` and the window by `3/2`). Then
`Ψ(X, X − 1) ≥ b* X³ − O(X²)`.

*Proof.* Iterating `j` times from `(X, X − 1)` while `y − jδ ≥ log 90`,
`Ψ(X, X − 1) ≥ Σ_{j=0}^{J} σ₀(X − jδ, X − 1 − jδ)` with `J = ⌊(X − 1 − log 90)/δ⌋`, and
`Σ_j [(X − 1 − jδ)² + β (X − 1 − jδ)²] = ((1 + β)/(3δ)) X³ − O(X²)`; `(1 + β)/(3δ) = b*`. ∎

So no bound of the form `a · 2^{b X^c}` with `c < 3`, or with `c = 3` and `b < b*`, can be
derived from the per-step bounds of this proof; a smaller exponent or constant would need a
smaller multiplicity per colouring step or more progress per step, i.e. a different analysis
(or algorithm). The proposition is about the proof: it does not show that an input exists on
which the program executes `2^{b* X³}` operations (the multiplicities of §10 are upper
bounds on the number of choice sequences, and the chain of colourings of the proposition
need not be realised by an input). Likewise `a(b)` is the smallest constant for the proved
function `U`, not for the program.
