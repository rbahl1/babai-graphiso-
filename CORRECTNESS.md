# Correctness of `babai_gi`

This document proves that the package computes String Isomorphism and Graph
Isomorphism exactly, that under `Params.paper()` none of its fallbacks and none of its
internal guards can be reached, and that it terminates. It also states the structural
facts (structure kinds, canonicity, the tower of block systems) on which the running-time
proof (`PROOF.md`, not covered here) relies. Points that could not be settled are
collected in §16.

## 0. Scope and conventions

**Code.** All references `file.py:N` are to `babai_gi/file.py` in this version of the
repository. The modules `opcount.py`, `interval.py`, `bounds.py` and `timebound.py` are not
imported by the algorithm and are not covered.

**Papers.** [B] is Babai, arXiv:1512.03547v2; [HBD] is Helfgott, Bajpai and Dona,
arXiv:1710.04574v1. Theorem numbers are those of the arXiv texts. Some docstrings in the
code use other numbers: "HBD Prop. 5" is [HBD] Prop. 5.7, "HBD Prop. 6" is Prop. 5.8,
"HBD Exercise 5.2" is Ex. 5.5, "HBD footnote 15" is footnote 17, "HBD Prop. 4" is
Prop. 5.1, and "Babai Prop. 4.0.4" is [B] Def. 4.0.2(ii), Def. 4.0.4 and Prop. 4.0.5,
eq. (23).

**Notation.** Permutations act on the right: `mul(p, q)` is "p, then q", and
`act_string(x, g)` is the string x^g with x^g(u^g) = x(u) (`perm.py:36-38`,
`perm.py:108-113`). ISO_G(x, y) = {g ∈ G : x^g = y} and Aut_G(x) = ISO_G(x, x).
ISO_G(x, y) is empty or equal to Aut_G(x)·ρ for any ρ in it ([B] eq. (16)). For a
window Δ (a G-invariant subset of Ω), ISO^Δ_G(x, y) = {g ∈ G : x(u) = y(u^g) for u ∈ Δ}.
A `Coset(H, r)` denotes the set H·r.

**`Params.paper()`.** `Solver()` uses `Params.paper()` (`main.py:212-214`). Its values
(`main.py:100-119`, `soj.py:70-78`): C_0 = 5040; no cap on quotient enumeration;
ℓ(n) = 10·k_paper(n) with k_paper(n) = max(9, ⌊log2 n⌋ + 3) (`main.py:189-198`);
α = 2/3 (a `Fraction`); `SOJParams()` with small_v1 = 6, small_v2 = 0, max_dim = None,
dl_alpha = 2/3; `allow_fallbacks = False`, so every `fallback(...)` call raises
`TheoremViolation` (`errors.py:18-21`). Note ℓ(n) ≥ 90 for every n.

**Preconditions** of the results below.

* (P1) G is a `PermGroup(n, gens)` whose `known_order` is `None` or equal to |⟨gens⟩|,
  whose generators are not changed after construction, and which has no attribute
  `johnson_hint` other than the one set by `graph.GraphInstance` (`graph.py:47-54`).
  The caches stored on G (`aut_cache`, `stage_cache`, `lifter_cache`, `prefix_cache`,
  `agg_cache`) are empty or were filled by this package.
* (P2) The `tower` argument of `Solver.iso` is `None` or a tower for G (§5), and all calls
  on the same group object pass the same tower. (The Johnson-case data cached in
  `G.agg_cache` are keyed by string and test-set size only, and the standard blocks depend on
  the tower. `string_isomorphism` and the graph functions always pass `None`, and inside the
  recursion every group object receives a single tower, derived from the tower of the call
  that created it.)
* (P3) Letters. `Solver.iso` compares letters by Python equality and hashing
  (`Counter`, dictionaries, tuple comparison) and, in the Johnson case, orders them with
  `canon` (`main.py:549`). For `Solver.iso` the letters must therefore be values that
  `canon` encodes (Lemma 2.1): `None`, `bool`, `int`, `str`, and tuples and frozensets
  of such values. `string_isomorphism` (`main.py:1077-1087`) and the graph functions
  (`graph.py:117`, `graph.py:136`) first replace the letters by integers, so for them
  any hashable letters are admitted, with "equal" meaning equal as dictionary keys.
* (P4) The statements are about the algorithm as an abstract program with unbounded
  recursion depth and memory (§16, point 1). There is no restriction on the size of the
  input: every threshold decision is made in exact arithmetic (Lemma 0.1).

**Lemma 0.1 (exact decisions).** Under `Params.paper()` every comparison of the algorithm
with a threshold is decided exactly, for every input size.

(a) The comparisons with m/2, n1/2 + 1, n2/2, n2/3, 2n2/3 and n1/2 are comparisons of
integers: `2 * len(Cx) > m` (`main.py:601`), `2 * len(orb) > m` (`main.py:793`),
`2 * len(S) >= m` (`main.py:800`), `2 * max_twin_class(...) <= n1 + 2` (`soj.py:189`),
`2 * d1 > n2` (`soj.py:463`), `2 * len(cl) > n2` (`soj.py:519`),
`n2 < 3 * len(groups[k]) <= 2 * n2` (`soj.py:657`), `3 * len(S_idx) > n2` (`soj.py:664`),
`2 * dk > n1` (`soj.py:725`, `soj.py:774`), `2 * max_twin_class(...) <= n1` (`soj.py:738`)
and `0 < 2 * dg < n2` (`soj.py:785`).
(b) The bounds α·|V|, β·n1_orig, (2/3)|V2| and α·n of the Split-or-Johnson procedures and of
the Design Lemma are `Fraction`s, and the comparisons of integers with them
(`soj.py:151`, `soj.py:249`, `soj.py:454`, `soj.py:582`, `soj.py:624`) are exact.
(c) The other thresholds are integers: m^{1+⌊log2 m⌋} and m^{2+⌊log2 m⌋}
(`main.py:167-179`), k_paper(n) and ℓ(n) (`main.py:189-198`, through `bit_length`), and the
giant tests |G|·2 ≥ n! (`main.py:273`, `main.py:923`, `johnson.py:417`, `certificates.py:158`).
(d) The s-th roots of `_cameron_candidates` are exact (Lemma 4.6).

*Proof.* (a) Each test is the real inequality (|C| > m/2, |C| ≤ n1/2 + 1, d1 > n2/2,
n2/3 < |g| ≤ 2n2/3, and so on) multiplied by the positive integer 2 or 3, which preserves
it, and Python integers have unbounded precision. (b) α = `Fraction(2, 3)` (`main.py:111`)
and dl_alpha = `Fraction(2, 3)` (`soj.py:75`). The parameter of `upcc_split_or_johnson` is
α itself in case 2b (`main.py:957`) and `Fraction(alpha) * m / len(C)` in the EDL path
(`design.py:81`); bound = α_U·|V| (`soj.py:319`), β = bound/|V1| (`soj.py:351`) and
bound = β·n1_orig (`soj.py:411`) are products and quotients of a `Fraction` with integers,
hence `Fraction`s, and the Design Lemma is called with α = P.alpha (`design.py:44`) or
dl_alpha (`soj.py:535`). (c) By inspection of the cited lines. (d) Lemma 4.6. ∎

The only floating-point computations in the algorithm modules are
`SOJParams.small_v2_bound` when small_v2 is `None` (`soj.py:96`) and the `small_scale`
rule of `Params.k_for` (`main.py:207`). `Params.paper()` reaches neither: small_v2 = 0, so
`small_v2_bound` returns at `soj.py:94-95`, and k_rule = "paper" returns at
`main.py:204-206`.

**Status markers.** "Cited" marks a theorem of [B] or [HBD], or a classical theorem,
used without proof. Everything else is proved here or reduced to a cited theorem.

## 1. Results

**Theorem A (correctness).** Assume (P1)–(P4). `Solver().iso(G, x, y)` returns `None`
if ISO_G(x, y) = ∅, and otherwise a `Coset` C such that C.group = Aut_G(x) as a set and
C.rep ∈ ISO_G(x, y); hence C.group·C.rep = ISO_G(x, y). `string_isomorphism(G, x, y)`
returns ISO_G(x, y) in the same form, for arbitrary hashable letters.
`graph_isomorphism` returns a vertex isomorphism or `None` exactly when none exists, and
`graph_automorphisms` returns generators and the order of the automorphism group (§15).

**Theorem B (no exception).** Under the same assumptions no call of `fallback(...)`, no
`raise` that guards an invariant and no `assert` is reached (§13). The only exceptions the
package can raise are the input-validation errors of §13.3, on invalid input.

**Theorem C (termination).** Every call terminates (§14).

**Theorem D (structure kinds).** The structures produced by the procedures passed to
`branch` are of the kinds listed in §12.

**Theorem E (canonicity).** Every such procedure is canonical relative to its choices
(§6.4, §11), and `branch` returns ISO_G(x, y) when this holds (Theorem 6.5).

**Theorem F (tower).** Every recursive call receives a tower invariant under its group,
and after the extension in `_solve` the group acts primitively on the top blocks (§5).

**Proof plan.** Let μ(G, x, y) = (n, |G|, [x ≠ y]), ordered lexicographically. Theorems
A, B and C are proved together by induction on μ: every recursive `iso` call made while
computing `iso(G, x, y)` has a smaller μ (§14), and every recursive call satisfies
(P1)–(P3): its group is created by the package with an exact `known_order` (Lemma 3.2), its
tower is a tower for its group (Lemma 5.5), and its letters satisfy (P3) (§2). So the
induction hypothesis gives the contract of §4.1 for all recursive calls. The steps of
`_solve` are then shown correct (§4, §6, §10) given that contract.

## 2. Letters (`canon.py`)

**Lemma 2.1.** On the values built from `None`, `bool`, `int`, `str`, `tuple`, `list`,
`frozenset`/`set` and `structure.Fixed`, `canon(a) == canon(b)` holds if and only if
`a == b`, and any two images are comparable, so `sorted(..., key=canon)` is a total order
that depends only on the values. On other types `canon` raises `TypeError`
(`canon.py:29-48`).

*Proof.* By structural induction. Each image is a pair (tag, payload) and tags are
compared first, so payloads are compared only between values of the same kind. `bool` is
encoded as its integer value, as Python has `True == 1`. A set is encoded by the sorted
tuple of the images of its elements; by induction distinct elements have distinct images,
so the encoding of a set depends only on the set. Tuples and lists have distinct tags,
and `(1,) != [1]` in Python. ∎

**Lemma 2.2.** `normalize_letters(x, y)` (`canon.py:51-74`) returns (f∘x, f∘y) for a map
f that is injective on the letters occurring in x or y (dictionary-key equality). Hence
ISO_G(x, y) = ISO_G(f∘x, f∘y).

*Proof.* `seen` collects the distinct letters; `order` is a permutation of them (sorted
by `canon`, or in order of first occurrence if `canon` raises), and `code` gives
distinct integers to distinct letters. The same `code` is applied to both strings, and
x^g = y if and only if (f∘x)^g = f∘y. ∎

All strings created inside the recursion have letters that are letters of the input or
nested tuples (letter, 0/1) (`certificates.py:341-344`), so (P3) is inherited by every
recursive call.

## 3. Permutation-group primitives (`perm.py`, `group.py`, `action.py`)

**Lemma 3.1 (Schreier–Sims).** Let `PermGroup(n, gens, known_order=K)` with K `None` or
K = |⟨gens⟩|. After `_build` (`group.py:78-197`) the levels form a complete base and
strong generating set: the group of level i is the pointwise stabiliser G^(i) of the
first i base points, `trans` at level i is a right transversal of G^(i+1) in G^(i), and
the product of the transversal lengths is |G|. Consequently `sift`, `contains`, `order`,
`elements`, `coset_reps_prefix`, `level_group`, `prefix_group` and
`pointwise_stabilizer` are exact (`group.py:204-276`, `group.py:406-440`), and the
pruning at `group.py:69-75` keeps ⟨gens⟩ unchanged. The `RuntimeError` at
`group.py:138` is unreachable.

*Proof (summary).* Invariants: every strong generator of level i lies in G^(i); the
groups of consecutive levels are nested; `extend_orbit` keeps each transversal equal to
the orbit of the base point under the level's generators. If `closure()` runs to
exhaustion, every Schreier generator of level i sifts to the identity through levels
> i, and by Schreier's lemma the level groups are the stabilisers (bottom-up induction).
If the early stop at `group.py:167-170` or `group.py:189-193` fires, the product of the
transversal lengths equals K = |G|; since each level group is contained in G^(i) and
each transversal is contained in the corresponding orbit of G^(i), equality of the
products forces equality at every level. Pruning keeps exactly the generators whose
residue was not the identity, and each residue differs from the generator by an element
of the group generated by the earlier ones. A new level is created only for a non-identity
residue that fixes all base points and all forced-prefix points; such a residue moves a
point outside the prefix, so the `RuntimeError` at `group.py:138` is unreachable. ∎

**Lemma 3.2 (every `known_order` is exact).** The values passed as `known_order` are
correct at every site:

| site | value | why it is exact |
|---|---|---|
| `main.py:363` | number of elements found by `_chain_search` | `_chain_search` yields each element of Aut_G(x) once (§4.2) |
| `main.py:530`, `main.py:541` | ∏ \|class\|!, halved for Alt if some class has ≥ 2 points | §4.2, trivial case |
| `group.py:250` | product of the transversal lengths below level i | Lemma 3.1 |
| `group.py:258`, `main.py:843` | the order of the same group | same generators |
| `action.py:134` | \|H\|·\|G_(Δ)\| | lift of H ≤ G^Δ (Lemma 3.4) |
| `action.py:181`, `action.py:188`, `certificates.py:216` | \|G\| for the group of pairs (g, φ(g)) | equal to \|G\| because φ is a homomorphism (Lemma 3.3) |
| `action.py:229`, `certificates.py:223` | order of a level group of a complete chain | Lemma 3.1 |
| `action.py:290` | image_order·\|ker φ\| | callers pass \|⟨gens⟩\|: `main.py:639` computes it by Schreier–Sims; `main.py:476` uses `Nbar.order()`; `certificates.py:181-184` uses k!(m−k)!, halved when φ(G) = Alt(Γ) (the product Sym(A)×Sym(Γ∖A) contains odd elements because m ≥ 3) |
| `action.py:295` via `certificates.py:185`, `certificates.py:246` | the order of the same or of a conjugate group | conjugation preserves order |
| `certificates.py:243` | order of the conjugated group | same |
| `graph.py:46` | v! | Sym(V) acts faithfully on pairs for v ≥ 3 |
| `group.py:495` | `None` at every caller | — |

**Lemma 3.3 (φ is a homomorphism at every `GroupWithAction`).** `GroupWithAction(G, m,
phi_gens)` (`action.py:150-175`) is correct only if `G.gens[j] ↦ phi_gens[j]` extends to
a homomorphism φ (condition HOM). HOM holds at every construction site:

* `main.py:280`: the identity map.
* `main.py:290`: the hint; φ is the inverse of the faithful action of Sym(V) on pairs,
  given on the two generators of `GraphInstance.G` in the same order (`graph.py:41-54`).
* `main.py:343`: φ = `johnson_phi` applied to the block image of each generator
  (Lemma 4.4).
* `main.py:444`, `main.py:474`: the action on a G-invariant partition (the blocks are
  G-invariant by Lemma 5.3).
* `main.py:477`, `johnson.py:325`: the action of Gbar on the s classes of parallel layers.
  The layers and classes are built from a Gbar-invariant orbital by constructions that
  commute with Gbar (components, equivalence closures of invariant relations,
  `johnson.py:196-309`), so every element of Gbar permutes the classes.
* `action.py:296` (`subgroup`): the restriction of φ to a subgroup, evaluated by `phi`.
* `main.py:846`, `main.py:851`: g ↦ φ(g)|Φ for a group preserving Φ (G1, respectively F;
  Φ is an orbit of φ(F), and G1 = φ^{-1}(Aut{Φ, Γ∖Φ} ∩ φ(G))). At `main.py:846` the list
  `phiPhi` is indexed by `G1w.G.gens` while the group is `G1`; Lemma 3.5 shows the two
  lists are equal.

Under HOM, `phi`, `kernel`, `lift`, `preimage`, `intersect_image` and `subgroup`
(`action.py:199-296`) are exact: the group of pairs (g, φ(g)) projects isomorphically
onto G, its chain with the Γ points first has as level group after the Γ levels the graph
of ker φ, and sifting a permutation τ of Γ through the Γ levels yields an element with
image τ, or fails exactly when τ ∉ φ(G). The `ValueError`s at `action.py:214` and
`action.py:220` are raised only for g ∉ G, at `action.py:284` only for a generator outside
φ(G), at `action.py:156` only on a length mismatch and at `action.py:167` only if `phi_fn`
disagrees with φ; none of these occurs (Lemma 3.5, §13.2).

**Lemma 3.4 (other primitives).**
* `WindowLifter` (`action.py:64-147`): for a G-invariant window Δ, `restricted` = G^Δ,
  `lift(π)` returns an element of G restricting to π or `None` iff π ∉ G^Δ, `kernel()` =
  G_(Δ), and `lift_group(H)` = {g ∈ G : g|Δ ∈ H} for H ≤ G^Δ ([B] Obs. 3.1.10).
* `generated_subcoset(n, [(H_i, s_i)])` (`group.py:480-495`) returns the smallest coset
  ⟨H_i, s_i s_1^{-1}⟩·s_1 containing every H_i s_i ([B] Def. 9.0.7). If every H_i s_i is
  contained in a coset K r and their union is K r, the result is K r as a set.
* `even_subgroup_gens(gens, n)` (`group.py:498-519`) returns Schreier generators of
  ⟨gens⟩ ∩ Alt(n) for the transversal {1, h_0}.
* `minimal_block_system()` (`group.py:338-384`) of a transitive group returns a
  G-invariant partition with at least 2 blocks (for n ≥ 2) on which G acts primitively,
  i.e. a system of maximal blocks, and the singletons iff G is primitive. `_atkinson`
  (`group.py:450-475`) returns the finest G-invariant equivalence relation containing
  (a, b); for a transitive action, some b gives a proper non-trivial relation iff the
  action is imprimitive.
* A right coset L·s that equals a group A as a set has s ∈ A and L = A.

*Proofs.* As in [B] Obs. 3.1.10, Def. 9.0.7 and [HBD] §2.1.2; the last item: 1·s ∈ A,
and L = A·s^{-1} = A. ∎

**Lemma 3.5 (generator lists in `top_action`).** In `top_action`, `G1w = Gw.subgroup(G1.gens,
known_order=|G1|)` (`main.py:843`) has `G1w.G.gens == G1.gens`.

*Proof.* `G1.gens` contains no identity and no repetition (`group.py:46-56`), so
`subgroup` passes the same list (`action.py:293-295`). If it has at most 6 elements it is
kept. Otherwise it was itself produced by pruning, so it is the list of essential
generators of an earlier build; in the rebuild the generator g_i is essential iff it is
not in ⟨g_1, …, g_{i−1}⟩ (the chain after each essential generator is complete, or the
target order has been reached, Lemma 3.1), which holds for every i because it held in the
build that produced the list. The early stop at the target order fires after the same
generator in both builds. ∎

## 4. `Solver.iso` and `_solve` (`main.py`)

### 4.1 Contracts

(C_iso) `iso(G, x, y, T)` returns `None` iff ISO_G(x, y) = ∅, and otherwise a coset C
with C.group = Aut_G(x) as a set and C.rep ∈ ISO_G(x, y).

(C_solve) `_solve(G, x, y, T)` is called only when G ⊄ Aut(x) and the letter multisets of
x and y agree. It returns `None` iff ISO_G(x, y) = ∅; otherwise a coset H·ρ with
ρ ∈ ISO_G(x, y) and H ≤ Aut_G(x); if x = y, then H·ρ = Aut_G(x). (For x ≠ y the result
can be a proper subset of ISO_G(x, y); `_one_iso`, the only caller with x ≠ y, uses only
the representative, `main.py:258-263`.)

**Theorem 4.1.** Under (P1)–(P4), if the recursive calls satisfy (C_iso), then `iso`
satisfies (C_iso) and `_solve` satisfies (C_solve).

*Proof of (C_iso) from (C_solve)* (`main.py:219-256`).
* `main.py:237-238`: if every generator fixes x, then G ≤ Aut(x) and ISO_G(x, y) is G
  when y = x and ∅ otherwise.
* `main.py:239-240`: an isomorphism maps the multiset of letters of x to that of y.
* `main.py:241-247` (x ≠ y): ρ = `_one_iso(...)` is in ISO_G(x, y), or `None` iff it is
  empty; A = `iso(G, x, x, T)` has μ smaller in the last component, so A.group = Aut_G(x),
  and ISO_G(x, y) = Aut_G(x)·ρ.
* `main.py:248-254` (x = y): the entries of `G.aut_cache` are written only at
  `main.py:251` and `main.py:364`, with values that equal Aut_G(x) by (C_solve) and §4.2;
  by Lemma 3.4 (last item) a coset equal to Aut_G(x) has group Aut_G(x) and
  representative in it.

*Proof of (C_solve)*, by the branch taken in `_solve` (`main.py:265-347`):
* `main.py:268-269`: `brute_force`, §4.2.
* `main.py:270-272`: G intransitive, `chain_rule`, §4.2.
* `main.py:273-281`: n ≥ 3 and |G| ≥ n!/2, so G is Alt(Ω) or Sym(Ω) (the only subgroups
  of index ≤ 2 of Sym(n)); `trivial_case`, §4.2. The `assert` at `main.py:277` holds by
  Lemma 5.4.
* `main.py:282-295`: the hint, §4.3 and §10.
* `main.py:296-311`: the blocks are the top partition of the (possibly extended) tower;
  they are G-invariant and G acts primitively on them (Lemma 5.3).
* `main.py:312-315`, `main.py:335`, `main.py:340`: `strong_luks`, §4.2.
* `main.py:318-324`: `cameron_reduction`, §4.2.
* `main.py:342-347`: the Johnson case, §10, with φ a giant representation (Lemma 4.4). ∎

### 4.2 The Luks layer

* **`brute_force`** (`main.py:350-369`). `_chain_search` (`main.py:1036-1074`) enumerates
  g = u_{k−1}⋯u_0 along the transversals; after u_i, …, u_0 are fixed, the images of the
  points fixed by G^(i+1) are final, and they are checked against y. Every element of G is
  produced once (Lemma 3.1), so the output is ISO_G(x, y), each element once. Aut_G(x)
  is computed and cached first; the result is `Coset(Aut_G(x), g)` for the first g found.
* **`iso_window`** (`main.py:371-389`). For an H-invariant window Δ it returns
  ISO^Δ_H(x, y): if H acts trivially on Δ, this is H or ∅ (`main.py:381-384`); otherwise
  it is the preimage under restriction of ISO_{H^Δ}(x|Δ, y|Δ) (Lemma 3.4, [B]
  Obs. 3.1.10). Every caller passes an invariant window (§5, Lemma 5.5).
* **`chain_rule`** (`main.py:391-434`). The orbits are processed in a fixed order; the
  cached stages satisfy stages[i] = (lifter of G_{i−1} on Δ_i, G_i) with
  G_i = Aut^{Δ_1∪…∪Δ_i}_G(x) (the cache is keyed by x and its entries do not depend on
  y). By induction on i, cur·acc = ISO^{Δ_1∪…∪Δ_i}_G(x, y) and cur_y = y^{acc^{-1}}
  ([B] Prop. 3.1.7 with Obs. 3.1.10). After the last orbit the result is ISO_G(x, y).
* **`strong_luks`** (`main.py:436-460`). N is the kernel of the action on the blocks;
  `coset_reps_prefix` yields one σ per coset Nσ (Lemma 3.1 for the group of pairs, which
  satisfies HOM). ISO_G(x, y) = ⊔_σ ISO_N(x, y^{σ^{-1}})·σ ([B] Prop. 3.1.6, Thm. 3.1.8).
  For x = y all pieces are collected and `generated_subcoset` returns their union
  exactly (Lemma 3.4); for x ≠ y the first non-empty piece is returned.
* **`cameron_reduction`** (`main.py:462-495`). The same with the preimage NG of the kernel
  of Gbar → Sym(s): `coset_reps_prefix` of Qw gives representatives of Gbar modulo that
  kernel, `Gw0.lift` lifts each one to G (it is an element of Gbar, the image of G, so the
  `RuntimeError` at `main.py:485` is unreachable), and G = ⊔ NG·σ.
* **`trivial_case`** (`main.py:505-541`). For Sym(Ω), ISO is non-empty iff the letter
  multiplicities agree; σ maps each letter class of x onto that of y, and Aut is the
  product of the symmetric groups of the letter classes (a transposition and a full cycle
  generate each). For Alt(Ω), Aut is the even part, of index 2 iff some class has two
  points; an odd σ is corrected by a transposition inside a class of y, and if all classes
  are singletons there is no even isomorphism.

### 4.3 The primitive quotient (`johnson.py`, `main.py:309-347`)

**Lemma 4.2 (recognisers; proofs condensed).**
(a) If `recognize_johnson(Gbar)` (`johnson.py:408-434`) returns a structure (m, t,
phi_gens, T_of_point), then the m sets built in `_identify` are permuted by Gbar, T_of_point
is a bijection from the points onto the t-subsets of [m], T(w^g) = T(w)^{φ(g)} for all
g ∈ Gbar, and φ(Gbar) ⊇ Alt(m); for t = 1 Gbar is a giant (`johnson.py:417-418`).
(b) It returns a structure for every group with A_k^{(t)} ≤ Gbar ≤ S_k^{(t)}, t ≥ 2,
k ≥ 2t+1: the orbitals of such a group are the t relations |T∖T'| = i, the Johnson
orbital passes the valency test, graph distance equals |T∖T'|, neighbours split into t
classes by their difference point (common-neighbour counts k−t−2 versus t−2), and the
sets P_i = {T : i ∈ T} are recovered.
(c) `recognize_cameron` (`johnson.py:163-363`) returns a structure for every Cameron
group with s ≥ 2, t ≥ 1, k ≥ max(5, 2t+1) ([B] Def. 3.2.2), and for any returned
structure the class action is a homomorphism Gbar → Sym(s) (Lemma 3.3) that is non-trivial
when Gbar is primitive (otherwise the layers of a class would form a block system). The
parameters (k, t, s) it tries are those of Lemma 4.6, for every degree.

**Lemma 4.3 (dispatch under `Params.paper()`).** Let Gbar be the action of G on the top
blocks (primitive by Lemma 5.3), of degree m and order q.
* If q < m^{1+⌊log2 m⌋} (`main.py:167-171`, `main.py:181-186`), `strong_luks`
  enumerates Gbar.
* Otherwise, if m ≥ 25, Gbar is a Cameron group with k ≥ max(5, 2t+1) (Maróti's theorem,
  as used in [B] Thm. 3.2.3 and [HBD] Thm. 3.1; cited, it uses CFSG). The weaker bound
  q ≥ m^{1+⌊log2 m⌋} suffices: Maróti's third alternative gives
  |Gbar| < m^{1+⌊log2 m⌋} for non-Cameron groups, M_11, M_12, M_23, M_24 have degree < 25,
  k = 2t is imprimitive, and k ≤ 4 gives orders below the bound. By Lemma 4.2,
  `recognize_johnson` succeeds when s = 1 and fails when s ≥ 2 (a returned structure
  would make Gbar a Johnson group, whose socle is a single alternating group), and then
  `recognize_cameron` succeeds. So `main.py:330-335` is not reached when m ≥ 25.
* If m < 25 and q ≥ m^{1+⌊log2 m⌋}: a giant is recognised (`johnson.py:417-418`) and is
  enumerated at `main.py:336-340`, since m < 25 < ℓ(n); any other group that is not
  recognised is enumerated at `main.py:335` without calling `fallback`, because the test at
  `main.py:331` requires m ≥ 25. (By Maróti's theorem these other groups are Mathieu groups:
  with the integer threshold, M_12, M_23 and M_24 lie above it, e.g.
  |M_23| = 10,200,960 > 23^5; M_11 lies below.)

Hence the `fallback` at `main.py:333` is unreachable.

**Lemma 4.4 (`johnson_phi`).** Let `jh = recognize_johnson(Gbar)` with Gbar the block action
of G and `imgs` the block images of `G.gens`. For every img ∈ Gbar, `johnson_phi(img, jh)`
(`johnson.py:366-398`) returns the unique permutation of Γ that induces img on the
t-subsets; none of its `ValueError`s is raised. The map g ↦ `johnson_phi(img(g))` is a
homomorphism G → Sym(Γ) with image ⊇ Alt(Γ), and the standard blocks satisfy
B_T^g = B_{T^{φ(g)}}.

*Proof.* By Lemma 4.2(a), every element of Gbar is induced on t-subsets by a permutation
of Γ, unique because Sym(Γ) acts faithfully on t-subsets for 1 ≤ t < m. For two t-sets
T1, T2 with T1 ∩ T2 = {γ} (they exist since m ≥ 2t+1 > 2t−1), the image of γ is the
unique common element of the images; the final check verifies the induced action on all
points. The map is the composite of the block action G → Gbar and the inverse of the
faithful action of φ(Gbar) on t-subsets, hence a homomorphism, and its image is
φ(Gbar) ⊇ Alt(Γ). ∎

`JohnsonData` installs `_make_fast_phi` (`certificates.py:60-110`), which computes the same
φ on every element of G (its rule is the one of `johnson_phi`); the `ValueError` at
`certificates.py:106` cannot occur by equivariance of the blocks.

**Lemma 4.5 (the hint).** The hint path (`main.py:282-295`) is taken only for the group
`GraphInstance.G` = S^{(2)}(V) with v ≥ 5, which is primitive on pairs, with the trivial
tower, and only when |G| ≥ N^{1+⌊log2 N⌋} for N = C(v, 2) and v ≥ ℓ(N), the conditions of
`main.py:309-347`. The hint states the true structure (φ = inverse of the pair action,
T_of_point = the pair), so the computation is the one of `main.py:342-347` with this φ.

**Lemma 4.6 (`iroot` and the Cameron candidates).**
(a) For integers N ≥ 0 and s ≥ 1, `iroot(N, s)` (`johnson.py:149-160`) returns ⌊N^{1/s}⌋,
the unique integer r ≥ 0 with r^s ≤ N < (r + 1)^s.
(b) `_cameron_candidates(N, ts)` (`johnson.py:123-146`) returns exactly the tuples
(k, t, s, c) with s ≥ 2, c ≥ 3, c^s = N and either t = 1, k = c, or t ≥ 2, k ≥ 2t + 1,
C(k, t) = c (only t ∈ ts if ts is given), each once. In particular it contains the
parameters of every Cameron group of degree N with s ≥ 2, since k ≥ max(5, 2t+1) gives
c = C(k, t) ≥ 5.

*Proof.* (a) Let b = `N.bit_length()`, so N < 2^b (also for N = 0, where b = 0). The loop
keeps the invariant (I): lo^s ≤ N < hi^s. Initially lo = 0, so lo^s = 0 ≤ N, and
hi = 2^{⌊b/s⌋+1}; since ⌊b/s⌋ + 1 > b/s, the exponent s(⌊b/s⌋ + 1) is an integer larger
than b, so hi^s ≥ 2^{b+1} > N. Because x ↦ x^s is strictly increasing on the non-negative
integers, (I) implies lo < hi. While hi − lo ≥ 2, mid = ⌊(lo + hi)/2⌋ satisfies
lo < mid < hi; the step sets lo = mid if mid^s ≤ N and hi = mid otherwise, which keeps (I)
and decreases hi − lo. So the loop ends, with hi = lo + 1, and then lo^s ≤ N < (lo + 1)^s.
This r is unique by monotonicity. All operations are on Python integers and are exact.
(b) N < 9 returns the empty list, and loses nothing: c ≥ 3 and s ≥ 2 give c^s ≥ 9. The loop
runs over s = 2, …, b − 1. No s with an integer root c ≥ 3 is left out: c^s = N with c ≥ 3
gives N ≥ 2^s, i.e. b ≥ s + 1, so s ≤ b − 1. For each s, c = ⌊N^{1/s}⌋ by (a), and the test
`c < 3 or c ** s != N` (`johnson.py:133`) keeps s exactly when N is the s-th power of an
integer c ≥ 3, which is then c. For such s the tuple (c, 1, s, c) is added (if 1 ∈ ts). The
loop over t ≥ 2 runs while C(2t + 1, t) ≤ c; C(2t + 1, t) is strictly increasing in t, so it
visits exactly the t ≥ 2 with C(2t + 1, t) ≤ c, and these are the t for which some
k ≥ 2t + 1 can have C(k, t) = c, because C(k, t) ≥ C(2t + 1, t) for k ≥ 2t + 1. For such t
the inner loop stops at the least k ≥ 2t + 1 with C(k, t) ≥ c (it stops because C(k, t)
grows without bound), and since k ↦ C(k, t) is strictly increasing for k ≥ t, the equation
C(k, t) = c has at most one solution k ≥ 2t + 1, which is this k when it exists. Distinct
(s, t) give distinct tuples. ∎

## 5. The tower of block systems (`tower.py`, `main.py`)

A *tower for* H ≤ Sym(n) is a sequence of partitions P_1, …, P_k of {0, …, n−1}, each
H-invariant, each strictly coarser than the previous one (P_0 = singletons) and each with
at least 2 blocks. The trivial tower has k = 0. `Tower` stores P_i as a block-index
vector (`tower.py:40-46`).

**Lemma 5.1.** A tower for H is a tower for every subgroup of H.

**Lemma 5.2 (`restrict`, `tower.py:98-113`).** Let T be a tower for H and Δ an H-invariant
set, `pts` = sorted(Δ), with point `pts[i]` renamed i. Then `T.restrict(pts)` is a tower
for the restriction H^Δ (on the renamed points).

*Proof.* The intersection with Δ of an H-invariant partition is H^Δ-invariant. The
restricted partitions are weakly coarsening. A level with one block on Δ is dropped
together with all coarser ones (`tower.py:107-108`). A level with as many blocks as the
last kept level is equal to it, because it is coarser, and is dropped
(`tower.py:109-110`). The kept levels are strictly coarsening with at least 2 blocks. ∎

**Lemma 5.3 (extension, `main.py:296-311`).** Let G be transitive with a tower T. After
`main.py:307`, the tower is a tower for G, `blocks` is its top partition (or the
singletons if the tower is trivial and G is primitive), and G acts primitively on
`blocks`.

*Proof.* `top` is the top partition of T (`tower.py:55-71`), or the singletons. It is
G-invariant, and G is transitive on its blocks. If T is trivial, `coarse` is
`G.minimal_block_system()`: the singletons if G is primitive, otherwise a block system
with at least 2 blocks and primitive action (Lemma 3.4). Otherwise `sup` is a maximal block
system of the transitive action Gp of G on the top blocks, and `coarse` merges the top
blocks along it (`main.py:301-304`): it is G-invariant, coarser than `top`, has at least 2
blocks, and the action of G on it is the action of Gp on `sup`, which is primitive. If
`sup` is the singleton system, Gp is primitive and `coarse = top`. If `coarse` has fewer
blocks than `top`, it is appended (`tower.py:89-96`), keeping strict coarsening and at
least 2 blocks. In both cases G acts primitively on `blocks = coarse`. ∎

**Lemma 5.4.** The `assert tower.is_trivial()` at `main.py:277` holds: there G is Alt(Ω)
or Sym(Ω), and n ≥ 8 because G passed the test |G| > C_0 = 5040 = 7! at `main.py:268`.
Such a G is primitive, so no G-invariant partition has between 2 and n−1 blocks, and a
tower for G is trivial.

**Lemma 5.5 (every recursive call receives a tower for its group).**

| call | group of the call | tower passed | reason |
|---|---|---|---|
| `main.py:243`, `main.py:246`, `main.py:250` | G | T | same group |
| `main.py:424` (chain rule) | cur^Δ, cur ≤ G, Δ a G-orbit | `T.restrict(Δ)` | Lemmas 5.1, 5.2 |
| `main.py:452` (`strong_luks`) | kernel N ≤ G | extended T | Lemma 5.3, 5.1 |
| `main.py:487` (`cameron_reduction`) | NG ≤ G | extended T | Lemma 5.3, 5.1 |
| `main.py:668` (`branch`) | G1 ≤ G | `jd.tower` = extended T (`main.py:344`) or trivial (`main.py:291`) | Lemma 5.1 |
| `main.py:859`, `main.py:875`, `main.py:884`, `main.py:890` (`top_action`) | K^{Ω(Φ)}, K ≤ G1 | `jd.tower` restricted to Ω(Φ) by `iso_window` (`main.py:385`) | Ω(Φ) is G1-invariant because φ(G1) preserves Φ |
| `main.py:899` (`top_action`) | Aut_top^{Ω∖Ω(Φ)}, Aut_top ≤ G1 | restricted `jd.tower` | the complement of an invariant set is invariant |
| `certificates.py:279`, `certificates.py:392` | N^{W_new}, N = ker(H(W_old) → Sym(A)) ≤ G | restricted `jd.tower` | W_new is H(W_old)-invariant (Lemma 10.2) |

In each case the window passed to `iso_window` is invariant under the group whose
restriction is taken, so Lemma 5.2 applies, and `Tower.restrict` produces a tower on
`len(pts)` points, which is the degree of the restricted group (so `main.py:229-230`
never raises). The towers do not influence the result, only which block system `_solve`
uses; but they must be invariant, since `induced_action` on a non-invariant partition
would not be an action.

The tower is the one of [HBD] App. A.1, with one difference: `cameron_reduction` does not
append the coordinate fibre system of the Cameron group (A.1 does); the call on NG
computes a maximal block system above the top level itself (§16, point 5).

## 6. Canonical structures, choices, `branch` and `align` (`structure.py`, `main.py:620-703`)

### 6.1 Structures

A `Structure` on Γ = {0, …, m−1} (`structure.py:179-202`) is a list of cells with keys
and at most one Johnson cell. The object it encodes: a partition of Γ into cells with
keys; cells with equal keys have equal size (`_normalize` appends the size to the key,
`structure.py:190`) and are interchangeable blocks of one *class*; optionally one cell J
with a bijection λ: J → binom([m'], t'). An isomorphism A → B in this category S is a
permutation σ of Γ mapping every cell of A onto a cell of B with the same key, and the
Johnson cell of A onto that of B with λ_B(v^σ) = π(λ_A(v)) for some π ∈ Sym([m']).

**Lemma 6.1 (invariants).** Every `Structure` built by the package satisfies: (I1) the
cells are non-empty, disjoint and cover Γ; (I2) the Johnson key `(k, "johnson", m', t')`
(a 4-tuple, `structure.py:202`) differs from every other key (2-tuples), and
`johnson_cell` is set only together with `johnson`; (I3) the labels of a Johnson cell
are a bijection onto all t'-subsets of {0, …, m'−1}, with 2 ≤ t' and m' ≥ 2t'+1.

*Proof.* (I1): the initial structures partition Γ (`main.py:607`, `main.py:613`,
`main.py:725-732`, `main.py:825`, `main.py:914`, `main.py:1030`); `refine`, `individualize`,
`mark` split cells; `split_by_blocks` (`soj.py:802-830`) is always called with blocks that
partition the given vertex set (§9, §10). (I2): the only constructor of a Johnson cell is
`soj.py:477-481`, and no structure is refined after it (it is returned to the caller of
`branch`). (I3): there the hypergraph H is complete (|H| = C(n2, d1)), V1' has no twins
(distinct neighbourhoods), so v ↦ labels[v] is a bijection onto all d1-subsets of
range(n2), and d1 ≥ 2, n2 ≥ 2d1+1 (`soj.py:477`). ∎

**Lemma 6.2 (automorphisms).** Under (I1)–(I3), `aut_gens` (`structure.py:285-316`)
generates Aut(S) = ∏_classes Sym(s)≀Sym(c) × (S_{m'} acting on the Johnson cell),
`aut_order` (`structure.py:318-331`) is its order, `has_odd_automorphism` is correct, and
`odd_automorphism` returns an odd element iff one exists (a group generated by even
permutations is even). The `assert` at `structure.py:296` holds by (I2).

### 6.2 `align` (`structure.py:375-423`)

**Lemma 6.3.** `align(A, B, need_even)` returns an element of Iso_S(A, B), even when
`need_even` is set, and returns `None` only if no such (even) element exists.

*Proof.* Keys are compared by `canon` (`structure.py:426-428`), which is value-faithful
(Lemma 2.1). If Iso_S(A, B) ≠ ∅, the multisets of (key, size) and the Johnson
parameters agree, so the tests at `structure.py:381-404` pass. Inside a key class any
bijection between A-cells and B-cells, composed with any bijections of paired cells, is
part of an isomorphism. For the Johnson cell, p = λ_B^{-1}∘λ_A is defined on all of J_A by
(I3); it is an isomorphism with π = id. If σ is any isomorphism, then p = σ·τ with τ the
automorphism of B induced by π^{-1}, so no isomorphism is lost by taking π = id. If an even
element is needed and p is odd, Iso_S(A, B) = p·Aut(B) contains an even element iff Aut(B)
contains an odd one, which `odd_automorphism` supplies (`structure.py:418-422`). ∎

The labels themselves depend on the order of V2 and are not canonical: for an isomorphic
input they differ by a permutation ψ_0 of the abstract set. This is harmless because the
category S identifies labellings up to Sym([m']), `align` uses π = id, and `aut_gens`
generates the whole induced S_{m'} (`structure.py:358-372`).

### 6.3 Choices and runs (`structure.py:74-160`)

A procedure `proc(s, chooser)` makes choices through `chooser.choose(candidates)` and
records invariants through `chooser.check(value)`. The x-side `RecordingChooser` takes
the first candidate and records the trace (events ("choice", count) and ("inv", value)).
The y-side `ReplayChooser` follows an index path and raises `Mismatch` at the first event
that differs from the trace, at an exhausted trace, or at an unconsumed trace.

**Lemma 6.4 (`enumerate_runs`).** `enumerate_runs(proc, trace)` executes `proc` once for
every sequence of choice indices that is consistent with the trace (odometer order),
yields exactly the runs that complete without `Mismatch`, each once, and executes `proc`
at most ∏_d k_d times (k_d the candidate counts of the trace; each execution ends at a leaf
of the tree of consistent index sequences). The first path is [], so for y = x the first
run reproduces the x-run.

### 6.4 Canonicity relative to choices

Fix G with a giant representation φ, strings x, y and a procedure `proc`. For g ∈ G write
ḡ = φ(g).

* (D) `proc(s, ·)` is a deterministic function of s and of the objects chosen.
* (E) For every g ∈ ISO_G(x, y) and every complete run c of `proc(x, ·)` there is a
  complete run c' of `proc(y, ·)` with the same trace whose result is isomorphic to the
  result of c via ḡ in S, i.e. R(y, c') = R(x, c)^ḡ up to relabelling of the Johnson
  cell's abstract set.
* (E+) For y = x and h ∈ Aut_G(x), the run c' of (E) is the componentwise image
  `apply_obj(c, h̄)` (`structure.py:57-71`).

(E) is [B] Def. 4.0.2(ii) for the category of tuples of structures; [B] Prop. 4.0.5
(eq. (23)) is the identity of Theorem 6.5. §11 proves (D) and (E) for every procedure,
and (E+) when no choice is a `Fixed` object.

**Lemma 6.6 (soundness of the trace checks).** If c' is the run of (E), then c' produces
exactly the trace of c, so it is never rejected. A y-run that is not of this form may be
accepted (for instance through a hash collision in `wl._summary`, `wl.py:152-161`); this is
harmless, because every piece that `branch` adds is a set of genuine isomorphisms. All
check values are counts, sizes, booleans, canonical colour data or tuples of these; the
hashes in traces are computed in one process, so equal data give equal hashes.

### 6.5 `branch`

`branch(Gw, x, y, proc, known_auts, recurse, tower)` (`main.py:620-687`) computes
Sx = proc(x, rc) (`main.py:633-634`), G1 = φ^{-1}(Aut(Sx) ∩ φ(G)) with its exact order
(`main.py:636-640`; the order is computed by Schreier–Sims, not read off the structure),
and for each run of `proc(y, ·)` the aligning permutation σ̄ (`main.py:658`), a lift σ
(`main.py:662`), and ISO_{G1}(x, y^{σ^{-1}})·σ (`main.py:666-673`).

**Theorem 6.5.** Assume (D), (E), the contract (C_iso) for the calls at `main.py:668`
(or that `recurse` returns ISO_{G1} exactly, §10.5), and that φ(G) ⊇ Alt(Γ). Then:
(a) ISO_G(x, y) = ⋃_c ISO_{G1}(x, y^{σ_c^{-1}})·σ_c, the union over the runs c that
complete and align;
(b) for x ≠ y, `branch` returns `None` iff ISO_G(x, y) = ∅, and otherwise a coset
contained in ISO_G(x, y);
(c) for x = y and with (E+) whenever pruning is on, `branch` returns a coset equal to
Aut_G(x).

*Proof.* (a) For a run c with result S_y, align returns σ̄_c ∈ Iso_S(Sx, S_y) ∩ φ(G) or
`None` iff this set is empty (Lemma 6.3; `need_even` is set iff φ(G) = Alt(Γ),
`main.py:641`). `lift` succeeds because σ̄_c ∈ φ(G), so the `RuntimeError` at
`main.py:665` is unreachable. Then G1·σ_c = φ^{-1}(Iso_S(Sx, S_y) ∩ φ(G)), and the term is
{g ∈ G1σ_c : x^g = y} ⊆ ISO_G(x, y). Conversely, for g ∈ ISO_G(x, y), (E) applied to the
recorded run gives a run c' with S_y = Sx^ḡ, so ḡ ∈ Iso_S(Sx, S_y) ∩ φ(G) and g lies in
the term of c'.
(b) The first non-empty term is returned (`main.py:674-675`); if all are empty the result
is `None` (`main.py:682-683`), which by (a) happens iff ISO_G(x, y) = ∅.
(c) By Lemma 6.4 the first run is the x-run; it is never pruned (`covered` is empty),
align returns the identity, and its piece is Aut_{G1}(x) with representative in it. So the
first piece's representative s_1 lies in the group L returned by `generated_subcoset`
(also when `known_auts` supplies the first piece, with s_1 = 1), and every element of
`H_gens` (known automorphisms, generators of the sub-results, piece representatives) lies
in L. A pruned run c' is `apply_obj(c, h̄)` for a processed c and a word h in `H_gens`
(`main.py:689-703`); by (E+) its result is R(x, c)^h̄, so its term is the term of c times h,
which lies in L. Every term is therefore contained in L·s_1 = L, L ≤ Aut_G(x) because all
its generators are automorphisms, and by (a) the union of the terms is Aut_G(x). ∎

**Lemma 6.7 (pruning and `Fixed` choices).** `branch` switches pruning off when a choice
of the x-run is a `Fixed` object (`main.py:651`). If the x-run makes no `Fixed` choice,
no run that completes consistently with its trace makes one. Hence pruning is applied only
to runs whose choices are vertices of Γ, tuples of them (with a kind string), or ideal
points (frozensets of such), for which (E+) holds (§11).

*Proof.* `Fixed` objects are created only by `select_min` when several candidates have the
minimal key (`soj.py:132-147`); without a tie `select_min` records ("inv", ("selmin", 1)),
with a tie it records ("choice", count). Every call of `select_min` is preceded, with no
other event in between, by a `check` whose tag occurs at no other place in the package: "upcc-cand"
(`soj.py:341`), "2b-disc" (`main.py:948`), "edl-disc" (`design.py:65`), "coh-disc1"
(`soj.py:704`), "coh-disc2" (`soj.py:713`), "coh-imp-acc" (`soj.py:740`, followed by
`soj.py:755` when no block is acceptable) and "coh-prim-blues" (`soj.py:787`). A run whose
trace agrees with the x-run up to that check is therefore at the same `select_min` call,
and if the x-run had no tie there, a tie in the other run produces a different event and a
`Mismatch`. ∎

Ties can occur only in case 2b, where colours are orbitals named by labels
(`main.py:941-946`); everywhere else the candidates are distinct WL colours whose key is
the colour itself (§7). `_covered` stops each orbit at 20000 elements; it only adds genuine
orbit elements, so this only reduces pruning.

## 7. Weisfeiler–Leman refinement and classical coherent configurations (`wl.py`, `cc.py`)

**Theorem 7.1.** `refine_structures([X0])` (`wl.py:204-206`) returns a k-ary coherent
configuration in the sense of [HBD] Def. 2.5 and 2.8 that refines X0 and has
Aut = Aut(X0). Its integer colour names are a function of the isomorphism type: for
σ ∈ Sym(Γ), refining X0^σ gives the σ-image of the refinement of X0 with the same names and
the same trace events.

*Proof (summary).* `to_configuration` (`wl.py:112-149`) is the functor F_2: the new
colour of a tuple is its equality pattern together with the colours of all its coordinate
substitutions τ: [k] → [k]; this is the coarsest configuration refining X0. One WL round
(`wl.py:164-201`) preserves the configuration axioms (it suffices to check permutations
and one idempotent, which generate the full transformation monoid). Each round refines the
previous partition; `ncolors` is exact (set by `to_configuration`), so the loop stops at
the first round without a split, which is the coherence condition. Names are ranks of
signatures in the sorted list of realised signatures, so they are equivariant. ∎

**Lemma 7.2.** For a homogeneous classical coherent configuration (constant diagonal),
every colour occurring off the diagonal has the same out-degree d ≥ 1 at every vertex, so
`disconnected_off_diagonal_colors` (`cc.py:130-138`) lists exactly the disconnected
constituents, `is_uniprimitive` (`cc.py:140-150`) is "primitive of rank ≥ 3"
([B] Def. 2.5.21), the components of a constituent have equal size ([HBD] Ex. 2.16(b))
and size ≥ 2.

**Lemma 7.3 (`canonical_keys`, `cc.py:203-244`).** For a coherent configuration whose
colours carry arbitrary names (case 2b), the keys are an isomorphism invariant of the
colours: an isomorphism of configurations maps each colour to a colour with the same key.
Two colours with the same key have the same out-degree. The loop terminates.

*Proof.* The initial key (is diagonal, out-degree, in-degree) and the structure constants
p^c_{ab} do not depend on the representative pair for a coherent configuration (orbital
configurations are coherent). Each refinement contains the previous key, so equal final
keys imply equal initial keys; the compressed names are ranks of canonical values
(Lemma 2.1). The number of distinct keys increases strictly until it stops. ∎

## 8. The Design Lemma and the Extended Design Lemma (`soj.py:227-276`, `design.py`)

**Theorem 8.1 (Design Lemma, [HBD] Prop. 5.1 with strict thresholds).** Let X be a
k-ary coherent configuration on n ≥ 2 points, 1/2 ≤ α < 1, and suppose that no set of
pairwise strong twins (transpositions in Aut(X)) has more than αn elements. Then
`design_lemma(X, α, ·)` does not return `None`: for some ℓ ≤ k−1 there is a tuple x of ℓ
distinct points such that (a) no class of X_x^(1) has more than αn points, or (b) ℓ ≤ k−2,
the class C of X_x^(1) with |C| > αn exists, and X_x^(2) takes at least two values on pairs
of distinct points of C.

*Proof (summary).* The code uses "dominant" as "> αn" (`soj.py:249`); with α ≥ 1/2 the
dominant class is unique. Suppose no distinct tuple of length ≤ k−1 works. Then for each
such x the dominant class C(x) exists, and by induction on ℓ, using that X_x^(2)[C(x)] is
a clique for |x| ≤ k−2 and [HBD] Lemma 5.2 (a colour class of more than half the points on
which a classical coherent configuration is a clique is a twin class), C(x) = C(∅) ∖
{x_1, …, x_ℓ}. Since |C(∅)| > αn, some
transposition (u v) of C(∅) is not in Aut(X); a shortest witness tuple has distinct entries
and contains u or v, which contradicts either "C(x) is one class" (it contains exactly one
of u, v) or "X_x^(2)[C(x)] is a clique" (it contains both). Repeated entries are never
needed, because a tuple with a repetition gives the same partitions as the tuple without
it. ∎ (With HBD's non-strict thresholds the statement fails at α = 1/2: two classes of
size n/2 and no other structure.)

`design_lemma` searches the levels ℓ = 0, 1, … and records ("dl", ℓ, |work_ℓ|) at each
level before returning (`soj.py:267`); its candidate set `work_ℓ` is a union of
Aut-orbits, so the choice is canonical relative to the chosen tuple.

**Lemma 8.2 (Extended Design Lemma, `design.py:36-81`).** Let X be the refinement of a
k-ary structure on Γ, |Γ| = m, satisfying the hypotheses of Theorem 8.1 with α = 2/3, and
let `base` be a structure on Γ. Then `extended_design_lemma` reaches neither fallback, and
returns one of:
(a) `base` individualised at the prefix and refined by X_x^(1), all classes of which have at
most (2/3)m points (`design.py:52-57`);
(b1) the dominant class C (|C| > (2/3)m) split into the components of the colour-minimal
disconnected constituent of Y = X_x^(2)[C], as c ≥ 2 interchangeable blocks of equal size
s ≥ 2 (`design.py:66-71`);
(b2) the output of `upcc_split_or_johnson(Y, (2/3)m/|C|, …)` (`design.py:81`).

*Proof.* `design.py:48` is unreachable by Theorem 8.1. In case (b), Y is a classical
coherent configuration ([HBD] Ex. 2.11–2.13), homogeneous (its diagonal is X_x^(1),
constant on C), not a clique (case (b)); if no constituent is disconnected it is primitive
(Lemma 7.2) of rank ≥ 3, i.e. uniprimitive, so `design.py:74` is unreachable. The
components in (b1) are as stated by Lemma 7.2. In (b2) the parameter β_0 = (2/3)m/|C| lies
in [2/3, 1) because (2/3)m < |C| ≤ m, as [HBD] Thm. 5.3 requires, and then the cells that
`upcc_split_or_johnson` creates inside C have at most β_0|C| = (2/3)m points, and a Johnson
cell has more than (2/3)m points ([B] Thm. 7.3.3(b) with α = 2/3). The threshold is an
exact `Fraction`. ∎

## 9. Split-or-Johnson (`soj.py`)

### 9.1 Setting and the two call sites

`upcc_split_or_johnson(cc, α_U, base, …)` (`soj.py:281-352`) is called from the Extended
Design Lemma (`design.py:81`, cc on V = C, α_U = (2/3)m/|C|) and from case 2b
(`main.py:957`, cc on V = pts, α_U = 2/3). In both cases:

* (U1) V is a single cell of `base`. EDL: C is a class of X_x^(1); the prefix points have
  their own classes (equality pattern), so C contains none of them and is a cell of the
  refined base; in case 3, C ⊆ Γ∖S because X_x^(1) separates S from Γ∖S (§10.7). Case 2b:
  pts is Φ minus the individualised points, one cell.
* (U2) cc is a uniprimitive classical coherent configuration: EDL by Lemma 8.2; case 2b
  because it is the orbital configuration of a transitive, not 2-transitive (§10.6) group
  H with no disconnected orbital (`main.py:949`). In particular cc is homogeneous and every
  off-diagonal colour is connected on V: every vertex has out-degree ≥ 1 in every
  off-diagonal colour (Lemma 7.2), so "not disconnected on its effective vertices"
  (`cc.py:130-138`) means connected on V. Lemma 9.12 uses only these two properties.
* bound = α_U·|V| is exact: (2/3)m in the EDL path, (2/3)|pts| in case 2b.
* Size facts under `Params.paper()`: m ≥ ℓ(n) ≥ 90 in every Johnson case (§10). EDL:
  |V| = |C| > (2/3)m ≥ 60 and bound ≥ 60. Case 2b: |Φ| > m/2 and at most 4 points are
  individualised (§10.6, CFSG), so |pts| > m/2 − 4 ≥ 41 and bound ≥ 28.

### 9.2 `upcc_split_or_johnson`

Steps: choose x ∈ V (`soj.py:294`); refine by the key of c(x, ·) (`soj.py:297-299`); visit
the key classes in the order of their keys (`soj.py:305-318`): a key class that contains
several colour classes is split into these colour classes as interchangeable blocks
(`soj.py:318`), except that if these colour classes have one point each, the procedure
returns `_thin_cycle_structure(...)` (`soj.py:315-317`, §9.2.1); take the unique cell V1
with |V1| > bound (`soj.py:319-323`); pick (beige, cyan) and call the bipartite procedure on
(V1, V2 = C_beige(x); R_cyan) with β = bound/|V1| (`soj.py:329-352`).

**Lemma 9.1.** (a) If the loop at `soj.py:309-318` ends without returning, every cell inside
V ∖ {x} is a single colour class C_i(x) = {v : c(x, v) = i}, and the colour classes of every
tied key class have at least 2 points each; in the EDL path no splitting and no return
happen (keys are the colours). (b) The `RuntimeError` at `soj.py:314` is unreachable. (c) If
V1 exists, it is a single colour class C_aqua(x), no other colour has the key of aqua, and
the `RuntimeError` at `soj.py:327` is unreachable. (d) The candidate set at `soj.py:329-339`
is non-empty, so the `fallback` at `soj.py:344` is unreachable.

*Proof.* (a) After refining by keys, cells inside V∖{x} lie in key classes (U1), and the
split separates the colour classes of each key class. A tied key class whose colour classes
have one point each ends the procedure at `soj.py:317` (all its colour classes have the same
size by (b)). In the EDL path cc is built without keys (`design.py:63`), so `cc.key` is the
identity (`cc.py:38-41`) and every key class contains one colour. (b) Colours with equal keys have
equal out-degree (Lemma 7.3), and the block of colour i has |C_i(x)| = out-degree of i
(homogeneous configuration). (c) V1 is a cell of size > bound ≥ |V|/2, so it lies in one
colour class; it is all of it, since a colour class with a tied key is a separate block and
an untied one is a whole cell. A second colour with the same key would have a disjoint
class of the same size > |V|/2. (d) aqua is symmetric: aqua and its paired colour have the
same valency, and two disjoint classes of size > |V|/2 cannot exist. By [HBD] Ex. B.7 the
graph {(u, w) : c(u, w) ≠ aqua} has diameter 2 in a uniprimitive configuration (cited).
For z ∈ V1, c(x, z) = aqua, so some y ∉ {x, z} has c(x, y) ≠ aqua and c(y, z) ≠ aqua,
hence c(z, y) ≠ aqua; both colours are off-diagonal since y ≠ x, z. So
(c(x, y), c(z, y)) ∈ cand. ∎

The split of tied key classes into colour classes is needed: if V were coloured by keys
only, then for the orbital configuration of a Paley tournament the two tied orbitals would
form one cell, `aqua` would be taken from an arbitrary element of that cell, and half of the
isomorphisms would be lost.

**Lemma 9.2 (the first bipartite call).** With V1 = C_aqua(x), V2 = C_beige(x),
adj = R_cyan ∩ (V1 × V2):
* V1 ∩ V2 = ∅, and V1 is a single cell of `base`;
* the graph is semiregular ([HBD] Ex. 2.17(b)), non-empty (it contains (z, y)) and not
  complete (the degree of y ∈ V2 is at most the valency of cyan^-, which is
  < (1 − α_U)|V| ≤ |V|/3 < |V1|), so every twin class of V1 has at most |V1|/2 points
  ([HBD] Ex. 5.4);
* |V2| ≤ |V| − 1 − |V1| < (1 − α_U)|V| ≤ α_U|V| = bound;
* β = bound/|V1| ∈ [2/3, 1), since bound ≥ (2/3)|V| ≥ (2/3)|V1| and |V1| > bound;
* |V1| > bound ≥ 28 (§9.1).

These are the hypotheses of [HBD] Prop. 5.7 (|V2| < β|V1|, 2/3 ≤ β < 1, twin classes
≤ 2|V1|/3).

### 9.2.1 The valency-1 exit (`_thin_cycle_structure`, `soj.py:355-379`)

If a key class of tied colours consists of colour classes of one point each,
`upcc_split_or_johnson` returns `_thin_cycle_structure(cc, x, cands, base, chooser, depth)`
(`soj.py:315-317`). Here `cands` lists the points of these colour classes, and `base` is the
structure built so far: x individualised, V refined by the keys of c(x, ·), and the tied key
classes visited earlier split into their colour classes. The procedure chooses y among
`sorted(cands)` (`soj.py:363`), sets c = c(x, y) (`soj.py:365`), computes for every u ∈ V
the list `nxt[u]` of the v ∈ V with c(u, v) = c (`soj.py:366-369`), walks u_0 = x and
u_j = the element of `nxt[u_{j−1}]` for j = 1, …, |V| − 1, gives u_j the value j
(`soj.py:370-378`), and refines `base` by this value, with `None` outside V (`soj.py:379`).
It makes no `check`. (Lemma 9.12 is stated here, before Lemmas 9.3–9.11, because it
concerns this exit.)

**Lemma 9.12.** Let cc be a homogeneous coherent configuration on V in which every
off-diagonal colour is connected on V, as at both call sites ((U2)).
(a) The pairs of a colour c of valency 1 are the pairs (u, f(u)) of a permutation f of V
without fixed points; the weakly connected components of its graph are the cycles of f;
hence f is one cycle of length |V|. Consequently, in `_thin_cycle_structure` every list `nxt[u]` has
exactly one element, u_j = f^j(x) for 0 ≤ j ≤ |V| − 1, these points are pairwise distinct,
the `RuntimeError`s at `soj.py:374` and `soj.py:377` are unreachable, and `place` is a
bijection from V onto {0, …, |V| − 1}.
(b) (Canonicity relative to x and y.) Let σ: V → V' be a bijection, cc' a configuration on
V' and π a bijection of colour names with c'(u^σ, v^σ) = π(c(u, v)) and
key'(π(i)) = key(i) for all u, v and all colours i (an isomorphism of configurations up to
colour names, as in case 2b, Lemma 7.3), and let base' = base^σ with the same keys, where
base is the structure passed to `upcc_split_or_johnson`. If the run on (cc, base) with first
choice x returns at `soj.py:317` with candidate list `cands`, then the run on (cc', base')
with first choice x' = x^σ returns at `soj.py:317` at the same key, has the same trace up to
and including the choice of y, and has the candidate set cands^σ. For y ∈ cands, y' = y^σ is
a candidate, and the structure returned for (x', y') is the σ-image of the structure
returned for (x, y), with the same keys.
(c) (Orbit pruning.) The choice objects of this exit are the vertices x and y. `apply_obj`
maps a vertex v to σ[v] = v^σ (`structure.py:61-62`). So for an automorphism h of the string
(the case y = x of `branch`, §6.4) the run of (b) with σ = h̄ is the run whose choice sequence
is the componentwise `apply_obj(·, h̄)` of the choice sequence of the run that chose the
vertices x and y, and (E+) holds for these choices.
The path to this exit makes no `Fixed` choice (it returns before `select_min` at
`soj.py:348`), so `branch` prunes such runs (`main.py:651`), which is correct by (E+) and
Theorem 6.5(c).
(d) (Kind.) The returned structure is discrete on V: every cell inside V is a singleton,
and its key differs from the key of every other cell. The cells outside V are those of the
input `base`, with extended keys.
(e) (When the exit is taken.) In the EDL path never. In case 2b exactly when H is regular
on pts; then H is cyclic of prime order p = |pts|, and its p − 1 off-diagonal orbitals have
valency 1 and one common key.

*Proof.* (a) In a homogeneous coherent configuration the out-degree of a colour i at u does
not depend on u (Lemma 7.2). The in-degree of i at v is the out-degree at v of the paired
colour i^- (c(u, v) = i iff c(v, u) = i^-), so it does not depend on v either. Counting the
pairs of colour i gives |V|·out(i) = |V|·in(i), so in(i) = out(i). If c has valency 1,
every u has exactly one v with c(u, v) = c, call it f(u), and every v has exactly one such
u; so f is an injective map of V to itself, a permutation. f(u) ≠ u because c is
off-diagonal and the diagonal colour does not occur off the diagonal. Every pair of colour c
is (u, f(u)), with u and f(u) in the same cycle of f, and the pairs (u, f(u)) of one cycle
connect it; so the weakly connected components of the graph of c (`cc.components`,
`cc.py:94-114`) are the cycles of f. The graph is connected on V by hypothesis, so f is one
cycle of length |V|. In `_thin_cycle_structure`, y ∈ cands is the only point of its colour
class {v ≠ x : c(x, v) = c(x, y)}, so c = c(x, y) has out-degree 1 at x, hence valency 1,
and it is off-diagonal because y ≠ x. So `nxt[u]` = [f(u)] for every u, and the walk gives
u_j = f^j(x). If f^j(x) = f^i(x) with 0 ≤ i < j ≤ |V| − 1, then f^{j−i}(x) = x with
0 < j − i < |V|, which contradicts the cycle length |V|. So neither `RuntimeError` is raised,
and `place` assigns the values 0, …, |V| − 1 to |V| distinct vertices, which are all of V.
The hypotheses are properties of the configuration computed in the same run (in case 2b:
H transitive by Lemma 10.6, which holds for every string that reaches case 2b, and no
disconnected orbital, tested at `main.py:949` in that run), so the argument also applies to
y-runs (§13.1).
(b) For v ∈ V, key'(c'(x', v^σ)) = key'(π(c(x, v))) = key(c(x, v)), so the refinement by
keys at `soj.py:297-299` is transported by σ, and for every key the colour classes of that key
class at x' are the σ-images of those at x (the class of colour i goes to the class of
colour π(i)). The loop at `soj.py:309-318` visits the same keys in the same order (it sorts
the key values, which are equal), finds the same numbers and sizes of colour classes, splits
the images of the same key classes (`split_by_blocks` is equivariant: the blocks are
transported as a set and all get the same key), and returns at the same key, with
cands' = cands^σ as a set. On this path `upcc_split_or_johnson` and `_thin_cycle_structure`
record only the events ("inv", ("upcc", |V|, number of colours)) (`soj.py:293`; π is a
bijection, so the numbers of colours agree), ("choice", |V|) for x and ("choice", |cands|)
for y, so the two traces agree. Let y' = y^σ and
e = c(x, y), the colour walked by the run for (x, y); the run for (x', y') walks
c'(x', y') = π(e). Then c'(u^σ, v^σ) = π(e) iff c(u, v) = e, so the successor maps f of e and
f' of π(e) satisfy f'(u^σ) = f(u)^σ, hence f'^j(x') = f^j(x)^σ and place'(v^σ) = place(v) for
all v ∈ V. `Structure.refine` is equivariant: the new key of a piece depends only on the old key,
the tag and the value. So the returned structure is the σ-image of the one for (x, y), with
the same keys. In case 2b the hypothesis of (b) holds for σ = ḡ, g ∈ ISO_G(x, y): ḡ maps
pts_x onto pts_y and the orbitals of H_x onto those of H_y, and the keys agree by Lemma 7.3
(§11, rows "aggregate" and "case 2b loop").
(c) As stated; the transport of the earlier choices of the run (the points of the case 2b
loop) is that of §11.
(d) The cells of `base` are either contained in V or disjoint from V: V is one cell of the
input structure (U1), and the steps of `upcc_split_or_johnson` before the exit only split
cells inside V. The refinement at `soj.py:379` splits each cell inside V into singletons
with the pairwise distinct values j, and leaves each cell outside V whole (value `None`). A
refined cell has the key (old key, tag, value), followed by its size (`structure.py:240`,
`structure.py:190`), so two cells have equal keys only if they come from cells with equal
keys and have equal values; the singletons inside V have distinct integer values, and the
cells outside V have the value `None`, which `canon` distinguishes from every integer.
(e) EDL path: Lemma 9.1(a). Case 2b: H is transitive on pts with connected orbital graphs,
hence primitive: if B were a block with 1 < |B| < |pts| and u ≠ w ∈ B, the orbital of (u, w)
would lie in the H-invariant relation "in the same block", and its graph would not be
connected. If an orbital O has valency 1, H_u fixes the unique w with (u, w) ∈ O. Then
H_u ≤ H_w, and |H_u| = |H_w| since H_w is conjugate to H_u, so H_u = H_w. The set
Fix(H_u) is a block: Fix(H_u)^h = Fix(H_{u^h}) for h ∈ H, and if z lies in Fix(H_u) and in
Fix(H_{u^h}), then H_u and H_{u^h} are contained in H_z and have its order, so
H_u = H_z = H_{u^h} and the two sets are equal. Fix(H_u) contains u and w ≠ u, so it is pts
by primitivity, i.e. H_u = 1 and H is regular. Conversely, if H is regular, every orbital has
valency |H_u| = 1. A regular primitive group has prime order: for K ≤ H, the sets
(u^K)^h = u^{Kh}, h ∈ H, are the images of the right cosets of K under the bijection
h ↦ u^h, so they form an H-invariant partition into blocks of size |K|; primitivity leaves
K = 1 or K = H, so H has no proper non-trivial subgroup and is cyclic of prime order
p = |pts|. Identify pts with Z_p by u^{h^i} ↦ i for a generator h; the orbitals are
O_d = {(i, i + d)}, d ≠ 0. For a ∈ Z_p^*, the map i ↦ ai sends O_d onto O_{ad}, so it is an
isomorphism of the configuration onto itself up to colour names, and Lemma 7.3 gives
key(O_d) = key(O_{ad}). Z_p^* is transitive on the non-zero residues, so the p − 1 ≥ 2
off-diagonal colours have one key, whose key class consists of p − 1 colour classes of one
point each: the exit is taken. If H is not regular, no orbital has valency 1, and the exit is
not taken. ∎

Whether F^Φ, or its stabiliser of d − 1 points at the end of the loop of §10.6, can be
regular of prime degree under the conditions of case 2b is not determined here. No statement
of this document depends on it.

### 9.3 `bipartite_split_or_johnson` (`soj.py:400-626`)

Let n1_orig be the size of V1 at the first call and bound = β·n1_orig (unchanged along the
recursion; exact).

**Lemma 9.3 (invariants of every call).** At every call:
(B1) |V1| ≤ n1_orig and n1_orig ≥ 29;
(B2) |V2| < bound, and |V2| is smaller than at the calling call;
(B3) the points of V2 (vertices of Γ or frozensets of them) have pairwise disjoint
underlying sets, disjoint from V1;
(B4) every twin class of V1 in the uncoloured graph (V1, V2; adj) has at most
|V1|/2 + 1 ≤ (2/3)n1_orig ≤ bound points;
(B5) V1 is a union of cells of `base`.

*Proof.* At the first call by Lemma 9.2. The chain |V1|/2 + 1 ≤ n1_orig/2 + 1 ≤
(2/3)n1_orig holds for n1_orig ≥ 6, and (2/3)n1_orig ≤ β·n1_orig since β ≥ 2/3. The
recursive calls are:
* `soj.py:530`: V1 = V1' and V2 replaced by the side chosen by `reduce_part2_by_color`,
  which checks (B4) for that side and returns a side by [HBD] Ex. 5.5 (V1' has no two
  twins, Lemma 9.4); the side is a proper subset of V2 (Lemma 9.6).
* `soj.py:677` (via `soj.py:543` and `soj.py:586`): the same, with |chosen| < |V2|
  (Lemma 9.8).
* `soj.py:608`: V2 ∖ C2 with C2 ≠ ∅. C1 lies in a twin class of (V1', C2) (the colour on
  C1 × C2 is constant and determines adjacency), of size > bound ≥ |V1'|/2 + 1, so by
  Ex. 5.5 the graph (V1', V2 ∖ C2) has no twin class of ≥ |V1'|/2 + 1 points.
* `soj.py:626`: (W1, W2) from Prop. 5.8 (Lemma 9.10): twin classes ≤ |W1|/2,
  |W2| ≤ |C2|/2 < |V2|, and |W1| > bound is checked at `soj.py:624`.
(B3) holds because V2 only loses points or is replaced by blocks of a partition of a subset
of V2. (B5): V1' is a cell, and W1 is made a cell (`soj.py:798`) or equals C1, a cell. ∎

The steps of one call:

* **Exit** (`soj.py:416-417`) if no cell inside V1 exceeds bound. Otherwise |V1| > bound
  ≥ 28.
* **`small_v1`** (`soj.py:421-423`): unreachable, since |V1| > 28 > 6 = small_v1. (This is
  where α = 2/3 needs m ≥ 90: from |V1| > (2/3)|V| and |V| ≥ |V1| + 2 alone one only gets
  |V1| ≥ 5.)
* **`small_v2`** (`soj.py:427-429`): disabled (small_v2 = 0 and |V2| ≥ 1).
* **Twins** (`soj.py:432-458`). Twin classes are computed in the vertex-coloured graph:
  key (cell of `base`, neighbourhood) (`soj.py:159-167`), [B] Def. 7.2.1. V1 is refined by
  (twin-class size, degree), and V1' is the unique cell larger than bound.

**Lemma 9.4.** (a) Every twin class meeting V1' lies in V1' and has size twsize(V1'), so
the `RuntimeError` at `soj.py:452` is unreachable. (b) If twsize ≥ 2, then
twsize ≤ |V1|/2 + 1 ≤ bound by (B4), so `soj.py:456` returns an equipartition of V1' into
c = |V1'|/twsize ≥ 2 blocks of size ≥ 2, and the `fallback` at `soj.py:457` is unreachable.
(c) If twsize = 1, no two vertices of V1' are twins in (V1', V2), coloured or not, because
V1' lies in one cell of `base`.

*Proof.* (a) Coloured twins lie in one cell of the old base and have equal size and degree,
so they lie in one refined cell. (b) Coloured twin classes are contained in uncoloured
ones. ∎

* **Degree** (`soj.py:459-470`). All of V1' has degree d1; the hypergraph is complemented
  if d1 > |V2|/2.

**Lemma 9.5.** d1 ≥ 2 after complementing; hence the `fallback`s at `soj.py:469` (d1 = 0)
and `soj.py:486` (d1 = 1) are unreachable. If the hypergraph H is complete, then either
d1 ≥ 2 and |V2| ≥ 2d1 + 1 (Johnson cell, `soj.py:477-481`), or |V2| = 2d1 (half split,
`soj.py:487-490`), and the half split yields two cells of |V1'|/2 ≤ bound points.

*Proof.* The neighbourhoods of the vertices of V1' are pairwise distinct (Lemma 9.4(c);
complementing preserves this), so |V1'| = |H| ≤ C(|V2|, d1). If d1 = 0 then |V1'| = |H| = 1,
but |V1'| > bound ≥ 28. If d1 = 1 then |V1'| = |H| ≤ |V2| < bound < |V1'| by (B2). After complementing,
d1 ≤ |V2|/2, so a complete H has |V2| ≥ 2d1. When |V2| = 2d1, every point of V2 lies in
C(2d1 − 1, d1 − 1) = |H|/2 edges, so the two cells of V1' have |V1'|/2 ≤ n1_orig/2 < bound
points. ∎

The half split is a regular step (one choice among |V2| points), not a fallback; J(2d1, d1)
is not a Johnson scheme in the sense of [HBD] §2.7 (r ≥ 2s + 1).

* **The d-ary structure** (`soj.py:493-517`), d = `params.arity(d1, |V1'|, |V2|)`
  (`soj.py:99-119`).

**Lemma 9.6 (arity; replaces HBD's choice d = 6⌈ℓ⌉).** Let s ≥ 1 be the value of `s` at the
end of the loop at `soj.py:113-115` (the loop keeps c = C(|V2|, s); the integer division is
exact). Then d = d1 if d1 ≤ 2s and d = 2s otherwise, 2 ≤ d ≤ d1, and the d-ary colouring
takes at least two values on tuples of distinct points. Hence the `fallback` at
`soj.py:516` is unreachable. Moreover no strong-twin class of the d-ary structure is all of
V2, so at `soj.py:521-531` both S and V2 ∖ S are non-empty and the recursive call is on a
proper subset of V2.

*Proof.* The loop stops when C(|V2|, s) > |V1'| or 2s ≥ d1. If d = d1, the colour of a
distinct tuple is 1 or 0 according as its set is an edge of H; H is neither empty nor
complete (the complete case returned earlier), so both values occur. If d = 2s < d1, then
C(|V2|, s) > |V1'|. Suppose all distinct d-tuples had the same count λ. Each edge has
d-subsets, so λ ≥ 1, and H is a 2s-(|V2|, d1, λ) design with |V1'| distinct blocks. Since
s < d1/2 ≤ |V2|/4, s ≤ min(2s/2, |V2| − d1), and Ray-Chaudhuri–Wilson ([HBD] Prop. 2.20,
cited) gives |V1'| ≥ C(|V2|, s), a contradiction. If one strong-twin class were all of V2,
every transposition of V2 would preserve the structure, which would then be constant on
distinct tuples. ∎

This argument needs neither |V2| > (6 log|V1|)^{3/2} nor HBD's s = 3⌈ℓ⌉: it uses only
C(|V2|, s) > |V1'|, which the code checks. When no such s with 2s < d1 exists, d = d1 and the
structure is H itself. So HBD's small-|V2| step, which cost |V2|! choices, is not needed and
is disabled.

* **Twin reduction on V2** (`soj.py:518-531`): `reduce_part2_by_color` never returns `None`
  ([HBD] Ex. 5.5, since V1' has no twins); so the `fallback` at `soj.py:527` is unreachable.
* **Design Lemma on V2** (`soj.py:534-543`).

**Lemma 9.7.** The `fallback` at `soj.py:537` is unreachable.

*Proof.* X = F_3(F_2(X0)) is a d-ary coherent configuration with Aut(X) = Aut(X0)
(Theorem 7.1), 2 ≤ d ≤ d1 ≤ |V2|/2, dl_alpha = 2/3 ∈ [1/2, 1), and at `soj.py:534` no
strong-twin class of X0 exceeds |V2|/2 ≤ (2/3)|V2| (`twin_classes_kary` computes the classes
of "(u v) ∈ Aut(X0)", `soj.py:194-222`). Theorem 8.1 applies. ∎

**Lemma 9.8 (case (a), `_split_by_coloring_of_v2`, `soj.py:647-678`).** If every colour class
of V2 has at most (2/3)|V2| points, the set S chosen at `soj.py:657-665` satisfies
|V2|/3 < |S| ≤ (2/3)|V2|, so both sides are non-empty; `reduce_part2_by_color` returns a side
(Ex. 5.5) and |chosen| < |V2|. Hence the `fallback`s at `soj.py:671` and `soj.py:675` are
unreachable. This applies at `soj.py:543` (Design Lemma case (a)) and at `soj.py:586`
(no class of size ≥ (2/3)|V2|).

*Proof.* If some class has size in (|V2|/3, (2/3)|V2|], it is S. Otherwise all classes have
at most |V2|/3 points, and the running union stops at the first size above |V2|/3, which is
at most (2/3)|V2|. ∎

**Lemma 9.9 (case (b), `soj.py:545-626`).** After classical WL on V1' ∪ V2 with V2 coloured
by the Design Lemma and C × C by Y (`soj.py:556-575`):
(a) at most one V2 class C2 has ≥ (2/3)|V2| points, and C2 ⊆ C;
(b) if the colour on C1 × C2 is constant, V2 ∖ C2 ≠ ∅, so the `fallback` at `soj.py:606` is
unreachable;
(c) X[C2] is not a clique, so the `fallback` at `soj.py:613` is unreachable;
(d) the hypotheses of [HBD] Prop. 5.8 hold at `soj.py:617`.

*Proof.* (a) Two disjoint classes of ≥ (2/3)|V2| points cannot exist; C2 refines the Design
Lemma colouring, whose classes other than C have < |V2|/3 points. (b) If C2 = V2, all of C1
(|C1| > bound ≥ 2) would have the same neighbourhood in V2, contradicting Lemma 9.4(c).
(c) X[C2] refines Y[C2]; if it were a clique, Y would be a clique on C2 with
|C2| ≥ (2/3)|V2| > |C|/2, contradicting [HBD] Ex. 2.15 (Y is not a clique). (d) The
configuration induced on C1 ∪ C2 is coherent (C1, C2 are vertex classes: V1' was a single
cell before `soj.py:581`, so the cells of V1' after it are WL classes); |C1| > bound > |V2| ≥
|C2|; the colouring is non-constant on C1 × C2 (`soj.py:602`) and on C2 × C2 (c). ∎

**Lemma 9.10 (`coherent_split_or_johnson`, `soj.py:683-799`).** Under the hypotheses of
[HBD] Prop. 5.8, the procedure returns either ("coloring", base') with every cell inside C1
of at most |C1|/2 points, or ("bipartite", (W1, W2, A'), base') with W1 ⊆ C1, |W1| ≥ |C1|/2,
W2 a subset of C2 or a set of blocks of a partition of C2, |W2| ≤ |C2|/2, no twin class of
W1 larger than |W1|/2, and W1 a cell of base'. The `fallback` at `soj.py:789` is unreachable,
and `select_min` at `soj.py:755` has candidates.

*Proof.* The imprimitive C1 case splits C1 into the components of a disconnected
constituent of the homogeneous coherent X[C1] (Lemma 7.2: ≥ 2 blocks of equal size ≥ 2,
hence ≤ |C1|/2). If X[C2] is imprimitive with blocks B_i: when no colour has degree
> |C1|/2 at w_0 (degrees do not depend on w, [HBD] Ex. 2.17(a)), marking w and colouring C1
by c(·, w) gives cells ≤ |C1|/2; an acceptable block is checked explicitly
(`soj.py:737-739`); otherwise the contracted graph of [HBD] Ex. 2.18 with a non-violet
colour (which exists: the colouring of C1 × C2 is not constant, so a second colour has
positive in-degree at every w ∈ C2, in particular at w_0) is semiregular, non-empty and not
complete (for each i the large twin class T_i is violet to all of B_i), so its twin classes
are ≤ |C1|/2 by Ex. 5.4, and there are ≤ |C2|/2 blocks. If X[C2] is primitive (the 2017
correction, [HBD] footnote 17), y is fixed, V1 = L_violet(y) with |V1| > |C1|/2, and a
colour of degree in (0, |C2|/2) exists because X[C2] is homogeneous with ≥ 2 off-diagonal
colours whose degrees sum to |C2| − 1; the twin bound is the end of the proof of
Prop. 5.8 (Ex. 5.4). ∎ (The twin bounds of the contraction and the 2017 outputs are taken
from [HBD]'s proof and are not re-checked by the code; see §16, point 4.)

**Lemma 9.11 (termination of Split-or-Johnson).** Every recursive call of the bipartite
procedure has a smaller |V2| (Lemma 9.3, (B2)), and `upcc_split_or_johnson` and
`coherent_split_or_johnson` do not recurse into themselves. `_thin_cycle_structure` makes
|V| − 1 steps and does not recurse. So the procedures terminate.

## 10. The Johnson case (`main.py:498-1033`, `certificates.py`)

Setting: G transitive on Ω, |Ω| = n, φ: G → Sym(Γ) with φ(G) ⊇ Alt(Γ), |Γ| = m ≥ ℓ(n) ≥ 90
(the Johnson case is entered only from `main.py:283-295` and `main.py:342-347`, which require
m ≥ ℓ(n)), standard blocks B_T (T ∈ binom(Γ, t)) with B_T^g = B_{T^ḡ}, m ≥ 2t + 1.
`johnson_case` (`main.py:498-503`) dispatches on primitivity; the primitive t = 1 branch
is dead (a primitive G with a giant Johnson quotient on singletons is a giant and was handled
at `main.py:273-281`).

### 10.1 Primitive case, t ≥ 2 (`main.py:590-617`)

Here Ω = binom(Γ, t) and φ is injective. `hypergraph_twin_classes` (`main.py:561-588`)
computes the classes of "(a b) preserves x", which are the strong-twin classes of the
t-ary structure X0 of `hypergraph_structure` (`main.py:544-559`), whose letters are
ordered by `canon` (Lemma 2.1; the letter sets of x and y agree by `main.py:239`).

* **Pullback** (`main.py:600-609`): if the largest twin class C of x has |C| > m/2, it is
  unique, and C ≠ Γ (otherwise Sym(Γ) would preserve x and `main.py:237` would have
  returned). The structure is {C, Γ∖C}.
* **EDL** (`main.py:611-617`): otherwise every twin class of x has ≤ m/2 ≤ (2/3)m points,
  t ≥ 2 and t ≤ m/2, so Lemma 8.2 applies to x. For a y-run see §13.1.

### 10.2 Local certificates (`certificates.py`)

k = k_paper(n) (`main.py:200-206`): since m ≥ ℓ(n) = 10·k_paper(n), the cap m − 2 does not
apply, k ≤ m/10, and k > max(8, 2 + log2 n) because ⌊log2 n⌋ + 3 > 2 + log2 n.

**Lemma 10.1 (`affected`, `certificates.py:190-207`).** If H ≤ G_A and H^A ⊇ Alt(A), then u is
affected ([B] Def. 10.1.4) iff |u^H| > 2|u^N|, N = ker(H → Sym(A)). `affected` is called only
after this hypothesis has been checked (`certificates.py:302-306`).

*Proof.* |u^N| = |u^H|/j with j = |H^A : (H_u)^A| ([B] Prop. 8.3.6). (H_u)^A ⊇ Alt(A) iff
j ≤ 2: an index-2 subgroup of Sym(A) is Alt(A), Alt(A) has no subgroup of index 2, and for
k ≤ 2 both sides hold. ∎

**Lemma 10.2 (`recompute` and the trajectory).** With H_0 = G_A (`certificates.py:175-185`),
W_0 = ∅ and W_i = W_{i−1} ∪ aff(H_{i−1}):
(a) W_i = aff(H_{i−1}) is H_{i−1}- and H_i-invariant, and W_{i−1} ⊊ W_i;
(b) `recompute` returns H_i = Aut^{W_i}_{H_{i−1}}(x) = Aut^{W_i}_{G_A}(x)
(`certificates.py:271-287`), by strong Luks reduction through N_i with `iso_window` on the
N_i-invariant window W_i; the identity coset gives a non-empty piece, so the `RuntimeError` at
`certificates.py:284` is unreachable;
(c) at a full exit K(A) = (H_r)_(Ω∖W) ≤ Aut_G(x) ([B] Claim 10.1.6), and at a non-full exit
Aut_G(x)_A^A ≤ M(A) ([B] Claim 10.1.7).

**Lemma 10.3.** The `fallback` at `certificates.py:324` is unreachable.

*Proof.* At a full exit the loop has found H_r^A ⊇ Alt(A) and aff(H_r) ⊆ W_r, so
Ω∖W_r is the set of points unaffected by ψ_A on H_r. [B] Thm. 8.3.5 (cited) applies to H_r
with k > max(8, 2 + log2 n_0), n_0 ≤ n the largest orbit of H_r, and gives
(H_r)_(Ω∖W)^A ⊇ Alt(A), which is the test at `certificates.py:320`. ([HBD] Prop. 4.4(a) states
this for transitive groups with ≥; the theorem needed is Babai's.) ∎

**Lemma 10.4.** `conjugate` (`certificates.py:233-269`) returns cert(x, A^ḡ) for
g ∈ Aut_G(x) (the trajectory is transported by conjugation), so the orbit shortcut in
`aggregate` (`main.py:759-781`) gives the same certificates as direct computation. `compare`
(`certificates.py:347-402`) returns Q = {π ∈ G : A^π̄ = A', W(A)^π = W(A'),
x(u) = x'(u^π) for u ∈ W(A)} as a coset H(W(A))·π_0, or `None` iff Q = ∅ ([HBD] (10); equal to
[B] Prop. 10.1.11 since Ω(A) ⊆ W(A) for 1 ≤ t < k). `ordered_label` (`certificates.py:404-413`)
is a complete invariant of the H(W(A))^A-orbit of an ordering of A. `Certificate.invariant`
(`certificates.py:146`) is equal for any two certificates with Q ≠ ∅.

### 10.3 `aggregate` and the case selection (`main.py:744-812`)

F = ⟨K(A) : A full⟩ ≤ Aut_G(x) is determined by x as a group, and for g ∈ ISO_G(x, y),
F(y) = g^{-1}F(x)g (Lemma 10.4 and canonicity of the certificates, [B] Thm. 10.1.3). S is the
support of φ(F); at most one φ(F)-orbit Φ exceeds m/2. The cases are those of [HBD] §6.2:
2a/2b if Φ exists (F^Φ ⊇ Alt(Φ) or not), 1 if |S| ≥ m/2 and no orbit exceeds m/2, 3 if
|S| < m/2. The values `case` and `sizes` are invariants, so `main.py:716-717` rejects only
non-isomorphic pairs.

### 10.4 Case 1 (`main.py:720-733`)

The cells are the φ(F)-orbits of length ≥ 2 with key ("orb", length), each of at most m/2
points, and the cell of fixed points, |Γ∖S| ≤ m/2. One run, no choices.

### 10.5 Case 2a and `top_action` (`main.py:815-902`)

G1 = φ^{-1}(Aut{Φ, Γ∖Φ} ∩ φ(G)) contains F (Φ is an F-orbit), and F^Φ ⊇ Alt(Φ), |Φ| > m/2.

**Lemma 10.5.** `top_action(jd, G1, Φ, F_gens, x, y)` returns ISO_{G1}(x, y) exactly, and the
`RuntimeError`s at `main.py:857`, `main.py:871` and the `assert` at `main.py:860` are
unreachable.

*Proof.* K = ker(G1 → Sym(Φ)); Δ = Ω(Φ) is G1-invariant. (i) Aut_top = Aut^Δ_{G1}(x): its
kernel part is CK = Aut^Δ_K(x) (non-empty, it contains 1, so the `assert` holds); F-lifts of
generators of Alt(Φ) exist because the image of Fw is F^Φ ⊇ Alt(Φ) (`main.py:854-858`); if
F^Φ = Sym(Φ) an F-lift of a transposition exists (`main.py:869-872`); if F^Φ = Alt(Φ) and
G1^Φ = Sym(Φ), the odd part is Aut^Δ_{Kσ_odd}(x), tried at `main.py:873-877` (σ_odd exists
because G1^Φ = Sym(Φ)). (ii) Composing an isomorphism with an element of F reduces its image
on Φ to 1 or a fixed transposition, so ISO^Δ_{G1}(x, y) ≠ ∅ iff ISO^Δ_K(x, y) ≠ ∅ or (Sym case)
ISO^Δ_{Kσ_odd}(x, y) ≠ ∅ (`main.py:881-895`). (iii) The Chain Rule with the windows Δ and Ω∖Δ
(`main.py:897-902`). ∎

### 10.6 Case 2b (`main.py:905-957`)

**Lemma 10.6.** The loop at `main.py:919-936` performs d − 1 individualisations, d the degree
of transitivity of F^Φ, and stops with H transitive on pts, not 2-transitive, with ≥ 2
orbitals. Hence the `fallback` at `main.py:939` is unreachable. By CFSG (cited, as in [HBD]
§6.2 Case 2b) d ≤ 5 for non-giants, so at most 4 points are individualised.

*Proof.* Invariant: H is transitive on pts and not a giant. It holds initially (case 2b).
If H is 2-transitive, H_v is transitive on pts∖{v}, and H_v is not a giant there, since
otherwise |H| = |pts|·|H_v| ≥ |pts|!/2. A 2-transitive group of degree ≤ 4 is a giant, so
under the invariant the exits "np_ ≤ 2" and "giant" never fire, and the loop ends with H
transitive, not 2-transitive, on ≥ 4 points, which has ≥ 2 orbitals. ∎

The orbitals are coloured by label-dependent indices (`main.py:941-944`); `canonical_keys`
(Lemma 7.3) gives invariant keys; ties in `select_min` are resolved by `Fixed` choices
(Lemma 6.7). If an orbital is disconnected, pts is split into its components (≥ 2 blocks of
equal size ≥ 2, Lemma 7.2), as interchangeable blocks (`main.py:949-953`). Otherwise the
configuration on pts is uniprimitive and `upcc_split_or_johnson` is called with α = 2/3
(`main.py:955-957`). If H is regular, it is cyclic of prime order p = |pts|, all p − 1
off-diagonal orbitals have valency 1 and one common key, and `upcc_split_or_johnson` returns
the discrete structure of `_thin_cycle_structure`, with one more choice (a vertex y among
p − 1 candidates). If H is not regular, no orbital has valency 1 and that exit is not taken
(Lemma 9.12(e)).

### 10.7 Case 3 (`main.py:960-1033`)

Classes of pairs (string, A), A ⊆ Γ∖S_string, |A| = k, are formed by `compare` inside buckets
of equal `invariant`, x's test sets first (`main.py:978-998`). "Q ≠ ∅" is an equivalence
relation (reflexive; Q(A' → A) = Q(A → A')^{-1}; Q composes), so the first matching
representative is the unique one, and for g ∈ ISO_G(x, y), (x, A) and (y, A^ḡ) are in the same
class. An ordering T of A gets the colour ("c", class, `ordered_label` of the transported
ordering of the representative); every other k-tuple gets ("other",) (`main.py:1001-1015`).

**Lemma 10.7.** For every string s (x or y) and the k-ary structure X0 built in `proc`
(`main.py:1018-1031`):
(a) no A ⊆ Γ∖S with |A| = k is full;
(b) every strong-twin class inside Γ∖S has fewer than k points;
(c) S is one strong-twin class and no point of S is a twin of a point of Γ∖S;
(d) the vertex colouring X_x^(1) of the refinement separates S from Γ∖S for every prefix x.
Hence the largest set of strong twins has max(|S|, k − 1) < m/2 ≤ (2/3)m points, Lemma 8.2
applies with α = 2/3, and the dominant class C of the Design Lemma lies in Γ∖S and is a single
cell of `base` (U1).

*Proof.* (a) A full A has K(A)^A ⊇ Alt(A), which moves every point of A (k ≥ 3), and
K(A) ≤ F, so A ⊆ S. (b) If A ⊆ C, C a twin class in Γ∖S, |A| = k, then all k! orderings of A
have one colour, so the representative A_0 of A's class has H(W(A_0))^{A_0} transitive on
orderings, i.e. equal to Sym(A_0), so A_0 is full; but A_0 is in the bucket of A, whose
`invariant` records non-fullness. (c) A transposition of two points of S maps tuples meeting S
to tuples meeting S, all coloured ("other",); for s ∈ S and r ∈ Γ∖S, a test set in Γ∖S
containing r (|Γ∖S| > m/2 ≥ k) has an ordering with a "c" colour, and its image under (r s)
meets S. (d) In the stable k-WL colouring c, c(v,…,v) = c(s,…,s) for v ∈ Γ∖S, s ∈ S would give,
replacing coordinates 1, …, k−1 one at a time, a tuple (b_1, …, b_{k−1}, s) with the colour of
an ordering (a_1, …, a_{k−1}, v) of a test set in Γ∖S, but the refined colour determines the
initial one, which is ("other",) for tuples containing s. The prefix colouring c(x, v, …, v)
determines c(v, …, v) by a coordinate map, since |x| ≤ k−1. ∎

## 11. Canonicity of every procedure (Theorem E)

Each `proc` passed to `branch` is a composition of steps of three types: (i) deterministic
computations whose output is an equivariant function of the input (sets, partitions,
colourings with canonical names, configurations); (ii) `check`s of quantities that are
invariant under the transport; (iii) choices among candidate sets that are transported to
the image candidate sets. By induction over the steps of a run, (D) and (E) follow (§6.4).
The steps whose equivariance is not immediate:

| procedure / step | why it is canonical |
|---|---|
| pullback (`main.py:604-607`) | twin classes are transported by ḡ; the largest class is unique (> m/2); the label tie-break at `main.py:598` is used only then |
| hypergraph structure (`main.py:544-559`) | letters ranked by `canon` over the common letter set |
| WL (`wl.py`) | Theorem 7.1: equal names on isomorphic inputs, same trace |
| `design_lemma` | `work_ℓ` is a union of Aut-orbits; the choice is transported |
| EDL (`design.py`) | C is the unique class > (2/3)m; `select_min` over distinct WL colours has no ties; the components form a canonical partition and get equal keys |
| UPCC, EDL path | keys are the WL colours, no ties; V1 unique; (beige, cyan) is the key-minimal pair, unique |
| UPCC, case 2b (`soj.py:305-318`) | keys are invariants (Lemma 7.3); the colour classes of a key class are transported as a set, and giving them equal keys makes the structure invariant under permutations of them; V1 is one colour class with a unique key (Lemma 9.1); tied (beige, cyan) pairs are chosen (`Fixed`) |
| UPCC, case 2b, valency-1 exit (`soj.py:315-317`, `soj.py:355-379`) | the run returns at the same key class for transported x; the candidates y are transported as a set; the walk along c(x, y) is transported, so the result for (x^ḡ, y^ḡ) is the image (Lemma 9.12(b)); x and y are vertices, so (E+) holds (Lemma 9.12(c)) |
| bipartite procedure | every decision depends on cells, neighbourhoods, coloured twin classes, degrees, sizes, d-ary counts, WL colours and the base keys, all transported; the unique dominant objects (V1', C, C2, C1) are unique by size; choices (prefix, half-split point, coherent point) are enumerated |
| Johnson cell labels (`soj.py:479`) | not canonical (they depend on the order of V2), but equal up to Sym([m']) for isomorphic inputs, which S allows (§6.2) |
| coherent procedure | WL colours, `select_min` without ties; w_0 = C2[0] is harmless because degrees do not depend on w ([HBD] Ex. 2.17(a)) |
| `aggregate` (cases 1, 2a, 2b, 3) | F, S, orbits, Φ are transported (§10.3); positions in sorted Φ are used only inside exact group computations and orbitals, whose names are replaced by keys |
| case 2b loop | individualised points are chosen among `sorted(pts)`; H is transported with the choices |
| case 3 colouring | class numbers are a joint naming for x and y within one call; col_y(T^ḡ) = col_x(T) (§10.7); the keys are sorted by `canon` |
| `split_by_blocks` (`soj.py:802-830`) | the blocks are a canonical partition; all blocks inside a cell get the same key |
| `individualize_until` (fallbacks only) | its `big[0]` is unique because every caller passes bound ≥ \|V\|/2 |

The tie-breaks that bypass the chooser (`dom[0]`, `max(..., key=len)`, `big[0]`,
`dominant_cell`, `w0`) select objects that are unique, as listed. (E+) holds whenever no choice
is `Fixed`: the choice objects are then vertices of Γ (among them x and y of the valency-1
exit), tuples (prefix, kind) of vertices or V2 points, or ideal points (frozensets of
vertices), and `apply_obj` transports them as the procedures do. In case 2b with tied keys
of valency ≥ 2, the choice in `select_min` can be `Fixed`; (E+) fails for such choices, and
pruning is off (Lemma 6.7). With tied keys of valency 1 the run ends in
`_thin_cycle_structure` before any `select_min` of `upcc_split_or_johnson`, makes no `Fixed`
choice, and pruning stays on (Lemma 9.12(c)).

## 12. Structure kinds (Theorem D)

Classes are unions of cells with equal key. "Other classes" means all classes except the
named one. The bounds use §9.1 (bound = (2/3)m in the EDL path, (2/3)|pts| in case 2b,
|pts| > m/2 − 4).

| procedure | outputs |
|---|---|
| pullback (`main.py:604-607`) | **P**: {C, Γ∖C} with m/2 < \|C\| < m |
| EDL, Design Lemma case (a) (`design.py:52-57`) | **C**: every class has ≤ (2/3)m points (all keys distinct) |
| EDL, case (b1) (`design.py:66-71`) | **E**: one class C, \|C\| > (2/3)m, of c ≥ 2 cells of equal size s ≥ 2; the other classes total < m/3 points |
| UPCC, valency-1 exit (`soj.py:315-317`, `_thin_cycle_structure` at `soj.py:355-379`) | case 2b only, when H is regular of prime degree (Lemma 9.12(e)). **C**: discrete on pts, every cell inside pts is a singleton with its own key (Lemma 9.12(d)); the other classes are rest (< m/2 points) and the ≤ 4 singletons of the case 2b loop, so every class has fewer than m/2 points |
| UPCC, no dominant cell (`soj.py:322-323`) | EDL path: **C**. Case 2b: every class inside pts has ≤ (2/3)\|pts\| points, except possibly one key class of tied colours, which consists of c ≥ 2 cells of equal size s ≥ 2, s the common valency of the tied colours (a tied key class of valency 1 returns at `soj.py:317`, Lemma 9.1(a)); the other classes: rest (< m/2) and singletons |
| bipartite exits with no dominant cell (`soj.py:416-417`, `441-442`, `589-591`, `624-625`) and the coherent colourings (`soj.py:727-733`, `776-779`) | inside V1 every cell ≤ bound, and every class inside V1 is a single cell; EDL path: **C**; case 2b: every class inside pts has ≤ (2/3)\|pts\| points, because the tied key classes lie in pts ∖ ({x} ∪ V1), which has fewer than \|pts\|/3 points |
| half split (`soj.py:487-490`) | V1' into two cells of \|V1'\|/2 ≤ bound; EDL path **C**; case 2b as for the bipartite exits |
| twin equipartition (`soj.py:454-456`) | **E**: V1' (> bound) into c ≥ 2 twin classes of size s ≥ 2 |
| coherent, C1 imprimitive (`soj.py:705-711`) | **E**: C1 (> bound) into c ≥ 2 components of size s ≥ 2 |
| Johnson cell (`soj.py:477-481`) | **J**: a cell J = V1' carrying J(m', t'), t' ≥ 2, m' ≥ 2t'+1, \|J\| = C(m', t') > bound, so C(m', 2) ≤ m and m' < 1 + √(2m); \|J\| > (2/3)m in the EDL path, \|J\| > (2/3)\|pts\| in case 2b |
| case 1 (`main.py:721-732`) | **O**: cells = φ(F)-orbits of length ≥ 2 (each ≤ m/2) keyed by length, and the fixed points (≤ m/2); a class is the union of the orbits of one length, so it has ≤ (2/3)m points or is a class > (2/3)m of c ≥ 2 blocks of size ≥ 2 |
| case 2a (`main.py:821-825`) | **A**: {Φ, Γ∖Φ}, \|Φ\| > m/2, F^Φ ⊇ Alt(Φ); `recurse` = `top_action` |
| case 2b, imprimitive (`main.py:949-953`) | **E'**: pts (\|pts\| > m/2 − 4) into ≥ 2 blocks of equal size ≥ 2; other classes: rest (< m/2), d−1 ≤ 4 singletons |
| case 2b, uniprimitive | the UPCC outputs above, inside pts; outside pts: rest and ≤ 4 singletons |
| case 3 | the EDL outputs, with base {S, Γ∖S}, \|S\| < m/2; S is a class of < m/2 points (< m/3 in case (b1)) |

In the EDL path the named class of kinds E and J has more than (2/3)m points (it is C, V1' or
C1, each larger than bound = (2/3)m), so all other classes together have fewer than m/3
points.

*The classes at the bipartite exits.* The cell V1 = C_aqua(x) of the first bipartite call
has a key that no other cell has (Lemma 9.1(c)). Along a run that ends at one of the exits
of the rows "bipartite exits", "coherent colourings" and "half split", the cells inside V1
arise from V1 only by `refine` and `mark` (`soj.py:438`, `soj.py:490`, `soj.py:581`,
`soj.py:732`, `soj.py:778`, `soj.py:798`); `split_by_blocks` inside V1 occurs only at
`soj.py:456` and `soj.py:710`, and both are followed by a return of kind E (the second
through `soj.py:620-621`). A refinement gives the pieces of one cell different keys, and
pieces of cells with different keys keep different keys, so every class inside V1 is a
single cell. The tied key classes of case 2b consist of colour classes of colours other
than aqua, so they lie in pts ∖ ({x} ∪ V1); the marks of V2 points (`soj.py:489`,
`soj.py:541`, `soj.py:730`, `soj.py:748`, `soj.py:769`) split only cells of
C_beige(x) ⊆ pts ∖ ({x} ∪ V1), because the points of every V2 of the recursion have
underlying sets inside the first V2 (proof of Lemma 9.3, (B3)). Since |V1| > bound = (2/3)|pts|,
pts ∖ V1 has fewer than |pts|/3 points.

*Case 2b measured against m.* Every output of `case_2b_structure` is of kind C, E or J with
the bounds of the EDL path: either every class has at most (2/3)m points, or exactly one
class has more, and that class consists of c ≥ 2 cells of equal size s ≥ 2 or is a Johnson
cell; the other classes then have fewer than m/3 points in total, because the classes
partition Γ. Proof: two classes of more than (2/3)m points cannot exist. Outside pts the
classes are rest (< m/2 points) and singletons. Inside pts, by the rows above: at the
valency-1 exit, the bipartite exits, the coherent colourings and the half split, every class
has at most (2/3)|pts| ≤ (2/3)m points. At the UPCC exit without a dominant cell the classes
inside pts are {x}, untied colour classes (single cells of at most bound ≤ (2/3)m points)
and tied key classes, each of c ≥ 2 cells of equal size s ≥ 2 (Lemma 9.1(a)). The twin
equipartition, the C1 components and the imprimitive split of pts make one class of c ≥ 2
cells of equal size s ≥ 2 (V1', C1 or pts: all blocks get one key, which no other cell
has); the Johnson cell is one class; every other class inside pts is a single cell of at
most bound ≤ (2/3)m points or lies in pts ∖ V1, which has fewer than |pts|/3 points. So if a class has more than (2/3)m points,
it is the named class of one of these rows.

Every output passed to the recursion on G1 (all kinds except A, which is handled by
`top_action`) has two cells with different keys, or is an equipartition of Γ into c ≥ 2 blocks
of size s ≥ 2: the pullback has C ≠ Γ; Design Lemma case (a) with an empty prefix has a
non-constant colouring, and with a non-empty prefix an individualised point; every other output
individualises a point (x in UPCC, the prefix, the case 2b points) or splits a class into
blocks of size ≥ 2. In both situations Aut(S) ⊉ Alt(Γ) (Alt(Γ) is transitive, and primitive for
m ≥ 3), so Aut(S) ∩ φ(G) < φ(G) (§14).

## 13. Every fallback and every guard is unreachable (Theorem B)

### 13.1 y-runs

`proc(y, ·)` is run for strings y that need not be isomorphic to x, and with choices other
than the recorded ones. The arguments below use only properties of the string being processed
that hold for every string reaching the code, with one exception: the twin bound of the
primitive EDL (§10.1) holds for x by `main.py:601` but not necessarily for y. For a y-run
there, the code of `proc2` before `design_lemma` emits a fixed sequence of events (one
"hyp", one "F2", one "WL" per round), so a y-run that reaches `design_lemma` without
`Mismatch` is at the position of the x-run's call; at each level ℓ it records
("dl", ℓ, |work_ℓ|) before deciding, so it either raises `Mismatch` or returns at the level
where the x-run returned. It never returns `None`. `Mismatch` is caught by `enumerate_runs`
(`structure.py:147-153`). No other exception can escape from a y-run.

### 13.2 Table

| site | condition | why unreachable |
|---|---|---|
| `main.py:333` | primitive quotient of degree ≥ 25 above the bound not recognised | Lemma 4.3 |
| `main.py:939` | case 2b stabiliser still 2-transitive | Lemma 10.6 |
| `design.py:48` | Design Lemma returns `None` | Theorem 8.1 with Lemma 8.2: primitive (§10.1, §13.1), case 3 (Lemma 10.7) |
| `design.py:74` | configuration on C not uniprimitive | Lemma 8.2 |
| `certificates.py:324` | certificate of fullness not full | Lemma 10.3 (Thm. 8.3.5) |
| `soj.py:344` | no (beige, cyan) pair | Lemma 9.1(d) |
| `soj.py:457` | twin class larger than the bound | Lemma 9.4(b) |
| `soj.py:469` | d1 = 0 | Lemma 9.5 |
| `soj.py:486` | complete hypergraph with d1 = 1 | Lemma 9.5 |
| `soj.py:516` | d-ary structure constant | Lemma 9.6 (arity rule, Ray-Chaudhuri–Wilson) |
| `soj.py:527` | `reduce_part2_by_color` fails | [HBD] Ex. 5.5, Lemma 9.4(c) |
| `soj.py:537` | Design Lemma on V2 fails | Lemma 9.7 |
| `soj.py:606` | C2 = V2 with constant C1 × C2 colour | Lemma 9.9(b) |
| `soj.py:613` | X[C2] a clique | Lemma 9.9(c) |
| `soj.py:671` | `reduce_part2_by_color` fails | Lemma 9.8 |
| `soj.py:675` | no proper part of V2 | Lemma 9.8 |
| `soj.py:789` | no blue colour | Lemma 9.10 |
| `soj.py:421-423` (not a `fallback`) | `small_v1` step | \|V1\| > 28 (§9.3) |
| `soj.py:427-429` (not a `fallback`) | `small_v2` step | disabled: small_v2 = 0 < \|V2\| |
| `main.py:277` (`assert`) | tower trivial for a giant | Lemma 5.4 |
| `main.py:485` (`RuntimeError`) | coset representative not liftable | §4.2 |
| `main.py:665` (`RuntimeError`) | aligning permutation not in φ(G) | Theorem 6.5(a) |
| `main.py:857`, `main.py:871` (`RuntimeError`), `main.py:860` (`assert`) | `top_action` | Lemma 10.5 |
| `certificates.py:284` (`RuntimeError`) | Aut^W(x) empty | Lemma 10.2(b) |
| `certificates.py:106` (`ValueError`) | fast φ on a non-Johnson element | Lemma 4.4 (equivariant blocks) |
| `soj.py:314`, `soj.py:327`, `soj.py:452` (`RuntimeError`) | tied valencies, dominant cell, twin blocks | Lemmas 9.1(b), 9.1(c), 9.4(a) |
| `soj.py:374`, `soj.py:377` (`RuntimeError`) | colour of valency 1 not a permutation; its walk from x returns to a visited vertex before \|V\| steps | Lemma 9.12(a): the colour is a permutation of V that is one cycle of length \|V\| |
| `soj.py:143` (`ValueError`) | `select_min` without candidates | every caller has a non-empty list (`soj.py:342`, `main.py:949`, `design.py:66`, `soj.py:705`, `soj.py:714`, Lemma 9.10 for `soj.py:755`, `soj.py:788`) |
| `structure.py:94` (`ValueError`) | `choose([])` | every candidate list is non-empty: V, pts, V2, C2, `work_ℓ` (`soj.py:268`), acceptable blocks (`soj.py:741`), ties (≥ 2), the candidates y of `_thin_cycle_structure` (`soj.py:363`; one point for each of the ≥ 2 colours of the tied key class) |
| `structure.py:296` (`assert`) | Johnson cell without data | Lemma 6.1 (I2) |
| `structure.py:71` (`TypeError`) | untransportable choice object | pruning is on only without `Fixed` objects, and all other choice objects are ints (among them x and y of the valency-1 exit), tuples, strings or frozensets (§11) |
| `johnson.py:384`, `391`, `394`, `397` (`ValueError`) | `johnson_phi` on a non-induced permutation | Lemma 4.4 |
| `group.py:138` (`RuntimeError`) | residue fixing all points | Lemma 3.1 |
| `group.py:349` (`ValueError`) | blocks of an intransitive group | called only for transitive groups (`main.py:299`, `main.py:302`) |
| `action.py:128`, `action.py:143` (`ValueError`) | lift of a non-element of G^Δ | arguments are elements of the restricted group (§4.2) |
| `action.py:156`, `action.py:167`, `action.py:214`, `action.py:220`, `action.py:273`, `action.py:284` (`ValueError`) | `GroupWithAction` misuse | Lemma 3.3, Lemma 3.5; `intersect_image` is called only with a giant image (`main.py:636`, `certificates.py:180`) |
| `main.py:230` (`ValueError`) | tower on a different domain | Lemma 5.5 |

### 13.3 Input validation (raised only on invalid input)

`main.py:105` (unknown `k_rule`), `main.py:234-235` (string length), `group.py:51`
(generator of wrong degree), `graph.py:28` (bad edge), `graph.py:91` (only for pair
permutations not induced by a vertex permutation; `C.rep` ∈ S^{(2)}(V) is always induced),
`graph.py:155` (empty file), `canon.py:48` (letters outside (P3) passed directly to
`Solver.iso`; see §16, point 3).

## 14. Termination (Theorem C)

**Lemma 14.1.** Every recursive `iso` call made while computing `iso(G, x, y)` has smaller
μ = (n, |G|, [x ≠ y]) in the lexicographic order:

| call | decrease |
|---|---|
| `main.py:246` | same G, x = y |
| `main.py:424` | degree \|Δ\| < n (G intransitive) |
| `main.py:452` | \|N\| = \|G\|/\|Gbar\| < \|G\| (G transitive on m ≥ 2 blocks) |
| `main.py:487` | \|NG\| = \|G\|/[Gbar : ker] < \|G\| (the class action is non-trivial, Lemma 4.2(c)) |
| `main.py:668` | \|G1\| < \|G\| = \|φ(G)\|·\|ker φ\|, because Aut(Sx) ∩ φ(G) < φ(G) (last paragraph of §12); in case 2a the call is `recurse` (`main.py:670`), whose calls are the rows below |
| `main.py:859`, `875`, `884`, `890` | order ≤ \|K\| < \|G1\| ≤ \|G\| (G1^Φ ⊇ Alt(Φ) ≠ 1), degree ≤ n |
| `main.py:899` | degree \|Ω∖Ω(Φ)\| < n |
| `certificates.py:279`, `certificates.py:392` | order ≤ \|N\| ≤ \|G_A\| < \|G\| (A is a proper non-empty subset of Γ and φ(G) ⊇ Alt(Γ) is transitive), degree ≤ n |

`iso_window` restricts to the window, which does not increase the degree or the order.

**Lemma 14.2.** Every loop terminates: `enumerate_runs` (finite tree, Lemma 6.4); the WL loop
(at most n^k rounds); `canonical_keys` (Lemma 7.3); `minimal_block_system` (the number of
blocks at least halves); Schreier–Sims (finitely many strong generators); the certificate loop
(W strictly grows); the case 2b loop (pts shrinks); `individualize_until` (a cell shrinks per
step); the BFS loops of `aggregate` and `_covered` (finite sets); Split-or-Johnson, including
the walk of `_thin_cycle_structure` (Lemma 9.11); `iroot` (hi − lo decreases) and the loops of
`_cameron_candidates` (a finite range of s; C(2t + 1, t) and C(k, t) grow without bound)
(Lemma 4.6).

Theorem C follows by induction on μ (well-founded on pairs of non-negative integers and a bit).

## 15. Entry points (`main.py:1077-1087`, `graph.py`)

* **`string_isomorphism`**: Lemma 2.2 and Theorem A.
* **`graph_isomorphism`** (`graph.py:96-124`). For v ≥ 3, a vertex permutation π maps graph 1
  to graph 2 (with colours) iff the induced π̂ on pairs maps x_1 to x_2, where x_i({u, w}) =
  (edge bit, sorted pair of colours) (`graph.py:70-79`). The colour condition on all pairs forces
  c_1(u) = c_2(u^π) for v ≥ 3: if c_1(u) ≠ c_2(u^π) for some u, then for any two other
  vertices w, w' the three pair conditions are contradictory. The action on pairs is faithful
  for v ≥ 3, so ISO_{S^{(2)}(V)}(x_1, x_2) corresponds bijectively to the isomorphisms, and
  `vertex_perm` recovers π from π̂ (the images of two pairs through u share exactly u^π). The
  cases v ≤ 2 are handled directly (`graph.py:107-115`). For v ≥ 3, if only one of the two
  graphs is coloured, the strings have letters of different types and the answer is `None`.
* **`graph_automorphisms`** (`graph.py:127-142`): generators of Aut_{S^{(2)}(V)}(x) mapped to
  vertex permutations, and its order, which equals |Aut(X)| by faithfulness.
* The shared `GraphInstance` (`graph.py:61-68`) keeps the caches of S^{(2)}(V) between calls;
  every cached value is a function of the group and the string, so reuse is correct. A cached
  `LocalCertificates` object refers to the solver that created it (`certificates.py:164-165`),
  so Theorem B for a later `Params.paper()` solver assumes the cache was filled by a
  `Params.paper()` solver (otherwise an exact fallback of the earlier solver may run instead of
  raising).

## 16. Open points

1. **Python limits.** `RecursionError` (default limit 1000 frames: the Solver recursion and the
   bipartite recursion, whose depth can reach |V2|) and `MemoryError` are not excluded.
2. **Correctness for other parameters.** The correctness argument uses the thresholds only to
   exclude the fallbacks. With `allow_fallbacks=True` each fallback is itself canonical relative
   to its choices, so Theorems A and C should extend to `Params.small_scale()`; this is not
   checked line by line here (for example the half split with an arity cap, or Lemma 9.3 with
   |V1| ≤ 6).
3. **Letters for `Solver.iso` and colours for the graph functions.** `Solver.iso` called directly
   with letters outside (P3) (for example floats) raises `TypeError` at `main.py:549` once a
   primitive Johnson case is reached. The graph functions sort colour pairs with `canon`
   (`graph.py:76`) and, for v ≤ 2, with Python's ordering (`graph.py:109-110`), so vertex colours
   must be `canon`-encodable and, for v ≤ 2, mutually comparable. `string_isomorphism` has no
   such restriction.
4. **Cited results.** Used without proof: Maróti's classification of large primitive groups and
   the bound d ≤ 5 on the transitivity of non-giants (both rely on CFSG); [B] Thm. 8.3.5 and
   Cor. 8.3.7; Ray-Chaudhuri–Wilson ([HBD] Prop. 2.20); Fisher's inequality; [HBD] Lemma 5.2,
   Ex. 2.11–2.18, 5.4–5.6 and B.7; the twin bounds of [HBD] Prop. 5.8 for the contraction and
   the 2017 outputs (Lemma 9.10), which the code does not check at run time; if they failed,
   `soj.py:457` would raise.
5. **Cameron fibre system (running time; handled in PROOF.md, §9.3).** `cameron_reduction`
   does not add the coordinate fibre system to the tower ([HBD] App. A.1 does). The call on NG
   computes some maximal block system above the top level. Correctness is not affected; whether
   this system is always a coordinate fibre system (so that the next step is the Johnson case of
   one coordinate) is not proved here. The time proof does not use it.
6. **Case 2b bounds are relative to |pts| (running time; handled in PROOF.md, §9.4).** In
   case 2b the Johnson cell satisfies only |J| > (2/3)|pts| > m/3 − 8/3, not |J| > (2/3)m, the
   class rest can have up to m/2 points, and the equipartition of pts may have |pts| ≤ (2/3)m
   (§12). Measured against m, every case 2b output is still of kind C, E or J (§12, "Case 2b
   measured against m"); this uses the valency-1 exit, which is of kind C (Lemma 9.12(d)).
7. **Recursion of `top_action` on Ω∖Ω(Φ) (running time; handled in PROOF.md, §9.5).** The
   window Ω∖Ω(Φ) can exceed (2/3)n; its Chain-Rule children are smaller. This is not a
   correctness gap.
