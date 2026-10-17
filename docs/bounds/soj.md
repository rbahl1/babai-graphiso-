# Operation and choice-count bounds for `babai_gi/soj.py` and `babai_gi/design.py`

The arity rule of `SOJParams.arity` is d = d1 or 2s, where s is the least integer with
C(n2, s) > |V1'|.  `SOJParams.small_v2 = 0` by default, so step 2 never runs, and the half
split is a regular step.

Paper parameters: `SOJParams()` gives

* `small_v1 = 6`;
* `small_v2 = 0`, so `small_v2_bound` returns 0;
* `max_dim = None`;
* `dl_alpha = 2/3` (a Fraction);
* `allow_fallbacks = False`.

The alpha of the callers is `Params.alpha = Fraction(2, 3)`.

Sections:

* §0: conventions, including the counting lemma used here (Lemma 1.1');
* §1: one subsection per function, in source order;
* §2: the run-level results:
  * (A) own work of one run;
  * (B) choice counts and the asymptotic bound;
  * output guarantees;
  * the invariants of the chain of calls for alpha = 2/3;
* §3: final table;
* §4: profile dicts.

---------------------------------------------------------------------------------------------------

## 0. Conventions

### 0.1 Sizes and the cost of data operations

**Object size σ(x).**
* An atom (int, bool, None, float, Fraction) has σ = 1.
* A string has σ = 1 + its length.
* A tuple, list or frozenset has σ = 1 + the sum of σ over its elements.

**Hashing and comparing.** Hashing x costs ≤ σ(x).  Comparing x with y (==, <) costs
≤ σ(x) + σ(y).  This is the specification's "one per element it touches, recursively";
a comparison of two ints costs 1.

**Dict and set operations.** A dict/set lookup, insertion or deletion with key x costs
η(x) := 1 + 3σ(x): 1, plus hashing (σ(x)), plus one comparison with a stored key (≤ 2σ(x)).
For an int key, η = 4.

**Built-ins.**
* Constructing a set, frozenset or dict from L elements costs Σ η(e).  Constructing a list
  or tuple costs L.
* Set algebra or set comparison costs Σ η over the elements of both operands (for int
  elements: 4(|A| + |B|)).
* `sorted` of L items whose comparison costs ≤ c costs L⌈lg L⌉·c + 2L + 1, plus the calls
  of its key function.  Here ⌈lg L⌉ := ⌈log2 L⌉, and it is 0 for L ≤ 1.
* `x in list` costs one comparison per element touched.
* `len`, `isinstance`, `iter` and `next` cost 1 each.
* `max`/`min` over L items cost 2L, plus the key calls.

**Iteration.** Iterating over a list or tuple costs only the FOR_ITER instruction.
Iterating over a range, set, frozenset, dict or dict view costs one extra per element
consumed.  An itertools generator costs the length of each tuple it produces.

**Other atoms of the model.**
* `math.comb(n, k)` costs k.
* Constructing or operating on a Fraction, and comparing an int with a Fraction, costs 1.
* `STATS[key] += 1` costs ≤ 64 beyond its instructions, plus ≤ 64 when the key is an
  f-string.

**Thresholds.** Every threshold test compares integers (for example `2 * d1 > n2`,
`n2 < 3 * len(groups[k]) <= 2 * n2`, `2 * max_twin_class(...) <= n1 + 2`) or an int with a
Fraction (`len(c) > bound`, with bound = alpha·|V| or beta·n1_orig, and `len(vs) > alpha * n`
in `design_lemma`); both are exact.  The only float computation, in `small_v2_bound` (L96),
is not executed under `SOJParams()`, which returns at L94-95.

**Callee symbols.**
* Callees in other modules appear as symbols `C[module.Qualname](parameters)`.
* `Ck(σ) := C[structure.Chooser.check](invariant of size σ)` and
  `Cc(L) := C[structure.Chooser.choose](L candidates)`, each meaning the maximum over
  `RecordingChooser` and `ReplayChooser`.
* `C_hk(σ) := C[structure._hk](σ)`.
* When a callback is passed to a callee (a lambda or nested function, or the closure `c`
  of `wl.KStructure.prefix_pair_coloring`), the callee symbol **excludes** the callback's
  own cost.  The callback's cost is added separately, times the number of calls, which is
  read off the callee's code:
  * `Structure.refine` calls f once per vertex of Γ, i.e. M times (structure.py L235-238);
  * `ClassicalCC.__init__` calls its colour function N² times (cc.py L27);
  * `wl.classical_wl` calls `vertex_color` N times and `pair_color` N(N-1) times
    (wl.py L215-220).
* The exception is `chooser.check`, which wl's procedures receive as their `trace`; it is
  charged inside the wl symbols.
* Calls of functions of soj/design are replaced by their bounds from §1.

**Fallbacks.** `errors.fallback(False, ...)` raises.  So **in a call that returns
normally, no code after a `fallback(...)` executes**, and it is not charged, apart from
the instructions themselves, which are included in `outside'`.

### 0.2 Instruction profiles and the counting lemma used here (Lemma 1.1')

**Attribution in `opcount`.** For loops and comprehensions, CPython 3.13 gives `FOR_ITER`
the source position of the *iterable*.  `opcount.profile` attributes `FOR_ITER` to its
loop, so that it is counted once per element consumed plus once per entry, and it
attributes position-less instructions to the innermost cycle that contains them.  When a
loop body is long, CPython emits `EXTENDED_ARG; FOR_ITER`, and the loop's `JUMP_BACKWARD`
targets the `EXTENDED_ARG`; this `EXTENDED_ARG` is attributed to the loop as well.  For
example, the inner loop L244 of `design_lemma` is (cycle 74, entry 0).  PROOF.md, Lemma 1.1
proves these rules in general.  In opcount's profile the two-clause comprehension at upcc
L318 is one loop; for it, "iterations" counts the elements of both clauses (PROOF.md,
Lemma 1.1).

**The counting lemma used in this document.** It is purely control-flow based and does
not depend on opcount's attribution.  For a code object, every `JUMP_BACKWARD*`
instruction J with target t defines the region [t, off(J)].
* Group the regions by target.  A group is one loop, or one generator clause of a
  comprehension.  Its span is [t, max off(J)].
* Each instruction belongs to the innermost group span that contains its offset; its count
  goes to `cycle'` of that group.  An instruction in no span counts in `outside'`.

§4.2 lists the numbers outside' and cycle'.  `tests/test_soj_regions.py` recomputes them for
every code object of soj and design (and of `johnson.iroot`), compares them with the table of
§4.2, and checks the following properties of every code object:
* (R1) the only instructions that transfer control to a smaller offset are the
  `JUMP_BACKWARD*` instructions;
* (R2) the group spans are laminar (nested or disjoint);
* (R3) every backward jump lies in the span of its own group and in no span nested in it;
* (R4) no jump from outside a span lands inside the span other than at its target t;
* (R5) every exception handler lies after the code it protects and outside every span, and
  is a straight run of instructions ending in `RERAISE`;
* (R6) soj.py, design.py and `johnson.iroot` contain no `try`, `with`, `yield` or `await`.

**Lemma 1.1'.** In one call, every instruction in no span executes at most once.  An
instruction whose innermost group is L executes at most P_L times, where P_L is the number
of passes of L: the number of executions of L's target instruction.  For a `for` loop or a
comprehension clause, P_L = (elements consumed) + (entries).  Hence

    own instructions ≤ outside' + Σ_L cycle'_L · P_L.

*Proof.* By (R6), the only generators among these code objects are generator expressions,
and no handler comes from a `try` or `with` statement.  By (R5), every exception handler
ends in `RERAISE`, so once a handler runs, the call ends with an exception; a call that
returns normally runs no handler.  In a generator expression a handler runs at most once,
when the generator is closed, and it lies in no span.  A suspended generator expression resumes at the instruction after its `YIELD_VALUE`.
So, by (R1), a second execution of an instruction i requires a backward jump J with
t ≤ off(i) ≤ off(J).  If i lies in no span, no such J exists.

Otherwise, let L be i's innermost group.  By (R4), control enters span(L) only at t.
During one stay inside span(L), the only backward jumps whose region contains i are those
of L:
* a backward jump of a group whose span contains span(L) does not lie in span(L), by (R2)
  and (R3);
* a backward jump of a group nested in span(L) has its region inside that group's span,
  which does not contain i;
* a backward jump of a group whose span is disjoint from span(L) is not executed during
  the stay.

So i executes at most once per pass of L, i.e. once per execution of t. ∎

For a generator expression, the same argument gives cost ≤ `outside'` + `cycle'`·(e + 1),
where e is the number of elements consumed.  For a lambda the cost is `outside'`
(= total) per call.

**Relation to the opcount numbers.** Both profiles count every instruction of a code object
once, so outside' + Σ cycle' equals opcount's outside + Σ (cycle + entry), the number of
instructions; `tests/test_soj_regions.py` checks this.  The two profiles attribute the
instructions to loops differently.

The proofs below use the region numbers (§4.2).  §4.1 lists the numbers of
`opcount.generate()`, as SPEC requires.  The bounds below are derived from the region
numbers alone and do not depend on opcount's attribution.

### 0.3 Parameters and standing hypotheses

* **(S1)** A `Structure` passed as `base` has cells that are pairwise disjoint, non-empty
  and cover range(M), where M = base.m.  So K_c := len(base.cells) ≤ M and Σ|c| = M.  Every
  structure built by `structure.py` from a partition has this property, and so does every
  base built by the callers in `main.py`.
* **K** = an upper bound on σ(key) for every key of every Structure handled in the run
  (parameter of the Structure callees; it is bounded in §2.A.4).
* **Points.** A point of V2 is an int (a vertex of Γ) or a frozenset of points (an ideal
  point).  For a point p:
  * u(p) is the size of its underlying set U(p) = flatten(p);
  * Σ2 := Σ_{p∈V2} σ(p) at a bipartite level;
  * U2 := |⋃_{p∈V2} U(p)|.
* **(U)**, for `upcc_split_or_johnson(cc, alpha, base, ...)`:
  * cc is a uniprimitive coherent configuration on V = cc.vertices, a list of distinct ints
    in range(M), with n := |V|;
  * cc.c[i][j] and cc.key(colour) are ints;
  * alpha is a Fraction with 2/3 ≤ alpha < 1;
  * V is a single cell of base.

  Both callers satisfy this.
  * EDL (design.py L63, L81): the colours are values of `X.prefix_pair_coloring`, which are
    WL ints; `cc.key` is the identity; alpha' = alpha·m/|C| ∈ [2/3, 1).
  * Case 2b (main.py, `case_2b_structure`): orbital names are ints and the keys come from
    `canonical_keys` (ints); alpha = 2/3.
* **(H61)** n = |V| ≥ 61.  Under the paper parameters the EDL call has
  |C| > (2/3)·X.n ≥ (2/3)·90 = 60, because m ≥ ell(n) ≥ 90.  For case 2b, PROOF.md §10 shows that
  only bound ≥ 6, n1_orig ≥ 6 and the final simplification at Y = log m ≥ log 90 are used, which hold for |pts| ≥ 41.  Consequence: bound = alpha·n ≥ 40.67.
* **Y := log2 n**, at the actual size of V; the final statements replace it by log2 m,
  using monotonicity.  **δ := log2(3/2) = 0.5849625**.
* Every statement in §2 is about **one run**: one execution with a fixed sequence of
  chooser answers that returns normally (fallbacks excluded).

---------------------------------------------------------------------------------------------------

## 1. Per-function bounds (source order)

Notation for each function:
* "opcount" gives `opcount.generate()`'s (outside, [(line, cycle, entry)]);
* "region" gives the region profile (outside', [(loop line, cycle')]) of §0.2;
* P_L is the number of passes of loop L, i.e. elements consumed plus entries (Lemma 1.1').

### soj.SOJParams.__init__  (L70)

* Profiles: opcount (15, []); region (15, []).
* Builtin: one Fraction construction, cost 1.
* **Bound: 16.**

### soj.SOJParams.small_scale  (L80; used only by presets and tests)

* Profiles: opcount (22, []); region (22, []).
* L_o := len(overrides).  A call that returns has L_o ≤ 5, because any other keyword makes
  `__init__` raise TypeError.
* Builtins:
  * `dict(...)`: 4 string-keyed insertions, each with η ≤ 1 + 3·16 = 49 (names have
    ≤ 15 characters);
  * `kw.update`: 49·L_o;
  * `cls(**kw)`: binds 4 + L_o keywords, each ≤ 49;
  * `__init__`: 16.
* **Bound: 22 + 196 + 49L_o + 49(4 + L_o) + 16 = 430 + 98·L_o ≤ 920.**

### soj.SOJParams.small_v2_bound  (L90)

* Profiles: opcount (26, []); region (26, []).
* Builtins: `max`, `log`, `int` (≤ 4 together).
* **Bound: 30.**
* Under `SOJParams()` it returns 0 (L94-95), so step 2 of bipartite never runs: n2 ≥ 1 > 0.

### soj.SOJParams.arity(d1, n1p, n2)  (L99)

* Profiles: opcount (31, [(113, 23, 9)]); region (40, [(114, 23)]).
* The region is the body together with the bottom test of the `while` (target L114).

**Loop L113.** Write s* for the final value of s.
* Invariant: c = C(n2, s).  It holds initially, and C(n2, s)·(n2 - s) = (s + 1)·C(n2, s+1),
  so the floor division is exact.
* Each iteration increments s and runs only while C(n2, s) ≤ n1p and 2s < d1.
* Hence s* = min{ s ≥ 1 : C(n2, s) > n1p or 2s ≥ d1 }, the loop makes s* - 1 iterations,
  and P ≤ s*.
* Integer arithmetic on c costs 1 per instruction.

**Builtins.** `min` (2) and `max(2, min(d, d1))` (4).

**Bound: 40 + 23·s* + 6 ≤ 46 + 23·s*, with s* ≤ max(1, ⌈d1/2⌉).  Closed form: ≤ 69 + 12·d1.**

**Lemma AR (output).** Assume d1 ≥ 2 and max_dim = None.
* (i) 2 ≤ d ≤ min(d1, 2s*).
* (ii) If s* ≥ 2, then C(n2, s* - 1) ≤ n1p and 2(s* - 1) < d1.
* (iii) If d < d1, then d = 2s* and C(n2, s*) > n1p.

*Proof.*
* (i) Write d' for the value of d at L116: d' = d1 if d1 ≤ 2s*, and d' = 2s* otherwise.
  So d' ≤ 2s*, and the return value max(2, min(d', d1)) lies in [2, min(d1, 2s*)].
* (ii) The loop went from s* - 1 to s*, so its condition held at s* - 1.
* (iii) d < d1 forces d1 > 2s*.  Then the loop did not stop because of 2s ≥ d1, so it
  stopped because C(n2, s*) > n1p. ∎

### soj.flatten(obj)  (L122, recursive)

* Profiles: opcount (23, [(127, 9, 0)]); region (23, [(127, 9)]).

**Leaf.** For an int: ≤ 23 instructions, plus `isinstance` (1), plus `frozenset([obj])`
(4): **28**.

**Internal node.** For a node q with r children and |U(q)| = U:
* the loop L127 has P = r + 1 passes;
* builtins: `isinstance` (1) and `set()` (1);
* `out |= flatten(o_i)` costs 4(|out_{i-1}| + |U(o_i)|) = 4|out_i| ≤ 4U, by disjointness
  (Lemma P below), so the r updates cost ≤ 4rU;
* `frozenset(out)` costs 4U.

Own cost: ≤ 34 + 9r + 4rU + 4U.

**Recursion.** One invocation per node of the tree of p.  By Lemma P every internal node
has ≥ 2 children, so a point with u leaves has ≤ u - 1 internal nodes and ≤ 2u - 1 nodes,
with Σ r = (#nodes) - 1 ≤ 2u - 2.  Summing:

    F(u) ≤ 28u + 34(u-1) + 9(2u-2) + 4u(2u-2) + 4u(u-1) = 12u² + 68u - 52.

**Bound: F(u(p)) ≤ 12·u(p)² + 68·u(p).**

**Lemma P (shape of points).** Fallbacks are excluded.  Let V be the vertex set of the
`upcc` call.  Then, in every bipartite and coherent call of a run:
* every point of V2 (and of W2) is an int in V, or a frozenset of ≥ 2 points;
* the underlying sets of the points of one V2 are pairwise disjoint;
* they are disjoint from V1, and contained in V.

*Proof.*
* `upcc` passes V2 ⊆ V \ (V1 ∪ {x}) (L349).
* Every recursive call passes a sub-list of the current V2 (L530, L608, L677), or a W2
  built by `coherent`.
* In `coherent`, W2 (L750, L794) is a sub-list of points, except in the contraction case
  (L756).  There W2 = [frozenset of the points of a block] for the components B of a
  disconnected colour of X2 = X.induced(C2).
* X is induced by the stable 2-WL configuration on V1' ∪ V2 on a union of vertex classes,
  and C2 is a WL vertex class.  So X2 is a homogeneous coherent configuration
  (CORRECTNESS.md §7; HBD Ex. 2.11-2.13).
* Every off-diagonal colour that occurs in X2 then has constant out-valency ≥ 1, so every
  component has ≥ 2 vertices, and the components partition C2.
* The points of a block are distinct, because their underlying sets are disjoint and
  non-empty by induction.  So each new point has ≥ 2 children with disjoint underlying sets.
* V1 only shrinks (V1' ⊆ V1, W1 ⊆ C1 ⊆ V1'). ∎

### soj.select_min(cands, key, chooser)  (L132)

* Profiles: opcount (42, [(136, 28, 0), (147, 7, 9)]); region (51, [(136, 28), (147, 7)]).
* Parameters:
  * L = len(cands) ≥ 1; for L = 0 the function raises ValueError (an error exit);
  * c_key is the cost of one call of `key`;
  * σ_k bounds σ(key(c)).

**Loop L136.** P = L + 1.  Per element:
* `key(c)`: c_key;
* `_hk`: C_hk(σ_k);
* two comparisons of canonical encodings.  canon maps every node to ("tag", payload), so
  σ(canon(x)) ≤ 4σ(x), and the two comparisons cost ≤ 2·8σ_k;
* `append`: 1.

**Loop L147.** Runs only when ties exist.  P = L' + 1, where L' = len(best) ≤ L; each
element costs one `Fixed(b)` (C_Fix := C[structure.Fixed.__init__], plus 1 for the
allocation).

**Bound:**

    SM(L; c_key, σ_k) ≤ 88 + 38L + L·(c_key + C_hk(σ_k) + 16σ_k + C_Fix) + Ck(9) + Cc(L)

Only one of `Ck(9)` and `Cc(L')` is actually incurred.

**Choice.** A choice is made only if the minimal key is attained ≥ 2 times; it has
L' ≤ L candidates.  canon is injective (canon.py), so a tie means equal key values.

### soj.dominant_cell(base, inside, bound)  (L150)

* Profiles: opcount (21, [(151, 17, 11)]); region (32, [(151, 17)]).
* Loop L151: P = K_c + 1 (one element per cell).
* Per cell:
  * `c <= inside` costs 4(|c| + s), where s = |inside|.  CPython short-cuts when
    |c| > |inside|, but the full cost is charged;
  * `len` costs 1.
* `len(big)`: 1.
* **Bound: 32 + 17(K_c + 1) + 4M + 4K_c·s + K_c + 1 = 50 + 18K_c + 4M + 4K_c·s ≤
  DC(s) := 50 + 22M + 4M·s.**

### soj.twin_classes_bipartite(V1, adj, cell_of)  (L159)

* Profiles: opcount (13, [(164, 23, 0)]); region (13, [(164, 23)]).
* Assumption: adj[v] ⊆ V2 is a frozenset of points, for v ∈ V1.  Write
  s_v := Σ_{p∈adj[v]} σ(p) ≤ Σ2.
* Loop L164: P = n1 + 1.  Per v:
  * `adj[v]`: 4;
  * `cell_of[v]`: 4;
  * `setdefault` with key (int, adj[v]), of size 3 + s_v: η = 10 + 3s_v;
  * `append`: 1.
* `list(groups.values())`: ≤ 2n1 + 1.
* **Bound: 37 + 44·n1 + 3·Σ_v s_v ≤ TCB := 37 + 44n1 + 3n1Σ2.**
* Without `cell_of` the key is smaller, so the same bound holds.

### soj.max_twin_class(V1, adj)  (L170)

* Profiles: opcount (16, []); region (16, []).
* Genexpr L171: opcount total 19; region (10, [(171, 9)]).
* Costs:
  * `twin_classes_bipartite` (without `cell_of`): TCB;
  * the genexpr over g ≤ n1 classes: 10 + 9(g + 1), plus `len` (g);
  * `max`: 2g.
* **Bound: 16 + TCB + 19 + 12n1 ≤ MTC := 72 + 56n1 + 3n1Σ2**, or 16 if V1 is empty.

### soj.restricted_adj(V1, adj, V2sub)  (L174)

* Profiles: opcount (13, [(176, 8, 9)]); region (22, [(176, 8)]).
* Let W be a set of points that contains V2sub and every adj[v], and let
  Σ2 := Σ_{p∈W} σ(p).  Then Σ_{p∈W} η(p) = |W| + 3Σ2 ≤ 4Σ2.
* `frozenset(V2sub)`: ≤ 4Σ2.
* Loop L176: P = n1 + 1.  Per v:
  * `adj[v]`: 4;
  * `adj[v] & S`: ≤ 8Σ2;
  * insertion: 4.
* **Bound: RA := 30 + 16n1 + 4Σ2 + 8n1Σ2.**

### soj.reduce_part2_by_color(V1, adj, C1, C2)  (L179)

* Profiles: opcount (11, [(186, 21, 4)]); region (15, [(186, 21)]).
* Loop L186: 2 elements, P = 3.
* Per iteration: `not C` (1), RA, MTC (on the restricted adjacency, whose values lie in
  C ⊆ C1 ∪ C2), and the integer test `2 * max_twin_class(...) <= n1 + 2` (instructions
  only).
* **Bound: 15 + 63 + 2(1 + RA + MTC) = RP := 284 + 144n1 + 8Σ2 + 22n1Σ2**, with Σ2 taken
  over C1 ∪ C2 ⊇ the values of adj.

### soj.twin_classes_kary(nV, d, colors)  (L194)

* Profiles:
  * opcount (56, [(205,6,11), (206,12,0), (207,36,0), (211,33,4), (220,15,0)]);
  * region (67, [(205,6), (206,12), (207,40), (211,33), (220,15)]);
  * `find`: opcount (4, [(199,19,6)]), region (10, [(200,19)]);
  * genexpr L213: region (11, [(213,18)]).
* n := nV, T := n^d.  Assumption: len(colors) = T, ints.  This holds at the only call site,
  L518.

**Loops.**

| loop | ranges over | P (passes) | per-pass builtins |
|---|---|---|---|
| L205 (dict comp) | the T tuples | T + 1 | insertion of a d-tuple: η = 3d + 4 |
| L206 | range(n) | n + 1 | + 1 (range) |
| L207 | range(u+1, n), entered once per u | Σ_u (n - u) = n(n-1)/2 + n | + 1 (range) |
| L211 | the T tuples, entered at most once per (u, v) pass that does not `continue`, so ≤ n(n-1)/2 entries | ≤ n(n-1)/2·(T + 1) | ≤ 24d + 33 (see below) |
| L220 | range(n) | n + 1 | + 1 (range), `setdefault` 4, `append` 1 |

The per-pass cost of L211 is ≤ 24d + 33:
* `u in t or v in t`: ≤ 2d;
* the genexpr: 11 + 18(d + 1);
* `tuple(...)`: d;
* `index[s]`: 3d + 4.

**find.** The while loop makes ≤ n - 1 iterations, since a parent chain has distinct
elements.  So find costs ≤ 10 + 19n.  There are ≤ 4 calls per (u, v) pair and n in L220,
2n² - n calls in total, costing ≤ (2n² - n)(19n + 10) ≤ 38n³ + n².

**Other builtins.**
* `list(range(n))`: 2n;
* `product(...)` with `list(...)`: (d + 1)T;
* `list(groups.values())`: 2n + 1.

**Bound** (sum of the above):

    TCK ≤ (12d+33)·n^(d+2) + (4d+11)·n^d + 38n³ + 38n² + 31n + 101 ≤ (13d + 76)·n^(d+2)

The closed form needs n ≥ 2 and d ≥ 2.

**Output.** The classes of the strong-twin relation.
* u ~ v iff the transposition (u v) preserves the colouring; this is an equivalence
  relation (Obs. 2.4.9).
* The union-find merges only true twins.  Every pair of true twins u < v is either already
  merged when (u, v) is examined, or passes the test.

### soj.design_lemma(X, alpha, chooser, objs)  (L227)

* Profiles:
  * opcount (47, [(242,29,48), (244,74,0), (247,13,0), (249,13,8), (257,13,2), (258,23,2),
    (269,18,11)]);
  * region (109, [(242,29), (244,81), (247,13), (249,13), (257,15), (258,23), (269,18)]);
  * genexpr L269: region (11, [(269,9)]).
* Parameters: n = X.n, k = X.k ≥ 1.  ℓ* is the length at which the loop stops: the
  returned prefix length, or k - 1 if it returns None.
* Counts:
  * P := Σ_{ell=0}^{ℓ*} (n)_ell is the number of tuples examined;
  * W := |work| at ℓ*;
  * σ_pt := max σ(objs[i]).
* Assumptions: X.prefix_vertex_coloring(tup) returns a list of n ints, and
  X.prefix_pair_coloring returns a function with int values (wl.py L53-70).

**Loops and passes.**

| loop | ranges over | P (passes) |
|---|---|---|
| L242 | range(0, k), but stops at ℓ* (the return at L268-274) | ≤ ℓ* + 2 (+ ℓ* + 1 for range) |
| L244 | permutations(range(n), ell): (n)_ell tuples of length ell | P + ℓ* + 1 (+ Σ ell·(n)_ell ≤ ℓ*·P for itertools) |
| L247 | enumerate(col1), a list of length n | n + 1 per tuple; each pass: `setdefault` 4 + `append` 1 |
| L249 | groups.values(), at most n groups | ≤ n + 1 per tuple; each pass: values 1 + `len` 1 |
| L257 | C = dom[0], ≤ n elements | ≤ n + 1 per tuple |
| L258 | C, entered ≤ |C| times per tuple | ≤ n² + n per tuple; each pass: `c2(u, v)` C_c + `seen.add` 4 + `len` 1 |
| L269 | work, W elements | W + 1; each element: genexpr 11 + 9(ℓ* + 1) + `tuple` ℓ* |

**Callees.**
* per tuple: C_pvc := C[wl.KStructure.prefix_vertex_coloring](n, k), and (when
  ell < k-1 and dom is non-empty) C_ppc := C[wl.KStructure.prefix_pair_coloring](k);
* ≤ n² calls of C_c := C[wl.KStructure.prefix_pair_coloring.<c@67>](k) per tuple;
* one Ck(6) per ell;
* once: Cc(W), `cands.index` (≤ W comparisons of candidate tuples, of size
  ≤ 4 + ℓ*·σ_pt), and C_pvc again;
* STATS: ≤ 64 + 128.

Per tuple:

    C_pvc + C_ppc + n²·C_c + 28n² + 72n + 43

Total:

    DL(n,k) ≤ 460 + 2n + 112ℓ* + P·(28n² + 72n + 124 + ℓ* + C_pvc + C_ppc + n²C_c)
                + W·(46 + 10ℓ* + 2ℓ*σ_pt) + (ℓ*+1)·Ck(6) + Cc(W) + C_pvc

**Closed form** (n ≥ 2, using ℓ* ≤ k - 1, P ≤ Σ_{ell<k} n^ell ≤ 2n^(k-1), W ≤ (n)_ℓ* ≤ n^(k-1)):

    DL(n,k) ≤ 2n^(k-1)·(28n² + 72n + 123 + k + C_pvc + C_ppc + n²C_c)
              + n^(k-1)·(36 + 10k + 2kσ_pt) + 460 + 2n + 112k + k·Ck(6) + Cc(n^(k-1)) + C_pvc

**Choice facts.**
* Exactly one `chooser.choose`, with W ≤ (n)_ℓ* ≤ n^(k-1) candidates, unless the
  function returns None.
* If the returned kind is 'b', then ℓ* ≤ k - 2, because 'b' entries are appended only when
  ell < k - 1 (L253).
* At most 2n^(k-1) tuples are examined.

### soj.upcc_split_or_johnson(cc, alpha, base, chooser, params, depth)  (L281)

* Profiles:
  * opcount (269, [(298,13,9), (306,27,0), (309,68,0), (317,7,9), (318,12,12), (331,23,0),
    (335,32,0), (349,15,8), (350,17,9)]);
  * region (302, [(298,13), (306,27), (309,82), (317,7), (318,8), (318,4), (331,23), (335,32),
    (349,15), (350,17)]);
  * nested code: lambda L299 (8), lambda L340 (20), lambda L348 (16), genexpr L313 (10, [9]),
    genexpr L326 (11, [14]), genexpr L350 (11, [23]).
* Hypotheses: (U) and (S1).
* Parameters:
  * n = |V|;
  * V1 = the dominant cell, if it exists;
  * e := |{y ∈ V : row[y] ∉ {aqua} ∪ diag}| ≤ n - |V1|;
  * Lc := |cand|, the number of candidate pairs;
  * g_k = |by_key| ≤ n - 1;
  * g_t = the number of key classes with ≥ 2 colours, g_t ≤ (n-1)/2;
  * q = the number of colours of a tied key class, S = its number of vertices;
  * n2 = |V2| ≤ e.

**Facts used for the loop bounds.**
* Every v ∈ V1 has row colour aqua (checked at L326).  So the y with beige ∉ {aqua} ∪ diag
  lie outside V1: e ≤ n - |V1|.
* Every candidate pair (beige, cyan) comes from such a y and some z ∈ V1, so
  Lc ≤ e·|V1| ≤ n²/4.
* V2 consists of such y, so n2 ≤ e.
* When V1 exists, |V1| > alpha·n ≥ 2n/3, so e < n/3.

| line | loop / call | passes or count | builtins / callees per pass |
|---|---|---|---|
| L291 | `frozenset(V)` | | 4n |
| L292 | STATS | | 64 |
| L293 | `chooser.check` | | Ck(8) + 1 |
| L294 | `sorted(V)` and `chooser.choose` | | n⌈lg n⌉ + 2n + 1, Cc(n) |
| L295 | `cc.pos[x]` | | 4 |
| L297 | `base.individualize(x, ("upcc-x", depth))` | | C_ind := C[structure.Structure.individualize](M, K_c, K; σ_tag = 9) |
| L298 | dict comp over V | n + 1 | `pos` 4, `cc.key` C_key := C[cc.ClassicalCC.key], insertion 4 |
| L299 | `base.refine(lambda@299, ("upcc-col", depth))` | f called M times, 12 each | C_ref := C[structure.Structure.refine](M, K_c+1, K+13; σ_f = 1, σ_tag = 11) |
| L306 | loop over V | n + 1 | `coloring[v]` 4, two `setdefault` 4 + 4, `pos` 4, `append` 1 |
| L309 | loop over `sorted(by_key, key=_hk)` | g_k + 1 ≤ n | sort: g_k (dict) + g_k·C_hk(1) + 8g_k⌈lg g_k⌉ + 2g_k + 1; per pass `by_key[kk]` 4, `len` 1 |
| L312-318 | only for the g_t tied classes | | `list(values)` 2q + 1; genexpr L313 10 + 9(q+1) + q; `set` 4q; `len(blocks[0])` 1; listcomp L318 8(q+1) + 4(S+q); SBB (split_by_blocks) |
| L315-317 | thin-cycle exit: only if the colour classes of a tied key class have one point each; then the call returns | listcomp L317: q + 1 ≤ n, at most one entry | `_thin_cycle_structure`: TC (next subsection) |
| L320 | `dominant_cell(base, Vset, bound)` | | DC(n) |
| L321 | `chooser.check` | | Ck(11) |
| L325-328 | `iter`, `next`, `pos`; genexpr L326 over V1 | | 2 + 4; 25 + 19|V1|; `sorted(V1)` |V1|⌈lg|V1|⌉ + 3|V1| + 1 |
| L329 | `cc.diagonal_colors()` | | C_diag := C[cc.ClassicalCC.diagonal_colors](n) |
| L331 | loop over V | n + 1 | `pos` 4, `in diag` 4 |
| L335 | loop over V1, entered for the e qualifying y | e(|V1| + 1) | `pos` 8, `in diag` 4, `cand.add` of a pair 10 |
| L340 | `sorted(cand, key=lambda@340)` | | Lc (set) + Lc·(20 + 2C_key + 2C_hk(1)) + 18Lc⌈lg Lc⌉ + 2Lc + 1 (key size 9, comparison ≤ 18) |
| L341, L347 | `chooser.check`; STATS | | Ck(12) + 1; 64 |
| L348 | `select_min(cands, lambda@348, chooser)` | | SM(Lc; c_key = 16 + 2C_key, σ_k = 3) |
| L349 | listcomp over V | n + 1 | `pos` 4 |
| L350 | dict comp over V1 | |V1| + 1 | genexpr over V2 11 + 23(n2+1) + 8n2; `frozenset` 4n2; insertion 4 |
| L351 | one Fraction division | | in instructions |
| L352 | the bipartite call | | counted as part of the run (§2) |

**Bound.** Sum of the table without the call of `_thin_cycle_structure`, with |V1| ≤ n,
e·|V1| ≤ n²/4, Lc ≤ n²/4, |V1|·n2 ≤ e·|V1|, e < n/3, g_k + 1 ≤ n, Σq ≤ n, ΣS ≤ n,
g_t ≤ n/2, and 18Lc⌈lg Lc⌉ ≤ 9n²·lg n:

    U(n) ≤ 761 + 354n + 53.5n² + 9n²·log2 n + 10n⌈lg n⌉ + 34M + 4M·n
           + Ck(8) + Ck(9) + Ck(11) + Ck(12) + Cc(n) + Cc(Lc) + C_ind + C_ref + C_diag(n)
           + (n + n²)·C_key + (n + n²/2)·C_hk(1) + (n²/4)·(C_hk(3) + C_Fix) + Σ_tied SBB

A call that takes the thin-cycle exit costs at most U(n) + TC; the rows after L318 then do
not run.

**WL path (EDL caller).** cc.key is the identity on distinct int colours.  So every key
class has one colour (g_t = 0, no SBB, no thin-cycle exit), and `select_min` has no tie, so
Cc(Lc) is not incurred.

**Choices.**
* x: n candidates.
* `select_min`: a tie only with equal keys, with ≤ Lc ≤ n²/4 candidates; this is possible
  only in case 2b.
* On the thin-cycle exit (case 2b only), the choice of y in `_thin_cycle_structure`, with
  q ≤ n - 1 candidates; then the call returns.

### soj._thin_cycle_structure(cc, x, cands, base, chooser, depth)  (L355)

* Profiles: opcount (58, [(367,17,0), (369,12,9), (372,31,0)]); region (61, [(367,23),
  (369,12), (372,31)]); lambda L379 (8).
* Called only from upcc L317.  Parameters: n = |V| = len(cc.vertices); q = len(cands) ≤ n - 1
  (the candidates are points of V \ {x}); M = base.m.

**Loops.**
* L367 over cc.vertices: P = n + 1.  Per u: `pos[u]` 4, the store `nxt[u] = ...` 4.
* Listcomp L369 over cc.vertices, entered once per u: P = n(n + 1) in total.  Per v:
  `pos[v]` 4; the comparison `row[pos[v]] == c` of two ints is an instruction.
* L372 over range(1, n): P = n (n - 1 elements, one entry).  Per j: the range element 1,
  `len(nxt[u])` with its lookup 5, `nxt[u][0]` 4, `u in place` 4, `place[u] = j` 4.

Instructions: 61 + 23(n + 1) + 12n(n + 1) + 31n = 12n² + 66n + 84.

**Other built-ins.** `sorted(cands)` ≤ 2n⌈lg n⌉ + 2n + 1; `pos[x]` and `pos[y]` 8; `nxt = {}` 1;
`place = {x: 0}` 5; `len(cc.vertices)` 1.

**Callees.** `chooser.choose`: Cc(q); `base.refine(lambda@379, ("upcc-cycle", depth))`:
C_ref (σ_f = 1, σ_tag = 13), plus the lambda, called M times, 8 + 4 (`place.get`) each.

**Bound:**

    TC ≤ 16n² + 2n⌈lg n⌉ + 94n + 82 + 12M + Cc(q) + C_ref

With Cc ≤ 104 (structure_cc_wl.md), TC ≤ 16n² + 2n⌈lg n⌉ + 97n + 204 + 13M + C_ref, the form
used in ownwork.md §3.4.

**Choice:** one, y, with q ≤ n - 1 candidates.

**Output.** In a run, every list `nxt[u]` has one element, the walk visits every vertex of
V once, and the returned structure is discrete on V (CORRECTNESS.md, Lemma 9.12(a), (d)).
The exit is taken only in case 2b (CORRECTNESS.md, Lemma 9.12(e)).

### soj.individualize_until(base, V, bound, chooser, tag)  (L382)

* Profiles: opcount (19, [(387,49,1), (388,17,11)]); region (24, [(388,56), (388,17)]).  The
  first region group is the `while` loop L387, whose target instruction lies on L388.
* Reached only through fallbacks (L346, L458, L470, L790; design L50, L76; main `2b-fb`)
  or through the small_v1 step L421-423.  That step is unreachable when
  bound ≥ small_v1 = 6: for n1 ≤ 6 ≤ bound, `dominant_cell` at L416 already returns None.
  So under (H61) this function never runs in a run.

**Bound for one call.** Hypothesis: bound ≥ 1.  This holds at every call site, where
bound ≥ alpha·|V| or bound = |C1|/2 with |C1| ≥ 2.

**Variant.** Φ := Σ_{cells c ⊆ V} max(0, |c| - ⌊bound⌋).
* Individualizing v ∈ big[0] splits only v's cell c, into {v} and c \ {v}, since
  `refine` with f(u) = [u == v] leaves the other cells unchanged.
* Because ⌊bound⌋ ≥ 1, this lowers Φ by exactly 1.
* Initially Φ ≤ |V| - ⌊bound⌋.

So there are s ≤ |V| - ⌊bound⌋ steps and s + 1 passes of the while loop.

**Per pass:**
* the listcomp over the cells: 17(K_c + 1) + Σ_c (4|c| + 4|V| + 1);
* `chooser.check`: Ck(12);
* `big.sort(key=...)`: b ≤ |V| key calls, each 5 + |c|⌈lg|c|⌉ + 3|c| + 1, plus
  b⌈lg b⌉ list comparisons of ≤ 2|V| each;
* `sorted(big[0])`, `chooser.choose`: Cc(|V|); `individualize`: C_ind.

Per pass this is ≤ 76 + 22M + 4M|V| + 14|V| + 2|V|⌈lg|V|⌉ + 2|V|²⌈lg|V|⌉ + Ck(12) +
Cc(|V|) + C_ind.

**Bound: 88 + 4|V| + (s + 1)·[that].**

**Choices:** s choices with ≤ |V| candidates each, so ≤ |V|^(|V| - ⌊bound⌋).

### soj.bipartite_split_or_johnson(V1, V2, adj, beta, base, chooser, params, depth, n1_orig)  (L400)

**Profiles.**
* opcount (1164, [36 loops]); region (1397, [36 loops]).  The full lists are in §4.
* Nested code:
  * lambdas: L438 (8), L490 (18), L575 (8), L581 (8), L618 (6 and 8);
  * genexprs: L451 (11, [25]), L479 (11, [9]), L494 (11, [9]), L514 (11, [10]),
    L553 (11, [9]), L592 (11, [10]);
  * nested defs: `vcol` (44) and `pcol` (78), no loops.

**Assumptions (B).** They hold at every call in a run; see §2.A.1.
* V1 is a list of distinct ints of V, and a union of cells of base.
* V2 is a list of points as in Lemma P.
* adj[v] ⊆ V2 is a frozenset for v ∈ V1.
* beta is a Fraction, and bound := beta·n1_orig = alpha·n (fixed along the chain).
* |V2| < bound.

**Parameters of one call.**
* n1 = |V1|, n2 = |V2|, Σ2, U2.
* N1 := |V1'| ≤ n1.
* d1: the common degree of V1' after a possible complement; d1 ≤ n2/2.
* d: the arity, T := n2^d, D := |distinct| ≤ min(T, N1 + 2).
* s*: the final s of `arity`.
* ℓ: the prefix length, ≤ d - 1.
* Ntot := N1 + n2 ≤ n.
* C1, C2: as in the code.

The costs below are the call's own work.  The **1397 `outside'` instructions** run at most
once per call; they are added once in the closed forms.  The per-pass cycle' costs of the
loops are included in the phases.  Calls of soj/design functions are replaced by
their bounds from this section, except the recursive bipartite call, `coherent` and
`_split_by_coloring_of_v2`, which §2 counts as separate members of the run.  Each line of
a phase is a loop (passes and per-pass cost) or a call.

**Phase 0 (L406-417, always):**
* `sorted(V1)` (a list): n1⌈lg n1⌉ + 2n1 + 1;
* `list(V2)`: n2;
* STATS 64, `chooser.check`: Ck(9);
* `frozenset(V1)`: 4n1;
* `dominant_cell`: DC(n1).

**P0 ≤ n1⌈lg n1⌉ + 6n1 + n2 + 67 + DC(n1) + Ck(9).**

**Phase 1 (L421-429):** the comparisons and `small_v2_bound` ≤ 30.  The small_v1 return
(L423) and the step-2 return (L429) are unreachable: the first because n1 > bound ≥ 6
(H61), the second because small_v2 = 0.

**Phase 2 (L432-442):**
* `base.cell_of()`: C_cof := C[structure.Structure.cell_of](M, K_c);
* `twin_classes_bipartite`: TCB ≤ 37 + 44n1 + 3n1Σ2;
* L434, over the g ≤ n1 classes: passes g + 1, cycle 7;
* L435, over the members of each class: passes n1 + g, cycle 9, plus `len` and insertion
  5 per pass (≤ 30n1 + 7 for L434-435 together);
* dict comp L437: passes n1 + 1, per pass 13 (≤ 25n1 + 12);
* `refine` with lambda L438: 12 per call, called M times, plus
  C_ref := C[structure.Structure.refine](M, K_c, K; σ_f = 3, σ_tag = 10);
* `dominant_cell`: DC(n1);
* `chooser.check`: Ck(11).

**P2 ≤ 56 + 99n1 + 3n1Σ2 + 12M + DC(n1) + C_cof + C_ref + Ck(11).**

**Phase 3 (L443-444, past L442):** `sorted(V1p_set)` (a frozenset) and one lookup.
**P3 ≤ N1⌈lg N1⌉ + 3N1 + 5.**

**Phase 3' (L445-456, the twin-equipartition terminal).**
* Twin classes are taken within cells (`cell_of`), and V1' is a cell all of whose
  vertices have twsize = c ≥ 2.  So the blocks partition V1' into B = N1/c ≤ N1/2 classes.
* Listcomp L450: passes g + 1, ≤ 15n1 + 11.
* Genexpr L451 with `any`: ≤ 36 + 31B + 8N1 + 4B·N1 ≤ 2N1² + 23.5N1 + 36.
* `chooser.check`: Ck(20); STATS 64.
* `split_by_blocks(base, V1p, blocks, ("bsoj-twins", depth))`: SBB with q = N1.

**P3' ≤ 112 + 15n1 + 23.5N1 + 2N1² + Ck(20) + SBB.**

**Phase 4 (L459-476):**
* lookups: 5;
* `frozenset(V2)`: ≤ 4Σ2;
* dict comps L461 and L464: passes N1 + 1 each, per pass ≤ 8 + 8Σ2 (`&` or `-`);
* `chooser.check`: Ck(11);
* set comp L473: passes N1 + 1, per pass 4 + η(adjp[v]) ≤ 8 + 3Σ2;
* dict comp L474: passes n2 + 1, insertions ≤ 4Σ2 in total;
* `comb(n2, d1)`: ≤ n2;
* `chooser.check`: Ck(17).

**P4 ≤ 38 + 48N1 + 19N1Σ2 + 9n2 + 8Σ2 + Ck(11) + Ck(17).**

**Johnson terminal (L477-481):**
* dict comp L479: passes N1 + 1, per pass ≤ 24 + 13d1 + 4Σ2, using genexpr L479;
* listcomp L480 over the cells: passes K_c + 1, per pass 4(|c| + N1);
* STATS 64;
* C_JC := C[structure.JohnsonCell.__init__] + 1;
* C_wj := C[structure.Structure.with_johnson](M, K_c, K).

**PJ ≤ 94 + 40N1 + 13N1d1 + 4N1Σ2 + 18M + 4M·N1 + C_JC + C_wj.**

**Half-split terminal (L485-490).**
* The `fallback` at L486 needs d1 = 1, which is impossible: then N1 = |H| = C(n2, 1) = n2
  < bound < N1.
* STATS 64; `list(V2)`: n2; `chooser.choose`: Cc(n2); `flatten(pt)`: F(u_pt);
* `mark`: C_mark := C[structure.Structure.mark](M, K_c, K; |S| = u_pt, σ_tag = 12);
* `refine` with lambda L490: ≤ 18 + 4 + 4 + 1 + 3σ(pt) per call, called M times, and
  C_ref (σ_f = 1, σ_tag = 13).

**PH ≤ 64 + n2 + F(u_pt) + M·(27 + 3σ(pt)) + Cc(n2) + C_mark + C_ref.**

**Phase 5 (L493-520, the d-ary structure).**
* `arity`: ≤ 46 + 23s*.
* Listcomp L494 over H: passes N1 + 1, per pass ≤ 20 + 13d1 + 4Σ2 (genexpr L494 and the
  set iteration).
* Counts:
  * if d = d1, loop L497: passes N1 + 1, insertion 3d1 + 4;
  * otherwise L500: passes N1 + 1, `sorted(e)` d1⌈lg d1⌉ + 3d1 + 1;
  * and L501: passes N1·(C(d1,d) + 1), per pass `combinations` d + `frozenset` 4d +
    get/set 2(3d + 4).

  Altogether ≤ 29N1 + 12 + N1(d1⌈lg d1⌉ + 3d1 + 4) + N1·C(d1,d)·(11d + 25).
* `list(product(...))`: (d + 1)T.
* Loop L506 over the T tuples: passes T + 1, per pass ≤ 11d + 6.
* `set(raw)` 4T; `sorted(distinct)` ≤ D⌈lg D⌉ + 3D + 1; dict comp L512: 8(D + 1) + 4D;
  listcomp L513: 7(T + 1) + 4T; C_KS := C[wl.KStructure.__init__].
* `chooser.check` at L514: genexpr L514 11 + 10(D + 1), `raw.count` D·T, `tuple` D;
  Ck(13 + D).
* Listcomp L515: 10(D + 1) + 1.  The `fallback` at L516 is unreachable (§2.A.1).
* `twin_classes_kary`: TCK ≤ (13d + 76)n2^(d+2).
* Listcomp L519: ≤ 15n2 + 14; `chooser.check`: Ck(11).

**P5 ≤ 163 + 23s* + 65N1 + N1(16d1 + d1⌈lg d1⌉ + 4Σ2) + 11(d+3)·N1·C(d1,d)·[d<d1]
+ (12d + 50 + D)·T + D⌈lg D⌉ + 36D + 15n2 + TCK + C_KS + Ck(13 + D) + Ck(11).**

**Phase 6 (L521-531, twin reduction, then recursion):**
* listcomps L522 and L524: ≤ 17n2 + 17;
* `set(S)`: ≤ 4Σ2;
* RP and RA; `chooser.check`: Ck(16).

**P6 ≤ 331 + 17n2 + 20Σ2 + 160N1 + 30N1Σ2 + Ck(16).**

**Phase 7 (L534-543, Design Lemma):**
* C_RS := C[wl.refine_structures](n2, d; one structure with D colours; trace = `chooser.check`);
* `design_lemma`: DL(n2, d), with σ_pt ≤ max σ(p) ≤ Σ2;
* loop L540: passes ℓ + 1 ≤ d, per pass `flatten(V2[p])` and C_mark (σ_tag = 11).
  Σ_p F(u_p) ≤ 12U2² + 68U2, by disjointness of the underlying sets.

**P7 ≤ C_RS + DL(n2, d) + 18d + 12U2² + 68U2 + Σ_{i<ℓ} C_mark.**

**Phase 8 (L545-626, kind 'b').**
* Loop L546: 14(n2 + 1) + 5n2.
* `max(..., key=len)`: 3n2; `sorted(C)`: n2⌈lg n2⌉ + 2n2 + 1.
* `prefix_pair_coloring`: C_ppc(d); `set(C)`: 4n2.
* Dict comp L553: ≤ 19N1 + 19 + N1(24 + 13d1 + 4Σ2).
* `key_of_vertex`: C_kov := C[structure.Structure.key_of_vertex](M, K_c).
* `classical_wl(Ntot, vcol, pcol, chooser.check)`: C_cwl(Ntot) := C[wl.classical_wl](Ntot).
  * `vcol` is called Ntot times, each ≤ 44 + 4 + 1 + C_hk(K);
  * `pcol` is called Ntot(Ntot - 1) times, each ≤ 78 + 8 + C_c(d).
* `ClassicalCC(list(range(Ntot)), lambda L575)`: 2Ntot + C_CC(Ntot) :=
  C[cc.ClassicalCC.__init__](Ntot), plus Ntot² calls of the lambda, each
  8 + C_col := 8 + C[wl.KStructure.color](2).
* Loops L577, L579 and L580: ≤ 21Ntot + 15 + 13Ntot + 12 + 16N1 + 11.
* `refine` with lambda L581: 12 per call, called M times, plus C_ref (σ_f = 1, σ_tag = 11).
* Listcomp L582: ≤ 16n2 + 15; `chooser.check`: Ck(15).
* L585 (when dom2 is empty): ≤ 11n2 + 10, and the run continues in
  `_split_by_coloring_of_v2`.
* Listcomp L587: ≤ 7n2 + 7.
* `dominant_cell`: DC(N1); `chooser.check`: Ck(15).
* Genexpr L592 with `sorted`, where each `V1p.index` costs ≤ N1:
  ≤ 22 + 13N1 + N1² + N1⌈lg N1⌉.
* Loops L594/L595: passes ≤ N1 + 1 and ≤ N1·n2 + N1; ≤ 26N1·n2 + 37N1 + 15.
* `chooser.check`: Ck(12).
* Then either the "seen ≤ 1" branch or the coherent branch:
  * "seen ≤ 1" branch: `set(C2)`, listcomp L604, RA: ≤ 20n2 + 42 + 16N1 + 4Σ2 + 8N1Σ2;
  * coherent branch:
    * listcomps L610/L616/L617;
    * C_indc := C[cc.ClassicalCC.induced](Ntot, ·), twice;
    * C_clq := C[cc.ClassicalCC.is_clique](|C2|), twice;
    * Ck(18), STATS 64, the list operations, Ck(15);
    * ≤ 22n2 + 3N1 + 87 + callees.
  * The fallbacks at L606 and L613 are unreachable (§2.A.1).

**P8 ≤ 220 + 73n2 + 125N1 + 13N1d1 + 12N1Σ2 + 26N1n2 + N1² + 85Ntot + 94Ntot² + 4Σ2
+ n2⌈lg n2⌉ + N1⌈lg N1⌉ + 34M + 4M·N1**, plus the callees
* C_ppc(d), C_kov, C_cwl(Ntot), Ntot·C_hk(K), Ntot²·(C_c(d) + C_col), C_CC(Ntot), C_ref;
* Ck(15) twice, Ck(12);
* in the coherent branch: 2C_indc + 2C_clq + Ck(18) + Ck(15).

**Composition.** A call executes:
* P0 + P1 + P2, and then either P3', or P3 + P4 + one of:
  * PJ;
  * PH;
  * P5 + P6;
  * P5 + P7 + `_split_by_coloring_of_v2` (kind 'a');
  * P5 + P7 + P8 + (`_split_by_coloring_of_v2` or `coherent`) (kind 'b').
* The returns at L417, L442, L591, L621 and L625 only shorten this.

**Closed forms.** Put n := |V| ≥ 61 and L := ⌈lg n⌉.  Use:
* N1, n1, Ntot < n and n2 < n/3 (§2.A.1);
* Σ2 ≤ 2U2 < 2n/3 (Lemma P, U2 ≤ n - n1);
* d1 ≤ n2/2 < n/6; D ≤ n + 1; s* ≤ n/12 + 1;
* the bounds for `_split_by_coloring_of_v2` and `coherent` given below.

Then:
* a call that makes **no Design-Lemma choice**:

      B ≤ 2287 + 454n + 41n² + (n²/6 + 3n + 2)·L + 85M + 12M·n + T·Q + (callee symbols)

* a call that makes the **Design-Lemma choice**, including its `_split_by_coloring_of_v2`
  or `coherent` member:

      B ≤ 3902 + 130d + 758n + 185n² + (n²/6 + 8n + 2)·L + 114M + 12M·n + T·Q
          + C_RS(n2, d) + (2T/n2)·(C_pvc(n2,d) + C_ppc(d)) + 2T·n2·C_c(d) + (callee symbols)

  The term (2T/n2)·(C_pvc + C_ppc) + 2T·n2·C_c is the callee part of DL.

Here Q := (13d + 76)·n2² + (6d + 33)·n + 15d + 250 at calls that reach Phase 5, and
Q := 0 otherwise.  Q collects:
* TCK;
* the T-terms of P5, using N1·C(d1, d) ≤ N1·n2^d/d! ≤ nT/2 for d ≥ 2;
* the T-terms of DL(n2, d), using n2^(d-1) = T/n2, n2 ≥ 6 and σ_pt ≤ 2n/3.

The other callee symbols are those listed in the phases.  n2 ≥ 6 holds at Phase 5,
because N1 > bound ≥ 40.67 distinct subsets of V2 force 2^n2 ≥ 42.

**Bounds on T = n2^d (all calls that reach Phase 5).**

**Lemma T.** With Y = log2 n:
* (i) T ≤ n2²·n^(1 + log2 Y);
* (ii) if n2 ≥ Y², then T ≤ n2²·n⁴;
* (iii) d < Y + 2.

*Proof.* Put t := s* - 1.
* If t = 0, then d ≤ 2s* = 2 and T ≤ n2².
* If t ≥ 1, Lemma AR(ii) gives C(n2, t) ≤ N1 < n and 2t < d1 ≤ n2/2, so n2/t > 4.
  * Hence 4^t < (n2/t)^t ≤ C(n2, t) < 2^Y, so t < Y/2.
  * Then n2^t = (n2/t)^t·t^t < n·t^t, and T ≤ n2^(2s*) = n2^(2t+2) < n2²·n²·t^(2t)
    < n2²·n²·(Y/2)^Y = n2²·n^(1 + log2 Y).
  * d ≤ 2s* = 2t + 2 < Y + 2.
* (ii) If n2 ≥ Y², then s* ≤ ⌈Y/Z'⌉ ≤ 2Y/Z + 1 ≤ 2^(Z/2) (the region-R1 argument of §2.B).  So
  log2 t < Z/2, and Y > t(Z - log2 t) > tZ/2.  Hence n2^(2t) < 2^(4Y) and T < n2²·n⁴. ∎

**Lemma T is not polynomial in general.** Take the parameter triple n2 = 70, d1 = 35,
N1 ≈ 2^63:
* C(70, s) ≤ 2^63 for all s ≤ 17, so the loop runs to 2s ≥ d1, and d = d1 = 35;
* T = 70^35 ≈ 2^214.5 = n^3.4 for n ≈ 2^64.

This triple satisfies every property of a Phase-5 call used in this document (twin-free,
not complete, d1 ≤ n2/2, N1 > n2).  More generally, with n2 = 2Y and N1 < 2^Y the rule
gives (approximately, from C(2Y, s) ≈ 2^(2Y·H(s/2Y))) d ≈ 0.44Y, so T ≈ n^(0.44·log2(2Y)).  Such calls are not excluded here.  So the
d-ary structure, and with it the own work, is n^(Θ(log log n)) in the worst case, not
n^O(1).  It is still 2^(O(log n · log log n)), negligible against 2^(b log³ n).

### soj._individualize_v2(V1, V2, adj, base, chooser, depth)  (L629)

* Profiles: opcount (53, [(636,34,3), (638,9,8), (642,6,12), (643,17,9)]); region (80,
  [(637,39), (638,9), (642,6), (643,17)]); genexpr L643 (11, [9]); lambda L644 (8).
* **Reachability.** Never reached in a run under `SOJParams()`:
  * L429 needs n2 ≤ small_v2 = 0;
  * L517, L538, L607, L614 and L676 come after a `fallback`.

  It is reachable under `small_scale` (small_v2 = 3).

**Loops.**
* The while loop L636 has n2 iterations: `remaining` loses exactly the chosen point each
  time, since the points are distinct by Lemma P.
* Listcomp L638: |rem| + 1 passes; each comparison q != p costs ≤ σ(q) + σ(p).  Summed
  over the iterations: Σ_r 9(r + 1) + 2n2Σ2.
* Dict comp L642: n2 + 1 passes.
* Dict comp L643: n1 + 1 passes; per v: `sorted` and `tuple` of |adj[v]| ≤ n2 positions,
  and lookups ≤ 4Σ2.

**Callees.**
* n2 calls of `chooser.choose` with n2, n2 - 1, ..., 1 candidates;
* n2 calls of `flatten`, Σ ≤ 12U2² + 68U2;
* n2 marks, C_mark (σ_tag = 9);
* one refine: f called M times, 12 each; σ_f ≤ n2 + 1, σ_tag = 7.

**Bound:**

    IV ≤ 206 + 60.5n2 + 4.5n2² + 2n2Σ2 + 4Σ2 + 12U2² + 68U2 + 46n1 + n1(13n2 + n2⌈lg n2⌉ + 4Σ2)
         + 12M + Σ_{r=1}^{n2} Cc(r) + n2·C_mark + C_ref

**Choices:** n2 of them, with product n2!.

### soj._split_by_coloring_of_v2(V1p, V2, adjp, col, beta, base, chooser, params, depth, n1_orig)  (L647)

* Profiles: opcount (126, [(654,13,0), (657,24,8), (662,17,2), (667,6,8), (668,10,8)]);
  region (152, [(654,13), (657,24), (662,17), (667,6), (668,10)]).
* Assumption: col is a list of n2 ints (DL colours at L543, WL vertex colours at L585).
* g ≤ n2 colour classes.

**Loops.**
* L654: n2 + 1 passes, `setdefault` and `append` 5 each.
* `sorted(groups, key=_hk)`: g + g·C_hk(1) + 8g⌈lg g⌉ + 2g + 1.
* Listcomp L657: g + 1 passes; per pass a lookup and a `len` (5; 10 are charged).
* L662, only without `mid`: g + 1 passes, per pass a lookup, `extend` |class| and `len`.
* `set(S_idx)`: 4|S|.
* Listcomps L667 and L668: |S| + 1 and n2 + 1 passes; L668 adds range 1 and a set lookup 4.

**Callees.** RP and RA (on V1p, Σ2 over V2), Ck(12), and the recursive call (separate).

**Bound:**

    SC ≤ 543 + 103n2 + 8n2⌈lg n2⌉ + 160N1 + 12Σ2 + 30N1Σ2 + n2·C_hk(1) + Ck(12)

**Output.** The chosen part has |chosen| ≤ 2n2/3:
* every class has ≤ 2n2/3 points: for col1 of a kind-'a' prefix by the absence of a
  > (2/3)n2 class; for the WL colours at L585 by `dom2 = []`;
* if some class has size in (n2/3, 2n2/3], S is that class (L657-659);
* otherwise every class has ≤ n2/3 points, and the running union of L661-665 stops at the
  first size > n2/3, which is ≤ 2n2/3;
* in both cases |rest| = n2 - |S| < 2n2/3, and both parts are non-empty.

`reduce_part2_by_color` does not return None (Ex. 5.5), so the `fallback` at
L671 and L675 is unreachable (CORRECTNESS.md, Lemma 9.8).

### soj.coherent_split_or_johnson(X, C1, C2, v1_of, v2_of, base, chooser, depth, allow_fallbacks)  (L683)

* Profiles: opcount (624, [29 loops]); region (802, [29 loops]).  The full lists are in §4.
* Nested code:
  * genexprs: L737 (11, [23]), L747 (11, [14]), L751 (11, [23]), L756 (11, [10]),
    L761 (11, [17]), L795 (11, [23]);
  * lambdas: L732 (8), L778 (8), L798 (16).
* The callbacks v1_of and v2_of (bipartite L618) cost 6 and 8 per call.
* Parameters: n1 = |C1|, n2 = |C2|, N := n1 + n2 (the vertex count of X).  Σ2 bounds
  Σ σ(v2_of(w)) over C2 (points of the bipartite level).
* Hypotheses:
  * X is a coherent configuration with ints as colours and identity key;
  * C1 and C2 are vertex classes, with n1 > n2 ≥ 1;
  * X1 and X2 are therefore homogeneous, with ≤ n1 - 1 and ≤ n2 - 1 off-diagonal colours.

  All of this holds at the only call site (bipartite L617; CORRECTNESS.md, Lemma 9.9(d)).

**Common part (L694-713):**
* `X.induced` twice: C_indc(N, n1) + C_indc(N, n2);
* listcomp L699: 13n1 + 7;
* STATS 64; Ck(8);
* C_disc(n1) := C[cc.ClassicalCC.disconnected_off_diagonal_colors](n1), and then
  (if disc1 is empty) C_disc(n2);
* Ck(12), twice.

**Branches** (passes as in the table of bipartite; all loops range over C1, C2, the
blocks B, or dicts with ≤ n1 keys):

**(A) X[C1] imprimitive (L705-711):**
* STATS 64;
* `select_min` over ≤ n1 - 1 distinct int colours: no tie, so no choice;
  SM ≤ 88 + 54n1 + n1(C_key + C_hk(1) + C_Fix) + Ck(9);
* C_comp(n1) := C[cc.ClassicalCC.components](n1);
* the nested listcomp L709, with q ≤ n1/2 components (each component has ≥ 2 vertices,
  because X1 is homogeneous): ≤ 30n1 + 15;
* `split_by_blocks`: SBB with q = n1.

**(B) X[C2] imprimitive (L714-726):**
* STATS 64; `select_min` over ≤ n2 - 1 colours; C_comp(n2);
* listcomp L719: ≤ 19.5n2 + 15;
* L722: 39n1 + 23; L725: ≤ 15n1 + 14;
* Ck(14).

Total ≤ 205 + 73.5n2 + 54n1 + callees.  Then one of:
* **(B1) no big degree (L727-733):**
  * `sorted(C2)` twice; listcomp L728; Cc(n2); `objs.index` ≤ (n2 + 1)Σ2;
  * `flatten` F(u); C_mark;
  * dict comp L731: 19n1 + 19 + n1(18 + C_key);
  * refine: 12M + C_ref.

  ≤ 37 + 20n2 + 37n1 + 2n2⌈lg n2⌉ + (n2 + 1)Σ2 + F(u) + 12M + callees.
* Otherwise, first the acceptability loop L736-739 over the q2 ≤ n2/2 blocks:
  * per block: dict comp L737 over C1 (per u ≤ 44 + 39|blk| + Σ_blk η) and `max_twin_class`
    (≤ 72 + 56n1 + 3n1·Σ_blk σ);
  * then Ck(14).

  ≤ 33 + 80n2 + 100n1n2 + 7n1Σ2 + Ck(14).  Then:
  * **(B2) acceptable block (L741-752):**
    * L743: n2⌈lg n2⌉ + 10n2 + 12; L745: 16n2 + 8; Cc; `index`;
    * genexpr L747: ≤ 25 + 8n2;
    * `flatten`; C_mark; L750: 16n2 + 8;
    * L751: 22n1 + 22 + n1(44 + 39n2 + 4Σ2).

    ≤ 83 + 50n2 + 66n1 + 39n1n2 + 4n1Σ2 + n2⌈lg n2⌉ + (n2 + 1)Σ2 + F(u) + callees.
  * **(B3) contraction (L753-764):**
    * L754: 11n1 + 10;
    * `select_min` over the green candidates (≤ n1 distinct ints, no tie):
      88 + 54n1 + n1(C_key + C_hk(1) + C_Fix) + Ck(9);
    * L756: ≤ 35.5n2 + 14 + 4Σ2;
    * L758/L760/L761: 21n1 + 21 + n1(39 + 58n2 + 6Σ2).

    ≤ 133 + 125n1 + 35.5n2 + 58n1n2 + 6n1Σ2 + 4Σ2 + callees.

**(C) X[C2] primitive (L766-799):**
* STATS 64; `sorted`, `objs`, Cc(n2), `index`;
* `flatten`; C_mark;
* L771: 39n1 + 23; L774: 15n1 + 14; Ck(15).

Then either:
* **(C1) no big degree (L777-779):** 19n1 + 19 + n1(18 + C_key) + 12M + C_ref; or
* **(C2) blues (L781-799):**
  * L781: 26n1 + 18;
  * L783: ≤ 37n2 + 32 + n2·C_od(n2), plus C_odc(n2) := C[cc.ClassicalCC.off_diagonal_colors](n2),
    which returns ≤ n2 - 1 colours;
  * Ck(17); `select_min` over the blues (no tie);
  * L792-L795: 26n2 + 18 + 13n1 + 7 + 16n2 + 8 + 22n1 + 22 + n1(44 + 39n2 + 4Σ2);
  * two `frozenset`s 8n1;
  * refine, whose lambda costs 24: 24M + C_ref.

(C) total ≤ 314 + 167n1 + 153n2 + 39n1n2 + 4n1Σ2 + 2n2⌈lg n2⌉ + (n2 + 1)Σ2 + F(u) + 24M +
callees.

**Bound** (the termwise maximum over the branches, plus the common part):

    CO ≤ 1247 + 192n1 + 204n2 + 158n1n2 + 13n1Σ2 + (n2 + 5)Σ2 + 2n2⌈lg n2⌉ + F(u) + 24M
         + C_indc(N,n1) + C_indc(N,n2) + C_disc(n1) + C_disc(n2) + C_comp(n1 or n2) + SBB
         + 2n·(C_key + C_hk(1) + C_Fix) + Cc(n2) + C_mark + C_ref + C_odc(n2) + n2·C_od(n2)
         + Ck(8) + 2Ck(12) + 2Ck(9) + Ck(14) + Ck(15) + Ck(17)

Here F(u) is the `flatten` of the one marked point, u = u(point) ≤ U2.

Closed form for n1 + n2 ≤ n, n2 ≤ n/3, Σ2 ≤ 2n/3:

    CO ≤ 1247 + 222n + 50n² + 0.67n⌈lg n⌉ + 24M + (callees)

The 50n² includes F(u) ≤ 12(n/3)² + 68n/3.

**Choices:** at most one choose, among ≤ n2 = |C2| candidates (L729, L746 or L768).  All
`select_min` calls have distinct int keys, hence no tie.

**Output** (used in §2): "coloring", or ("bipartite", (W1, W2, adjW)) with:
* |W2| ≤ n2/2:
  * B2: one block, with ≥ 2 blocks of equal size, because the components of an
    off-diagonal colour of the homogeneous coherent X2 are the classes of a colour union
    that is an equivalence relation;
  * B3: the number of blocks, each block having ≥ 2 points;
  * C2: the degree dg of the blue colour, with 0 < dg < n2/2;
* W1 = C1 in B2 and B3; W1 = L_violet(y), with |W1| > n1/2, in C2.

### soj.split_by_blocks(base, cell_vertices, blocks, tag)  (L802)

* Profiles: opcount (49, [(810,8,0), (811,6,0), (817,35,0), (820,13,0), (822,13,0)]); region
  (49, [(810,8), (811,6), (817,35), (820,13), (822,13)]).
* Parameters: q = |cell_vertices|; the blocks partition cell_vertices, so there are
  B ≤ q of them with Σ|b| = q.  This holds at every call site: upcc L318; bipartite L456;
  coherent L710; design L71; main `2b-comp`.  J is the Johnson cell, |J| = 0 if there is
  none.

**Loops.**
* L810: B + 1 passes.
* L811: Σ(|b| + 1) = q + B passes, insertion 4 each.
* L817: K_c + 1 passes; per cell `c <= cv` costs 4(|c| + q).
* Inside cells: L820 over c, |c| + 1 passes (+|c| for the frozenset, and 9 per element for
  lookups); L822 over the groups, g_c + 1 passes (+1 per group, `frozenset` 4|g|).
  Σ|c| ≤ q and Σg_c ≤ q.
* Outside cells: one comparison with J, 4(|c| + |J|), and an `append`.

**Callee.** C_S := C[structure.Structure.__init__](M, ≤ K_c + q cells, keys ≤ K + σ(tag) + 3).

**Bound:**

    SBB ≤ 92 + 96q + 36K_c + 8M + 4K_c(q + |J|) + C_S ≤ 92 + 96q + 44M + 4M(q + |J|) + C_S

### design.extended_design_lemma(X, base, alpha, chooser, params, vertices)  (design.py L36)

* Profiles: opcount (257, [(52,12,0), (59,13,0), (70,7,11), (70,8,11)]); region (271,
  [(52,12), (59,13), (70,15), (70,8)]); lambda L54 (6).
* Parameters: m = X.n, k = X.k ≥ 1.  base has M = base.m; in both callers M = m (main.py
  `primitive_johnson`, `case_3`).
* Hypotheses: the X of the callers is a refined k-ary coherent configuration (wl), and
  alpha = 2/3 is a Fraction.

**Costs.**
* outside' 271; STATS ≤ 3·64; `list(range(m))` 2m.
* DL(m, k), with σ_pt = 1 (the candidates are tuples of ints); Ck(10).
* Loop L52: ℓ + 1 ≤ k passes; ℓ ≤ k - 1 calls of C_ind (σ_tag = 10).
* refine: 6M + C_ref (σ_f = 1, σ_tag = 8).
* Loop L59: 13(m + 1) + 5m.
* `max`: 3m; `sorted(C)`: ≤ m⌈lg m⌉ + 2m + 1.
* C_ppc(k); C_CC(|C|) + |C|²·C_c(k), for the ClassicalCC(C, c2), whose colour callback is
  wl's closure; C_disc(|C|); Ck(12).
* Equipartition branch:
  * `select_min` over ≤ |C| - 1 distinct int colours (no tie):
    ≤ 88 + 54|C| + |C|(C_key + C_hk(1) + C_Fix) + Ck(9);
  * C_comp(|C|);
  * the nested listcomp L70: ≤ 19.5|C| + 15;
  * SBB with q = |C|.
* UPCC branch: C_up(|C|) := C[cc.ClassicalCC.is_uniprimitive](|C|); 3 Fraction operations;
  then the upcc run.

**Own bound:**

    E ≤ 583 + 98.5m + m⌈lg m⌉ + 12k + 6M + DL(m,k) + Ck(10) + Ck(12) + Ck(9) + (k-1)·C_ind
        + C_ref + C_ppc(k) + C_CC(|C|) + |C|²·C_c(k) + C_disc(|C|) + m·(C_key + C_hk(1) + C_Fix)
        + C_comp(|C|) + SBB + C_up(|C|)

The UPCC branch is followed by the upcc run of §2.

**Fallbacks.** L45-50 and L72-76 are unreachable.
* `design_lemma` does not return None when its hypotheses hold (CORRECTNESS.md,
  Theorem 8.1).
* With kind 'b', `cc` is homogeneous and not a clique; without a disconnected colour it is
  primitive, hence uniprimitive.

---------------------------------------------------------------------------------------------------

## 2. One run: recursion structure, own work (A), choice counts (B), output guarantees

Throughout this section, **a run** is one execution of `upcc_split_or_johnson` (or of
`extended_design_lemma`) with a fixed sequence of chooser answers, under `SOJParams()`,
that returns normally.  So no `fallback` is reached.  Hypotheses (U), (S1) and (H61).
n := |V| ≤ m, Y := log2 n, δ := log2(3/2).

### 2.A.1 The chain of calls and its invariants (alpha = 2/3, |V| ≥ 61)

`upcc` makes at most one call of bipartite (L352); a run that leaves upcc at L317, through
`_thin_cycle_structure`, makes none.  Each bipartite call makes at most one
further bipartite call: directly (L530, L608, L626), via `_split_by_coloring_of_v2`
(L543/L586 → L677), or after one `coherent` call (L617).  So a run is a **chain**

    upcc → B_0 → B_1 → ... → B_L,

with at most one `design_lemma`, one `_split_by_coloring_of_v2` and one `coherent` member
between consecutive B_i.  Write n1_i, n2_i, N1_i, d_i for the parameters of B_i.

**(I1) The bound is fixed.** At L351, beta = bound/|V1_0| is an exact Fraction, and the
recursive calls pass beta and n1_orig unchanged.  So bound = beta·n1_orig = alpha·n at
every B_i, with alpha ∈ [2/3, 1).  (In EDL: alpha' = alpha·m/|C|, so bound = (2/3)·m.)

**(I2) Size of V1.** V1_i ⊆ V \ {x}.  A call with n1_i ≤ bound returns at L417, because no
cell inside V1 exceeds the bound.  Every call that goes further has n1_i > bound ≥ 2n/3 ≥
40.67.  Hence:
* the small_v1 step L421-423 is unreachable, since 6 < bound;
* for alpha = 2/3, 6 < bound holds once |V| ≥ 10, in particular under (H61).

**(I3) Shape of V2.** V2_i is as in Lemma P; n2_i ≥ 1, and n2_0 ≤ n - 1 - |V1_0| < n/3.
Hence n2_i < n/3 < bound for all i (CORRECTNESS.md, Lemma 9.3 (B2)).

**(I4) V1 is a union of cells.** V1_0 is a cell (L320); V1' is a cell (L439).  W1 is C1
(a cell, L588) in coherent B2/B3, or is made a cell at L798 (C2).

**(I5) Twin bound.** Every twin class of (V1_i, V2_i; adj) has ≤ n1_i/2 + 1 points
(CORRECTNESS.md, Lemma 9.3 (B4)).
* At B_0 this is Ex. 5.4, a semiregular non-trivial bipartite graph.
* At L530, L677 and L608 it comes from `reduce_part2_by_color`'s test or from Ex. 5.5.
* At L626 it comes from Prop. 5.8.

Coloured twin classes (L432, within cells) are subsets of these.  Since
n1_i ≤ |V1_0| =: n1_orig and n1_orig ≥ 41, it follows that
n1_i/2 + 1 ≤ n1_orig/2 + 1 ≤ (2/3)·n1_orig < beta·n1_orig = bound
(beta = alpha·n/n1_orig > alpha ≥ 2/3).  So the inequality
"twin ≤ |V1|/2 + 1 ≤ (2/3)n1_orig ≤ bound" holds for alpha = 2/3 whenever n1_orig ≥ 6.
**The fallback at L457-458 is unreachable.**

**(I6) Past L458.** At a call that passes L458:
* V1' is twin-free (twsize = 1);
* N1 = |V1'| > bound > n2, so H consists of N1 distinct d1-sets, d1 ≤ n2/2;
* d1 ∉ {0, 1}: d1 = 0 forces twins; d1 = 1 forces N1 ≤ n2 (CORRECTNESS.md, Lemma 9.5).

**The fallbacks at L470 and L486 are unreachable.**

**(I7) The other fallbacks are unreachable.**
* **L516, constant d-ary structure.**
  * If d = d1: the distinct d1-tuples are coloured 1 (the set is an edge) or 0 (it is
    not).  H is non-empty and not complete (L475 failed), so both values occur.
  * If d < d1: by Lemma AR(iii), d = 2s* and C(n2, s*) > N1.  A constant count λ on the
    distinct d-tuples would give λ ≥ 1 (each edge contains d-subsets), and H would be a
    2s*-(n2, d1, λ) design with N1 distinct blocks.  Ray-Chaudhuri–Wilson (HBD Prop. 2.20)
    applies, since n2 ≥ d1 + s* (s* < d1/2 ≤ n2/4), and gives N1 ≥ C(n2, s*), a
    contradiction.

  This argument does not use the threshold n2 > (6 ln n1)^1.5 of HBD's small-|V2| step,
  so disabling step 2 (small_v2 = 0) is sound.
* **L527: `reduce_part2_by_color` returns None.** Impossible, by Ex. 5.5 on the twin-free
  V1'.
* **L537: `design_lemma` returns None.** Impossible (CORRECTNESS.md, Lemma 9.7): X is d-ary
  coherent, 2 ≤ d ≤ d1 ≤ n2/2, alpha = 2/3, twin classes ≤ n2/2 (checked at L519-521).
* **L606, L613, coherent L789, L671, L675:** CORRECTNESS.md, Lemma 9.9(b), Lemma 9.9(c),
  Lemma 9.10 and Lemma 9.8 (for both L671 and L675).  These arguments do not depend on
  alpha.
* **design L45-50, L72-76:** unreachable (§1, EDL).

**(I8) n2 strictly decreases along the chain.**
* L530: |chosen| ≤ n2 - 1.  S is a twin class with |S| > n2/2, and S ≠ V2: if all of V2
  were one strong-twin class, Sym(V2) would preserve the colouring, which would then be
  constant on distinct d-tuples, excluded by (I7).  Both S and rest are non-empty.
* L677: |chosen| ≤ 2n2/3 (§1, `_split_by_coloring_of_v2`).
* L608: 1 ≤ |rest| ≤ n2/3, since |C2| ≥ (2/3)n2.
* L626: |W2| ≤ |C2|/2 ≤ n2/2 (§1, coherent).

So **the number of bipartite calls is L + 1 ≤ n2_0 < n/3**: the n2_i are distinct
integers in [1, n2_0].

A call **makes a Design-Lemma choice** ("choice level") iff it reaches L535.  The next
call after a choice level has n2 ≤ (2/3)·n2: kind 'a' and "no dom2" give 2/3, "seen ≤ 1"
gives 1/3, coherent gives 1/2.  So successive choice levels j < j' satisfy
**Z_j' ≤ Z_j - δ**, where Z := log2 n2.  Choice levels have n2 ≥ 6 (Phase 5), so

    J := #choice levels ≤ 1 + log_{3/2}(n2_0/6) < Y/δ.

There are at most J `coherent` calls and J `_split_by_coloring_of_v2` calls.  The levels
that do not make a choice (twin reductions L530, or terminal calls) can shrink V2 by as
little as 1.  They are counted in L + 1 ≤ n/3.  (Python's stack has ≤ 2(L+1) + 2 soj
frames.)

### 2.A.2 Theorem A: own work of one run of `upcc_split_or_johnson`

    W_UPCC ≤ U(n) + Σ_{i=0}^{L} B_i,  and  W_UPCC ≤ U(n) + TC for a run that takes the
                                        thin-cycle exit (it makes no bipartite call).

Here:
* U(n) is the own-work bound of upcc from §1, and TC that of `_thin_cycle_structure`;
* B_i is the bound of §1 for bipartite call i.  B_i includes the `_split_by_coloring_of_v2`
  or `coherent` member of the chain at that level, and its module callees.

**Closed form.** Combine:
* the per-call closed forms of §1 (the no-choice bound for the ≤ n/3 calls, plus the
  choice bound for the < Y/δ choice levels);
* Lemma T (T_i ≤ n2_i²·n^(1 + log2 Y) and d_i < Y + 2), which gives
  Q_i ≤ (13Y + 102)(n2_i² + n) for n ≥ 61;
* Σ over distinct n2_i < n/3: Σ n2_i⁴ ≤ (n/3)⁵ and Σ n2_i² ≤ (n/3)³.

Then:

    W_UPCC ≤ (Y/16 + 1/2) · n^(6 + log2 log2 n)                                    [d-ary part]
             + 14n³ + (n³/18 + n² + n)⌈lg n⌉ + 152n² + 763n + 4M·n² + 29M·n    [no-choice levels]
             + (Y/δ)·(4162 + 130Y + 758n + 185n² + (n²/6 + 8n + 2)⌈lg n⌉ + 114M + 12M·n) [choice levels]
             + 765 + 354n + 54n² + 9n²·log2 n + 10n⌈lg n⌉ + 34M + 4M·n            [upcc itself]
             + 16n² + 2n⌈lg n⌉ + 94n + 82 + 12M                                  [thin-cycle exit]
             + Σ (callee symbols)

The last line is TC without its callees; adding it bounds both kinds of run.

Notes on the d-ary part:
* n2_i^(d_i) ≤ n2_i²·n⁴ when n2_i ≥ Y² (Lemma T(ii)).  So the d-ary part is also
  ≤ (Y/16 + 1/2)·n⁹ + (13Y + 102)(Y^10 + n·Y⁶)·n^(1 + log2 Y).
* The exponent 6 + log2 log2 n is not a constant (see "Lemma T is not polynomial" in §1):
  **the own work of one run is n^(O(log log n)), not polynomial.**

**The callee symbols** of one run:
* per bipartite call:
  * C_cof(M), C_ref(M, ·) (Phase 2), C_KS, Ck(9), Ck(11) twice, Ck(17), Ck(16),
    Ck(13 + D_i);
  * a terminal SBB or C_wj + C_JC, or Cc(n2) + C_mark + C_ref;
* per choice level j:
  * C[wl.refine_structures](n2_j, d_j);
  * 2n2_j^(d_j - 1)·(C_pvc(n2_j, d_j) + C_ppc(d_j));
  * 2n2_j^(d_j + 1)·C_c(d_j) (the closure of `prefix_pair_coloring` inside the Design
    Lemma);
  * Cc(n2_j^(d_j - 1)), d_j·Ck(6), and ≤ d_j - 1 marks;
  * for kind 'b':
    * C[wl.classical_wl](Ntot_j), with Ntot_j ≤ n;
    * Ntot_j·C_hk(K) and Ntot_j²·(C_c(d_j) + C_col) for the callbacks;
    * C_CC(Ntot_j), C_kov, C_ref, C_ppc(d_j);
    * 2C_indc + 2C_clq;
    * the callees of `coherent` (listed in §1).
* upcc's callees: C_ind, C_ref, C_diag(n), Cc(n), (n + n²)·C_key, (n + n²/2)·C_hk(1), and
  in case 2b the tie terms;
* on the thin-cycle exit: Cc(q) and C_ref (σ_f = 1, σ_tag = 13) of `_thin_cycle_structure`.

**Solver calls: none.** soj and design never call `Solver.iso`.

### 2.A.3 Own work of one run of `extended_design_lemma`

    W_EDL ≤ E(m, k) + DL(m, k) + W_UPCC(|C|)

* E is the own bound of §1, and DL is the bound of `design_lemma` with n = m = X.n and
  σ_pt = 1.
* The last term is present only in the uniprimitive branch, where |C| ≤ m (and
  |C| > (2/3)m ≥ 61 under the paper parameters).
* With DL's closed form: DL(m, k) ≤ 2m^(k-1)(28m² + 72m + 123 + k + C_pvc(m, k) + C_ppc(k) +
  m²·C_c(k)) + m^(k-1)(36 + 12k) + 460 + 2m + 112k + k·Ck(6) + Cc(m^(k-1)) + C_pvc.

### 2.A.4 Key sizes (parameter K of the Structure callees)

Every refine, mark, individualize or `split_by_blocks` adds ≤ 19 to the size of every key.
The increment is σ(tag) + σ(f-value) + 3: the tags have σ ≤ 15, the f-values in a run have
σ ≤ 3, and the size-wrapping of `_normalize` adds 2.  `with_johnson` adds 13.

A run performs ≤ 3 + g_t + (L + 1) + Σ_j (d_j + 3) + 2 such operations:
* upcc: 2 + g_t, and on the thin-cycle exit one refine in `_thin_cycle_structure`
  (increment 13 + 1 + 3 = 17), after which the run makes no bipartite call;
* one per bipartite call (L438);
* per choice level: ≤ d_j - 1 marks, 1 + 2 refines or marks;
* a terminal: ≤ 2.

With g_t ≤ n/2, L + 1 ≤ n/3, d_j < Y + 2 and J < Y/δ:

    K ≤ K_in + 16n + 33Y² + 170Y + 150,

where K_in bounds the key sizes of the base passed in.

### 2.B Choice counts

**Choice points of a run** (fallbacks excluded; this follows from (I2), (I7) and
`small_v2 = 0`):

| where | candidates |
|---|---|
| L294: x | n |
| L348: `select_min` tie (only case 2b with tied keys; none in the WL path) | ≤ Lc ≤ n²/4 |
| L363: y on the thin-cycle exit (only case 2b; the run ends there) | q ≤ n - 1 |
| choice level j: DL prefix (L270) | (n2_j)_ℓ, with ℓ ≤ d_j - 1 (kind 'a') or ℓ ≤ d_j - 2 (kind 'b') |
| choice level j, kind 'b', coherent point (L729, L746 or L768) | ≤ \|C2\| ≤ n2_j |
| terminal half split (L488) | n2_T < n/3 |

There are no other choices:
* `individualize_until` and `_individualize_v2` are not reached;
* every other `select_min` has distinct int keys;
* twin-reduction levels make no choice.

So the factor of choice level j is ≤ n2_j^(d_j - 1).  For kind 'b', (n2_j)_ℓ·|C2| ≤
n2_j^(d_j - 2)·n2_j.  Hence

    log2 s_UPCC ≤ Y + [2Y - 2]_2b + Σ_j (d_j - 1)·Z_j + log2(n/3),   Z_j := log2 n2_j        (★)

Z_1 < Y - log2 3, and Z_{j+1} ≤ Z_j - δ (I8).  A run that takes the thin-cycle exit makes
only the choices x and y, with n and q ≤ n - 1 candidates.  It occurs only in case 2b, and
n - 1 ≤ n²/4 = 2^(2Y - 2), so (★) covers these runs as well.

**Lemma R (arity at a choice level).** Let t ≥ 1 be an integer with t ≤ n2 and
t(Z - log2 t) ≥ Y.  Then s* ≤ t, so d - 1 ≤ 2t - 1.

*Proof.* C(n2, t) ≥ (n2/t)^t = 2^(t(Z - log2 t)) ≥ 2^Y = n > N1.  The loop of `arity`
increments s past t only if C(n2, t) ≤ N1.  Then d ≤ 2s* (Lemma AR(i)). ∎

The choice levels are split into three regions by n2.

* **(R3) n2 < 2Y + 4.** Use d - 1 ≤ d1 - 1 ≤ n2/2 - 1.  The n2_j of these levels decrease
  geometrically (factor ≤ 2/3), so Σ n2_j < 3(2Y + 4) and

      Σ_{R3} (d_j - 1)·Z_j < (3/2)(2Y + 4)·log2(2Y + 4) = (3Y + 6)·log2(2Y + 4).

* **(R2) 2Y + 4 ≤ n2 < Y².** Take t = ⌈Y/2⌉ ≤ Y/2 + 1 ≤ n2/4.  Then n2/t ≥ 4, so
  t(Z - log2 t) ≥ 2t ≥ Y.  Lemma R gives d - 1 ≤ 2t - 1 ≤ Y + 1, and a level costs
  ≤ (Y + 1)·2log2 Y.  These levels have Z ∈ [1 + log2 Y, 2log2 Y), spaced by ≥ δ, so there
  are < (log2 Y - 1)/δ + 1 of them, and

      Σ_{R2} ≤ 2(Y + 1)·log2 Y·((log2 Y - 1)/δ + 1).

* **(R1) n2 ≥ Y².** This region carries the main term; it is worked out below.

**Region R1: the leading term.** Put μ(Z) := log2(2Y/Z + 1) and Z' := Z - μ(Z).
* **μ ≤ Z/2.** Since Z ≥ 2log2 Y, 2^(Z/2) ≥ Y.  Also 2Y/Z + 1 ≤ Y/log2 Y + 1 ≤ Y
  for Y ≥ 4.
* **The arity bound.** Take t := ⌈Y/Z'⌉.
  * Y/Z' ≤ 2Y/Z, so t ≤ 2Y/Z + 1 = 2^μ, and log2 t ≤ μ.
  * t ≤ 2^(Z/2) ≤ n2.
  * t(Z - log2 t) ≥ t·Z' ≥ Y.

  By Lemma R, d - 1 ≤ 2⌈Y/Z'⌉ - 1.
* **Cost of a level.** The level costs

      (d - 1)Z ≤ (2⌈Y/Z'⌉ - 1)(Z' + μ) = h(Z') + (2⌈Y/Z'⌉ - 1)·μ,    h(z) := (2⌈Y/z⌉ - 1)·z.

* **Spacing.** μ is decreasing in Z.  So Z'_j - Z'_{j+1} ≥ Z_j - Z_{j+1} ≥ δ, and the
  values Z' lie in [log2 Y, Y - 1 - δ], with Z' ≥ Z/2 ≥ log2 Y.

**Lemma Σ (sawtooth sums).** Let c ≥ 1 and h_c(z) := (c⌈Y/z⌉ - 1)·z.  Let
z_1 > z_2 > ... > z_J > ζ > 0 with z_j - z_{j+1} ≥ δ and z_1 + δ ≤ Y.  Then

    Σ_j h_c(z_j) ≤ (1/δ)·∫_0^Y h_c(z) dz + c·Y·ln(Y/ζ),
    ∫_0^Y h_c = Y²·Σ_{k≥2} (ck - 1)/2·(1/(k-1)² - 1/k²) = Y²·(c/2·π²/6 + (c - 1)/2).

For c = 2 the constant is 1/2 + π²/6 =: S_2 = 2.1449341.  For c = 6 it is 5/2 + π²/2 =
7.4348022.

*Proof.*
* **Shape of h_c.** On [Y/k, Y/(k-1)), with k ≥ 2, ⌈Y/z⌉ = k and h_c(z) = (ck - 1)z is
  increasing.  At each breakpoint b = Y/k' (k' ≥ 1), h_c drops by c·b, from (c(k'+1) - 1)b
  to (ck' - 1)b.  Hence, for z ≥ z_j, h_c(z) ≥ h_c(z_j) - Σ_{b ∈ (z_j, z]} c·b.
* **One level.** Integrating over [z_j, z_j + δ):
  δ·h_c(z_j) ≤ ∫_{z_j}^{z_j+δ} h_c + δ·Σ_{b ∈ (z_j, z_j+δ)} c·b.
* **Summing.** The intervals [z_j, z_j + δ) are disjoint and contained in (ζ, Y).
  The breakpoints in (ζ, Y) are Y/k with 2 ≤ k < Y/ζ, and Σ_{k=2}^{K} cY/k ≤ cY·ln K.
* **The integral.** ∫_{Y/k}^{Y/(k-1)} (ck - 1)z dz = (ck - 1)/2·Y²·(1/(k-1)² - 1/k²).
  Writing ck - 1 = c(k - 1) + (c - 1), the sum telescopes to
  c·Σ_{k≥2} (1/(k-1) - 1/k + 1/k²) + (c - 1) = c·π²/6 + (c - 1), times Y²/2. ∎

**The R1 sum.** Apply Lemma Σ with c = 2 and ζ = log2 Y to the values Z'_j of the R1
levels, and bound the corrections using:
* (2⌈Y/Z'⌉ - 1)μ ≤ (2Y/Z' + 1)·μ_max, with μ_max = μ(2log2 Y) = log2(Y/log2 Y + 1);
* Σ_j 1/Z'_j ≤ 1/log2 Y + (1/δ)·ln(Y/log2 Y);
* #R1 < Y/δ.

The result:

    Σ_{R1} (d_j - 1)Z_j ≤ (S_2/δ)·Y² + 2Y·ln(Y/log2 Y)
                          + log2(Y/log2 Y + 1)·(2Y/log2 Y + (2Y/δ)·ln(Y/log2 Y) + Y/δ).

#### Theorem B (choice count of one `upcc` call)

Let m ≥ |V| ≥ 61 and Y := log2 m.  The number of complete choice sequences enumerated
for one `upcc_split_or_johnson` call satisfies

    log2 s_UPCC(m) ≤ (S_2/δ)·Y² + R(Y),   S_2 = 1/2 + π²/6,   S_2/δ = 2.1449341/0.5849625 = 3.66679,

with

    R(Y) = 2Y + [2Y]_2b + 2Y·ln(Y/log2 Y)
           + log2(Y/log2 Y + 1)·(2Y/log2 Y + (2Y/δ)·ln(Y/log2 Y) + Y/δ)
           + 2(Y + 1)·log2 Y·((log2 Y - 1)/δ + 1)
           + (3Y + 6)·log2(2Y + 4)
         ≤ 5.8·Y·log2²Y + 6.1·Y·log2 Y + 10.3·Y + 3.5·log2²Y + 6·log2 Y + 9.

So R(m) = O(log m·(log log m)²), which is of smaller order than
(log m)^1.5·log log m.  [2Y]_2b is present only in case 2b.

*Proof.*
* **(★) at the actual size.** Put Y_V := log2 n.  Apply (★) with the regions R1-R3
  evaluated at Y_V; every inequality above used Y_V = log2 n (in particular N1 < n = 2^Y_V
  in Lemma R).
* **The regions.** Add R1 + R2 + R3.  The term 2Y covers x (Y_V) and the half split
  (log2(n/3) < Y_V).
* **Passing to m.** Every term of R is non-decreasing in Y for Y ≥ e: ln(Y/log2 Y),
  Y/log2 Y and log2(Y/log2 Y + 1) are increasing for Y > e.  So Y_V can be replaced by
  log2 m ≥ Y_V.
* **The simplified form.** Use:
  * log2(Y/log2 Y + 1) ≤ log2 Y (Y ≥ 4);
  * ln(Y/log2 Y) ≤ ln 2·log2 Y;
  * 2(Y + 1)·log2 Y·((log2 Y - 1)/δ + 1) ≤ (2/δ)(Y + 1)·log2²Y;
  * log2(2Y + 4) ≤ log2 Y + 1.42 for Y ≥ 5.93.

  Collecting coefficients: 2ln2/δ + 2/δ = 5.79 for Y·log2²Y; 2ln2 + 1/δ + 3 = 6.10 for
  Y·log2 Y; 4 + 2 + 4.26 for Y; 2/δ for log2²Y; 6 and 8.52 for the rest. ∎

Numerical values (the two formulas above, evaluated at the given Y):

| Y = log2 m | (S_2/δ)Y² | R(Y) (WL path) |
|---|---|---|
| 8 | 235 | 486 |
| 20 | 1467 | 2043 |
| 64 | 15019 | 11572 |
| 128 | 60077 | 30979 |
| 1000 | 3.67e6 | 4.88e5 |

The main term dominates from about Y ≈ 40 on.

**Choice counts of `design_lemma`.**
* It examines P = Σ_{ell ≤ ℓ*} (n)_ell ≤ 2n^(k-1) tuples (n ≥ 2).
* It offers one choice with W ≤ (n)_ℓ* ≤ n^(k-1) candidates; ℓ* ≤ k - 2 if the result has
  kind 'b'.

**Choice count of `extended_design_lemma`** (X.n = m, X.k = k):

    s_EDL ≤ max( m^(k-1),  m^(k-2)·s_UPCC(m) ),
    log2 s_EDL ≤ (k - 2)·log2 m + max(log2 m, (S_2/δ)·log2²m + R(log2 m)).

* The first argument is kind 'a', or kind 'b' with a disconnected colour.  There the
  `select_min` keys are distinct ints (no tie), and `split_by_blocks` makes no choice.
* The second is kind 'b' uniprimitive, where ℓ ≤ k - 2 and the upcc call has |C| ≤ m and
  the WL key (no ties).

### 2.C Output guarantees (summary; the reachability proofs are in §2.A.1)

Let bound = alpha·|V|; for EDL this is (2/3)·m.  The structure returned by a run of `upcc`
satisfies one of:

**(a) Partition.** Every cell inside V has ≤ bound points.  The exits:
* L322-323: no dominant cell.
* B_i at L417 or L442: no cell > bound inside V1.  Cells inside V \ V1_0 have
  < n/3 < bound points, and the cells of V1_i \ V1'_i are ≤ bound.
* L454-456: an equipartition of V1' into N1/c ≥ 2 interchangeable blocks of size
  c = twsize ∈ [2, bound] (2 ≤ c by L444, c ≤ bound by (I5), and N1 > bound ≥ c).
* L485-490, half split: the two halves of V1' have size C(2d1 - 1, d1 - 1) = N1/2 < n/2 <
  bound.
* L590-591: no C1.
* L620-621, coherent "coloring":
  * L705-711: an equipartition of C1 into ≥ 2 blocks of equal size ≥ 2 and ≤ |C1|/2;
  * L727-733 or L776-779: colour classes of c(·, w), each of size ≤ |C1|/2 (Ex. 2.17a);
  * |C1|/2 < n/2 < bound.
* L624-625: |W1| ≤ bound, which is possible only in case C.  Then C1 \ W1 has
  < |C1|/2 < bound points.
* The tie split in upcc (L318, case 2b only) produces equal-size blocks of one key class,
  of size ≥ 2 (singleton classes take the thin-cycle exit); the class has ≤ n/3 < bound
  points.
* L315-317, thin-cycle exit (case 2b only): the structure is discrete on V (CORRECTNESS.md,
  Lemma 9.12(d)).

**(b) Johnson cell (L477-481).** Exactly one cell W ⊆ V has more than bound points:
* W = V1' with |W| = N1 = C(m', t') > bound;
* it carries `JohnsonCell(m' = n2, t' = d1)` with t' = d1 ≥ 2 and m' = n2 ≥ 2t' + 1;
* every other cell inside V has ≤ bound points.

Here n2 is |V2| at that level: n2 < n/3, and C(n2, d1) = N1 > (2/3)n.  The labels are a
bijection onto the d1-subsets of range(n2), as `align` requires (CORRECTNESS.md, Lemmas 6.1
and 6.3).

For EDL:
* kind 'a' (L55-57): the col1 classes have ≤ alpha·m points, because no class is
  > alpha·m;
* disconnected colour (L66-71): an equipartition of C into ≥ 2 blocks of equal size, in
  [2, |C|/2];
* uniprimitive: (a) or (b) with bound = (2/3)·m (alpha' = alpha·m/|C|, Babai Thm. 7.3.3).

---------------------------------------------------------------------------------------------------

## 3. Final table

Symbols:
* n = |V|, M = |Γ| (base.m), K_c ≤ M, Σ2 ≤ 2U2 ≤ 2n/3, L = ⌈lg n⌉.
* T = n2^d ≤ n2²·n^(1 + log2 log2 n).
* Q = (13d+76)n2² + (6d+33)n + 15d + 250.
* `Ck`/`Cc` are the Chooser symbols; other `C[...]` are the callees outside soj/design as
  named in §1.

| function | closed-form bound (one call) |
|---|---|
| soj.SOJParams.__init__ | 16 |
| soj.SOJParams.small_scale | ≤ 430 + 98·len(overrides) ≤ 920 (presets/tests only) |
| soj.SOJParams.small_v2_bound | 30 |
| soj.SOJParams.arity | ≤ 46 + 23s* ≤ 69 + 12·d1 |
| soj.flatten | F(u) ≤ 12u² + 68u, with u = |flatten(p)| (Lemma P) |
| soj.select_min | ≤ 88 + 38L' + L'(c_key + C_hk(σ_k) + 16σ_k + C_Fix) + Ck(9) + Cc(L'), with L' = len(cands) |
| soj.dominant_cell | ≤ 50 + 18K_c + 4M + 4K_c·|inside| ≤ 50 + 22M + 4M·|inside| |
| soj.twin_classes_bipartite | ≤ 37 + 44n1 + 3n1Σ2 |
| soj.max_twin_class | ≤ 72 + 56n1 + 3n1Σ2 |
| soj.restricted_adj | ≤ 30 + 16n1 + 4Σ2 + 8n1Σ2 |
| soj.reduce_part2_by_color | ≤ 284 + 144n1 + 8Σ2 + 22n1Σ2 |
| soj.twin_classes_kary(n, d) | ≤ (12d+33)n^(d+2) + (4d+11)n^d + 38n³ + 38n² + 31n + 101 ≤ (13d+76)n^(d+2) |
| soj.design_lemma(n, k) | ≤ 2n^(k-1)(28n² + 72n + 123 + k + C_pvc + C_ppc + n²C_c) + n^(k-1)(36 + 10k + 2kσ_pt) + 460 + 2n + 112k + kCk(6) + Cc(n^(k-1)) + C_pvc |
| soj.upcc_split_or_johnson (own) | ≤ 761 + 354n + 53.5n² + 9n²log2 n + 10nL + 34M + 4Mn + Ck(8,9,11,12) + Cc(n) + Cc(n²/4) + C_ind + C_ref + C_diag(n) + (n+n²)C_key + (n+n²/2)C_hk(1) + (n²/4)(C_hk(3)+C_Fix) + Σ_tied SBB (+ TC on the thin-cycle exit) |
| soj._thin_cycle_structure | ≤ 16n² + 2nL + 94n + 82 + 12M + Cc(q) + C_ref, q = len(cands) ≤ n - 1 |
| soj.individualize_until | ≤ 88 + 4|V| + (|V| - ⌊bound⌋ + 1)(76 + 22M + 4M|V| + 14|V| + 2|V|⌈lg|V|⌉ + 2|V|²⌈lg|V|⌉ + Ck(12) + Cc(|V|) + C_ind) (fallback only) |
| soj.bipartite_split_or_johnson (own, no DL choice) | ≤ 2287 + 454n + 41n² + (n²/6 + 3n + 2)L + 85M + 12Mn + T·Q + callees |
| soj.bipartite_split_or_johnson (own, DL level, incl. split/coherent member) | ≤ 3902 + 130d + 758n + 185n² + (n²/6 + 8n + 2)L + 114M + 12Mn + T·Q + C_RS(n2,d) + (2T/n2)(C_pvc + C_ppc) + 2T·n2·C_c + callees |
| soj._individualize_v2 | ≤ 206 + 60.5n2 + 4.5n2² + 2n2Σ2 + 4Σ2 + 12U2² + 68U2 + 46n1 + n1(13n2 + n2⌈lg n2⌉ + 4Σ2) + 12M + Σ_{r≤n2}Cc(r) + n2·C_mark + C_ref (not reached under SOJParams()) |
| soj._split_by_coloring_of_v2 | ≤ 543 + 103n2 + 8n2⌈lg n2⌉ + 160N1 + 12Σ2 + 30N1Σ2 + n2C_hk(1) + Ck(12) |
| soj.coherent_split_or_johnson | ≤ 1247 + 192n1 + 204n2 + 158n1n2 + 13n1Σ2 + (n2+5)Σ2 + 2n2⌈lg n2⌉ + F(u) + 24M + callees ≤ 1247 + 222n + 50n² + 0.67nL + 24M + callees |
| soj.split_by_blocks | ≤ 92 + 96q + 36K_c + 8M + 4K_c(q + |J|) + C_S ≤ 92 + 96q + 44M + 4M(q + |J|) + C_S |
| design.extended_design_lemma (own) | ≤ 583 + 98.5m + m⌈lg m⌉ + 12k + 6M + DL(m,k) + (callees of §1) |
| **one run of upcc** (Theorem A) | ≤ (Y/16 + 1/2)·n^(6+log2 log2 n) + 14n³ + (n³/18 + n² + n)L + 152n² + 763n + 4Mn² + 29Mn + (Y/δ)(4162 + 130Y + 758n + 185n² + (n²/6+8n+2)L + 114M + 12Mn) + 765 + 354n + 54n² + 9n²log2 n + 10nL + 34M + 4Mn + 16n² + 2nL + 94n + 82 + 12M + Σ callees (§2.A.2) |
| **one run of EDL** | ≤ E(m,k) + DL(m,k) + W_UPCC(|C|) |
| **choices, upcc** (Theorem B) | log2 s_UPCC(m) ≤ 3.66679·log2²m + R(log2 m), R(Y) ≤ 5.8Y·log2²Y + 6.1Y·log2 Y + 10.3Y + 3.5log2²Y + 6log2 Y + 9 |
| **choices, EDL** | log2 s_EDL ≤ (k-2)·log2 m + max(log2 m, log2 s_UPCC(m)) |
| **choices, design_lemma** | 1 choice, ≤ (n)_ℓ* ≤ n^(k-1) candidates; ≤ 2n^(k-1) tuples examined |

Functions used only by tests or presets: `SOJParams.small_scale` (`Params.small_scale`, tests).

**Could not prove, or shown false:**
1. **Own work of one run is not polynomial**, and n2^d ≤ m^c with a constant c is false for
   the arity rule as written.  The proven bound is n2^d ≤ n2²·n^(1 + log2 log2 n) (Lemma T).
   The parameter triple (n2, d1, N1) = (70, 35, ≈2^63) gives d = 35 and n2^d ≈ n^3.4, and
   n2 = 2Y with N1 < 2^Y gives n^(Θ(log log n)).  Such levels are not excluded
   here.  The resulting own work 2^(O(log n·log log n)) is negligible for a
   2^(b log³ n) bound.
2. **Case 2b's |V| ≥ 61** (H61) is assumed; for case 2b, PROOF.md §10 shows that |pts| ≥ 41 suffices.  For the EDL caller it follows from m ≥ ell(n) ≥ 90.
3. **Coherence of the WL outputs** (used in Lemma P and in the reachability lemmas) is taken
   from CORRECTNESS.md §7.


---------------------------------------------------------------------------------------------------

## 4. Profile numbers

### 4.1 `opcount.generate()` profiles

These are the soj and design entries of `babai_gi/_opprofiles.py`, which
`tests/test_opbounds.py` checks against `opcount.generate()`.  The two lambdas at bipartite
L618 share one key in `generate()`; they have 6 and 8 instructions.

```python
OPCOUNT_PROFILES = {   # opcount.generate(): (outside, [(line, cycle, entry), ...])
    'soj.SOJParams.__init__': (15, []),
    'soj.SOJParams.small_scale': (22, []),
    'soj.SOJParams.small_v2_bound': (26, []),
    'soj.SOJParams.arity': (31, [(113, 23, 9)]),
    'soj.flatten': (23, [(127, 9, 0)]),
    'soj.select_min': (42, [(136, 28, 0), (147, 7, 9)]),
    'soj.dominant_cell': (21, [(151, 17, 11)]),
    'soj.twin_classes_bipartite': (13, [(164, 23, 0)]),
    'soj.max_twin_class': (16, []),
    'soj.restricted_adj': (13, [(176, 8, 9)]),
    'soj.reduce_part2_by_color': (11, [(186, 21, 4)]),
    'soj.twin_classes_kary': (56, [(205, 6, 11), (206, 12, 0), (207, 36, 0), (211, 33, 4), (220, 15, 0)]),
    'soj.twin_classes_kary.<find@198>': (4, [(199, 19, 6)]),
    'soj.design_lemma': (47, [(242, 29, 48), (244, 74, 0), (247, 13, 0), (249, 13, 8), (257, 13, 2), (258, 23, 2), (269, 18, 11)]),
    'soj.upcc_split_or_johnson': (269, [(298, 13, 9), (306, 27, 0), (309, 68, 0), (317, 7, 9), (318, 12, 12), (331, 23, 0), (335, 32, 0), (349, 15, 8), (350, 17, 9)]),
    'soj._thin_cycle_structure': (58, [(367, 17, 0), (369, 12, 9), (372, 31, 0)]),
    'soj.individualize_until': (19, [(387, 49, 1), (388, 17, 11)]),
    'soj.bipartite_split_or_johnson': (1164, [(434, 7, 0), (435, 9, 0), (437, 12, 9), (450, 11, 8), (461, 8, 9), (464, 9, 9), (473, 7, 8), (474, 8, 12), (479, 16, 8), (480, 14, 16), (494, 14, 8), (497, 7, 0), (500, 12, 0), (501, 17, 0), (506, 28, 0), (512, 8, 11), (513, 7, 9), (515, 10, 9), (519, 14, 8), (522, 7, 8), (524, 10, 8), (540, 18, 0), (546, 14, 0), (553, 19, 12), (577, 15, 0), (579, 12, 8), (580, 11, 9), (582, 15, 8), (585, 10, 8), (587, 7, 8), (594, 13, 2), (595, 21, 2), (604, 12, 11), (610, 7, 9), (616, 7, 9), (617, 7, 9)]),
    'soj.bipartite_split_or_johnson.<vcol@556>': (44, []),
    'soj.bipartite_split_or_johnson.<pcol@562>': (78, []),
    'soj._individualize_v2': (53, [(636, 34, 3), (638, 9, 8), (642, 6, 12), (643, 17, 9)]),
    'soj._split_by_coloring_of_v2': (126, [(654, 13, 0), (657, 24, 8), (662, 17, 2), (667, 6, 8), (668, 10, 8)]),
    'soj.coherent_split_or_johnson': (624, [(699, 7, 8), (709, 7, 11), (709, 11, 11), (719, 7, 12), (719, 8, 11), (722, 23, 0), (725, 14, 11), (728, 8, 8), (731, 19, 9), (736, 26, 0), (737, 22, 9), (743, 12, 0), (745, 8, 8), (750, 8, 8), (751, 22, 9), (754, 10, 8), (756, 14, 8), (758, 21, 0), (760, 28, 0), (767, 8, 8), (771, 23, 0), (774, 14, 11), (777, 19, 9), (781, 18, 8), (783, 32, 0), (792, 18, 8), (793, 7, 8), (794, 8, 8), (795, 22, 9)]),
    'soj.split_by_blocks': (49, [(810, 8, 0), (811, 6, 0), (817, 35, 0), (820, 13, 0), (822, 13, 0)]),
    'design.extended_design_lemma': (257, [(52, 12, 0), (59, 13, 0), (70, 7, 11), (70, 8, 11)]),
}

OPCOUNT_NESTED = {     # lambdas / generator expressions: (total instructions, loops)
    'soj.max_twin_class.<genexpr@171>': (19, 1),
    'soj.twin_classes_kary.<genexpr@213>': (29, 1),
    'soj.design_lemma.<genexpr@269>': (20, 1),
    'soj.upcc_split_or_johnson.<lambda@299>': (8, 0),
    'soj.upcc_split_or_johnson.<genexpr@313>': (19, 1),
    'soj.upcc_split_or_johnson.<genexpr@326>': (25, 1),
    'soj.upcc_split_or_johnson.<lambda@340>': (20, 0),
    'soj.upcc_split_or_johnson.<lambda@348>': (16, 0),
    'soj.upcc_split_or_johnson.<genexpr@350>': (34, 1),
    'soj._thin_cycle_structure.<lambda@379>': (8, 0),
    'soj.individualize_until.<lambda@392>': (5, 0),
    'soj.bipartite_split_or_johnson.<lambda@438>': (8, 0),
    'soj.bipartite_split_or_johnson.<genexpr@451>': (36, 1),
    'soj.bipartite_split_or_johnson.<genexpr@479>': (20, 1),
    'soj.bipartite_split_or_johnson.<lambda@490>': (18, 0),
    'soj.bipartite_split_or_johnson.<genexpr@494>': (20, 1),
    'soj.bipartite_split_or_johnson.<genexpr@514>': (21, 1),
    'soj.bipartite_split_or_johnson.<genexpr@553>': (20, 1),
    'soj.bipartite_split_or_johnson.<lambda@575>': (8, 0),
    'soj.bipartite_split_or_johnson.<lambda@581>': (8, 0),
    'soj.bipartite_split_or_johnson.<genexpr@592>': (21, 1),
    'soj.bipartite_split_or_johnson.<lambda@618>': (8, 0),
    'soj._individualize_v2.<genexpr@643>': (20, 1),
    'soj._individualize_v2.<lambda@644>': (8, 0),
    'soj.coherent_split_or_johnson.<lambda@732>': (8, 0),
    'soj.coherent_split_or_johnson.<genexpr@737>': (34, 1),
    'soj.coherent_split_or_johnson.<genexpr@747>': (25, 1),
    'soj.coherent_split_or_johnson.<genexpr@751>': (34, 1),
    'soj.coherent_split_or_johnson.<genexpr@756>': (21, 1),
    'soj.coherent_split_or_johnson.<genexpr@761>': (28, 1),
    'soj.coherent_split_or_johnson.<lambda@778>': (8, 0),
    'soj.coherent_split_or_johnson.<genexpr@795>': (34, 1),
    'soj.coherent_split_or_johnson.<lambda@798>': (16, 0),
    'design.extended_design_lemma.<lambda@54>': (6, 0),
}
```

### 4.2 Region profiles used in the proofs (Lemma 1.1')

`tests/test_soj_regions.py` recomputes this table from the code and checks the hypotheses
(R1)-(R6) of §0.2 on every code object listed.  Keys are as in §4.1; a second code object
with the same key gets the suffix `#2`.  The entry `johnson.iroot` is the region profile
used in ownwork.md §3.1.

```python
# region profiles (Lemma 1.1'): (outside', [(line of the loop's target instruction, cycle'), ...])
REGION_PROFILES = {
    'soj.SOJParams.__init__': (15, []),
    'soj.SOJParams.small_scale': (22, []),
    'soj.SOJParams.small_v2_bound': (26, []),
    'soj.SOJParams.arity': (40, [(114, 23)]),
    'soj.flatten': (23, [(127, 9)]),
    'soj.select_min': (51, [(136, 28), (147, 7)]),
    'soj.dominant_cell': (32, [(151, 17)]),
    'soj.twin_classes_bipartite': (13, [(164, 23)]),
    'soj.max_twin_class': (16, []),
    'soj.max_twin_class.<genexpr@171>': (10, [(171, 9)]),
    'soj.restricted_adj': (22, [(176, 8)]),
    'soj.reduce_part2_by_color': (15, [(186, 21)]),
    'soj.twin_classes_kary': (67, [(205, 6), (206, 12), (207, 40), (211, 33), (220, 15)]),
    'soj.twin_classes_kary.<find@198>': (10, [(200, 19)]),
    'soj.twin_classes_kary.<genexpr@213>': (11, [(213, 18)]),
    'soj.design_lemma': (109, [(242, 29), (244, 81), (247, 13), (249, 13), (257, 15), (258, 23),
                               (269, 18)]),
    'soj.design_lemma.<genexpr@269>': (11, [(269, 9)]),
    'soj.upcc_split_or_johnson': (302, [(298, 13), (306, 27), (309, 82), (317, 7), (318, 8), (318, 4),
                                        (331, 23), (335, 32), (349, 15), (350, 17)]),
    'soj.upcc_split_or_johnson.<lambda@299>': (8, []),
    'soj.upcc_split_or_johnson.<genexpr@313>': (10, [(313, 9)]),
    'soj.upcc_split_or_johnson.<genexpr@326>': (11, [(326, 14)]),
    'soj.upcc_split_or_johnson.<lambda@340>': (20, []),
    'soj.upcc_split_or_johnson.<lambda@348>': (16, []),
    'soj.upcc_split_or_johnson.<genexpr@350>': (11, [(350, 23)]),
    'soj._thin_cycle_structure': (61, [(367, 23), (369, 12), (372, 31)]),
    'soj._thin_cycle_structure.<lambda@379>': (8, []),
    'soj.individualize_until': (24, [(388, 56), (388, 17)]),
    'soj.individualize_until.<lambda@392>': (5, []),
    'soj.bipartite_split_or_johnson': (1397, [
        (434, 7), (435, 9), (437, 12), (450, 11), (461, 8), (464, 9), (473, 7), (474, 8), (479, 16),
        (480, 14), (494, 14), (497, 7), (500, 12), (501, 17), (506, 28), (512, 8), (513, 7),
        (515, 10), (519, 14), (522, 7), (524, 10), (540, 18), (546, 14), (553, 19), (577, 15),
        (579, 12), (580, 11), (582, 15), (585, 10), (587, 7), (594, 15), (595, 21), (604, 12),
        (610, 7), (616, 7), (617, 7)]),
    'soj.bipartite_split_or_johnson.<lambda@438>': (8, []),
    'soj.bipartite_split_or_johnson.<genexpr@451>': (11, [(451, 25)]),
    'soj.bipartite_split_or_johnson.<genexpr@479>': (11, [(479, 9)]),
    'soj.bipartite_split_or_johnson.<lambda@490>': (18, []),
    'soj.bipartite_split_or_johnson.<genexpr@494>': (11, [(494, 9)]),
    'soj.bipartite_split_or_johnson.<genexpr@514>': (11, [(514, 10)]),
    'soj.bipartite_split_or_johnson.<genexpr@553>': (11, [(553, 9)]),
    'soj.bipartite_split_or_johnson.<vcol@556>': (44, []),
    'soj.bipartite_split_or_johnson.<pcol@562>': (78, []),
    'soj.bipartite_split_or_johnson.<lambda@575>': (8, []),
    'soj.bipartite_split_or_johnson.<lambda@581>': (8, []),
    'soj.bipartite_split_or_johnson.<genexpr@592>': (11, [(592, 10)]),
    'soj.bipartite_split_or_johnson.<lambda@618>': (6, []),
    'soj.bipartite_split_or_johnson.<lambda@618>#2': (8, []),
    'soj._individualize_v2': (80, [(637, 39), (638, 9), (642, 6), (643, 17)]),
    'soj._individualize_v2.<genexpr@643>': (11, [(643, 9)]),
    'soj._individualize_v2.<lambda@644>': (8, []),
    'soj._split_by_coloring_of_v2': (152, [(654, 13), (657, 24), (662, 17), (667, 6), (668, 10)]),
    'soj.coherent_split_or_johnson': (802, [
        (699, 7), (709, 15), (709, 11), (719, 15), (719, 8), (722, 23), (725, 14), (728, 8),
        (731, 19), (736, 32), (737, 22), (743, 12), (745, 8), (750, 8), (751, 22), (754, 10),
        (756, 14), (758, 21), (760, 28), (767, 8), (771, 23), (774, 14), (777, 19), (781, 18),
        (783, 32), (792, 18), (793, 7), (794, 8), (795, 22)]),
    'soj.coherent_split_or_johnson.<lambda@732>': (8, []),
    'soj.coherent_split_or_johnson.<genexpr@737>': (11, [(737, 23)]),
    'soj.coherent_split_or_johnson.<genexpr@747>': (11, [(747, 14)]),
    'soj.coherent_split_or_johnson.<genexpr@751>': (11, [(751, 23)]),
    'soj.coherent_split_or_johnson.<genexpr@756>': (11, [(756, 10)]),
    'soj.coherent_split_or_johnson.<genexpr@761>': (11, [(761, 17)]),
    'soj.coherent_split_or_johnson.<lambda@778>': (8, []),
    'soj.coherent_split_or_johnson.<genexpr@795>': (11, [(795, 23)]),
    'soj.coherent_split_or_johnson.<lambda@798>': (16, []),
    'soj.split_by_blocks': (49, [(810, 8), (811, 6), (817, 35), (820, 13), (822, 13)]),
    'design.extended_design_lemma': (271, [(52, 12), (59, 13), (70, 15), (70, 8)]),
    'design.extended_design_lemma.<lambda@54>': (6, []),
    'johnson.iroot': (19, [(155, 21)]),
}
```
