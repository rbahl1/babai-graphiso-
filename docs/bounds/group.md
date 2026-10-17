# Instruction-count bounds for `perm.py`, `group.py`, `action.py`, `canon.py`, `tower.py`

Scope: every function and method of `babai_gi/perm.py`, `babai_gi/group.py`,
`babai_gi/action.py`, `babai_gi/canon.py`, `babai_gi/tower.py`, in the cost model of
`SPEC.md`.  All profile numbers are those of `babai_gi/opcount.py` (`FOR_ITER` attributed to
its loop, `yield from` as loop kind `YieldFrom`, EXTENDED_ARG prefixes of loop heads, `loops`
count of nested code objects; PROOF.md, Lemma 1.1).
None of these modules calls back into the solver (`grep solver|iso_window|\.iso(` finds only
comments), so **no function below has a "solver calls" item**.

---------------------------------------------------------------------------------------------

## 0. Facts used outside this document

1. **`FOR_ITER` attribution.**  CPython 3.13 gives the `FOR_ITER` of a `for` loop or
   comprehension the position of the iterable; `opcount.profile` attributes it to its loop
   (PROOF.md, Lemma 1.1), so the profiles count it once per iteration plus once per entry
   (e.g. `perm.inv` on a permutation of length 100 executes at most `18 + 7·101 = 725` own
   instructions, §3).
2. **`yield from`** (`PermGroup.elements`, `PermGroup.coset_reps_prefix` and their `rec`) is a
   loop (`YieldFrom`); its iterations are the values passed through.  The amortised bounds of
   §4 (`elements`) use it.
3. **Cameron–Solomon–Turull** is `λ_N = ⌈3N/2⌉ - b(N) - 1` (with the ceiling); the form
   `3N/2 - b(N) - 1` without the ceiling is false for odd N (N = 3: `1 < C_2 < S_3` has
   length 2 > 1.5).  §1.5.
4. In the package `base_order` is never passed to `PermGroup`, `forced_prefix` is always
   duplicate-free, and every `PermGroup` keeps at most `max(6, λ_N)` generators (Lemma G), so
   the number of generators of any existing group is bounded by a function of its degree.
5. `group.PermGroup._build.<genexpr@94>` has `loops 1`: its three `JUMP_BACKWARD`s (the two
   `if` filters and the loop end) all target its single `FOR_ITER` (offset 12), so each
   element of `range(n)` executes each instruction at most once and the rule
   "total × (L + 1)" applies.  The same holds for every genexpr of these modules (each has
   exactly one backward-jump target, a `FOR_ITER`; checked by `tests/test_attribution.py`);
   there are no lambdas in these modules.

---------------------------------------------------------------------------------------------

## 1. Conventions

### 1.1 Parameters and standing assumptions

* `N` — degree (`.n`) of the `PermGroup` at hand.  A **permutation of degree N** is a tuple
  of length N whose entries are a rearrangement of `range(N)`.
* (A1) Every element of the `gens` iterable passed to `PermGroup(n, gens, ...)` is a sequence
  of length `n` that is a permutation of `range(n)` (wrong length: `ValueError` exit).  All
  constructions in the package produce such sequences (generators of groups, images under
  induced actions / restrictions, projections `g[:n]` of combined permutations — which map
  `range(n)` onto itself —, products and inverses of those).
* `r` — number of elements of the `gens` iterable passed to a constructor; `ρ = ρ_G =
  len(G.gens)` for an existing group (distinct, non-identity, `ρ ≤ r`).
* `F = len(forced_prefix)`.  (A2) `forced_prefix` is duplicate-free with entries in
  `range(n)`: its callers are `prefix_group` (deduplicates with `dict.fromkeys`),
  `comb_omega` / `comb_gamma` (`range(n)`, `range(n, n+m)`) and
  `certificates.kernel_and_lifts` (`[n + a for a in sorted(A)]`, `A` a frozenset).  So F ≤ N.
* `B = len(base_order)`.  (A3) No caller passes `base_order`, so `self.base_order =
  list(range(n))` and `B = N`.  General formulas keep `B` (assuming `base_order ⊆ range(n)`).
* Stabilizer chain of a built group: `ℓ` levels, `d_k = len(levels[k].trans)`,
  `s_k = len(levels[k].gens)`.
* `λ_N` — maximal length of a strictly increasing chain of subgroups of `S_N` (§1.5);
  `γ_N = max(6, λ_N)`.
* `GroupWithAction`: `n = G.n = |Ω|`, `m = |Γ|`, `M = n + m` (degree of the combined group).
* Letters of strings are `int`s (the solver's entry point normalizes them: `main.py:1086`,
  `normalize_letters`); comparing two letters is one instruction.
* Bounds hold for all parameter values ≥ 0 unless a range is stated; simplified closed forms
  state their range (usually N ≥ 2).  `⌈log2 x⌉ := 0` for x ≤ 1.

### 1.2 Counting own instructions (Lemma R)

**Lemma R.**  One execution of a code object of these modules (function, method, inner
function, generator — including the instructions run when an abandoned generator is closed)
executes at most

    outside + Σ_loops [ cycle·(I + E) + entry·E ]

of its own instructions (profile numbers of `opcount.profile`; `I`/`E` = total
iterations/entries of the loop in that execution; for a `YieldFrom` loop, `I` = number of
values passed through, `E` = number of executions of the `yield from`).  A generator expression
of total `T` consuming an iterable of `L` elements executes at most `T·(L+1)` instructions.

*Proof.*  An instruction at offset x executed twice in one frame requires, in between, a
backward jump `j → t` with `t ≤ x ≤ j` (a resumed generator continues after its
`YIELD_VALUE`).  `tests/test_attribution.py` checks the hypotheses of PROOF.md, Lemma 1.1
on every code object of the five modules (every backward jump belongs to a loop; every
instruction in the range `[t, j]` of a backward jump is attributed to the cycle of the loop
owning that jump or to a loop nested in it; every exception handler lies after the code it
protects).  The only backward jump outside these hypotheses is the exit jump of the
`except TypeError` handler of `canon.normalize_letters` (offset 328 → 154, back to the code
after the `try`), which belongs to no loop.  That code is reached either by falling out of the
`try` body or through the handler, never both, and the handler runs at most once (no loop
encloses the `try`).  Hence every instruction of a loop's cycle runs at most once per
iteration plus once per entry, every other instruction of a level at most once per entry
(once per call for `outside`).  When a suspended generator is closed,
`GeneratorExit` enters the `CLEANUP_THROW` handler (in the `YieldFrom` cycle, executed at most
once, and `I + E ≥ 1` there) and leaves through `CALL_INTRINSIC_1, RERAISE` (outside,
executed at most once), so the close path is covered.  Genexprs: each has one backward-jump
target, its `FOR_ITER` (`tests/test_attribution.py`, §0.5), so each element runs every
instruction at most once and prologue, exhaustion and epilogue are distinct instructions.  ∎

### 1.3 Built-in costs (beyond the instructions)

| operation | cost charged |
|---|---|
| fixed-size built-in call: `len`, `isinstance`, `getattr`, `int()`, `bit_length`, `list.append`, `deque.append/popleft`, `list.pop()`, `set()`/`deque()` empty, `min(a, b)`, truth test of a deque, import of an already loaded module | 1 |
| dict/set lookup, `in`, `.get`, `[]`, store, `.add`, `.setdefault` with an `int` key (1 + hash 1 + one comparison 1) | 3 |
| the same with a key that is a tuple of L ints (hash L, comparison L) | 2L + 1 |
| the same with a frozenset of L ints (hash L, comparison of both operands 2L) | 3L + 1 |
| `list(it)`, `tuple(it)` (also when `it` is already a tuple), `deque(it)` with L elements; `[x]*L`; slice of length L; tuple/list concatenation of result length L; `list.extend` by L | L + 1 |
| `set(it)`, `frozenset(it)`, `dict.fromkeys(it)` with L int keys (touch + insertion) | 4L + 1 |
| one step of `range`, `enumerate`, `zip`, `map`, dict iteration, `.values()` | 1 per element produced, + 1 for the exhausting step |
| `map(f, …)` with a built-in `f` (`q.__getitem__`) | additionally 1 per call of `f` |
| `==`, `!=`, `<` on flat tuples/lists of ints | (element pairs compared) + 1 ≤ min length + 1 |
| `str` comparison | 1 + min length |
| `sorted` / `list.sort` of L items | `L·⌈log2 L⌉·κ + 2L + 1`, κ = max cost of one key comparison (+ the key calls) |
| `x in list` | len + 1 |
| `deque.clear()` of size s | s + 1 |
| `math.factorial(m)` | m |
| int arithmetic and comparison (any size) | 0 (only the instruction) |

Python code reached from a built-in is charged by its own bound (e.g. `key=canon`).

### 1.4 Callees, laziness and caches

`C[f](params)` denotes the bound proved for `f`.  Abbreviations (proved in §3, §4):

    Id(N) = C[perm._ident] = 2N + 28        Ident(N) = C[perm.identity] = 2N + 33
    Isid(N) = C[perm.is_identity] = 3N + 39  Mul(N) = C[perm.mul] = 3N + 11
    Inv(N) = C[perm.inv] = 10N + 29         Par(N) = C[perm.parity] = 55N + 43
    Init0(N, r, F) = 113 + 2N + 2F + r(8N + 80)        (PermGroup.__init__ without _build)
    Build(N, ρ, F, B)                                  (one real run of _build, Lemma B)
    Build(N, ρ) := Build(N, ρ, F, N) with F ≤ N        (all callers)

**Laziness convention.**  `G._build()` does real work at most once per `PermGroup` object (it
returns at once when `self._levels is not None`, and `self._levels` is assigned on line 95,
before any statement that can raise on valid input).  Define

    β(G) = cost of one call G._build()  ≤ Build(N_G, ρ_G, F_G)  if G was not built,
                                        ≤ 149 (the outside count; actually 15) otherwise,

and **charge β every time a function may trigger the build (upper bound β ≤ Build)**.  The
small value is used only where the group is proved to be already built at that point (stated
each time; the charge written there is 153 ≥ 149).  A group constructed with more than 6
distinct non-identity generators is built inside `__init__`; so "construct H, then build H"
costs at most `Init0(N, r, F) + Build(N, ρ, F) + 153` in all cases.  The other caches (`_orbits`,
`prefix_cache`, `lifter_cache`, `_comb_omega`, `_comb_gamma`, `_kernel`, `_image`,
`_image_is_giant`, `_H`, `_lifted_by`) are charged at their full uncached cost; a cheaper
"cached / steady" bound is given in addition and is used only where the hit is proved.

### 1.5 Chains of subgroups

**Lemma C.**  Let `λ_N` be the maximum t with `1 = H_0 < H_1 < … < H_t ≤ S_N`.
(a) `λ_N ≤ ⌊log2 N!⌋ ≤ N·log2 N` (elementary: `|H_{i+1}| ≥ 2|H_i|` by Lagrange).
(b) P. J. Cameron, R. Solomon, A. Turull, *Chains of subgroups in symmetric groups*,
J. Algebra 127 (1989) 340–352: `λ_N = ⌈3N/2⌉ - b(N) - 1`, `b(N)` = number of ones in the
binary expansion of N.  Hence `λ_N ≤ (3N+1)/2 - 2 = (3N-3)/2 < 3N/2` for N ≥ 1.
All bounds are stated with the symbol λ_N; "CST" marks the substitution λ_N ≤ 3N/2; with (a)
instead (replace 3N/2 by N·log2 N) everything remains valid without the citation.
λ is monotone in N.

---------------------------------------------------------------------------------------------

## 2. The Schreier–Sims build (`PermGroup._build`): structural lemmas

Fix one call of `_build` that does real work.  Levels `L_0, …, L_{ℓ-1}` (ℓ grows during the
run); level k has base point `b_k`, generator list `S_k` (`lev.gens`), transversal dict `T_k`
(`lev.trans`; `lev.trans_inv` has the same keys and the inverse values), pending deque `Q_k`.
`ρ = len(self.gens)` at the call (`= len(gl)` of `__init__`), `F = len(forced_prefix)`.
Recall `mul(p, q)` is "p then q": `i^{pq} = q[p[i]]`, and `h[b] = b^h`.

**Lemma S0 (early stop).**  Let the *shadow run* be the execution of the same call with
`target = None`.  The real run (`target = known_order`) performs the same state changes as
the shadow run until the first time `current_order() == target` is evaluated true (lines 167,
189; line 180 at the start); then it clears every pending deque once (loop 168 or 190), the
main loop stops at its next iteration (`if done: break`), and line 195 runs.  The only other
difference is the evaluations of `current_order()`, which change no state.
*Proof.*  `target` is used only on lines 96, 167, 180, 189; inspection.  ∎
Hence every iteration count of the real run is at most the corresponding count of the shadow
run, and the real run costs at most the shadow-run bound plus the `current_order()` calls
(charged below after *every* add, whatever `target` is) plus one clearing loop (charged).
**No bound below depends on whether `known_order` is correct** (a wrong value only yields a
wrong group, e.g. a proper subgroup).  S1–S4 are statements about the shadow run.

**Lemma S1 (invariants).**  Outside the execution of `add_strong_gen`:
(a) every element of `S_k` fixes `b_0, …, b_{k-1}`;
(b) `keys(T_k)` is the orbit `b_k^{<S_k>}`, `T_k[p] ∈ <S_k>` with `b_k^{T_k[p]} = p`, and
    `trans_inv[p] = T_k[p]^{-1}`; entries are never changed or removed;
(c) `<S_j> ≤ <S_k>` for `k ≤ j`;
(d) the pairs ever appended to `Q_k` are exactly `{(p, i) : p ∈ keys(T_k), 0 ≤ i < |S_k|}`,
    each appended once;
(e) for every pair `(p, i)` already popped from `Q_k`, `y(p, i) = T_k[p]·S_k[i]·T_k[q]^{-1}`
    (`q = p^{S_k[i]}`) lies in `<S_{k+1}>` (`<S_ℓ> := 1`);
(f) the base points are distinct points moved by some generator; the `RuntimeError` branch
    (line 138) is unreachable.

*Proof.*  (a) `sift(g, start)` multiplies g on the right by `trans_inv_i[g[b_i]] ∈ <S_i>`,
which maps `g[b_i]` to `b_i`; by induction on i (using (a), (b) for `S_i`) the product fixes
`b_0..b_i` if g fixed `b_0..b_{start-1}`.  Main loop: start 0.  Closure at level i:
`y = T_i[p]·s·T_i[q]^{-1}` with all three factors in `<S_i>` (fixing `b_0..b_{i-1}`) and
`b_i ↦ p ↦ q ↦ b_i`, so y fixes `b_0..b_i`, and sift starts at `i+1`.  So the residue h at
level j fixes `b_0..b_{j-1}`, and h is appended only to `S_k` with `k ≤ j`.
(b) Initially `{b_k: id}`.  `extend_orbit` inserts `T[q] = T[p]·s` for a key p and `s ∈ S_k`
only when q is not a key; its queue starts with *all* keys and receives every new key, and
every popped point is tried against every `s ∈ S_k`; so on return the keys are closed under
`S_k`, i.e. equal the orbit.  `trans_inv[q] = inv(T[q])` is inserted together with `T[q]`.
(c) Induction over the calls `add_strong_gen(h, lo, hi)`.  The only way to break (c) is to add
h to `S_j` and not to `S_k` for some `k < j`.  Main loop: `lo = 0`, impossible.  Closure at
level i: `lo = i+1`; h is the residue of `y ∈ <S_i>` after multiplication by elements of
`<S_t>`, `t ≥ i+1`, which lie in `<S_i>` by induction; so `h ∈ <S_i> ≤ <S_k>` for `k ≤ i`.
A new level starts with `S = [h]`, covered by the same argument.
(d) `extend_orbit(lev, t)` (t = index of the new generator) appends `(p, t)` for every key p
present before the call; every newly found q gets `(q, i)` for all `i < |S_k|` (t included).
So `(p, i)` is appended exactly when the later of "p becomes a key" and "`S_k[i]` is added"
happens.  In the shadow run pairs leave `Q_k` only by `popleft`.
(e) At the pop: if `y = id` trivially.  Otherwise `(j, h) = sift(y, k+1)`, so
`y·v_{k+1}⋯v_{j-1} = h` with `v_t ∈ <S_t> ≤ <S_{k+1}>` by (c).  If `h = id`, `y ∈ <S_{k+1}>`.
Else `add_strong_gen(h, k+1, j)` puts h into `S_{k+1}` (`j ≥ k+1`), so again `y ∈ <S_{k+1}>`.
Groups only grow and `T_k` entries never change, so this persists.
(f) Forced levels: distinct by (A2) and moved (line 89).  A new level is created when the
residue h has `j = len(levels)`, so h fixes all existing base points (a).  h lies in
`<gens>`, so it moves only points moved by some generator; the moved prefix points are all
base points of forced levels; hence every point moved by h is outside `prefix_set`, and
`rest_order` contains every point of `range(n) \ prefix_set` (lines 92–94).  So the loop of
line 133 finds a new point b.  ∎

**Lemma S2 (completeness).**  If at some moment `Q_k = ∅` for all `k ≥ k_0`, then
`Stab_{<S_k>}(b_k) = <S_{k+1}>` for every `k_0 ≤ k < ℓ`.
*Proof.*  By Schreier's lemma `Stab_{<S_k>}(b_k)` is generated by the elements `y(p, i)` of
S1(e) for the transversal `T_k` of S1(b); all of them have been popped (S1(d)), so they lie
in `<S_{k+1}>`.  Conversely `S_{k+1} ⊆ <S_k>` (S1(c)) fixes `b_k` (S1(a)).  ∎

**Invariant (I) of `closure`.**  At the head of every iteration of the `while` loop (line 154)
with current value i, `Q_k = ∅` for all `k > i`.  *Proof.*  True for `i = len(levels)-1`.  A
pop at level i either adds nothing, or adds pairs to levels `i+1..j` only (add_strong_gen)
and then sets `i := j` (line 171; after the call `j < len(levels)`, so `i = j`); levels `> j`
are untouched.  A decrement happens only when `Q_i = ∅`.  ∎  Consequently `closure()`
returns `False` only when all deques are empty.

**Lemma S3 (strict growth).**  At every call `add_strong_gen(h, lo, hi)` of the shadow run,
`h ∉ <S_k>` for every `lo ≤ k ≤ hi` (`S_k` before the call; `S_k = ∅` for a level about to be
created).
*Proof.*  At the call, `Q_k = ∅` for all `k ≥ lo`: in the main loop (`lo = 0`) all deques are
empty — before the first essential generator only forced levels with empty `S`, `Q` exist,
and before each later one the previous `closure()` returned `False`; in `closure` (`lo = i+1`)
by (I).  Suppose `h ∈ <S_k>`, `lo ≤ k ≤ j := hi`.  h fixes `b_k..b_{j-1}` (S1(a)), so S2 at
levels `k, …, j-1` gives `h ∈ <S_j>`.  If `j` is the old `len(levels)`, `<S_j> = 1` and
`h ≠ id`: contradiction.  Otherwise `b_j^h ∈ keys(T_j)` (S1(b)), contradicting that `sift`
stopped at level j (`trans_inv_j.get(h[b_j])` is `None`).  ∎

**Corollary S4 (counts of the shadow run).**  At its end let `e` = number of essential
generators, `A` = number of `add_strong_gen` calls, `E` = number of `extend_orbit` calls,
`P = Σ_k d_k s_k` (Schreier pairs registered, S1(d)).
(a) `ℓ ≤ μ ≤ N` (μ = number of points moved by the generators); base points distinct (S1(f)).
(b) `d_k ≤ N - k` (the orbit of `b_k` avoids `b_0..b_{k-1}`, S1(a)).
(c) `s_k ≤ λ_N` (indeed `≤ λ_{N-k}`): by S3 each addition to `S_k` strictly enlarges `<S_k>`,
    so `<∅> < <S_k^{(1)}> < …` is a chain of length `s_k` in `S_N` (in the pointwise
    stabilizer of `b_0..b_{k-1}`).
(d) `e = s_0 ≤ min(ρ, λ_N)`: the main loop adds each essential residue to level 0, `closure`
    never adds to level 0 (`lo = i+1 ≥ 1`).
(e) `A ≤ Σ_k (d_k - 1) ≤ N(N-1)/2`: a call with `hi = j` makes `b_j^h` a new key of `T_j`
    (for a new level, `d_j` goes from 1 to ≥ 2).  The A strong generators are pairwise
    distinct (two equal ones added to overlapping level ranges contradict S3; if the ranges
    are disjoint, say `hi_1 < lo_2`, the one added to `[lo_1, hi_1]` is a residue at `hi_1`
    and moves `b_{hi_1}`, the other fixes `b_0..b_{hi_2 - 1} ∋ b_{hi_1}`).  Also `A ≤ ℓ·λ_N`.
(f) `E = Σ_k s_k ≤ ℓ·λ_N ≤ N·λ_N`.
(g) `P ≤ λ_N · Σ_{k<ℓ} (N - k) ≤ λ_N·N(N+1)/2`; number of pops ≤ P; number of calls of the
    inner `sift` ≤ ρ + P; number of `closure()` calls ≤ e.
(h) The total number `W` of iterations of the `while` loop of `closure` (over all calls) is
    `≤ P + ℓ(e + A)`: an iteration pops a pair or decrements i; in one call i starts at
    `≤ ℓ-1` and ends at -1, each reset `i := j` raises it by `≤ ℓ-1`; there are `≤ e` calls
    and `≤ A` resets.
(i) `Q := Σ_k d_k s_k(s_k+1) ≤ λ_N(λ_N+1)·N(N+1)/2`, `V := Σ_k (d_k - 1) ≤ N(N-1)/2`,
    `V_s := Σ_k (d_k - 1)s_k ≤ λ_N·N(N-1)/2`.

**Lemma G (generators kept).**  After `PermGroup.__init__`, `len(self.gens) ≤ min(r, γ_N)`,
`γ_N = max(6, λ_N)` (CST: `≤ max(6, (3N-3)/2)`).  Precisely: `self.gens = gl` (distinct,
non-identity) if `|gl| ≤ 6`, and otherwise `self.gens = essential`, of length `e ≤
min(|gl|, λ_N)` (S4(d); in the real run `essential` is a prefix of the shadow run's list,
S0).  The pruned list is irredundant: by induction `<S_0> = <essential so far>` (each residue
differs from its generator by a product of transversal elements, which lie in `<S_0>` by
S1(c)), and the t-th essential generator is not in the group generated by the earlier ones
(S3 for `k = 0`).  `self.gens` is assigned only in `__init__` (line 56) and in `_build`
under `prune=True` (line 197), called only from `__init__` (grep), so the bound holds for every
`PermGroup` object at all times.  Strong generators: per level `s_k ≤ λ_N`, in total
`A ≤ min(N(N-1)/2, ℓ·λ_N)` distinct ones (S4(e)).

---------------------------------------------------------------------------------------------

## 3. `perm.py`

Throughout, `p`, `q`, `g` are permutations of degree N (= `len(p)`), `L = len(x)` for a string
or a sequence argument.  Notation: `loop ℓ (kind c/e)` = profile line, cycle, entry;
"I, E" are the iteration/entry bounds; its charge is `c(I+E) + e·E` (Lemma R).

### perm.identity
Profile: outside 5, no loops.  Callee `_ident(n)`.  Bound: `5 + Id(n) = 2n + 33`.

### perm._ident
Profile: outside 20.  Built-ins: `_ID_CACHE.get(n)` 3; on a miss `tuple(range(n))` (range
n+1, tuple n+1) and the store 3 (charged as a miss every time).
Bound: `20 + 3 + 2(n+1) + 3 = 2n + 28`.

### perm.is_identity
Profile: outside 9.  Built-ins: `len` 1, tuple `==` ≤ N+1.  Callee `_ident(N)`.
Bound: `9 + 1 + (2N+28) + (N+1) = 3N + 39`.

### perm.mul
Profile: outside 9.  Built-ins: `map` N+1 steps and N calls of `q.__getitem__`, `tuple` N+1.
Bound: `9 + (N+1) + N + (N+1) = 3N + 11`.

### perm.mul_all
K = len(perms), all of degree n.  Profile: outside 11; loop 43 (For 7/0): I = K, E = 1 →
`7(K+1)`.  Callees: `identity(n)`, K × `mul`.
Bound: `11 + 7(K+1) + (2n+33) + K(3n+11) = K(3n + 18) + 2n + 51`.  (Not used by the package.)

### perm.inv
Profile: outside 18; loop 50 (For 7/0): I = N (enumerate over p), E = 1 → `7(N+1)`.
Built-ins: `len` 1, `[0]*N` N+1, `enumerate` N+1, `tuple(r)` N+1.
Bound: `18 + 7(N+1) + 1 + 3(N+1) = 10N + 29`.

### perm.identity_perm
outside 5 + `_ident(n)`: `2n + 33`.  (Not used by the package.)

### perm.conj
outside 11; `inv(g)`, 2 × `mul`: `11 + (10N+29) + 2(3N+11) = 16N + 62`.  (Not used.)

### perm.from_cycles
c = number of cycles, T = Σ len(cyc).  Profile: outside 15; loop 66 (For 13/0): I = c, E = 1
→ `13(c+1)`; loop 68 (For 13/0): one entry per cycle, `len(cyc)` iterations each: I = T,
E = c → `13(T+c)`.  Built-ins: `list(range(n))` 2n+2, `len(cyc)` c, `range(k)` T+c,
`tuple(r)` n+1.  Bound: `15 + 13(c+1) + 13(T+c) + (2n+2) + c + (T+c) + (n+1)
= 3n + 28c + 14T + 31`.

### perm.cycles
Profile: outside 20; loop 76 (For 23/0): I = N → `23(N+1)`; loop 80 (While 16/4): entered once
per i with `not seen[i] and p[i] != i` (E ≤ N); each iteration marks a new j (I ≤ N) →
`16(I+E) + 4E ≤ 36N`.  Built-ins: `len` 2, `[False]*N` N+1, `range` N+1, `c.append` ≤ N,
`out.append` ≤ N.  Bound: `20 + 23(N+1) + 36N + 2 + 2(N+1) + 2N = 63N + 47`.  (Not used.)

### perm.parity
Profile: outside 20; loop 92 (For 19/0): I = N → `19(N+1)`; loop 96 (While 15/4): entered once
per unseen i (E ≤ N), each iteration marks a new point (I ≤ N) → `15(I+E) + 4E ≤ 34N`.
Built-ins: `len` 2, `[False]*N` N+1, `range` N+1.
Bound: `20 + 19(N+1) + 34N + 2 + 2(N+1) = 55N + 43`.

### perm.support
Profile: outside 11; loop 105 (ListComp 10/12): I = N → `10(N+1) + 12`; `enumerate` N+1.
Bound: `11N + 34`.  (Not used by the package.)

### perm.act_string
L = len(x), p a permutation of degree L.  Profile: outside 18; loop 111 (For 8/0): I = L →
`8(L+1)`.  Built-ins: `len` 1, `[None]*L` L+1, `enumerate` L+1, `tuple` L+1.
Bound: `11L + 30`.

### perm.act_set
L = len(S).  Profile: outside 13; genexpr@117 (total 20, 1 loop) → `20(L+1)`; `frozenset`
4L+1 (int keys).  Bound: `24L + 34`.  (Not used.)

### perm.act_tuple
outside 13; genexpr@121 (total 20) `20(L+1)`; `tuple` L+1.  Bound: `21L + 34`.  (Not used.)

### perm.restrict
L = len(points).  outside 15; genexpr@126 (total 22) `22(L+1)`; L lookups `index[...]` 3
each; `tuple` L+1.  Bound: `26L + 38`.  (Not used.)

### perm.is_string_automorphism
L = len(x).  Profile: outside 8; loop 130 (For 11/2): I ≤ L, E = 1 → `11(L+1) + 2`;
`enumerate` L+1; letters are ints (§1.1).  Bound: `12L + 22`.

### perm.maps_string
Profile: outside 8; loop 138 (For 11/2).  Same argument.  Bound: `12L + 22`.

### perm.sym_gens
L = len(points).  Profile: outside 38.  Built-ins: `list(points)` L+1, `len` 2, `pts[:2]` 3,
`append` 1.  Callees: `from_cycles(n, [pts[:2]])` (c = 1, T = 2): `3n + 87`;
`from_cycles(n, [pts])` (c = 1, T = L): `3n + 14L + 59`.
Bound: `38 + (L+1) + 2 + 3 + (3n+87) + (3n+14L+59) + 1 = 6n + 15L + 191`.

### perm.alt_gens
Profile: outside 59.  Built-ins: `list` L+1, `len` ≤ 3, `pts[:3]` 4, `pts[1:]` ≤ L+1,
`append` 1.  Callees: `from_cycles` with T = 3 (`3n + 101`) and one with T ≤ L
(`3n + 14L + 59`).  Bound: `6n + 16L + 229`.

---------------------------------------------------------------------------------------------

## 4. `group.py`

### group._Level.__init__
Profile: outside 29.  Callees: 2 × `identity(n)`.  Built-ins: two one-entry dicts (int key) 3
each, `deque()` 1.  Bound: `29 + 2(2N+33) + 6 + 1 = 4N + 102`.

### group.PermGroup.__init__
r elements of `gens` (A1), `F = len(forced_prefix)`, ρ = |gl| ≤ r.
Profile: outside 72; loop 48 (For 36/0): I = r, E = 1 → `36(r+1)`.
Per element: `tuple(g)` N+1, `len` 1, `g in seen` 2N+1, `is_identity(g)` 3N+39, `seen.add`
2N+1, `gl.append` 1: `8N + 44`.  After the loop: `list(range(n))` 2N+2 (A3; with an explicit
`base_order`: B+1), `list(forced_prefix)` ≤ 2F+2 (a `range` is iterated and listed),
`len(gl)` 1.  Callee: `_build(prune=True)` iff ρ > 6.
Bound: `72 + 36(r+1) + r(8N+44) + (2N+2) + (2F+2) + 1 + [ρ>6]·Build(N, ρ, F)
= Init0(N, r, F) + [ρ>6]·Build(N, ρ, F)`,  `Init0(N, r, F) = 113 + 2N + 2F + r(8N + 80)`.
(If the caller passes a generator, its own code is the caller's cost.)

### group.PermGroup._build  (and its nested code objects)

The nested functions are charged per call; their call counts come from S4.  ℓ ≤ N,
`d_k ≤ N - k`, `s_k ≤ λ := λ_N` (S4).

**`<sift@98>`** (inner sift).  Profile: outside 17; loop 99 (For 26/0): I ≤ ℓ - start ≤ ℓ,
E = 1 → `26(ℓ+1)`.  Built-ins: `len` 1, `range` ≤ ℓ+1, per iteration `trans_inv.get` 3 and
`mul` 3N+11.  `C_sift(ℓ) ≤ 17 + 26(ℓ+1) + 1 + (ℓ+1) + ℓ(3N + 14) = 45 + ℓ(3N + 41)`.

**`<extend_orbit@107>`**.  For a call on level k: D = orbit size before, d = after
(`D ≤ d ≤ d_k`), ν = d - D new points, s = `len(lev.gens)` (constant during the call).
Profile: outside 18; loop 111 (For 10/0): I = D, E = 1 → `10(D+1)`; loop 114 (While 19/5): the
queue receives the D old points and each new point once, so I = d, E = 1 → `19(d+1) + 5`;
loop 117 (For 46/0): one entry per popped point, s iterations each: I = ds, E = d →
`46(ds+d)`; loop 125 (For 10/0): one entry per new point: I = sν, E = ν → `10(sν+ν)`.
Built-ins: `list(lev.points)` D+1, `pending.append` D, `deque(lev.points)` D+1, `popleft` d,
`trans[pt]` 3d, `enumerate` d(s+1), `q not in trans` 3ds; per new point `mul` 3N+11, two dict
stores 6, `inv` 10N+29, two appends 2, `len` 1, `range` s+1, s appends.
`C_ext ≤ 54 + 83d + 50ds + ν(13N + 12s + 60)`  (D ≤ d used).

**`<add_strong_gen@128>`** (own work, `extend_orbit` excluded).  w = hi - lo + 1.
Profile: outside 37; loop 133 (For 8/4): runs only when a level is created; I ≤
len(rest_order) ≤ B + N, E ≤ 1 → `8(B+N+1) + 4`; loop 140 (For 24/0): I = w, E = 1 →
`24(w+1)`.  Built-ins: `len` 1, `range` w+1, per iteration `append` + `len` 2; new level:
`_Level` 4N+102, `append` 1.  `C_asg ≤ 63 + 27w + [new level]·(8B + 12N + 115)`.

**`<current_order@145>`**.  outside 10; loop 147 (For 10/0): I = ℓ → `10(ℓ+1)`; `len` ℓ.
`C_co(ℓ) ≤ 20 + 11ℓ`.

**`<closure@151>`** (own work, callees excluded).  outside 9; loop 154 (While 108/0); loop 168
(For 8/0, the clearing loop, executed at most once in the whole `_build`, S0).  Per call
`9 + 108` (cycle × the entry); per iteration `108 + 1` (deque truth test); per pop additionally
`popleft` 1, `trans[pt]` 3, `trans_inv[q]` 3, 2 × `mul`, 2 × `is_identity`, `sift`
(C_sift(ℓ)), 2 × `len`: `≤ 12N + 154 + ℓ(3N + 41)`; per add one `current_order()`.

**`<genexpr@94>`**: total 27, one loop (§0.5), iterates `range(n)` → `27(N+1)`.

**Main body.**  outside 149 (includes the creation of the five inner functions);
loop 84 (For 9/0): I = ρ → `9(ρ+1)`; loop 85 (For 13/0): E = ρ, I = ρN → `13(ρN+ρ)`, with
`enumerate` ρ(N+1) and `moved_by_gens.add` ≤ 3ρN; loop 88 (For 15/0): I = F → `15(F+1)`, per
iteration `in` 3, `append` 1, `_Level` 4N+102; `set(forced_prefix)` 4F+1; loop 92
(ListComp 9/9): I = B → `9(B+1) + 9`, B lookups 3; `set(base_order)` 4B+1; genexpr@94
`27(N+1)` + `range` N+1 + 2 lookups per element 6N + `extend` N+1; loop 181 (For 52/0, main
loop): I ≤ ρ → `52(ρ+1)`; per iteration inner `sift(g, 0)` and `is_identity`, for essential
ones `append` 1 and one `current_order()`; loop 190 (For 8/0, clearing; at most once overall,
shared with loop 168): `8(ℓ+1) + Σ_k(|Q_k| + 1) ≤ 9ℓ + 9 + P`; two more `current_order()`
(lines 180, 195).

**Lemma B (total).**  Summing (all coefficients are non-negative, so the upper bounds of S4
may be substituted):

    prep    = 222 + 17ρN + 23ρ + F(4N + 125) + 16B + 35N
    main    = 61 + ρ(3N + 136 + ℓ(3N + 41)) + e + (e + 2)(20 + 11ℓ) + 9ℓ + P
    asg     = 63A + 27E + ℓ(8B + 12N + 115)                 (Σ w = E; ≤ ℓ new levels)
    ext     = 54E + 83P + 25Q + V(13N + 60) + 12V_s         (Σ over the E calls; the t-th
              call on level k has s = t, so Σ_t 50·d·t ≤ 25·d_k s_k(s_k+1))
    closure = 117e + 109W + P(12N + 154 + ℓ(3N + 41)) + A(20 + 11ℓ),   W ≤ P + ℓ(e + A)

    Build(N, ρ, F, B) ≤ prep + main + asg + ext + closure
      = 323 + 159ρ + 20Nρ + 41ℓρ + 3Nℓρ + 125F + 4FN + 16B + 8Bℓ + 35N + 12Nℓ + 146ℓ
        + 138e + 120eℓ + 83A + 120Aℓ + 81E + 347P + 12NP + 41ℓP + 3NℓP
        + 25Q + 60V + 13NV + 12V_s.

Substituting ℓ ≤ N, e ≤ λ, A ≤ N(N-1)/2, E ≤ Nλ, P ≤ λN(N+1)/2, Q ≤ λ(λ+1)N(N+1)/2,
V ≤ N(N-1)/2, V_s ≤ λN(N-1)/2 (S4) and expanding:

    Build(N, ρ, F, B) ≤ (3/2)λN^4 + 28λN^3 + (437/2)λN^2 + 381λN + 138λ + (25/2)λ^2(N^2 + N)
                        + (133/2)N^3 + 17N^2 + (219/2)N + 323
                        + 8BN + 16B + 4FN + 125F + ρ(3N^2 + 61N + 159).

With B = N (A3) and F ≤ N (A2) — the form used everywhere below:

    Build(N, ρ) ≤ (3/2)λN^4 + 28λN^3 + (437/2)λN^2 + 381λN + 138λ + (25/2)λ^2 N(N+1)
                  + (133/2)N^3 + 29N^2 + (501/2)N + 323 + ρ(3N^2 + 61N + 159),   λ = λ_N.

Simplified (N ≥ 2, using N^j ≤ N^k / 2^{k-j}):
`Build(N, ρ) ≤ 127λN^4 + 19λ^2 N^2 + 184N^3 + 74ρN^2`.
CST (λ ≤ 3N/2): `Build(N, ρ) ≤ (9/4)N^5 + (561/8)N^4 + (3379/8)N^3 + (1201/2)N^2 + (915/2)N
+ 323 + ρ(3N^2 + 61N + 159) ≤ 257N^5 + 74ρN^2` (N ≥ 2).
Elementary (λ ≤ N log2 N): `Build(N, ρ) ≤ 127N^5 log2 N + 19N^4 (log2 N)^2 + 184N^3 + 74ρN^2`.
Construction plus build, `PermGroup(N, r gens)` with ρ > 6: `Init0 + Build ≤ 127λN^4 +
19λ^2N^2 + 200N^3 + 98rN^2` (N ≥ 2; CST: `≤ 259N^5 + 98rN^2`).

The dominant term `(3/2)λN^4` is P × (cost of one Schreier generator: two `mul`, two
`is_identity` and one sift through ≤ N levels, ≈ 3N^2).  Cost of each inner sift:
`≤ 45 + ℓ(3N+41) ≤ 3N^2 + 41N + 45`.  Number of Schreier pairs processed ≤ P ≤ λN(N+1)/2.
The early stop (`known_order`) only shortens the run (S0) and its correctness is not used.
`prune=True` changes only line 197; `forced_prefix` adds ≤ F forced levels (prep);
`base_order` enters through B.  An already built group: `β ≤ 149`.

### group.PermGroup.levels
outside 8 + `_build()`: `8 + β(G)`.

### group.PermGroup.order
outside 17; `_build()` is called unless `_order is None and known_order is not None`:
`17 + β(G)`.

### group.PermGroup.is_trivial
outside 6: `6`.

### group.PermGroup.base
outside 10; `levels` 8 + β; loop 214 (ListComp 5/9): I = ℓ → `5(ℓ+1) + 9`.
Bound: `5ℓ + 32 + β(G) ≤ 5N + 32 + β(G)`.  (Not used by the package.)

### group.PermGroup.sift
g of degree N, ℓ levels.  Profile: outside 19; loop 218 (For 25/0): I ≤ ℓ, E = 1 → `25(ℓ+1)`.
Built-ins: `len` 1, `range` ≤ ℓ+1, per iteration `get` 3 and `mul` 3N+11.  Callee `levels`
8 + β.  Bound: `19 + 25(ℓ+1) + 8 + β + 1 + (ℓ+1) + ℓ(3N+14) = ℓ(3N + 40) + 54 + β(G)
≤ 3N^2 + 40N + 54 + β(G)`.

### group.PermGroup.contains
outside 23; `tuple(g)` N+1; `self.sift`; `len(self.levels)`: `levels` with the group already
built (the first statement of `sift` built it, §1.4) `8 + 153`, `len` 1; `is_identity` 3N+39.
Bound: `ℓ(3N+40) + 4N + 279 + β(G) ≤ 3N^2 + 44N + 279 + β(G)`.

### group.PermGroup.strong_gens
outside 13; loop 233 (For 8/0): I = ℓ → `8(ℓ+1)`; loop 234 (For 17/0): E = ℓ, I = Σ s_k = E ≤
ℓλ → `17(E+ℓ)`; per inner iteration tuple-key lookup 2N+1, `add` 2N+1, `append` 1; `levels`.
Bound: `29 + 25ℓ + E(4N + 20) + β(G) ≤ λN(4N + 20) + 25N + 29 + β(G)`.  (Not used.)

### group.PermGroup.level_group
outside 35; `levels` 8 + β; `len` 1; if `known_order is None`: loop 247 (For 10/0): I = ℓ - i
≤ ℓ → `10(ℓ+1)`, slice `levels[i:]` ≤ ℓ+1, `len` per iteration.  Callee `PermGroup(N,
levels[i].gens, known_order)`: the list has `s_i ≤ λ` distinct non-identity elements (S4(c),
S4(e)), or is empty.
Bound: `12ℓ + 55 + β(G) + Init0(N, s_i, 0) + [s_i > 6]Build(N, s_i)
≤ 168 + 14N + λ(8N + 80) + β(G) + [s_i > 6]·Build(N, s_i)`.

### group.PermGroup.prefix_group
L = len(points), L' = number of distinct points (≤ min(L, N)).  outside 37; built-ins
`dict.fromkeys` 4L+1, `list` L'+1, `tuple(pts)` L'+1, `prefix_cache.get` 2L'+1, on a miss
`known_order_or_none` 10 and the store 2L'+1.  Callee (miss): `PermGroup(N, self.gens,
forced_prefix=pts, …)` with ρ = ρ_G (already distinct, non-identity), F = L'.
Bound: `52 + 4L + 6L' + Init0(N, ρ_G, L') + [ρ_G > 6]Build(N, ρ_G)`.

### group.PermGroup.known_order_or_none
outside 10: `10`.

### group.PermGroup.pointwise_stabilizer
L = len(points), L' distinct.  outside 36; `dict.fromkeys` 4L+1; loop 267 (ListComp 4/8): I =
L' (dict iteration L'+1) → `4(L'+1) + 8`; callee `prefix_group(pts)` (duplicate-free argument:
`52 + 10L' + Init0(N, ρ_G, L') + …`); `H.levels` 8 + β(H); `set(pts)` 4L'+1; loop 274
(While 17/12): each iteration passes a level whose base point lies in `pset`; base points are
distinct (S4(a)), so I = k ≤ L', E = 1 → `17(k+1) + 12`, each test `len` 1 and `in` 3 →
`4(k+1)`; callee `H.level_group(k)` with H built (just accessed `H.levels`):
`12N + 55 + 153 + Init0(N, s_k(H), 0) + [s_k>6]Build(N, s_k)`.  H is built at most once
(§1.4): `Init0(N, ρ_G, L') + β(H) ≤ Init0(N, ρ_G, L') + Build(N, ρ_G) + 153`.
Bound: `505 + 4L + 40L' + 12N + Init0(N, ρ_G, L') + Build(N, ρ_G) + Init0(N, s_k, 0)
+ [s_k>6]Build(N, s_k)`
`≤ 731 + 4L + 42L' + 16N + (ρ_G + λ)(8N + 80) + Build(N, ρ_G) + [s_k > 6]Build(N, s_k)`,
`s_k ≤ λ`, `ρ_G ≤ γ_N`.  Empty `points`: `≤ 36 + 4L + 1 + 12 = 4L + 49`.

### group.PermGroup.point_stabilizer
outside 7 + `pointwise_stabilizer([p])` (L = L' = 1):
`≤ 784 + 16N + (ρ_G + λ)(8N + 80) + Build(N, ρ_G) + [s_k > 6]Build(N, s_k)`.

### group.PermGroup.orbits
ρ = len(self.gens) (no build).  outside 25; loop 287 (For 24/0): I = N → `24(N+1)`; loop 293
(While 13/3): one entry per orbit (o ≤ N); every point enters a queue exactly once (the start
point s, or v when `seen[v]` turns true), so I = N → `13(N+o) + 3o`; loop 295 (For 24/0): one
entry per popped point (N), ρ iterations each → `24(Nρ + N)`.  Built-ins: `[False]*n` N+1,
`range` N+1, `deque([s])` 2 per orbit, `popleft` N, two appends per newly seen point ≤ 2N,
`out.append` o.
Bound: `51 + 66N + 19o + 24Nρ ≤ 24Nρ + 85N + 51`.  Cached (`_orbits` set): ≤ 25.

### group.PermGroup.orbit
outside 9; `orbits()`; loop 306 (For 6/4): I ≤ o ≤ N → `6(o+1) + 4`; `s in orb` costs
`|orb| + 1`, total ≤ N + o.  Bound: `19 + N + 7o + C[orbits] ≤ 24Nρ + 93N + 70`.  (Not used.)

### group.PermGroup.is_transitive
outside 9, `len` 1, `orbits()`: `10 + C[orbits] ≤ 24Nρ + 85N + 61`.

### group.PermGroup.orbits_on
L = len(items); items hashable with hash cost h and comparison cost h (an int: 1, a pair of
ints: 2); `act` a callable of cost `C_act` per call (a caller's lambda, outside these modules).
Assumption: `items` is closed under `act(·, g)` (else `KeyError`).
outside 28; loop 316 (DictComp 6/11): I = L → `6(L+1) + 11`, `enumerate` L+1, L insertions
`1 + 2h`; `[False]*len` L+2; loop 319 (For 25/0): I = L → `25(L+1)`, `enumerate` L+1; loop 325
(While 13/3): one entry per orbit (o ≤ L); every enqueue sets a distinct `seen[x]` from False
to True (for the start item `seen[i]`, otherwise `seen[j]`), so I ≤ L → `13(L+o) + 3o`;
loop 327 (For 29/0): E ≤ L (one per pop), I ≤ Lρ → `29(Lρ + L)`; per iteration `act` (C_act)
and `index[nx]` (1 + 2h); `deque([it])` 2 per orbit, `popleft` ≤ L, appends ≤ 2L,
`out.append` o.
Bound: `74 + 80L + 19o + 2hL + Lρ(30 + 2h + C_act) ≤ 74 + L(99 + 2h) + Lρ(30 + 2h + C_act)`.
For the only caller (`johnson.orbitals`: pairs, `lambda p, g: (g[p[0]], g[p[1]])`, h = 2):
`74 + 103L + Lρ(34 + C[johnson lambda])`.

### group.PermGroup.minimal_block_system
ρ = len(self.gens), N ≥ 2 (for N ≤ 1 it returns after `is_transitive` and the first list:
`≤ 62 + 6N + C[orbits]`).  `C_atk` is the bound of `group._atkinson` below.
*What the loops iterate over.*  The `while True` loop (354) maintains a partition `blocks`
of `range(N)` into m blocks.  It is G-invariant: initially singletons; `_atkinson` returns the
finest partition of the m blocks that relates `a, b` and is closed under the induced
generators (every successful union is pushed and its images under every generator are
unioned, so the equivalence generated by the pushed pairs is mapped into itself by each
generator; for a finite group this means G-invariance), and the induced generators `igens`
are well defined because `blocks` is G-invariant.  G is transitive (checked on line 348),
hence transitive on the blocks, hence all classes of the found partition have the same size:
`nb | m`.  An iteration that does not return replaces m by `nb` with `1 < nb < m`, so
`m_{t+1} ≤ m_t/2`, `m_t ≤ N/2^t`, and since every `m_t ≥ 2` there are at most
`τ = ⌊log2 N⌋` iterations (the last one returns); `Σ_t m_t^j ≤ N^j/(1 - 2^{-j})`.
Within an iteration with m blocks: loop 359 (For 8/0) over the m blocks, loop 360 (For 7/0)
over their points (N in total), loop 364 (For 21/0) over the ρ generators with genexpr@365
(total 26, one loop) over `range(m)`, loop 368 (For 35/0) over `b ∈ range(1, m)` (m - 1
values, each calls `_atkinson`), loop 381 (For 15/0) over `range(m)`, loop 383 (ListComp 7/9)
over the `nb ≤ m` classes.
Per iteration (`_atkinson` excluded; `nb ≤ m`, `lg = ⌈log2 N⌉`):
`8(m+1) + (m+1) + 7(N+m) + 3N + 21(ρ+1) + ρ(31m + 29) + 35m + m + (m-1)(4m+2) + 15(m+1)
+ (m+1) + 3m + (N+m) + 7(nb+1) + 9 + (nb+1) + (N·lg + 2N + nb) + (2nb·lg + 2nb + 1) + 1
≤ 63 + 81m + 4m^2 + 13N + ρ(31m + 50) + (N + 2m)·lg`
(per generator: genexpr 26(m+1), `range` m+1, lookups 3m, `tuple` m+1, `append` 1; per b:
`set(part)` 4m+1, `len` 1; per block `setdefault` 3 and `extend` |blk|+1; `sorted(v)` over the
classes ≤ N·lg + 2N + nb; `blocks.sort()` of nb lists with pairwise distinct first elements,
comparison cost ≤ 2).  `_atkinson` calls: `(m-1)·C_atk(m, ρ) ≤ m·C_atk(m, ρ)`.
Outside the loop: outside 37, `is_transitive` `10 + C[orbits]`, loop 350 (ListComp 5/9)
`5(N+1) + 9`, `range` N+1; while loop 354 (While 61/1): `61(τ+1) + 1`, `len` τ.
Summing with `Σ m_t ≤ 2N`, `Σ m_t^2 ≤ 4N^2/3`, `Σ m_t^3 ≤ 8N^3/7` and `C[orbits]` substituted
(o ≤ N):

    C[mbs] ≤ (152/7)N^3 + 132N^2 + 425N + 175 + 125τ + 13Nτ + N(τ + 4)·lg
             + ρ((304/7)N^3 + (92/3)N^2 + 86N + 50τ)
           ≤ 238N^3 + 87ρN^3                                  (N ≥ 2; τ ≤ N/2, lg ≤ N).

### group.PermGroup.induced_action
`blocks`: M blocks with S = Σ|blk| points (callers pass a G-invariant partition of
`range(N)`: tower top blocks, the output of `minimal_block_system`, the fibers in
`johnson.py`; S = N).  outside 27; loop 390 (For 8/0): I = M → `8(M+1)`, `enumerate` M+1;
loop 391 (For 7/0): E = M, I = S → `7(S+M)`, stores 3S; loop 394 (For 18/0): I = ρ →
`18(ρ+1)`; per generator genexpr@395 (total 24) `24(M+1)`, lookups 3M, `tuple` M+1,
`append` 1; `len` 1.  Callee `PermGroup(M, imgs)` (ρ images; ρ' ≤ ρ distinct non-identity).
Bound: `55 + 16M + 10S + ρ(28M + 44) + Init0(M, ρ, 0) + [ρ'>6]Build(M, ρ')`
`= 168 + 18M + 10N + ρ(36M + 124) + [ρ' > 6]·Build(M, ρ')`  (S = N).

### group.PermGroup.restriction
L = len(points) (a G-invariant set).  outside 35; `list` L+1; loop 401 (DictComp 6/12):
`6(L+1) + 12`, `enumerate` L+1, inserts 3L; loop 402 (ListComp 15/9): I = ρ → `15(ρ+1) + 9`;
per generator genexpr@402 (total 22) `22(L+1)`, lookups 3L, `tuple` L+1; `len` 1.  Callee
`PermGroup(L, imgs)`.
Bound: `80 + 11L + ρ(26L + 38) + Init0(L, ρ, 0) + [ρ'>6]Build(L, ρ')
= 193 + 13L + ρ(34L + 118) + [ρ' > 6]·Build(L, ρ')`.  (Not used by the package.)

### group.PermGroup.elements  (generator; with `<rec@414>`)
Structure: `elements` calls `levels` (8 + β), `len` 1, `identity(n)` (2N+33) and delegates by
`yield from` (loop 422, YieldFrom 9/13) to `rec(ℓ-1, id)`; `rec(i, acc)` for `i ≥ 0` iterates
(loop 418, For 2/0) over the `d_i` values of `levels[i].trans` and delegates (loop 419,
YieldFrom 12/11) to `rec(i-1, mul(acc, u))`; `rec(-1, acc)` yields acc (outside 22).
The invocations form a tree with `ℓ+1` levels whose leaves are the `Π_k d_k` produced
elements, visited depth first; an invocation at level `i ≥ 0` starts its first child without
yielding (`d_i ≥ 1`), so when the t-th element is yielded every invocation started so far is
an ancestor-or-self of one of the first t leaves: **started invocations ≤ (ℓ+1)t**; the
iterations of the `for` loops (each starts one child) are ≤ (ℓ+1)t, and these are also the
entries of the `YieldFrom` loops of `rec`; the values passed through a `rec` frame number ≤ ℓt
(each element passes the frames of levels 0..ℓ-1), through `elements` t.
Charges (Lemma R): per invocation of `rec`: outside 22 + For entry term 2 + `.values()` 1 + its
exhaustion 1 = 26; per iteration: For 2 + YieldFrom entry 11 + YieldFrom cycle (entry part)
12 + `values` step 1 + `mul(acc, u)` (3N+11) = 3N + 37; per value passed through a `rec` frame
12, through `elements` 9.  Closing an abandoned chain is covered by Lemma R.
**Bound:** after the t-th element (t = `Π d_k` for a full run, exhaustion included) the
generator has executed at most `one-time + t·per-element` with
`one-time = 32 + 13 + 9 + 8 + 1 + (2N+33) + β = 96 + 2N + β(G)` and
`per-element ≤ (ℓ+1)·26 + (ℓ+1)(3N+37) + 12ℓ + 9 ≤ (ℓ+1)(3N + 75) ≤ (N+1)(3N + 75)`.
(For ℓ = 0 one element, the identity.)

### group.PermGroup.coset_reps_prefix  (generator; with `<rec@433>`)
Identical structure with k' = min(k, ℓ) levels: profile outside 29 (with `min`, `len`: 2),
loop 440 (YieldFrom 9/11); `rec` outside 22, loop 437 (For 2/0), loop 438 (YieldFrom 12/11).
Produces `Π_{i<k'} d_i` elements.
**Bound:** `one-time = 29 + 11 + 9 + 8 + 2 + (2N+33) + β = 92 + 2N + β(G)`,
`per-element ≤ (k'+1)(3N + 75)`.

### group.PermGroup.random_free_subgroup_gens
outside 6, `list(self.gens)` ρ+1: `ρ + 7`.  (Not used by the package.)

### group.PermGroup.__repr__
Diagnostics only (no bound needed); for completeness `≤ 14 + 2(⌊log10 N⌋ + ⌊log10 ρ⌋ + 2) + 40`.

### group._atkinson  (with `<find@454>`, `<union@460>`)
m = number of points, ρ = len(gens) permutations of degree m, a ≠ b.
**`find`**: outside 4; loop 455 (While 19/6): each iteration moves x two steps towards the root
of its tree in the forest `parent` (path halving); a path has ≤ m - 1 edges, so I ≤ m - 1,
E = 1 → `C_find ≤ 4 + 19m + 6 = 19m + 10`.
**`union`**: outside 20 + 2 finds: `C_union ≤ 38m + 40`.
**Body**: outside 45; `list(range(m))` 2m+2; the first `union(a, b)`; loop 469 (While 13/3): a
pair is pushed only after a successful union (the first one included); each successful union
decreases the number of classes, so at most m - 1 pushes: I = W ≤ m - 1, E = 1 →
`13(W+1) + 3`, `pop` W; loop 471 (For 21/0): E = W, I = Wρ → `21(Wρ + W)`, one `union` per
iteration, appends ≤ W; loop 475 (ListComp 8/9): I = m → `8(m+1) + 9`, `range` m+1, one `find`
per element.
Bound: `121 + 59m + 36W + 19m^2 + Wρ(38m + 61)` with W ≤ m - 1:
`C_atk(m, ρ) ≤ 38ρm^2 + 23ρm + 19m^2 + 95m + 86`.

### group.generated_subcoset
L = len(cosets) (entries None or pairs (H_i, σ_i), H_i a PermGroup of degree N, σ_i of degree
N), `Σρ_i = Σ len(H_i.gens)`, `R = Σρ_i + L'` generators collected (L' ≤ L non-None).
outside 36; loop 486 (ListComp 7/8): `7(L+1) + 8`; `inv(s1)` 10N+29; loop 492 (For 17/0):
I = L' → `17(L'+1)`; per coset `extend` ρ_i + 1, `mul` 3N+11, `append` 1.  Callee
`PermGroup(N, gens, known_order)`.
Bound: `97 + 10N + L(3N + 37) + Σρ_i + Init0(N, R, 0) + [R'>6]Build(N, R')
≤ 210 + 12N + L(3N + 37) + Σρ_i + R(8N + 80) + [R' > 6]·Build(N, R')`,
`ρ_i ≤ γ_N` (Lemma G), so `R ≤ L(γ_N + 1)`.

### group.even_subgroup_gens
L = len(gens), all of degree D (`intersect_image` passes degree m).  outside 61 (the
function-level `from .perm import parity` imports a loaded module: 1); loops 501 and 502
(ListComp 12/8): I = L each → `2(12(L+1) + 8)`, one `parity` per element; `list(even)` L+1;
`inv(h0)` 10D+29; loop 508 (For 13/0): I = L_e → `13(L_e+1)`, 2 `mul` + `append`; loop 510
(For 17/0): I = L_o → `17(L_o+1)`, 2 `mul` + 2 `append`; loop 515 (For 23/0): I = |out| =
2L_e + 2L_o = 2L → `23(2L+1)`, per item tuple lookup 2D+1, `is_identity` 3D+39, `add` 2D+1,
`append` 1.  (`L_e + L_o = L`.)
Bound: `185 + 10D + 282L + 130LD`.

---------------------------------------------------------------------------------------------

## 5. `action.py`

### action.Coset.__init__
outside 9; `tuple(rep)` N+1.  Bound: `N + 10`.

### action.Coset.n
outside 5: `5`.

### action.Coset.order
outside 6 + `group.order()`: `23 + β(group)`.

### action.Coset.contains
outside 15; `tuple(g)` N+1; `inv(rep)` 10N+29; `mul` 3N+11; `group.contains`.
Bound: `14N + 56 + C[contains] ≤ 3N^2 + 58N + 335 + β(group)`.  (Not used by the package.)

### action.Coset.elements  (generator)
outside 13; loop 43 (For 10/0) over `group.elements()`: per element `10 + mul (3N+11)`, plus
the entry term 10; plus the cost of `group.elements()`.
Bound: one-time `119 + 2N + β(group)`, per element `3N + 21 + (ℓ+1)(3N + 75)`.
(Not used by the package.)

### action.Coset.shift_right
outside 11; `mul` 3N+11; `Coset.__init__` N+10.  Bound: `4N + 32`.  (Not used.)

### action.Coset.__repr__
Diagnostics only (formats `group.order()` and the tuple `rep`); no bound needed.

### action.window_lifter
L = len(window) (points of `range(N)`).  outside 23; `frozenset(window)` 4L+1;
`lifter_cache.get(key)` (frozenset key) 3L+1; on a miss `WindowLifter(G, window)` and the
store 3L+1.  Bound: `26 + 10L + C[WindowLifter.__init__]` (miss), `≤ 26 + 10L` (hit).

### action.WindowLifter.__init__  ("WindowLifter construction")
L = len(window), w = |set(window)| ≤ min(L, N); the window is G-invariant (`index[g[p]]`
exists); ρ = ρ_G ≤ γ_N.  outside 51; `set(window)` 4L+1; `sorted` of w ints
`w·⌈log2 w⌉ + 2w + 1`; loop 70 (DictComp 6/12): `6(w+1) + 12`, `enumerate` w+1, inserts 3w;
loop 75 (For 36/0): I = ρ → `36(ρ+1)`; per generator genexpr@76 (total 23) `23(w+1)`, lookups
3w, `tuple` w+1, `r not in seen` 2w+1, `is_identity(r)` 3w+39, `seen.add` 2w+1, `append` 1;
`len` 1.  Callee `PermGroup(w, imgs)` (ρ' ≤ ρ distinct non-identity images).
Bound: `109 + 4L + 12w + w⌈log2 w⌉ + ρ(34w + 102) + Init0(w, ρ, 0) + [ρ'>6]Build(w, ρ')`
`= 222 + 4L + 14w + w⌈log2 w⌉ + ρ(42w + 182) + [ρ' > 6]·Build(w, ρ')`.
The forced-prefix group (prefix = the window) is *not* built here; the first `_chain()`
builds it.

### action.WindowLifter._chain
outside 33; if `_H` is set: ≤ 33.  Otherwise: `G.prefix_group(self.pts)` (duplicate-free,
L = L' = w): `52 + 10w + Init0(N, ρ, w) + …`; `H.levels` 8 + β(H); `set(pts)` 4w+1; loop 88
(While 17/12): each iteration passes a level whose base point is in the window, base points
distinct, so I = k ≤ w, E = 1 → `17(k+1) + 12`, tests `len` + `in` `4(k+1)`.  H is built once
(`Init0 + β(H) ≤ Init0(N, ρ, w) + Build(N, ρ) + 153`, §1.4).
Bound (first call): `280 + 35w + Init0(N, ρ, w) + Build(N, ρ)
= 393 + 37w + 2N + ρ(8N + 80) + Build(N, ρ)`;  later calls `≤ 33` (`_H` is assigned on line
90 before returning).

### action.WindowLifter.kernel
outside 11; `_chain()`; `H.level_group(k)` with H built (by `_chain`, which accessed
`H.levels`): `12N + 55 + 153 + Init0(N, s_k(H), 0) + [s_k>6]Build(N, s_k)`, `s_k ≤ λ_N`.
Bound: `219 + 12N + C[_chain] + Init0(N, s_k, 0) + [s_k>6]Build(N, s_k)
≤ 332 + 14N + λ(8N + 80) + C[_chain] + [s_k > 6]·Build(N, s_k)`;
first call (`_chain` included): `≤ 725 + 16N + 37w + (ρ + λ)(8N + 80) + Build(N, ρ)
+ [s_k>6]Build(N, s_k)`.

### action.WindowLifter.lift  ("WindowLifter lift")
`pi` a permutation of degree w; k ≤ w as in `_chain`.  outside 47; `_chain()`; `H.levels`
(built) 8 + 153; `len` 1; `range(w)` w+1; loop 103 (ListComp 8/8): `8(w+1) + 8`;
`identity(N)` 2N+33; loop 105 (For 38/0): I = k → `38(k+1)`, `range` k+1; per iteration
`index[...]` 3, `trans.get` 3, `trans_inv[...]` 3, `mul(u, g)` 3N+11; loop 112 (ListComp 6/8)
inside it over `cur` (length w): I = kw, E = k → `6(kw + k) + 8k`; loop 114 (For 9/2): I ≤ w →
`9(w+1) + 2`, `enumerate` w+1.
Bound: `310 + 19w + 2N + k(6w + 3N + 73) + C[_chain]
≤ 6w^2 + 3Nw + 92w + 2N + 310 + C[_chain]`;
steady state (chain cached): `≤ 6w^2 + 3Nw + 92w + 2N + 343`;
first call: `≤ 6w^2 + 3Nw + 129w + 4N + 703 + ρ(8N + 80) + Build(N, ρ)`.

### action.WindowLifter.lift_group
ρ_H = len(H.gens) (H a group on the w window positions), ρ_K = len(kernel gens) ≤ λ_N.
outside 64; `getattr` 1; loop 125 (For 19/0): I = ρ_H → `19(ρ_H+1)`, per generator `lift` and
`append` 1; `kernel()`; `extend` ρ_K+1; `known_order_or_none` 10; in the branch taken only if
`H.known_order_or_none()` is not None, `H.order()` ≤ 17 + 153 (it returns `known_order`
without building, or `_order` is set, i.e. H is built) and `K.order()` ≤ 170 (K was created by
`level_group` with an int `known_order`); callee `PermGroup(N, gens, …)` with ρ_H + ρ_K
generators.  Only the first `_chain()` among the ρ_H + 1 calls (lifts and kernel) pays more
than 33.
Bound: `435 + 20ρ_H + ρ_K + ρ_H·C[lift] + C[kernel] + Init0(N, ρ_H + ρ_K, 0)
+ [·>6]Build(N, ρ_H + ρ_K)`; with the chain paid once and ρ_K ≤ λ:
`≤ 1273 + 37w + 18N + 161λ + 16Nλ + ρ(8N + 80) + ρ_H(6w^2 + 3Nw + 92w + 10N + 443)
+ Build(N, ρ) + [s_k>6]Build(N, s_k) + [ρ_H + ρ_K > 6]Build(N, ρ_H + ρ_K)`.
Cached (`H._lifted_by[0] is self`): `≤ 65`.

### action.WindowLifter.lift_coset
outside 25; `lift(C.rep)`; `Coset(...)` N+10; `lift_group(C.group)`.
Bound: `N + 35 + C[lift] + C[lift_group]`.  (`C is None`: ≤ 25.)

### action.WindowLifter.restrict_string
outside 14; genexpr@147 (total 20) `20(w+1)`; `tuple` w+1.  Bound: `21w + 35`.

### action.GroupWithAction.__init__
ρ = len(G.gens) = len(phi_gens), n = G.n, m.  outside 81; `len` 2; loop 160 (ListComp 7/9):
`7(ρ+1) + 9`, `tuple(p)` m+1 each; if `phi_fn` is given, loop 165 (For 11/4): `11(ρ+1) + 4`,
`zip` ρ+1, per generator `phi_fn(g)` (`C[phi_fn]`, outside these modules) and `!=` m+1;
loop 169 (ListComp 19/12): `19(ρ+1) + 12`, `zip` ρ+1, per generator `tuple(g)` n+1,
genexpr@169 (total 20) `20(m+1)`, `tuple` m+1, concatenation n+m+1.
Bound: `147 + ρ(2n + 24m + 64) + [phi_fn]·ρ·C[phi_fn]`.

### action.GroupWithAction.comb_omega
outside 27; on the first call `known_order_or_none` 10 and `PermGroup(M, combined_gens,
forced_prefix=range(n))` (ρ combined generators, distinct and non-identity because the
`G.gens` are).  Bound: first `37 + Init0(M, ρ, n) + [ρ>6]Build(M, ρ)`, cached `≤ 27`.

### action.GroupWithAction.comb_gamma
outside 32; first `42 + Init0(M, ρ, m) + [ρ>6]Build(M, ρ)`; cached `≤ 32`.

### action.GroupWithAction._gamma_levels
outside 12; `comb_gamma()`; `H.levels` 8 + β(H_Γ); loop 195 (While 18/13): the top levels of
the Γ-first chain are exactly the forced levels (base points in `[n, M)`, distinct), the
later base points are `< n` (rest_order = `range(n)`), so I = k ≤ m, E = 1 → `18(k+1) + 13`,
`len` per test.
Bound: `52 + 19m + C[comb_gamma] + β(H_Γ)`; first (H_Γ constructed and built once):
`≤ 52 + 19m + 42 + Init0(M, ρ, m) + Build(M, ρ) + 153`; steady `≤ 237 + 19m`.

### action.GroupWithAction.phi
With `phi_fn`: `≤ 61 + C[phi_fn]`.  Otherwise: outside 61; `comb_omega()`; `H.levels`
8 + β(H_Ω); `list(g)` n+1; `identity(M)` 2M+33; loop 208 (For 42/0): the first levels of the
Ω-first chain are the forced levels (base points `< n`), the later ones have base points
`≥ n`, so I ≤ k_Ω + 1 (k_Ω ≤ n full iterations and possibly one breaking iteration), E = 1 →
`42(k_Ω + 2)`; per full iteration `get` 3, `trans_inv` 3, `mul(u, acc)` 3M+11; loop 216
(ListComp 6/8) inside it over `cur` (length n): I = k_Ω·n, E = k_Ω; loop 218 (For 8/4):
`8(n+1) + 4`, `range` n+1; genexpr@221 (total 24) `24(m+1)`, `range` m+1, `tuple` m+1.
Bound: `226 + 12n + 28m + k_Ω(9n + 3m + 73) + C[comb_omega] + β(H_Ω)`
`≤ 9n^2 + 3nm + 85n + 28m + 226 + C[comb_omega] + β(H_Ω)`;
steady (H_Ω cached and built: `≤ 27 + 153`): `≤ 9n^2 + 3nm + 85n + 28m + 406`;
first call: `≤ 9n^2 + 3nm + 89n + 30m + 529 + ρ(8n + 8m + 80) + Build(M, ρ)`.

### action.GroupWithAction.kernel
outside 39; cached: ≤ 39.  Otherwise: `comb_gamma()`, `_gamma_levels()` (which calls
`comb_gamma()` again — cached — and builds H_Γ), `H.level_group(k)` with H built
(`12M + 55 + 153 + Init0(M, s_k, 0) + [s_k>6]Build(M, s_k)`, `s_k ≤ λ_M`), loop 229
(ListComp 7/9) over the ρ_K ≤ s_k ≤ λ_M generators of K: `7(ρ_K+1) + 9`, slices n+1 each;
`K.order()` ≤ 170 (K has an int `known_order`); `PermGroup(n, …, known_order)` with ρ_K
generators (ρ' ≤ ρ_K distinct non-identity).
Own work: `433 + 12n + 12m + ρ_K(n + 8)`.
Bound (first call, H_Γ not yet built):
`≤ 1051 + 18n + 37m + λ_M(17n + 8m + 168) + ρ(8n + 8m + 80)
+ Build(M, ρ) + [s_k>6]Build(M, s_k) + [ρ'>6]Build(n, ρ')`;
H_Γ already built: `≤ 928 + 16n + 33m + λ_M(17n + 8m + 168) + [s_k>6]Build(M, s_k)
+ [ρ'>6]Build(n, ρ')`;  `s_k, ρ' ≤ λ_M`.

### action.GroupWithAction.image
outside 15; first `PermGroup(m, phi_gens)`: `15 + Init0(m, ρ, 0) + [ρ'>6]Build(m, ρ')`;
cached ≤ 15.

### action.GroupWithAction.image_order
outside 7; `image()`; `.order()` (17 + β).  First: `≤ 305 + 2m + ρ(8m + 80) + Build(m, ρ)`
(the image group is built once, §1.4); steady (image built): `≤ 7 + 15 + 170 = 192`.

### action.GroupWithAction.image_is_giant
outside 19; first: `image_order()` and `factorial(m)` (m): `≤ 19 + m + C[image_order]`;
cached ≤ 19.

### action.GroupWithAction.image_is_sym
outside 10; `image_order()`, `factorial(m)`: `10 + m + C[image_order]`.

### action.GroupWithAction.lift
`tau` a permutation of degree m.  outside 51; `comb_gamma()`; `_gamma_levels()`; `H.levels`
(built by `_gamma_levels`) 8 + 153; loop 254 (ListComp 7/8): `7(m+1) + 8`, `range` m+1;
`identity(M)` 2M+33; loop 256 (For 37/0): I = k ≤ m → `37(k+1)`, `range` k+1; per iteration
`get` 3, `trans_inv` 3, `mul(u, g)` 3M+11; loop 263 (ListComp 6/8) inside it over `cur`
(length m): I = km, E = k; loop 265 (For 9/2): `9(m+1) + 2`, `range` m+1; `g[:n]` n+1.
Bound: `312 + 20m + 3n + k(9m + 3n + 69) + C[comb_gamma] + C[_gamma_levels]`
`≤ 9m^2 + 3nm + 89m + 3n + 312 + C[comb_gamma] + C[_gamma_levels]`;
steady (H_Γ cached and built: `32 + 237 + 19m`): `≤ 9m^2 + 3nm + 108m + 3n + 581`;
first call: `≤ 9m^2 + 3nm + 112m + 5n + 704 + ρ(8n + 8m + 80) + Build(M, ρ)`.

### action.GroupWithAction.intersect_image
L = len(gens) permutations of degree m.  outside 31; `image_is_giant()`, `image_is_sym()`;
Sym branch: loop 275 (ListComp 11/9) `11(L+1) + 9` and L × `is_identity` (3m+39); otherwise
`list(gens)` L+1 and `even_subgroup_gens(L, D = m)` (185 + 10m + 282L + 130Lm), which
dominates the Sym branch.
Bound: `217 + 10m + 283L + 130Lm + C[image_is_giant] + C[image_is_sym]`; the two calls cost
`≤ 526 + 4m + ρ(8m + 80) + Build(m, ρ)` on the first use of the image, `≤ 221 + m` afterwards.

### action.GroupWithAction.preimage
L = len(gens) permutations of Γ.  outside 30; loop 281 (For 19/0): I = L → `19(L+1)`, per
generator `lift` and `append` 1; `kernel()`; `K.order()` ≤ 170 (the stored kernel has an int
`known_order`); list concatenation L + ρ_ker + 1 (ρ_ker ≤ λ_M); callee `PermGroup(n, lifted +
K.gens, known)`.  Only the first call of `lift` / `kernel` can build H_Γ.
Bound: `220 + 21L + ρ_ker + L·C[lift] + C[kernel] + Init0(n, L + ρ_ker, 0) + [·>6]Build(n, ·)`;
fully expanded (every lazy structure charged once):
`≤ L(9m^2 + 3nm + 108m + 11n + 682) + 8λ_M m + 25λ_M n + 249λ_M + 8ρ(n + m + 10) + 37m + 20n
+ 1384 + Build(M, ρ) + [s_k>6]Build(M, s_k) + [ρ'>6]Build(n, ρ') + [·>6]Build(n, L + ρ_ker)`.

### action.GroupWithAction.subgroup
L = len(gens) of degree n; ρ_H ≤ min(L, γ_n) = number of generators of the new group H.
outside 39; loop 293 (ListComp 13/8): `13(L+1) + 8`, per element `is_identity` 3n+39 and
`tuple` n+1; `dict.fromkeys` (tuple keys) `L(2n+2) + 1`; `list` L+1; callee
`PermGroup(n, uniq, known_order)`; loop 296 (ListComp 7/9): `7(ρ_H+1) + 9`, one `self.phi` per
generator of H; callee `GroupWithAction(H, m, …, phi_fn)`.
Bound: `78 + L(6n + 56) + 7ρ_H + Init0(n, L, 0) + [·>6]Build(n, ρ_H) + ρ_H·C[phi]
+ C[GroupWithAction.__init__](ρ_H)`;  expanded:
without `phi_fn`: `≤ 461 + 136L + 14Ln + 6n + 2m + 8ρ(n + m + 10) + ρ_H(9n^2 + 3nm + 87n + 52m
+ 477) + Build(M, ρ) + [·>6]Build(n, ρ_H)` (`Build(M, ρ)` only if the parent's `comb_omega`
was not built yet);
with `phi_fn`: `≤ 338 + 136L + 14Ln + 2n + ρ_H(2n + 24m + 132) + 2ρ_H·C[phi_fn]
+ [·>6]Build(n, ρ_H)`.

### action.GroupWithAction.restricted_image_gens
L = len(points) (a φ-invariant subset of Γ).  outside 27; `list` L+1; loop 301 (DictComp
6/12) `6(L+1) + 12`, `enumerate` L+1, inserts 3L; loop 302 (ListComp 15/11): `15(ρ+1) + 11`,
per image genexpr@302 (total 22) `22(L+1)`, lookups 3L, `tuple` L+1.
Bound: `73 + 11L + ρ(26L + 38)`.  (Not used by the package.)

### action.GroupWithAction.odd_lift_fixing
outside 35; `len` 1; `list(range(m))` 2m+2; `tuple(tau)` m+1; `lift`.
Bound: `39 + 3m + C[lift]`.  (Not used by the package.)

### action.restrict_gens
L = len(pts), r = len(gens).  outside 21; loop 315 (DictComp 6/12) `6(L+1) + 12`, `enumerate`
L+1, inserts 3L; loop 316 (ListComp 15/10): `15(r+1) + 10`, per generator genexpr@316 (total
22) `22(L+1)`, lookups 3L, `tuple` L+1.  Bound: `65 + 10L + r(26L + 38)`.  (Not used.)

### action.perm_parity_on
outside 5 + `parity`: `55N + 48`.  (Not used.)

---------------------------------------------------------------------------------------------

## 6. `canon.py`

**Size parameters of an object x** accepted by `canon` (None, bool, int, str, tuple, list,
set, frozenset, or an object with `canon_value` — in the package only `structure.Fixed`,
whose `canon_value()` returns the stored value): its tree has the atoms as leaves, the
elements of a container as its children, and for a `canon_value` object the returned value as
its single child.  `σ(x)` = number of nodes (atoms + containers + `canon_value` objects),
`ω(x) = σ(x) + Σ_{str atoms s} len(s)`, `d(x)` = height (atoms 0), `n_cv(x)` = number of
`canon_value` nodes, `L_v` = number of children of node v.

**Canonical images.**  `I(x)` is `("n",)`, `("i", int)`, `("s", s)`, `(tag, (I(c)…))` or
`("x", I(value))`.  Counting a str node as `1 + len`, `|I(x)| ≤ 4ω(x)` (an atom gives ≤ 4 + len,
a container `4 + Σ|I(c)|`, a `canon_value` node `3 + |I(c)|`) and the nesting depth is
`δ(I(x)) ≤ 2d(x) + 1`.
**Comparison cost.**  For nested tuples A, B (CPython compares element pairs with `==` up to
the first difference, then that pair with `<`): `cost(A == B) ≤ min(|A|, |B|)` and
`cost(A < B) ≤ (δ(A) + 1)·min(|A|, |B|)` (induction on δ: the equal prefix costs ≤ min - 1 by
the first claim, the differing pair ≤ δ(A)·min by induction, + 1).  Hence comparing the images
of two children of a node of x costs `κ ≤ (2(d(x)-1) + 2)·4ω(x) = 8d(x)ω(x)`.

### canon.canon
Profile: outside 114, no loops (every instruction at most once per call); genexprs @40, @42,
@44 (total 19 each, one loop each), each consuming the `L_v` children.  Per call (= per node
v): ≤ 114 instructions, built-ins ≤ 8 (≤ 6 `isinstance`, `int`, `getattr`); for a tuple/list
`19(L_v+1)` genexpr + `tuple` `L_v+1`; for a set/frozenset the same plus `sorted`
`L_v⌈log2 L_v⌉·κ + 2L_v + 1`; for a `canon_value` node one call `value()`
(`C[structure.Fixed.canon_value]`, outside these modules).  The recursion makes exactly one
call per node, and `Σ_v (L_v + 1) = 2σ - 1`.
Bound: `T(x) ≤ 165σ + 8·d·ω·Σ_{set nodes v} L_v⌈log2 L_v⌉ + n_cv·C[Fixed.canon_value]`
`≤ 165σ + 8dωσ⌈log2 σ⌉·[x contains a set/frozenset] + n_cv·C[Fixed.canon_value]`.
Closed forms: without sets `165σ + n_cv·C[cv]`; in general, with Λ = max string length,
`T(x) ≤ 165σ + 8(1 + Λ)σ^3⌈log2 σ⌉ + n_cv·C[cv]` (d ≤ σ, ω ≤ (1+Λ)σ).  An int or str atom:
`≤ 165`.

### canon.normalize_letters
L = len(x) + len(y), A ≤ L distinct letters, H = hash + comparison cost of a letter
(int: 2; tuple of ints of size s: 2s; if letters were `structure.Fixed`, their
`__hash__`/`__eq__` would be external callees), letters of height ≤ d_ℓ and weight ≤ ω_ℓ.
Profile: outside 63; loop 64 (For 7/0): 2 iterations → `7·3`; loop 65 (For 17/0): E = 2,
I = L → `17(L+2)`; per occurrence `a not in seen` 1+H; per new letter store 1+H, `len` 1,
`append` 1; `sorted(letters, key=canon)`: A calls of `canon` (`Σ_a T(a)`), `A⌈log2 A⌉`
comparisons of images (κ_ℓ ≤ 8(d_ℓ+1)ω_ℓ), `2A + 1`; on `TypeError` the partial work is at most
that (the handler's exit jump: Lemma R); loop 73 (DictComp 6/12): `6(A+1) + 12`, `enumerate`
A+1, inserts A(1+H); genexprs@74 (total 20 each) `20(L+2)`, lookups L(1+H), two `tuple` L+2.
Bound: `180 + L(40 + 2H) + A(13 + 2H) + Σ_a T(a) + A⌈log2 A⌉·κ_ℓ`.
For int letters (H = 2, T(a) ≤ 165, κ_ℓ ≤ 8): `≤ 180 + 226L + 8L⌈log2 L⌉`.

---------------------------------------------------------------------------------------------

## 7. `tower.py`

K = `len(self.levels)` (number of stored partitions), n = `self.n`; every stored partition is
a tuple of length n.  (For a tower in the sense of the module docstring the block counts
strictly decrease from n and are ≥ 2, so K ≤ n - 1; in the transitive case K ≤ log2 n.)

### tower.Tower.__init__
outside 13; genexpr@45 (total 19) over the K levels `19(K+1)`; `tuple(b)` n+1 each; outer
`tuple` K+1.  Bound: `K(n + 21) + 33`.

### tower.Tower.trivial
outside 6 + `Tower(n, ())`: `39`.

### tower.Tower.is_trivial
outside 6: `6`.

### tower.Tower.top_blocks
outside 34; trivial tower: loop 59 (ListComp 5/9) `5(n+1) + 9`, `range` n+1 (= 6n + 49);
otherwise loop 63 (For 31/0): I = n → `31(n+1)`, `range` n+1, per point `get` 3 and either
store 3 + `len` 1 + `append` 1 or `append` 1 (≤ 8).  Bound: `40n + 66`.

### tower.Tower.block_counts
outside 14; loop 75 (ListComp 9/9): `9(K+1) + 9`; per level `set(b)` 4n+1, `len` 1;
concatenation K+2.  Bound: `K(4n + 12) + 34`.

### tower.Tower.potential
outside 21; `block_counts()`; `+ [1]` K+2; slice `counts[1:]` K+2; `zip` K+2; loop 82
(For 24/0): I = K+1 → `24(K+2)`; `bit_length` ≤ K+1.  Bound: `K(4n + 40) + 110`.
(Not used by the package.)

### tower.Tower.extend
c = len(blocks), S = Σ|b| (callers pass a partition of `range(n)`: S = n, c ≤ n).
outside 25; `[0]*n` n+1; loop 93 (For 8/0): `8(c+1)`, `enumerate` c+1; loop 94 (For 6/0):
E = c, I = S → `6(S+c)`; `tuple(blk)` n+1; concatenation K+2; `Tower(n, K+1 levels)`
`(K+1)(n+21) + 33`.  Bound: `92 + 3n + 6S + 15c + K(n + 22) ≤ 92 + 24n + K(n + 22)`.

### tower.Tower.restrict
L = len(pts).  outside 21; `len` 1; loop 103 (For 38/0): I ≤ K → `38(K+1)`; per level
genexpr@105 (total 26) `26(L+1)`, per element `setdefault` 3 + `len` 1, `tuple` L+1, `len` 1,
`append` 1; `len` 1 and `Tower(L, ≤ K levels)` `K(L+21) + 33`.
Bound: `94 + K(32L + 88)`.

### tower.Tower.__repr__
Diagnostics only (no bound needed).

---------------------------------------------------------------------------------------------

## 8. Final table

Callees inside these modules are substituted; `Build(N, ρ)` is the closed form of Lemma B
(`(3/2)λN^4 + 28λN^3 + (437/2)λN^2 + 381λN + 138λ + (25/2)λ^2N(N+1) + (133/2)N^3 + 29N^2
+ (501/2)N + 323 + ρ(3N^2 + 61N + 159)`, λ = λ_N; ≤ `127λN^4 + 19λ^2N^2 + 184N^3 + 74ρN^2`
for N ≥ 2; CST ≤ `257N^5 + 74ρN^2`).  `β(G) ≤ Build(N_G, ρ_G)` (≤ 149 if built).
`[X > 6]Build(…)` is present only when the new group has more than 6 distinct non-identity
generators.  External symbols: `C[phi_fn]`, `C_act`, `C[structure.Fixed.canon_value]`.
"first" = lazy structures not yet built (everything charged), "steady" = the cached
structures named in §5 exist.

| function | closed-form bound (one call) |
|---|---|
| perm.identity | 2n + 33 |
| perm._ident | 2n + 28 |
| perm.is_identity | 3N + 39 |
| perm.mul | 3N + 11 |
| perm.mul_all | K(3n + 18) + 2n + 51 |
| perm.inv | 10N + 29 |
| perm.identity_perm | 2n + 33 |
| perm.conj | 16N + 62 |
| perm.from_cycles | 3n + 28c + 14T + 31 |
| perm.cycles | 63N + 47 |
| perm.parity | 55N + 43 |
| perm.support | 11N + 34 |
| perm.act_string | 11L + 30 |
| perm.act_set (+genexpr@117) | 24L + 34 |
| perm.act_tuple (+genexpr@121) | 21L + 34 |
| perm.restrict (+genexpr@126) | 26L + 38 |
| perm.is_string_automorphism | 12L + 22 |
| perm.maps_string | 12L + 22 |
| perm.sym_gens | 6n + 15L + 191 |
| perm.alt_gens | 6n + 16L + 229 |
| group._Level.__init__ | 4N + 102 |
| group.PermGroup.__init__ | 113 + 2N + 2F + r(8N + 80) + [ρ>6]Build(N, ρ) |
| group.PermGroup._build (all nested code incl.) | Build(N, ρ) (general B, F: Lemma B) |
| group.PermGroup._build.<genexpr@94> | 27(N + 1) |
| group.PermGroup._build.<sift@98> | 45 + ℓ(3N + 41) ≤ 3N^2 + 41N + 45 |
| group.PermGroup._build.<extend_orbit@107> | 54 + 83d + 50ds + ν(13N + 12s + 60) |
| group.PermGroup._build.<add_strong_gen@128> (own) | 63 + 27w + [new level](8B + 12N + 115) |
| group.PermGroup._build.<current_order@145> | 20 + 11ℓ |
| group.PermGroup._build.<closure@151> (own) | 117 + 109·(iterations) + (pops)(12N + 154 + ℓ(3N+41)) + (adds)(20 + 11ℓ); summed in Lemma B |
| group.PermGroup.levels | 8 + β |
| group.PermGroup.order | 17 + β |
| group.PermGroup.is_trivial | 6 |
| group.PermGroup.base | 5N + 32 + β |
| group.PermGroup.sift | 3N^2 + 40N + 54 + β |
| group.PermGroup.contains | 3N^2 + 44N + 279 + β |
| group.PermGroup.strong_gens | λN(4N + 20) + 25N + 29 + β |
| group.PermGroup.level_group | 168 + 14N + λ(8N + 80) + β + [s_i>6]Build(N, s_i) |
| group.PermGroup.prefix_group | 165 + 4L + 8L' + 2N + ρ(8N + 80) + [ρ>6]Build(N, ρ) |
| group.PermGroup.known_order_or_none | 10 |
| group.PermGroup.pointwise_stabilizer | 731 + 4L + 42L' + 16N + (ρ + λ)(8N + 80) + Build(N, ρ) + [s_k>6]Build(N, s_k) |
| group.PermGroup.point_stabilizer | 784 + 16N + (ρ + λ)(8N + 80) + Build(N, ρ) + [s_k>6]Build(N, s_k) |
| group.PermGroup.orbits | 24Nρ + 85N + 51 (cached ≤ 25) |
| group.PermGroup.orbit | 24Nρ + 93N + 70 |
| group.PermGroup.is_transitive | 24Nρ + 85N + 61 |
| group.PermGroup.orbits_on | 74 + L(99 + 2h) + Lρ(30 + 2h + C_act) |
| group.PermGroup.minimal_block_system (+genexpr@365, _atkinson) | (152/7)N^3 + 132N^2 + 425N + 175 + 125τ + 13Nτ + N(τ+4)⌈log2 N⌉ + ρ((304/7)N^3 + (92/3)N^2 + 86N + 50τ) ≤ 238N^3 + 87ρN^3 (N ≥ 2) |
| group.PermGroup.induced_action (+genexpr@395) | 168 + 18M + 10N + ρ(36M + 124) + [ρ'>6]Build(M, ρ') |
| group.PermGroup.restriction (+genexpr@402) | 193 + 13L + ρ(34L + 118) + [ρ'>6]Build(L, ρ') |
| group.PermGroup.elements (+rec@414) | one-time 96 + 2N + β; per element (ℓ+1)(3N + 75) ≤ (N+1)(3N + 75) |
| group.PermGroup.coset_reps_prefix (+rec@433) | one-time 92 + 2N + β; per element (k'+1)(3N + 75), k' = min(k, ℓ) |
| group.PermGroup.random_free_subgroup_gens | ρ + 7 |
| group.PermGroup.__repr__ | diagnostics |
| group._atkinson | 38ρm^2 + 23ρm + 19m^2 + 95m + 86 |
| group._atkinson.<find@454> | 19m + 10 |
| group._atkinson.<union@460> | 38m + 40 |
| group.generated_subcoset | 210 + 12N + L(3N + 37) + Σρ_i + R(8N + 80) + [R'>6]Build(N, R'), R = Σρ_i + L ≤ L(γ_N + 1) |
| group.even_subgroup_gens | 185 + 10D + 282L + 130LD |
| action.Coset.__init__ | N + 10 |
| action.Coset.n | 5 |
| action.Coset.order | 23 + β |
| action.Coset.contains | 3N^2 + 58N + 335 + β |
| action.Coset.elements | one-time 119 + 2N + β; per element 3N + 21 + (ℓ+1)(3N + 75) |
| action.Coset.shift_right | 4N + 32 |
| action.Coset.__repr__ | diagnostics |
| action.window_lifter | 26 + 10L (+ WindowLifter.__init__ on a miss) |
| action.WindowLifter.__init__ (+genexpr@76) | 222 + 4L + 14w + w⌈log2 w⌉ + ρ(42w + 182) + [ρ'>6]Build(w, ρ') |
| action.WindowLifter._chain | first 393 + 37w + 2N + ρ(8N + 80) + Build(N, ρ); later 33 |
| action.WindowLifter.kernel | first 725 + 16N + 37w + (ρ + λ)(8N + 80) + Build(N, ρ) + [s_k>6]Build(N, s_k); chain cached 365 + 14N + λ(8N + 80) + [s_k>6]Build(N, s_k) |
| action.WindowLifter.lift | first 6w^2 + 3Nw + 129w + 4N + 703 + ρ(8N + 80) + Build(N, ρ); steady 6w^2 + 3Nw + 92w + 2N + 343 |
| action.WindowLifter.lift_group | 1273 + 37w + 18N + 161λ + 16Nλ + ρ(8N + 80) + ρ_H(6w^2 + 3Nw + 92w + 10N + 443) + Build(N, ρ) + [s_k>6]Build(N, s_k) + [·>6]Build(N, ρ_H + ρ_K); cached 65 |
| action.WindowLifter.lift_coset | N + 35 + C[lift] + C[lift_group] |
| action.WindowLifter.restrict_string (+genexpr@147) | 21w + 35 |
| action.GroupWithAction.__init__ (+genexpr@169) | 147 + ρ(2n + 24m + 64) + [phi_fn]·ρ·C[phi_fn] |
| action.GroupWithAction.comb_omega | first 150 + 4n + 2m + ρ(8n + 8m + 80) + [ρ>6]Build(M, ρ); cached 27 |
| action.GroupWithAction.comb_gamma | first 155 + 2n + 4m + ρ(8n + 8m + 80) + [ρ>6]Build(M, ρ); cached 32 |
| action.GroupWithAction._gamma_levels | first 360 + 2n + 23m + ρ(8n + 8m + 80) + Build(M, ρ); steady 237 + 19m |
| action.GroupWithAction.phi (+genexpr@221) | first 9n^2 + 3nm + 89n + 30m + 529 + ρ(8n + 8m + 80) + Build(M, ρ); steady 9n^2 + 3nm + 85n + 28m + 406; with phi_fn 61 + C[phi_fn] |
| action.GroupWithAction.kernel | first 1051 + 18n + 37m + λ_M(17n + 8m + 168) + ρ(8n + 8m + 80) + Build(M, ρ) + [s_k>6]Build(M, s_k) + [ρ'>6]Build(n, ρ') (s_k, ρ' ≤ λ_M); cached 39 |
| action.GroupWithAction.image | first 128 + 2m + ρ(8m + 80) + [ρ'>6]Build(m, ρ'); cached 15 |
| action.GroupWithAction.image_order | first 305 + 2m + ρ(8m + 80) + Build(m, ρ); steady 192 |
| action.GroupWithAction.image_is_giant | first 324 + 3m + ρ(8m + 80) + Build(m, ρ); cached 19 |
| action.GroupWithAction.image_is_sym | first 315 + 3m + ρ(8m + 80) + Build(m, ρ); steady 202 + m |
| action.GroupWithAction.lift | first 9m^2 + 3nm + 112m + 5n + 704 + ρ(8n + 8m + 80) + Build(M, ρ); steady 9m^2 + 3nm + 108m + 3n + 581 |
| action.GroupWithAction.intersect_image | first 743 + 14m + 283L + 130Lm + ρ(8m + 80) + Build(m, ρ); steady 438 + 11m + 283L + 130Lm |
| action.GroupWithAction.preimage | L(9m^2 + 3nm + 108m + 11n + 682) + 8λ_M m + 25λ_M n + 249λ_M + 8ρ(n + m + 10) + 37m + 20n + 1384 + Build(M, ρ) + [s_k>6]Build(M, s_k) + [ρ'>6]Build(n, ρ') + [·>6]Build(n, L + ρ_ker) |
| action.GroupWithAction.subgroup | no phi_fn: 461 + 136L + 14Ln + 6n + 2m + 8ρ(n + m + 10) + ρ_H(9n^2 + 3nm + 87n + 52m + 477) + Build(M, ρ) + [·>6]Build(n, ρ_H); phi_fn: 338 + 136L + 14Ln + 2n + ρ_H(2n + 24m + 132) + 2ρ_H·C[phi_fn] + [·>6]Build(n, ρ_H) |
| action.GroupWithAction.restricted_image_gens (+genexpr@302) | 73 + 11L + ρ(26L + 38) |
| action.GroupWithAction.odd_lift_fixing | 39 + 3m + C[lift]: first 9m^2 + 3nm + 115m + 5n + 743 + ρ(8n + 8m + 80) + Build(M, ρ); steady 9m^2 + 3nm + 111m + 3n + 620 |
| action.restrict_gens (+genexpr@316) | 65 + 10L + r(26L + 38) |
| action.perm_parity_on | 55N + 48 |
| canon.canon (+genexprs@40,42,44) | 165σ + 8dωσ⌈log2 σ⌉·[sets] + n_cv·C[Fixed.canon_value] ≤ 165σ + 8(1+Λ)σ^3⌈log2 σ⌉ + n_cv·C[cv] |
| canon.normalize_letters (+genexpr@74) | 180 + L(40 + 2H) + A(13 + 2H) + Σ_a T(a) + A⌈log2 A⌉κ_ℓ; int letters ≤ 180 + 226L + 8L⌈log2 L⌉ |
| tower.Tower.__init__ (+genexpr@45) | K(n + 21) + 33 |
| tower.Tower.trivial | 39 |
| tower.Tower.is_trivial | 6 |
| tower.Tower.top_blocks | 40n + 66 |
| tower.Tower.block_counts | K(4n + 12) + 34 |
| tower.Tower.potential | K(4n + 40) + 110 |
| tower.Tower.extend | 92 + 3n + 6S + 15c + K(n + 22) ≤ 92 + 24n + K(n + 22) |
| tower.Tower.restrict (+genexpr@105) | 94 + K(32L + 88) |
| tower.Tower.__repr__ | diagnostics |

Size facts used by callers: every `PermGroup` has `ρ ≤ γ_N = max(6, λ_N)` generators (Lemma
G); its chain has `ℓ ≤ N` levels, transversals `d_k ≤ N - k`, `s_k ≤ λ_N` strong generators
per level, `≤ min(N(N-1)/2, Nλ_N)` strong generators in total, and `≤ λ_N N(N+1)/2` Schreier
pairs (S4).

**Functions used only by tests, diagnostics or nothing** (bounds given anyway): `perm.mul_all`,
`identity_perm`, `conj`, `cycles`, `support`, `act_set`, `act_tuple`, `restrict`;
`PermGroup.base`, `strong_gens`, `orbit`, `restriction`, `random_free_subgroup_gens`,
`__repr__`; `Coset.contains`, `Coset.elements`, `shift_right`, `__repr__`;
`GroupWithAction.restricted_image_gens`, `odd_lift_fixing`; `action.restrict_gens`,
`perm_parity_on`; `Tower.potential`, `Tower.__repr__` (grep over `babai_gi/`).

---------------------------------------------------------------------------------------------

## 9. Profile numbers used

From `opcount` (`opcount.generate()` for `perm`, `group`, `action`; `canon` and `tower` are
not in `opcount.MODULES`, their entries are `opcount.profile` of the functions and
`opcount._add_code` keys for nested code).  Format
`"module.Qualname": (outside, [(line, cycle, entry), ...])`; nested generator expressions are
listed separately as `(total, loops)`, matching opcount's `{"total": T, "loops": k}`.

```python
PROFILES = {
    "perm.identity": (5, []),
    "perm._ident": (20, []),
    "perm.is_identity": (9, []),
    "perm.mul": (9, []),
    "perm.mul_all": (11, [(43, 7, 0)]),
    "perm.inv": (18, [(50, 7, 0)]),
    "perm.identity_perm": (5, []),
    "perm.conj": (11, []),
    "perm.from_cycles": (15, [(66, 13, 0), (68, 13, 0)]),
    "perm.cycles": (20, [(76, 23, 0), (80, 16, 4)]),
    "perm.parity": (20, [(92, 19, 0), (96, 15, 4)]),
    "perm.support": (11, [(105, 10, 12)]),
    "perm.act_string": (18, [(111, 8, 0)]),
    "perm.act_set": (13, []),
    "perm.act_tuple": (13, []),
    "perm.restrict": (15, []),
    "perm.is_string_automorphism": (8, [(130, 11, 2)]),
    "perm.maps_string": (8, [(138, 11, 2)]),
    "perm.sym_gens": (38, []),
    "perm.alt_gens": (59, []),
    "group._Level.__init__": (29, []),
    "group.PermGroup.__init__": (72, [(48, 36, 0)]),
    "group.PermGroup._build": (149, [(84, 9, 0), (85, 13, 0), (88, 15, 0), (92, 9, 9), (181, 52, 0), (190, 8, 0)]),
    "group.PermGroup._build.<sift@98>": (17, [(99, 26, 0)]),
    "group.PermGroup._build.<extend_orbit@107>": (18, [(111, 10, 0), (114, 19, 5), (117, 46, 0), (125, 10, 0)]),
    "group.PermGroup._build.<add_strong_gen@128>": (37, [(133, 8, 4), (140, 24, 0)]),
    "group.PermGroup._build.<current_order@145>": (10, [(147, 10, 0)]),
    "group.PermGroup._build.<closure@151>": (9, [(154, 108, 0), (168, 8, 0)]),
    "group.PermGroup.levels": (8, []),
    "group.PermGroup.order": (17, []),
    "group.PermGroup.is_trivial": (6, []),
    "group.PermGroup.base": (10, [(214, 5, 9)]),
    "group.PermGroup.sift": (19, [(218, 25, 0)]),
    "group.PermGroup.contains": (23, []),
    "group.PermGroup.strong_gens": (13, [(233, 8, 0), (234, 17, 0)]),
    "group.PermGroup.level_group": (35, [(247, 10, 0)]),
    "group.PermGroup.prefix_group": (37, []),
    "group.PermGroup.known_order_or_none": (10, []),
    "group.PermGroup.pointwise_stabilizer": (36, [(267, 4, 8), (274, 17, 12)]),
    "group.PermGroup.point_stabilizer": (7, []),
    "group.PermGroup.orbits": (25, [(287, 24, 0), (293, 13, 3), (295, 24, 0)]),
    "group.PermGroup.orbit": (9, [(306, 6, 4)]),
    "group.PermGroup.is_transitive": (9, []),
    "group.PermGroup.orbits_on": (28, [(316, 6, 11), (319, 25, 0), (325, 13, 3), (327, 29, 0)]),
    "group.PermGroup.minimal_block_system": (37, [(350, 5, 9), (354, 61, 1), (359, 8, 0), (360, 7, 0), (364, 21, 0), (368, 35, 0), (381, 15, 0), (383, 7, 9)]),
    "group.PermGroup.induced_action": (27, [(390, 8, 0), (391, 7, 0), (394, 18, 0)]),
    "group.PermGroup.restriction": (35, [(401, 6, 12), (402, 15, 9)]),
    "group.PermGroup.elements": (32, [(422, 9, 13)]),
    "group.PermGroup.elements.<rec@414>": (22, [(418, 2, 0), (419, 12, 11)]),
    "group.PermGroup.coset_reps_prefix": (29, [(440, 9, 11)]),
    "group.PermGroup.coset_reps_prefix.<rec@433>": (22, [(437, 2, 0), (438, 12, 11)]),
    "group.PermGroup.random_free_subgroup_gens": (6, []),
    "group.PermGroup.__repr__": (14, []),
    "group._atkinson": (45, [(469, 13, 3), (471, 21, 0), (475, 8, 9)]),
    "group._atkinson.<find@454>": (4, [(455, 19, 6)]),
    "group._atkinson.<union@460>": (20, []),
    "group.generated_subcoset": (36, [(486, 7, 8), (492, 17, 0)]),
    "group.even_subgroup_gens": (61, [(501, 12, 8), (502, 12, 8), (508, 13, 0), (510, 17, 0), (515, 23, 0)]),
    "action.Coset.__init__": (9, []),
    "action.Coset.n": (5, []),
    "action.Coset.order": (6, []),
    "action.Coset.contains": (15, []),
    "action.Coset.elements": (13, [(43, 10, 0)]),
    "action.Coset.shift_right": (11, []),
    "action.Coset.__repr__": (14, []),
    "action.window_lifter": (23, []),
    "action.WindowLifter.__init__": (51, [(70, 6, 12), (75, 36, 0)]),
    "action.WindowLifter._chain": (33, [(88, 17, 12)]),
    "action.WindowLifter.kernel": (11, []),
    "action.WindowLifter.lift": (47, [(103, 8, 8), (105, 38, 0), (112, 6, 8), (114, 9, 2)]),
    "action.WindowLifter.lift_group": (64, [(125, 19, 0)]),
    "action.WindowLifter.lift_coset": (25, []),
    "action.WindowLifter.restrict_string": (14, []),
    "action.GroupWithAction.__init__": (81, [(160, 7, 9), (165, 11, 4), (169, 19, 12)]),
    "action.GroupWithAction.comb_omega": (27, []),
    "action.GroupWithAction.comb_gamma": (32, []),
    "action.GroupWithAction._gamma_levels": (12, [(195, 18, 13)]),
    "action.GroupWithAction.phi": (61, [(208, 42, 0), (216, 6, 8), (218, 8, 4)]),
    "action.GroupWithAction.kernel": (39, [(229, 7, 9)]),
    "action.GroupWithAction.image": (15, []),
    "action.GroupWithAction.image_order": (7, []),
    "action.GroupWithAction.image_is_giant": (19, []),
    "action.GroupWithAction.image_is_sym": (10, []),
    "action.GroupWithAction.lift": (51, [(254, 7, 8), (256, 37, 0), (263, 6, 8), (265, 9, 2)]),
    "action.GroupWithAction.intersect_image": (31, [(275, 11, 9)]),
    "action.GroupWithAction.preimage": (30, [(281, 19, 0)]),
    "action.GroupWithAction.subgroup": (39, [(293, 13, 8), (296, 7, 9)]),
    "action.GroupWithAction.restricted_image_gens": (27, [(301, 6, 12), (302, 15, 11)]),
    "action.GroupWithAction.odd_lift_fixing": (35, []),
    "action.restrict_gens": (21, [(315, 6, 12), (316, 15, 10)]),
    "action.perm_parity_on": (5, []),
    "canon.canon": (114, []),
    "canon.normalize_letters": (63, [(64, 7, 0), (65, 17, 0), (73, 6, 12)]),
    "tower.Tower.__init__": (13, []),
    "tower.Tower.trivial": (6, []),
    "tower.Tower.is_trivial": (6, []),
    "tower.Tower.top_blocks": (34, [(59, 5, 9), (63, 31, 0)]),
    "tower.Tower.block_counts": (14, [(75, 9, 9)]),
    "tower.Tower.potential": (21, [(82, 24, 0)]),
    "tower.Tower.extend": (25, [(93, 8, 0), (94, 6, 0)]),
    "tower.Tower.restrict": (21, [(103, 38, 0)]),
    "tower.Tower.__repr__": (13, []),
}

# nested generator expressions: (total instructions, loops)  — opcount: {'total': T, 'loops': k}
NESTED = {
    "perm.act_set.<genexpr@117>": (20, 1),
    "perm.act_tuple.<genexpr@121>": (20, 1),
    "perm.restrict.<genexpr@126>": (22, 1),
    "group.PermGroup._build.<genexpr@94>": (27, 1),
    "group.PermGroup.minimal_block_system.<genexpr@365>": (26, 1),
    "group.PermGroup.induced_action.<genexpr@395>": (24, 1),
    "group.PermGroup.restriction.<genexpr@402>": (22, 1),
    "action.WindowLifter.__init__.<genexpr@76>": (23, 1),
    "action.WindowLifter.restrict_string.<genexpr@147>": (20, 1),
    "action.GroupWithAction.__init__.<genexpr@169>": (20, 1),
    "action.GroupWithAction.phi.<genexpr@221>": (24, 1),
    "action.GroupWithAction.restricted_image_gens.<genexpr@302>": (22, 1),
    "action.restrict_gens.<genexpr@316>": (22, 1),
    "canon.canon.<genexpr@40>": (19, 1),
    "canon.canon.<genexpr@42>": (19, 1),
    "canon.canon.<genexpr@44>": (19, 1),
    "canon.normalize_letters.<genexpr@74>": (20, 1),
    "tower.Tower.__init__.<genexpr@45>": (19, 1),
    "tower.Tower.restrict.<genexpr@105>": (26, 1),
}
```

---------------------------------------------------------------------------------------------

## 10. What is cited, assumed or not proved

* **Cited, not proved:** Cameron–Solomon–Turull (λ_N = ⌈3N/2⌉ - b(N) - 1).  Every bound is
  written with λ_N, and the elementary bound λ_N ≤ log2 N! ≤ N log2 N (Lemma C(a)) can be
  substituted instead (the simplified "CST" forms then gain a factor ≈ (2/3)log2 N).
* **Lemma R** rests on opcount's attribution (PROOF.md, Lemma 1.1) plus the bytecode facts
  checked by `tests/test_attribution.py`: the only backward jump of the five modules outside
  the hypotheses of Lemma 1.1 is the exit jump of `canon.normalize_letters` (bounded by hand
  in §1.2), and every genexpr has one backward-jump target, its `FOR_ITER` (§0.5).  The test
  runs with the test suite and fails if a change to `opcount.py` or to the code of these
  modules invalidates these facts.
* **Cost-model conventions** where `SPEC.md` is silent: string comparison `1 + min length`; a
  fixed-size built-in call costs 1; `tuple(t)` of a tuple is charged `len + 1`; the import
  statement inside `even_subgroup_gens` (already loaded module) costs 1.
* **External callees** are left symbolic: `C[phi_fn]` (callers' φ functions, e.g. in
  `certificates.py`/`main.py`), `C_act` (`johnson.orbitals`' lambda), `C[structure.Fixed.
  canon_value]`, and `__hash__`/`__eq__` of letters if they were not ints.
* **Assumptions checked against the callers by grep:** (A1) generators are permutations of the
  stated degree; (A2) `forced_prefix` duplicate-free; (A3) `base_order` never passed; windows,
  `points` of `restriction`/`restricted_image_gens` and `items` of `orbits_on` are invariant
  (otherwise a `KeyError` exit, whose cost up to the exception is bounded by the same
  expressions); blocks passed to `induced_action`/`Tower.extend` partition the domain; letters
  are ints.
* **Crude parts (valid, not tight):** the union-find path bound (≤ m - 1 per `find`), the
  sorting term of `canon` for sets (cubic in σ in the worst case), charging every lazy build at
  every possible trigger (β ≤ Build).
* `__repr__` methods (diagnostics) are not bounded, as allowed by `SPEC.md`.
