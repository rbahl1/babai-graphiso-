# Operation bounds for `babai_gi/main.py` and `babai_gi/graph.py`

The code documented here is `main.py` and `graph.py` of this repository. Line numbers refer to these files.

Section 1 fixes the conventions. Section 2 gives the lemmas for the functions, in source order. Section 3 gives the own work W(node) of every node type of the recursion, with its nested `Solver.iso` calls. Section 4 is the final table, Section 5 the profile dictionary, and Section 6 lists what is not proved here.

---------------------------------------------------------------------------

## 1. Conventions

### 1.1 Parameters

* `n = G.n` is the degree of the group of the call, and `r = len(G.gens)`. For other groups `H`, `r_H = len(H.gens)`.
* **Letter size λ ≥ 1.**
  * Define `size(a) = 1` for an `int`, `bool`, `None` or a constant string of at most 8 characters, and `size(c) = 1 + Σ size(e)` over the elements `e` of a tuple, list or frozenset `c`.
  * Hashing a letter `a`, or comparing it with `==` / `!=` / `<` against any value, touches at most `size(a)` elements. λ is the maximum of `size(a)` over the letters of `x` and `y`.
  * The root call has `λ = 1`: `graph_isomorphism`, `graph_automorphisms` and `string_isomorphism` pass the strings through `canon.normalize_letters`, which produces `int` letters. The recursion keeps the letters, except in `certificates.LocalCertificates.compare`. There `colored_string` builds the letters `(ℓ, 0/1)`, so those calls have `λ' ≤ λ + 2`.
* `N` denotes the degree of a group argument of a callee, and `L` the length of a list argument.
* **BSGS quantities of a `PermGroup` `H`.** `g = |H|`. After `_build`, `k_H = len(H.levels)`, `u_i = len(levels[i].trans)` and `S_H = Σ_i len(levels[i].gens)`.
* **Johnson case.**
  * `m = Gw.m = |Γ|` and `t = jd.t`.
  * `b = len(jd.blocks) = len(jd.block_of_T)` is the number of standard blocks. The blocks partition Ω, so `b ≤ n`. For a recognised Johnson group `b = C(m, t)`.
  * `k = Params.k_for(n, m)` and `M = C(m, k)`.
  * The Johnson case is entered (lines 283, 336) only when `m ≥ gamma_threshold(n) = 10·k_paper(n) ≥ 90`. So, under the paper parameters, `k = min(k_paper(n), m-2) = k_paper(n) = max(9, n.bit_length()+2) ≤ m/10`.
* **Branch parameters** (Lemma R):
  * `d` is the number of choices of one run of `proc`, and `c_1..c_d` their candidate counts.
  * `s = ∏_j c_j` is the number of complete choice sequences.
  * `R ≤ s` is the number of runs of `proc` on `y`, `s' ≤ R` the number of runs yielded, and `S ≤ s'` the number of successful recursive calls.
  * `κ` is the maximal `size(tuple(chosen))` of a yielded run. `κ ≤ 1 + dμ`, where μ is the maximal size of a choice object; μ is defined by the soj/design modules.
  * `A_key` is the cost of `apply_obj` on all components of one key, at most `C[structure.apply_obj](κ)`.
* `ρ(N) = max(6, ⌊N log₂ N⌋)` bounds the number of generators of any `PermGroup` of degree N (Lemma G4).

### 1.2 Cost of built-ins (SPEC rules, made explicit)

The instruction that calls a built-in is counted in the profile. The charges below come on top of it.

* **K1.** `list` / `tuple` of an iterable of L elements: `L+1`.
* **K2.** `set` / `frozenset` / `dict` / `dict.fromkeys` / `Counter` of L keys of size ≤ h: `(2+2h)L+1`. This is 1 per element touched plus one insertion `1+h+h`. For `int` keys it is `4L+1`.
* **K3.** One lookup, insertion, membership test, `.get`, `.setdefault`, `.add` or `[] =` in a dict or set, with a key of size ≤ h: `1+2h`. For `int` keys it is 3, for 2-tuples of `int` 5, and for constant string keys of at most 8 characters 17.
* **K4.** Set algebra or set comparison (`-`, `|`, `&`, `|=`, `-=`, `<=`, `==`, `!=`) with elements of size ≤ h: `(1+2h)(|A|+|B|)+1`. For `int` elements it is `3(|A|+|B|)+1`.
* **K5.** `==` / `!=` / `<` of two tuples or lists of at most L elements of size ≤ h: `hL+1`. For strings of length n this is `λn+1`.
* **K6.** `in` on a list, `list.index` or `list.count` over L elements of size ≤ h: `(h+1)L+1`.
* **K7.** `sorted` or `list.sort` of L items whose keys compare at cost ≤ c: `c·L⌈log₂L⌉ + 2L + 1`, plus L calls of the key function.
* **K8.** Iteration.
  * `range`: 1 per element consumed, plus 1.
  * `zip` / `enumerate`: 1 per step, plus 1.
  * `dict` views: 1 per element, plus 1.
  * `itertools.combinations/permutations/product`: the tuple length per element produced, plus 1.
  * Iterating a list, tuple, set or dict: nothing beyond the `FOR_ITER`.
* **K9.**
  * `[a]*L`, slicing L elements, `list.extend` by L elements, `any/all/max/min/sum` over L elements: `L+1`, plus the key or genexpr costs. `math.factorial(L)`: `L+1`.
  * Fixed-arity built-ins (`len`, `isinstance`, `getattr`, `int`, `bit_length`, `append`, `pop()`, `next`, `min/max` of a fixed tuple): 1 per argument, at least 1.
* **K10.** `canon` of an object of size z costs `C[canon.canon](z)`. Its encoding has size ≤ 3z: by induction, `size(("i",v)) = 3` and `size(("t",(…))) = 3 + Σ`. So comparing two encodings costs ≤ 3z.
* **K11.** `self.stats[key] += 1`: 128 with a constant key (two dict operations of ≤ 64 each, SPEC), 192 with an f-string key (64 more for the formatting). `self.stats[key] = v`: 64.
* **K12.** Importing an already imported name inside a function (`from itertools import product`): 1.
* **K13.** `Fraction(a)` of an `int`/`Fraction`: 2. `Counter.__eq__`/`__ne__` of two Counters with at most n keys each: two lookups per key of each, `≤ 2n·(3+4λ)+4`.

### 1.3 Symbols

* `C[module.Qualname](params)` is the bound for one call proved in the document that covers that module, with the size parameters listed. For a generator such as `group.PermGroup.coset_reps_prefix`, it is the cost of producing the stated number of elements.
* By the SPEC, `C[...]` does not contain operations inside `Solver.iso` / `Solver.iso_window` calls made by the callee. Where a callee makes such calls (`certificates.LocalCertificates.certificate`, `.compare`), the own work `W_iw` of every `iso_window` call is added explicitly to the node (Section 3).
* `Ord(N,r) := C[group.PermGroup.order](N, r)` includes a `_build` if one happens.
* All bounds are upper bounds on the cost of one call. Several `C[...]` terms are charged for mutually exclusive branches; this is harmless.

### 1.4 Assumptions

* **(A1) Returning runs under `Params.paper()`.**
  * The bounds are for runs that return. So no `ValueError` / `RuntimeError` / `AssertionError` branch is taken, and every `fallback(...)` (it raises `TheoremViolation` because `allow_fallbacks=False`) together with the code after it is unreachable.
  * `small_scale` is bounded too where it differs; it only adds the fallback callees.
* **(A2) String lengths.** `len(x) == len(y) == G.n` for every `Solver.iso` call. The callers pass:
  * `restrict_string` of the window (lines 379, 416);
  * `act_string` of a string of length n;
  * the strings themselves;
  * `GraphInstance.string` of length `C(v,2) = G.n`.
* **(A3) Correctness of `group.py` / `action.py`, used only for counting.**
  * (i) Every `known_order=` passed to `PermGroup` equals the order of the generated group.
  * (ii) Schreier–Sims is complete. After `closure()` returns `False`, and after `_build`, the levels form a BSGS of the group generated so far, so `∏ u_i = |H|`.
  * (iii) The `phi` of every `GroupWithAction` is a homomorphism.
  * These give `g = ∏ u_i`, the number of coset representatives in `strong_luks` / `cameron_reduction`, and Lemma G4.
* **(A4) No forced prefix.** Every group reaching `Solver.iso` has `forced_prefix = ()`. In the package source, `forced_prefix` is set only for `comb_omega`, `comb_gamma`, `prefix_group` and the `comb` of `kernel_and_lifts`. None of these is passed to `iso`, because the solver only receives `level_group` / `PermGroup(...)` results built from them.
* **(A5) Determinism of `proc`.** Two executions of `proc(s, ·)` whose chooser returns the same answers make the same chooser calls with the same arguments.
  * The package has no randomness; caches store values equal to what recomputation gives.
  * This is the canonicity of Babai Prop. 4.0.4, and without it `enumerate_runs` need not terminate.
* **(A6) Exception handlers.** No exception-table handler of a `main`/`graph` code object lies below the code it protects. This is the property (H3) of exception handlers used in the proof of PROOF.md, Lemma 1.1. `tests/test_attribution.py` checks it (`target ≥ end` for every entry of the exception table) on every code object, including lambdas and generator expressions; the function code objects contain the handlers of the inlined comprehensions, of `yield from` and of the `try/finally` of `Solver.iso`, the only `try`.

### 1.5 Lemma P (the profiles are sound for these modules)

For every function and inner `def` of `main.py` / `graph.py`, one call executes at most

    outside + Σ_loops [ cycle·(I + E) + entry·E ]

of its own instructions, with the profiles of `opcount.profile` (Section 5). Here I is the number of iterations of a loop and E the number of its entries. For a `YieldFrom` loop, I is the number of values passed through.

*Proof.*
1. Between two executions of an instruction at offset o, control must pass from an offset ≥ o to an offset ≤ o. The only such transfers are `JUMP_BACKWARD*` instructions: by (A6) handlers lie above their ranges, and resuming a generator continues after its `YIELD_VALUE`. So o runs at most `1 + Σ exec(j)` times per call, the sum over the backward jumps j with `target(j) ≤ o ≤ j`.
2. The attribution of `opcount.profile` is proved in PROOF.md, Lemma 1.1. Each backward jump is attributed to the loop that owns its target: the loop whose `FOR_ITER`, while-test or `SEND` is the jump target, after skipping `EXTENDED_ARG`. With point 1, that lemma gives: an instruction outside every backward-jump range runs at most once per call; an instruction in the range of a loop's own jumps but not in the range of an inner loop's jumps runs at most once per execution of the loop head plus once per entry; and the head runs once per iteration plus once per entry.
3. Hence, by PROOF.md Lemma 1.1, the following hold for every instruction, with the single exception of point 4. `tests/test_attribution.py` checks these four properties (its hypotheses H1 and H2) on every function and inner `def` of `main.py` and `graph.py`, and that point 4 is the only exception.
   * An instruction counted as *outside* lies in no backward-jump range.
   * An instruction counted as *entry of L* lies only in ranges of loops strictly enclosing L.
   * An instruction counted as *cycle of L* lies only in ranges of L or of loops enclosing L.
   * The jumps of L are those of L's own loop, which execute at most I_L times.
4. The single exception is benign. The handler stubs at offsets 606–620 of `_chain_search`, attributed as entry of the comprehensions at lines 1051 and 1057, lie inside the `CLEANUP_THROW` range 596–624 of the `yield from` at 1074. They end in `RERAISE` and run at most once per call.
5. Two nested code objects contain loops (`opcount` reports `"loops"` for them) and are bounded by hand:
   * `_solve.<genexpr@303>` has two `for` clauses. By point 1, each of its 27 instructions runs at most `1 + I_outer + I_inner` times.
   * `largest_twin.<lambda@598>` contains the comprehension `[-v for v in c]`. Its 5 cycle instructions run at most `|c|+1` times and the others once, so one call costs at most `27 + 5|c|`.
6. Every other lambda executes each instruction at most once per call. Every other genexpr (one `for` clause) executes each instruction at most once per element produced, plus once: at most `total·(L+1)` for L elements. □

### 1.6 Lemma G (facts about BSGS and generator counts)

Let H be a `PermGroup` of degree N with `forced_prefix = ()`, after `_build`.

* **(G1) Every level has `u_i ≥ 2`.**
  * With an empty prefix, the loop at group.py:88 creates no level. Levels are created only at group.py:139, inside `add_strong_gen(h, lo, hi)` with `hi == len(levels)`, on the first point b with `h[b] ≠ b`.
  * The same call appends h to that level (lines 140–143), and `extend_orbit` puts `h[b] ≠ b` into `trans`, so `u ≥ 2`.
  * `trans` only grows, and no code outside `_build` modifies levels.
* **(G2) `k_H ≤ log₂|H|`.** By (A3)(ii) `∏ u_i = |H|`, and each `u_i ≥ 2`.
* **(G3) `S_H ≤ |H| + k_H²`.**
  * Let `Φ = Σ_i (|trans_i| − 1)`. Every call of `add_strong_gen` increases Φ by at least 1:
    * a new level is created with `|trans| = 1` and then grows to ≥ 2;
    * otherwise h is the residue of `sift`, which stopped at level j because `h[b_j] ∉ trans_j` (lines 101–103), and `extend_orbit` on level j adds `h[b_j]`.
  * Hence the number A of calls is at most `Σ(u_i − 1)`.
  * Each call appends h to at most `k_H` levels, so `S_H ≤ k_H·A`.
  * For reals `a, b ≥ 2`, replacing `(a, b)` by `(ab/2, 2)` keeps the product and does not decrease `(a−1)+(b−1)`, because `(a−2)(b−2) ≥ 0`. Hence `Σ(u_i−1) ≤ |H|/2^{k−1} + k − 2`.
  * So `S_H ≤ k|H|/2^{k−1} + k² ≤ |H| + k²`, using `k/2^{k−1} ≤ 1`.
* **(G4) `len(H.gens) ≤ max(6, ⌊log₂|H|⌋) ≤ ρ(N)`.**
  * `__init__` keeps at most the distinct non-identity generators. If there are more than 6, `_build(prune=True)` replaces them by `essential` (lines 69–75, 197).
  * A generator is appended to `essential` (line 187) only if `sift(g, 0)` leaves a non-identity residue. At that moment the chain is a complete BSGS of ⟨essential so far⟩ by (A3)(ii): either nothing has been added yet, or the previous `closure()` returned `False`; once the target order is reached the loop stops (lines 182, 189–193).
  * So each essential generator at least doubles the order, giving `|essential| ≤ log₂|H| ≤ log₂ N! ≤ N log₂ N`.

  This applies to every `PermGroup` (G4 needs no prefix hypothesis).

### 1.7 Lemma R (number of executions of `proc` in `branch`)

Let the x-side run `proc(x, rc)` record `rc.trace` with d events `("choice", c_j)`. Each `c_j ≥ 1`, because `RecordingChooser.choose` raises on an empty candidate list. Let `s = ∏_{j=1}^{d} c_j` (`s = 1` if `d = 0`). Under (A5), `enumerate_runs(lambda ch: proc(y, ch), rc.trace)` has the following properties:

* (a) it executes `proc` at most s times;
* (b) it yields at most s runs;
* (c) in every yielded run `len(chosen) = d`.

*Proof.*
1. Every `choose` or `check` call of a `ReplayChooser` consumes one trace event. `choose` raises `Mismatch` before recording anything unless the event is `("choice", len(candidates))`. Hence the j-th recorded choice of a run consumed the j-th choice event of the trace: `taken_j < counts_j = c_j`, and `len(taken) ≤ d`.
2. A run is yielded only if `ch.pos == len(trace)`, i.e. all d choice events were consumed. This gives (c).
3. Map a taken sequence τ to `φ(τ) = Σ_{j≤|τ|} τ_j·∏_{l>j} c_l`. Then `0 ≤ φ(τ) ≤ Σ_{j≤d}(c_j−1)∏_{l>j}c_l = s − 1`.
4. If the DFS continues after a run with taken sequence τ, let i be the last index with `τ_i + 1 < c_i`. Then `τ_j = c_j − 1` for all `j > i`, and the next path is `p = (τ_1..τ_{i−1}, τ_i+1)`.
5. By (A5) the next run repeats the first `i−1` choices, reaches its i-th `choose` with the same c_i candidates, and takes `τ_i + 1`. So its taken sequence τ' extends p, and

       φ(τ') ≥ φ(p) = φ(τ_{<i}) + (τ_i+1)∏_{l>i}c_l
              > φ(τ_{≤i}) + ∏_{l>i}c_l − 1 ≥ φ(τ).

6. So φ strictly increases from run to run and takes at most s values. This gives (a), and (b) follows. □

Also, `apply_obj` with a permutation preserves the size of an object: it is injective on ints and acts elementwise on containers. So every key built in `_covered` has size `= size(key) ≤ κ`.

---------------------------------------------------------------------------

## 2. Lemmas, in source order

Notation inside a lemma:
* "instr" is the instruction count from the profile and Lemma P;
* "+K…" marks a built-in charge;
* "callees" lists `C[...]` terms;
* "solver calls" lists `Solver.iso` / `Solver.iso_window` calls (not included in the bound).

### main.Params.__init__

* **Profile:** outside 44, no loops.
* **Built-ins:**
  * `Fraction(alpha)`: 2 (K13).
  * `k_rule not in ("paper","small_scale")`: K6 with two strings of ≤ 11 characters, `12·2+1 = 25`.
* **Callees:** `C[soj.SOJParams.__init__]()`, only if `soj is None`.
* **Bound:** `44 + 2 + 25 + C[soj.SOJParams.__init__]() = 71 + C[soj.SOJParams.__init__]()`.

### main.Params.paper

* **Profile:** outside 14.
* **Built-ins:** `cls(**overrides)` with o keyword overrides (keys ≤ 20 characters): K2 gives `42o+1`.
* **Callees:** `Params.__init__`.
* **Bound:** `86 + 42o + C[soj.SOJParams.__init__]()`. For the default (`o = 0`): `86 + C[soj.SOJParams.__init__]()`.

### main.Params.small_scale

Not used by paper runs; bounded anyway.

* **Profile:** outside 32.
* **Built-ins:**
  * `dict(...)` of 6 keyword items: `42·6+1 = 253`.
  * `kw.update(overrides)`: `42o+1`.
  * `cls(**kw)`: `42(6+o)+1`.
* **Callees:** `C[soj.SOJParams.small_scale](o)`, and `Params.__init__` without its SOJParams term (soj is given): 71.
* **Bound:** `610 + 84o + C[soj.SOJParams.small_scale](o)`.

### main.Params.__repr__

Diagnostics only; no bound needed.

### main.Params.luks_threshold

* **Profile:** outside 12.
* **Built-ins:** `m.bit_length()`: 1.
* **Bound:** 13.

### main.Params.enumeration_cap

* **Profile:** outside 14.
* **Built-ins:** `bit_length`: 1.
* **Bound:** 15.

### main.Params.small_quotient

* **Profile:** outside 20.
* **Callees:** `luks_threshold` (13).
* **Bound:** 33.

### main.Params.k_paper

* **Profile:** outside 13.
* **Built-ins:** `max(n,1)` 2, `bit_length` 1, `max(9,·)` 2.
* **Bound:** 18.

### main.Params.gamma_threshold

* **Profile:** outside 14.
* **Callees:** `k_paper` (18).
* **Bound:** 32.

### main.Params.k_for

* **Profile:** outside 57.
* **Path costs:**
  * paper path: `k_paper` 18, `min` 2, `max` 2, total 22;
  * small-scale path: `max(n,2)` 2, `log2` 1, `ceil` 1, `int` 1, `max` 2, `min` of 3 arguments 3, `max` 2, total 12;
  * `local_k` path: 4.
* **Bound:** `57 + 22 = 79`.

### main.Solver.__init__

* **Profile:** outside 18.
* **Built-ins:** `Counter()`: 1.
* **Callees:** `Params.paper()` if `params is None` (86 + C).
* **Bound:** `105 + C[soj.SOJParams.__init__]()`.

### main.Solver.iso — the wrapper W_iso

* **Profile:** outside 212, no loops. `<genexpr@237>` has total 21 and one loop.
* **Instructions:**
  * 212;
  * the genexpr over `G.gens` (r elements): `21(r+1)` (Lemma P).
* **Built-ins:**
  * `tuple(x)`, `tuple(y)`: `2(n+1)` (A2).
  * Two `len`: 2.
  * `all(...)`: `r+1`.
  * Two stats increments (`"calls"`, `"aut_cache_hits"`): 256.
  * `Counter(x) != Counter(y)`: each Counter costs `(3+4λ)n+1` (one touch and two dict operations per letter, K2/K3), and the comparison costs `2n(3+4λ)+4` (K13). Total ≤ `(12+16λ)n+6`.
  * `x == y` and `x != y`: `2(λn+1)` (K5).
  * `G.aut_cache.get(x)` and `G.aut_cache[x] = A`: key x of size ≤ `λn+1`, so `2(1+2(λn+1)) = 4λn+6` (K3).
* **Callees:**
  * `r·C[perm.is_string_automorphism](n, λ)`. Each of its letter comparisons costs ≤ λ; if that bound is stated for int letters, multiply its comparison count by λ.
  * `C[tower.Tower.trivial](n)`, `C[perm.identity](n)`, `C[action.Coset.__init__](n)`.
* **Bound:**

      W_iso ≤ 508 + 22r + (14+22λ)n + r·C[perm.is_string_automorphism](n,λ)
              + C[tower.Tower.trivial](n) + C[perm.identity](n) + C[action.Coset.__init__](n)
            ≤ 508 + 22r + 36λn + (same callees)          (λ ≥ 1).

* **Solver calls (the recursion):**
  * If `x ≠ y`, `G ≰ Aut(x)` and the letter multisets agree: one call `_one_iso(G,x,y)`, i.e. one node `_solve(G,x,y)`, and one nested call `iso(G, x, x, tower)` on the same group and degree n.
  * If `x == y` and `aut_cache` misses: one node `_solve(G,x,x)`.
  * Otherwise none.

### main.Solver._one_iso

* **Profile:** outside 14.
* **Bound:** 14.
* **Solver calls:** one node `_solve(G, x, y, tower)`.

### main.Solver._solve — the dispatch part D

* **Profile:** outside 499; loops 291 (5,9), 303 (14,10), 342 (8,8), 344 (7,9). `<lambda@280>` total 3; `<genexpr@303>` total 27 with 2 loops (Lemma P(5)).
* Let `Ord = Ord(n,r)`, `m_b = len(blocks)` (the number of blocks of the quotient), and ℓ the number of tower levels.
* `G.order()` is called at most 3 times on any path (lines 268, 273, 284, or 268, 273, 281). Each call is charged `Ord`.
* `Gbar` and `Gp` have at most r generators: `PermGroup` of r images, deduplicated.
* **Loop iteration bounds:**
  * 291: `range(n)`, n iterations.
  * 303: over `sup`, `|sup| ≤ |top| ≤ n`. `sup` is a block system of the action on the top blocks, i.e. a partition of `range(|top|)`.
  * 342: over `imgs`, r iterations.
  * 344: over `blocks`, `m_b ≤ n` iterations.
* **Line 303 in detail:**
  * The list comprehension costs `14(|sup|+1) + 10 ≤ 14n + 24`.
  * The genexpr for a group `grp` iterates over `bi ∈ grp` and over `p ∈ top[bi]`, with `L_grp = Σ_{bi∈grp} |top[bi]|`. By Lemma P(5) it costs `27(1 + |grp| + L_grp)`. Summed over the groups this is `≤ 27(|sup| + |top| + n) ≤ 81n`.
  * `sorted` of `L_grp` ints (K7), summed: `≤ n⌈log₂n⌉ + 3n`.
  * The comparison `len(sup) < len(top)`: 2.
  * `coarse.sort()`: the elements are disjoint non-empty lists, so one comparison costs ≤ 2. Total `≤ 2n⌈log₂n⌉ + 2n + 1`.
  * Together, line 303 and the sort cost `≤ 100n + 27 + 3n⌈log₂n⌉`.
* **Path costs:**
  * **Brute force:** `D_bf ≤ 499 + Ord`.
  * **Chain rule:** `D_cr ≤ 500 + Ord + C[group.PermGroup.orbits](n,r)`.
  * **Giant** (lines 273–281).
    * Charges: two `factorial(n)` `2(n+1)`; two stats 256; `list(G.gens)` `r+1`. The lambda@280 (3 instructions) is called r times, by `GroupWithAction.__init__` (action.py:164–167, one call per generator); `trivial_case` never calls `Gw.phi`.
    * `D_gi ≤ 759 + 2n + 4r + 3Ord + C[orbits](n,r) + C[tower.Tower.is_trivial]() + C[action.GroupWithAction.__init__](n, n, r)`.
  * **Hint** (lines 282–295; only for the group of `GraphInstance`).
    * Charges: the failed giant test `n+1`; `getattr` 1; `gamma_threshold` 32; `small_quotient` 33; two `agg_cache` operations 34; loop 291 `6n+15`; stats `128+192`.
    * `D_hint ≤ 936 + 7n + 3Ord + C[orbits](n,r) + C[tower.Tower.is_trivial]() + C[action.GroupWithAction.__init__](n, m, r) + C[certificates.JohnsonData.__init__](n, m, t; b = n)`.
  * **Transitive, before the quotient decision** (lines 297–311).
    * Charges both branches of line 298, and the hint tests (65) in case a hint is present.

          D_e0 ≤ 631 + 101n + 3n⌈log₂n⌉ + 3Ord + C[orbits](n,r) + C[tower.Tower.is_trivial]()
                 + C[tower.Tower.top_blocks](n,ℓ) + 2·C[group.PermGroup.minimal_block_system](n,r)
                 + C[group.PermGroup.induced_action](n,r; ≤ n blocks) + C[tower.Tower.extend](n,ℓ)
                 + C[group.PermGroup.induced_action](n,r; m_b blocks) + Ord(m_b, r) + 33.

      (The 33 of `small_quotient` is already inside 631; the explicit +33 is kept as slack.)
    * Then, with `RJ = C[johnson.recognize_johnson](m_b, r)` and `RC = C[johnson.recognize_cameron](m_b, r)`:
      * `D_luks1 = D_e0 + 128` (line 312);
      * `D_luks2 = D_e0 + 271 + RJ + RC + C[errors.fallback]()` (unrecognised quotient, lines 330–335);
      * `D_luks3 = D_e0 + 160 + RJ` (line 336);
      * `D_cam = D_e0 + 320 + RJ + RC`;
      * `D_J = D_e0 + 384 + 8r + 8m_b + n + r·C[johnson.johnson_phi](m_b, m, t) + RJ + C[action.GroupWithAction.__init__](n,m,r) + C[certificates.JohnsonData.__init__](n,m,t; b = m_b)`. Here the loop at 344 gives `7(m_b+1)+9 + Σ(|b|+1) = 8m_b + n + 16`, and the loop at 342 gives `8(r+1)+8`.
* **Solver calls:** none directly. The handlers are charged in Section 3.

### main.Solver.brute_force

* **Profile:** outside 60; loop 367 (0, 10). The loop body returns, so it has no backward jump and `E ≤ 1`.
* **Context:** reached only from `_solve` when `G.order() ≤ 5040`, so `g := |G| ≤ 5040` by (A3)(i).
* **Instructions:** `60 + 10 = 70`.
* **Built-ins:**
  * stats 128;
  * `aut_cache.get` and `aut_cache[x] =`: `4λn+6`;
  * `list(_chain_search(G,x,x))`: `|Aut_G(x)| + 1 ≤ g+1`;
  * `len`: 1;
  * `x == y`: `λn+1`.
* **Callees:**
  * `_chain_search` twice. The first runs to exhaustion; the second is consumed for at most one element. Both cost ≤ `C_cs`.
  * `C[group.PermGroup.__init__](n, g)` (at most `|Aut_G(x)| ≤ g` generators, with `known_order`).
  * `C[perm.identity](n)`, `2·C[action.Coset.__init__](n)`.
* **Bound:**

      W_bf ≤ 207 + 5λn + g + 2·C_cs + C[group.PermGroup.__init__](n,g) + C[perm.identity](n)
             + 2·C[action.Coset.__init__](n).

* **Solver calls:** none.

### main.Solver.iso_window — W_iw(N, L)

* **Profile:** outside 78.
* **Parameters:** `N = H.n`, `L = len(window) ≤ N`. Callers pass duplicate-free windows: `sorted` of a frozenset, or the list `rest` of distinct points.
* **Built-ins:** `sorted(window)` `L⌈log₂L⌉ + 2L + 1`; `xr != yr` `λL + 1`.
* **Callees:** `C[action.window_lifter](N, L, r_H)`, `2·C[action.WindowLifter.restrict_string](L)`, `C[group.PermGroup.is_trivial]()`, `C[perm.identity](N)`, `C[action.Coset.__init__](N)`, `C[tower.Tower.trivial](N)`, `C[tower.Tower.restrict](N, L, ℓ)`, `C[action.WindowLifter.lift_coset](N, L, r_C)`.
* **Bound:**

      W_iw(N,L) ≤ 80 + L⌈log₂L⌉ + (2+λ)L + C[action.window_lifter](N,L,r_H)
                  + 2C[action.WindowLifter.restrict_string](L) + C[group.PermGroup.is_trivial]()
                  + C[perm.identity](N) + C[action.Coset.__init__](N) + C[tower.Tower.trivial](N)
                  + C[tower.Tower.restrict](N,L,ℓ) + C[action.WindowLifter.lift_coset](N,L,r_C).

  The bound is monotone in L, so `W_iw(N) := W_iw(N, N)` is a uniform bound.
* **Solver calls:** at most 1. It is `iso(Hr, x|Δ, y|Δ, tower|Δ)`, where `Hr = lifter.restricted` is the restriction of H to the window, of degree L. It is made only if the window is non-empty and Hr is nontrivial.

### main.Solver.chain_rule

* **Profile:** outside 54; loop 410 (113, 0). `<lambda@402>` total 10.
* **Parameters:** `ω = len(orbits)`, with `2 ≤ ω ≤ n` (the caller requires `len(orbits) > 1`). `n_i = |Δ_i|`, `Σ n_i = n` (the orbits partition Ω).
* **Loop iteration bound:** `order` is a permutation of `orbits`, so there are ω iterations, possibly fewer because of a `return None`.
* **Instructions:** `54 + 113(ω+1)`. The key lambda costs 10 per call, ω calls.
* **Built-ins:**
  * stats 128;
  * the key's `len` and `min(o)`: `12ω + n` in total;
  * `sorted` with 2-tuple keys (comparison cost 2): `2ω⌈log₂ω⌉ + 2ω + 1`;
  * `stage_cache.get` and the store: `4λn + 6`;
  * `enumerate`: `ω+1`;
  * per iteration: two `len` and one `append`, 3, and `xr != yr`, `λn_i + 1`.
* **Callees:**
  * `(ω+1)·C[perm.identity](n)`, `C[action.Coset.__init__](n)`;
  * per orbit i: `C[action.window_lifter](n, n_i, r_i)`, `2C[action.WindowLifter.restrict_string](n_i)`, `C[group.PermGroup.is_trivial]()`, `C[tower.Tower.restrict](n, n_i, ℓ)`, `C[action.WindowLifter.lift](n, n_i)`, `C[action.WindowLifter.lift_group](n, n_i, r'_i)`, `C[perm.inv](n)`, `C[perm.act_string](n)`, `C[perm.mul](n)`. Here `r_i` is the generator count of the stage group `cur_i`, and `r'_i` that of `C.group`.
  * The stage cache (line 403): when `i < len(stages)` the cached `(lifter, group)` is used, and neither `window_lifter` nor `lift_group` is called. The bound charges them anyway.
* **Bound:**

      W_cr ≤ 303 + 132ω + 2ω⌈log₂ω⌉ + (1+5λ)n + (ω+1)C[perm.identity](n) + C[action.Coset.__init__](n)
             + Σ_{i=1}^{ω} [ C[action.window_lifter](n,n_i,r_i) + 2C[action.WindowLifter.restrict_string](n_i)
               + C[group.PermGroup.is_trivial]() + C[tower.Tower.restrict](n,n_i,ℓ)
               + C[action.WindowLifter.lift](n,n_i) + C[action.WindowLifter.lift_group](n,n_i,r'_i)
               + C[perm.inv](n) + C[perm.act_string](n) + C[perm.mul](n) ].

* **Solver calls:** at most ω calls `iso(Hr_i, x|Δ_i, cur_y|Δ_i, tower|Δ_i)`, one per orbit Δ_i whose restricted group is nontrivial.
  * Hr_i is the restriction to Δ_i of the stage group `Aut_G^{Δ_1∪…∪Δ_{i−1}}(x)` (lifted). It has degree `n_i ≤ n−1`, and `Σ n_i = n`.
  * The calls stop at the first failure.
  * The stage cache does not reduce the number of calls.

### main.Solver.strong_luks

* **Profile:** outside 61; loop 449 (40, 2).
* **Parameters:**
  * `m = len(blocks)`.
  * I is the number of iterations.
  * S is the number of successful calls: at most 1 if `x ≠ y`, at most I otherwise.
  * `q = |Gbar|`.
* **Loop iteration bound:** `comb.coset_reps_prefix(k)` (group.py:424–440) yields `∏_{i<k} |levels[i].trans|` elements, where `k = _gamma_levels()`.
  * The first k levels of `comb_gamma` have base points in Γ: the forced prefix is Γ, and non-prefix levels take base points from `rest_order ⊆ Ω`.
  * Their pointwise stabilizer is the kernel N.
  * By (A3), `I ≤ |G : N| = |Gbar| = q`.
  * The loop breaks at the first success if `x ≠ y`.
* **Instructions:** `61 + 40(I+1) + 2`.
* **Built-ins:**
  * stats 128; `len(blocks)` 1;
  * per iteration: the slice `r[:n]`, `n+1`;
  * per success: `append` 1 and `x != y`, `λn+1`.
* **Callees:**
  * `C[action.GroupWithAction.__init__](n,m,r)`, `C[action.GroupWithAction.kernel](n,m,r)`, `C[action.GroupWithAction.comb_gamma](n,m,r)`, `C[action.GroupWithAction._gamma_levels](n,m,r)`;
  * `C[group.PermGroup.coset_reps_prefix](n+m, k; I elements)`;
  * `I·(C[perm.inv](n) + C[perm.act_string](n))`, `S·C[perm.mul](n)`;
  * `C[group.generated_subcoset](n, S, ·)`, `C[action.Coset.__init__](n)`.
* **Bound:** `W_sl ≤ 232 + (41+n)I + (2+λn)S + (callees)`.
* **Solver calls:** `I ≤ q` calls `iso(N, x, y^{σ^{-1}}, tower)`, with N the kernel of G on the blocks (degree n).
  * Path `D_luks1`: `q < m^{1+⌊log₂m⌋}`, because `small_quotient` holds.
  * Path `D_luks2`: `q < m^{2+⌊log₂m⌋}`, or `m < 25` and `q ≤ 24!`. Otherwise `fallback` raises.
  * Path `D_luks3`: `q ≤ (jh.m)! ≤ (ℓ(n)−1)!`, since Gbar is a Johnson group on `jh.m < ℓ(n)` points (recognize_johnson).

### main.Solver.cameron_reduction

* **Profile:** outside 78; loop 481 (52, 2).
* **Parameters:** `m = Gbar.n`; `s_c = hs.s`; `ν = len(hs.N_gens)`; `r_b = len(Gbar.gens) ≤ r`.
* **Loop iteration bound:** as in `strong_luks`, applied to `Qw = GroupWithAction(Gbar, s_c, class_images)`.
  * `I ≤ |Gbar : ker(Gbar → S_{s_c})| ≤ s_c!`.
  * `s_c ≤ log₂ m`, because `m = c^{s_c}` with `c = C(k', t') ≥ 2`, in the product action of `johnson.CameronStructure`.
  * The loop breaks at the first success if `x ≠ y`.
* **Instructions:** `78 + 52(I+1) + 2`.
* **Built-ins:** stats 128; per iteration the slice `r[:m]`, `m+1`; per success `λn+2`.
* **Callees:**
  * `C[action.GroupWithAction.__init__](n,m,r)`, `C[group.PermGroup.__init__](m,ν)`, `C[group.PermGroup.order](m,ν)`, `C[action.GroupWithAction.preimage](n,m,r,ν)`;
  * `C[action.GroupWithAction.__init__](m,s_c,r_b)`, `C[action.GroupWithAction.comb_gamma](m,s_c,r_b)`, `C[action.GroupWithAction._gamma_levels](m,s_c,r_b)`;
  * `C[group.PermGroup.coset_reps_prefix](m+s_c, ·; I elements)`;
  * `I·(C[action.GroupWithAction.lift](n,m,r) + C[perm.inv](n) + C[perm.act_string](n))`, `S·C[perm.mul](n)`;
  * `C[group.generated_subcoset](n,S,·)`, `C[action.Coset.__init__](n)`.
* **Bound:** `W_cam ≤ 260 + (53+m)I + (2+λn)S + (callees)`.
* **Solver calls:** `I ≤ s_c!` calls `iso(NG, x, y^{σ^{-1}}, tower)`, where `NG = φ^{-1}(Nbar)` has degree n.

### main.Solver.johnson_case

* **Profile:** outside 30.
* **Bound:** `30 + C[certificates.JohnsonData.is_primitive]()`, plus the handler (`trivial_case`, `primitive_johnson` or `imprimitive_johnson`), charged in Section 3.

### main.Solver.trivial_case

* **Profile:** outside 165; loops 513 (23,0), 519 (14,0), 520 (7,0), 524 (13,0), 527 (13,0). Genexprs 516 (28), 533 (21), 537 (27).
* **Parameters:**
  * `n = Gw.n`;
  * `d = len(cx) ≤ n` is the number of distinct letters;
  * `n_l = len(cx[l])`, with `Σ n_l = n`.
* **Loop iteration bounds:**
  * 513: `range(n)`.
  * 519, 524, 527: over `cx`, d iterations.
  * 520: over `zip(cx[l], cy[l])`, `n_l` iterations per entry, d entries.
* **Costs, line by line:**
  * Instructions 165, stats 128.
  * Loop 513: `23(n+1) + (n+1)` for the range, and per u two `setdefault` (`2(1+2λ)`, K3) and two `append`. Total `≤ 24n + 24 + (4+4λ)n`.
  * Line 516:
    * `set(cx)`, `set(cy)`: `2((2+2λ)n+1)`;
    * `!=`: `(1+2λ)·2n + 1`;
    * the genexpr `28(d+1)` and `any` `d+1`;
    * per l two lookups and two `len`: `(4+4λ)n`.
    * Total `≤ (39+12λ)n + 32`.
  * `[0]*n`: `n+1`.
  * Loops 519/520: `14(d+1) + d(3+4λ) + 7(n+d) + (n+d)` (zip). Total `≤ (33+4λ)n + 14`.
  * `tuple(sigma)`: `n+1`.
  * Loop 524: `13(d+1) + d(4+2λ)`: per l a lookup and `extend` by ≤ 2 generators. Total `≤ (17+2λ)n + 13`.
  * Loop 527: `13(d+1) + d(3+2λ) + Σ n_l`: per l a lookup `1+2λ`, `len` 1 and `factorial` `n_l+1`. Total `≤ (17+2λ)n + 13`.
  * Alt branch:
    * genexpr 533 `21(d+1)`, the values view, `any` and `len`: `24d + 23`;
    * genexpr 537 `27(d+1)` plus `d(2+2λ) + 1`;
    * `cy[l][0], cy[l][1]`: `2(1+2λ)`.
    * Total `≤ (53+2λ)n + 53 + 4λ`.
* **Callees:**
  * `C[action.GroupWithAction.image_is_sym](m,r)`, only if `is_sym is None`;
  * `Σ_l C[perm.sym_gens](n_l, n)`;
  * `C[group.PermGroup.__init__](n, 4n)`: `gens` has at most 2d entries (`sym_gens` returns ≤ 2), and `even_subgroup_gens` returns at most twice as many;
  * `C[group.even_subgroup_gens](n, 2n)`, `C[perm.parity](n)`, `C[perm.from_cycles](n, 2)`, `C[perm.mul](n)`, `C[action.Coset.__init__](n)`.
* **Bound:**

      W_tc ≤ 444 + 4λ + (189+26λ)n + Σ_l C[perm.sym_gens](n_l,n) + C[action.GroupWithAction.image_is_sym](m,r)
             + C[group.PermGroup.__init__](n,4n) + C[group.even_subgroup_gens](n,2n) + C[perm.parity](n)
             + C[perm.from_cycles](n,2) + C[perm.mul](n) + C[action.Coset.__init__](n)
           ≤ 448λ + 215λn + (same callees).

* **Solver calls:** none.

### main.Solver.hypergraph_structure — W_hs

* **Profile:** outside 97; loops 549 DictComp (6,11), 550 For (30,0), 556 DictComp (6,11), 557 ListComp (6,9). `<genexpr@558>` total 21.
* **Parameters:**
  * `T = m^t` is the number of tuples produced by `product(range(m), repeat=t)`.
  * `d ≤ n` is the number of distinct letters of s.
  * `D = len(distinct)`, with `D ≤ min(d+1, T) ≤ n+1`: the values of `raw` are −1 or a letter index `< d`.
* **Loop iteration bounds:** 549 and 556 have d and D iterations (their dicts); 550 and 557 have T iterations (`raw` has exactly T entries).
* **Costs:**
  * Instructions 97; the import 1.
  * Line 549:
    * `set(s)`: `(2+2λ)n+1`;
    * `sorted(·, key=canon)`: `d·C[canon.canon](λ) + 3λd⌈log₂d⌉ + 2d + 1` (K7, K10);
    * `enumerate`: `d+1`;
    * the dictcomp `6(d+1)+11` plus d insertions `1+2λ`.
    * Total `≤ (12+4λ)n + 20 + 3λn⌈log₂n⌉ + n·C[canon.canon](λ)`.
  * Loop 550:
    * `product`: `tT+1`; `range(m)`: `m+1`; the loop `30(T+1)`.
    * Per tuple:
      * `set(tup)`: `4t+1`; `len`: 1;
      * then either `append` (1), or:
        * `frozenset(tup)`: `4t+1`;
        * the `block_of_T` lookup with a key of size `t+1`: `2t+3`;
        * the `letter_index` lookup: `1+2λ`;
        * `append`: 1.
      * So `≤ 10t + 8 + 2λ` per tuple.
    * Total `≤ (11t+38+2λ)T + m + 32`.
  * Line 555: `set(raw)` `4T+1`; `sorted` `D⌈log₂D⌉ + 2D + 1`.
  * Line 556: `6(D+1) + 11 + (D+1) + 3D`.
  * Line 557: `6(T+1) + 9 + 3T`.
  * Line 558:
    * the genexpr `21(D+1)`;
    * `raw.count(c)`: `2T+1` each, D times (K6);
    * `tuple`: `D+1`.
  * `[X0]`: 1.
* **Callees:** `C[wl.KStructure.__init__](m, t)`, `C[structure.Chooser.check](D+2)`, `C[wl.refine_structures](m, t)`. The latter receives `chooser.check` as its trace; those check calls are inside its bound.
* **Bound:**

      W_hs ≤ 208 + m + (12+4λ)n + 3λn⌈log₂n⌉ + 35D + D⌈log₂D⌉ + (11t + 51 + 2λ + 2D)·m^t
             + n·C[canon.canon](λ) + C[wl.KStructure.__init__](m,t) + C[structure.Chooser.check](D+2)
             + C[wl.refine_structures](m,t)
           ≤ 243 + m + (47+4λ)n + (n+1)⌈log₂(n+1)⌉ + 3λn⌈log₂n⌉ + (11t + 53 + 2λ + 2n)·m^t + (same callees),

  using `D ≤ n+1`.

### main.Solver.hypergraph_twin_classes — W_tw

* **Profile:** outside 39; loops 572 (12,0), 573 (37,0), 577 (34,4), 586 (15,0). Inner `find`: outside 4, while 567 (19,6). `<genexpr@579>` total 29.
* **Parameters:** `P2 = m(m−1)/2`; `b = len(jd.block_of_T)`.
* **Loop iteration bounds:**
  * 572 and 586: `range(m)`.
  * 573: entered m times, `P2` iterations in total.
  * 577: entered at most once per pair (the `continue` skips it), b iterations (the items of `block_of_T`).
  * `find`'s while loop: each iteration replaces a by its grandparent. The structure stays a forest: path halving only re-links a node to an ancestor, and line 584 links one root below another root (the two roots are distinct by line 574). So the depth of a strictly decreases, and the loop has at most `m−1` iterations. Hence `F := cost(find) ≤ 4 + 19m + 6 = 19m + 10`.
* **Per pair:**
  * 2 calls of `find`, plus 2 more at line 584.
  * The items view `b+1` and the loop `34(b+1)+4`.
  * Per T:
    * two frozenset membership tests: 6;
    * the genexpr: `29(t+1)`;
    * `frozenset`: `4t+1`;
    * the lookup with a key of size `t+1`: `2t+3`;
    * the letter comparison: λ.
    * So `≤ 39 + 35t + λ` per T.
  * In total `≤ 4F + 39 + b(74+35t+λ)` per pair.
* **Other costs:**
  * `list(range(m))`: `2m+2`.
  * Loop 572: `13(m+1)`.
  * Loop 573: `38(P2+m)`, including the range.
  * Loop 586: `16(m+1) + m(F+4)`.
  * `list(groups.values())`: `≤ 2m+2`.
* **Bound:**

      W_tw ≤ 72 + 85m + 19m² + P2·(117 + 76m + b(74 + 35t + λ))
           ≤ 72 + 85m + 78m² + 38m³ + ½m²·b(74 + 35t + λ).

* **Solver calls:** none.

### main.Solver.primitive_johnson — W_pj, and its inner functions

* **Profile:** outside 110. Inner functions:
  * `largest_twin`: outside 13; its `<lambda@598>` has total 27 and contains a loop (Lemma P(5)).
  * `proc@604`: outside 39.
  * `proc2@611`: outside 29.
* **`largest_twin(s)` — LT.**
  * Instructions 13, plus `W_tw`.
  * `max` over the c twin classes: `c+1`.
  * The key lambda costs `27+5|c_i|` per class.
  * There are `c−1` key comparisons of `(len, list)` tuples, each `≤ 2+|c_i|`.
  * The classes partition Γ (`Σ|c_i| = m`, `c ≤ m`), so `LT ≤ 14 + 36m + W_tw`.
* **`proc@604` (pullback) — P_pull.**
  * Instructions 39, plus LT, plus `C[structure.Chooser.check](3)`.
  * `set(range(m))`: `5m+2`; `set(C)`: `4|C|+1`; the difference: `3(m+|C|)+1`; two frozensets: `≤ 4m+1 + 4|C|+1`.
  * Plus `C[structure.Structure.__init__](m, 2)`.
  * `P_pull ≤ 59 + 59m + W_tw + C[structure.Chooser.check](3) + C[structure.Structure.__init__](m,2)`.
* **`proc2@611` (Extended Design Lemma) — P_edl.**
  * Instructions 29, plus `W_hs`, plus `frozenset(range(m))` `5m+2`.
  * `P_edl ≤ 31 + 5m + W_hs + C[structure.Structure.__init__](m,1) + C[design.extended_design_lemma](m, t)`. The second callee is on the t-ary configuration X on m points.
* **The function itself.**
  * Instructions 110; two stats 256; `largest_twin(x)` LT; `len` 1.
  * `W_pj ≤ 381 + 36m + W_tw`. The `branch` call is charged in Section 3.
* **Solver calls:** none directly; `branch` makes them.

### main.Solver.branch — W_br

* **Profile:** outside 138; loops 642 ListComp (11,8), 652 For (160,0). `<genexpr@651>` total 20; `<lambda@652>` total 8.
* **Parameters (Lemma R):** d, s, R, s', S, κ. Further:
  * `f_a = len(known_auts)`;
  * `a_x = len(Sx.aut_gens())`. `intersect_image` returns at most `2a_x` generators, since `even_subgroup_gens` returns ≤ 2 per input;
  * `r̄` is the maximal `len(sub.group.gens)`, `≤ ρ(n)` by G4;
  * `ℓ_tr = len(rc.trace)`;
  * `P_x` is the cost of `proc(x, rc)`; `P_y,j` is the cost of the j-th run `proc(y, ch)`, at most the full bound of proc, also for an aborted run (Lemma P counts every executed instruction).
* **Loop iteration bounds:**
  * 642: over `known_auts`, `f_a` iterations.
  * 652: over the results of `enumerate_runs`, `s' ≤ s` iterations (Lemma R). It returns at the first success if `x ≠ y`.
  * `proc` runs `1 + R ≤ 1 + s` times, and the lambda@652 R times.
* **Costs:**
  * Instructions: `138 + 11(f_a+1) + 8 + 160(s'+1)`, plus `20(d+1)` for the genexpr over `rc.chosen` (which has length d).
  * `x == y`: `λn+1`.
  * stats: 128 once; per iteration ≤ 256 (`branches`, plus `branches_pruned` or `branches_unaligned`).
  * `set()`: 1; `any`: `d+1`; `isinstance`: d.
  * Per iteration: `tuple(chosen)` `d+1`, and `key in covered` `1+2κ`.
  * Per success: two `append`, `extend` by `r̄`, one `append`: `≤ 5+r̄`.
* **Callees:**
  * `C[structure.RecordingChooser.__init__]()`, `C[structure.Structure.aut_gens](Sx)`;
  * `C[action.GroupWithAction.intersect_image](m, a_x)`, `C[group.PermGroup.__init__](m, 2a_x)`, `C[group.PermGroup.order](m, 2a_x)`;
  * `C[action.GroupWithAction.preimage](n, m, r, 2a_x)` (this computes G1), `C[action.GroupWithAction.image_is_sym](m, r)`;
  * `f_a·C[perm.is_identity](n)`, `C[group.PermGroup.__init__](n, f_a)`, `C[perm.identity](n)`;
  * `C[structure.enumerate_runs](ℓ_tr, d; R runs)`, the own work of `enumerate_runs` including the `ReplayChooser` constructions;
  * per iteration: `C[structure.align](Sx, Sy)`, `C[action.GroupWithAction.lift](n, m, r)`, `C[perm.inv](n)`, `C[perm.act_string](n)`, and `W_rec` — 0 if `recurse is None`, otherwise the own work of `recurse` (Section 3, case 2a);
  * `S·C[perm.mul](n)`, `C[group.generated_subcoset](n, S+1, h*)`, `2C[action.Coset.__init__](n)`;
  * `S` calls of `_covered` (only when `x == y` and `prune`), with p = 1..S keys and `h_j ≤ h* := f_a + S(r̄+1)` generators.
* **Bound:**

      W_br ≤ 468 + λn + 22d + 11f_a + P_x + Σ_{j≤R}(8 + P_y,j) + s'·(418 + d + 2κ) + S·(5 + r̄)
             + s'·(C[structure.align] + C[action.GroupWithAction.lift](n,m,r) + C[perm.inv](n)
                   + C[perm.act_string](n) + W_rec)
             + Σ_{j=1}^{S} C_cov(j, h_j) + (the fixed callees above)
           ≤ 468 + λn + 22d + 11f_a + P_x + s·(426 + d + 2κ + P_y + 5 + r̄ + C[align] + C[lift] + C[inv] + C[act_string] + W_rec)
             + Σ_j C_cov + (fixed callees),

  where `P_y` bounds one run.
* **Solver calls:**
  * If `recurse is None`: `s' ≤ s` calls `iso(G1, x, y^{σ^{-1}}, tower)`, where `G1 = φ^{-1}(Aut(Sx) ∩ G^φ)` has degree n. With `x ≠ y` they stop after the first success.
  * Otherwise none directly: the calls of `recurse` = `top_action` are listed there.

### main.Solver._covered — C_cov(p, h)

* **Profile:** outside 19; loops 690 ListComp (14,8), 692 For (12,0), 695 While (18,9), 697 For (28,0). `<genexpr@698>` total 21.
* **Parameters:**
  * `p = len(processed)`, `h = len(H_gens)`, `ι = len(imgs) ≤ h`;
  * `cap = 20000` (the default; no caller passes `cap`);
  * keys have d components and size κ (Lemma R, last remark).
* **Loop iteration bounds:**
  * 690: h iterations. 692: p iterations. 697: ι iterations per entry.
  * While loop 695, iteration j (per key): the j−1 popped elements and the element about to be popped are distinct members of `orbit`. An element is pushed only when it is added to `orbit`; the initial key is in `orbit`. So `|orbit| ≥ j`, and the loop test `len(orbit) < cap` gives `j ≤ cap − 1`.
  * At the end `|orbit| ≤ cap − 1 + ι`. `covered` holds at most `p(cap+h)` elements before a union.
* **Costs:**
  * Instructions `19 + 14(h+1) + 8 + 12(p+1)`; `set()` 1.
  * Per key:
    * `{key}`: `1+2κ`;
    * the while loop: `18(cap+1) + 9`, and per iteration `pop` and `len`, 2;
    * loop 697: `28(ι+1)` per entry;
    * per g: the genexpr `21(d+1) + A_key`, `tuple` `d+1`, `not in` and `add` `2(1+2κ)`, `append` 1;
    * `covered |= orbit`: `(1+2κ)p(cap+h)+1` (K4).
* **Callees:** `h·(C[perm.is_identity](n) + C[action.GroupWithAction.phi](n, m, r))`, and `apply_obj` inside `A_key` (structure).
* **Bound:**

      C_cov(p,h) ≤ 54 + 14h + 12p + h·(C[perm.is_identity](n) + C[action.GroupWithAction.phi](n,m,r))
                   + p·(960029 + 2κ) + 20000·p·h·(53 + 22d + 4κ + A_key) + (1+2κ)·p²·(20000 + h).

* **Summed over the S calls in `branch`** (`p = j`, `h_j ≤ h*`, `Σ_{j≤S} j ≤ S²`, `Σ j² ≤ S³`):

      Σ_j C_cov ≤ S·(54 + 14h* + h*·(C[perm.is_identity](n) + C[action.GroupWithAction.phi](n,m,r)))
                  + S²·(960041 + 2κ + 20000·h*·(53 + 22d + 4κ + A_key)) + S³·(1+2κ)(20000 + h*).

### main.Solver.imprimitive_johnson — W_ij, and its inner procs

* **Profile:** outside 162. Inner functions `proc@721` (outside 49; loop 726 (29,0)) and `proc@737` (outside 15).
* **The function itself:**
  * Instructions 162; stats `128 + 192`; `k_for` 79; `y != x` `λn+1`.
  * Four dict lookups with string keys: 68.
  * The comparisons of `case` (≤ 3) and of `sizes` (`≤ m+3`; `sizes` has ≤ m+1 components).
  * `W_ij ≤ 653 + λn + m`, plus the two `aggregate` calls and the case handler (Section 3).
* **Cache hit of `aggregate`.** In `proc`, `aggregate(jd, s, k)` with `s ∈ {x, y}` always hits:
  * `ax = aggregate(jd, x, k)` and `ay = aggregate(jd, y, k)` (or `ay = ax` when `y == x`) are computed first.
  * They are stored in `Gw.G.agg_cache` (line 810) under the same key `("agg", s, k)`, and nothing deletes entries.
  * The hit path executes 21 instructions (lines 746–752) plus two lookups of a key of size `≤ λn+6`, so `C_agg_hit ≤ 21 + 2(1 + 2(λn+6)) = 4λn + 47`.
* **`proc@721` (case 1) — P_1.**
  * Instructions 49, plus `C_agg_hit`, plus two lookups 34, plus `C[structure.Chooser.check](m+5)`.
  * `set(range(m))`: `5m+2`. Loop 726, over the `o ≤ m` orbits: `29(o+1)`.
  * Per orbit of length ≥ 2: `len`, `frozenset`, `append`, `set`, and `fixed -= set(orb)` (K4). In total `≤ 5 + 11|orb| + 3m`.
  * `frozenset(fixed)`: `4m+1`; `append`: 1.
  * `P_1 ≤ 163 + 4λn + 54m + 3m² + C[structure.Chooser.check](m+5) + C[structure.Structure.__init__](m, m+1)`.
* **`proc@737` (case 2b) — P_2b.**
  * `P_2b ≤ 15 + C_agg_hit + W_2b = 62 + 4λn + W_2b`.

### main.Solver.aggregate — A (on a miss), C_agg_hit (on a hit)

* **Profile:** outside 197; loops 759 For (86,0), 767 While (16,5), 769 For (47,0), 785 ListComp (11,8), 789 ListComp (8,9), 791 ListComp (19,9), 793 ListComp (14,8), 796 ListComp (8,8). Genexprs 770 (20), 787 (21), 791 (21), 803 (19).
* **Parameters:**
  * `M = C(m,k)`;
  * `r_K = len(cert.K.gens)` for a full test set;
  * `F = len(F_gens)` before deduplication, `F = Σ_{full A} r_K ≤ M·ρ(n)` (G4: `K(A)` is a `PermGroup` of degree n);
  * `r_F = len(Fimg.gens) ≤ F`;
  * `o = len(orbits) ≤ m`; `φ = len(Phi) ≤ m`.
* **Loop iteration bounds:**
  * 759: `combinations(range(m), k)`, M iterations.
  * 767: per test set, at most `|seen| ≤ M` iterations. `seen` contains only k-subsets of Γ; elements are pushed only when new to `seen`, so pops ≤ pushes + 1 ≤ `|seen|`.
  * 769: `zip(F_gens, F_img)`, at most F iterations.
  * 785, 787: `r_K` iterations. 789: F. 791: m, and the genexpr `r_F` per v. 793 and 803: o. 796: `r_F`.
* **Per test set A:**
  * The cycle of 759 (86), `combinations` (k), `frozenset(A)` (`4k+1`), `processed[A]` (`2k+3`).
  * The full part (lines 784–787): `34(r_K+1) + 9`, plus `r_K·(C[perm.is_identity](n) + C[action.GroupWithAction.phi](n,m,r))`.
  * The BFS, only if `F_img` is non-empty:
    * `seen` insertion `2k+3`, `C[perm.identity](n)`, while `16(I_w+1)+5`;
    * per pop: `pop`, `zip`, and `47(f+1)`;
    * per pair `(gg, gb)`: the genexpr `20(k+1)`, `frozenset` `4k+1`, at most 5 lookups of k-subsets `5(2k+3)`, `append`, a zip step, and `C[perm.mul](n)`.
    * So `BFS_A ≤ 24 + 2k + C[perm.identity](n) + I_w·(65 + F(85 + 34k + C[perm.mul](n)))`.
  * Certificate: charged as `C[certificates.LocalCertificates.certificate](n,m,k) + C[perm.inv](n) + C[certificates.LocalCertificates.conjugate](n,m,k)`, both branches for every A ("charge the full count").
* **After the loop:**
  * `dict.fromkeys(F_gens)`: keys of size `n+1`, `(4+2n)F + 1`; `list`: `F+1`.
  * Line 789: `8(F+1) + 9 + F·C[action.GroupWithAction.phi](n,m,r)`.
  * Line 791: `19(m+1) + 9 + (m+1) + m·22(r_F+1)`.
  * `frozenset(support)`: `4m+1`. Line 793: `14(o+1) + 8 + o`.
  * The `big` branch: `sorted` `φ⌈log₂φ⌉ + 2φ + 1`, line 796 `8(r_F+1) + 8`, two `len`.
  * The `elif` branch: line 803 `19(o+1)`, `sorted` `o⌈log₂o⌉ + 2o + 1`, `tuple` `o+1`.
  * The data dict with 9 string keys: 153. The two cache operations: `2(2λn+13)`. stats: 128.
* **Callees:** `C[certificates.LocalCertificates.__init__](n)`, `C[group.PermGroup.__init__](m, F)`, `C[group.PermGroup.orbits](m, r_F)`, `r_F·C[certificates.restrict_to](m, φ)`, `C[certificates.is_giant_on](φ, r_F)`.
* **Bound (miss):**

      A ≤ 705 + 4λn + 86m + 2m⌈log₂m⌉ + (22m+8)·r_F + (47+2n)·F + M·(157 + 9k)
          + M²·(65 + F·(85 + 34k + C[perm.mul](n)))
          + M·(C[certificates.LocalCertificates.certificate](n,m,k) + C[certificates.LocalCertificates.conjugate](n,m,k)
               + C[perm.inv](n) + C[perm.identity](n))
          + F·(C[perm.is_identity](n) + 2C[action.GroupWithAction.phi](n,m,r))
          + C[certificates.LocalCertificates.__init__](n) + C[group.PermGroup.__init__](m,F)
          + C[group.PermGroup.orbits](m,r_F) + r_F·C[certificates.restrict_to](m,φ) + C[certificates.is_giant_on](φ,r_F)
        ≤ 705 + 4λn + 86m + 2m⌈log₂m⌉ + (55 + 2n + 22m)·F + M(157+9k) + M²(65 + F(85+34k+C[perm.mul](n))) + ...

  where `F ≤ M·ρ(n)`.
* **Bound (hit):** `C_agg_hit ≤ 4λn + 47`.
* **Solver calls:** those of the at most M calls `lc.certificate(A)` that are not cache hits. These are the `iso_window` calls listed in the solver-call item of `C[certificates.LocalCertificates.certificate]`, made in `recompute`. Their own work `W_iw` is added in Section 3.

### main.Solver.case_2a, and its inner functions

* **Profile:** outside 65. Inner functions `proc@821` (outside 45) and `recurse@830` (outside 11).
* **The function itself:** instructions 65, stats 128, two lookups 34: `W_2a ≤ 227`, plus `branch`.
* **`proc@821` — P_2a.**
  * Instructions 45, plus `C_agg_hit` (a hit, as above), plus the lookup 17, plus `C[structure.Chooser.check](3)`.
  * Sets: `frozenset(Phi)`, `set(range(m))`, `set(Phi)`, the difference, `frozenset`: `≤ 12m + 11φ + 6 ≤ 23m + 6`.
  * `P_2a ≤ 115 + 4λn + 23m + C[structure.Chooser.check](3) + C[structure.Structure.__init__](m,2)`.
* **`recurse@830`:** `11 + W_ta`. Its solver calls are those of `top_action`.

### main.Solver.top_action — W_ta

* **Profile:** outside 348; loops 844 (8,8), 850 (11,9), 851 (11,9), 854 For (24,0), 897 (12,8). `<lambda@845>` total 10.
* **Parameters:**
  * `φ = len(Phi)`, with `m/2 < φ ≤ m`;
  * `r1 = len(G1.gens)`, `r1' = len(G1w.G.gens) ≤ r1`;
  * `f = len(F_gens)`, `f' = len(Fgroup.gens) ≤ f`;
  * `w = |Ω(Φ)| ≤ n`.
* **Loop iteration bounds:**
  * 844: `r1'` iterations. 850: f. 851: `f'`. 897: n.
  * 854: over `alt_gens(...)`, which returns at most 2 permutations (perm.py:155–166).
* **The lambda@845.** It is called only by the `GroupWithAction.__init__` checks of `Gp` and `Fw`: once per generator, `r1 + f'` calls.
  * `Gp` and `Fw` are local, and `phi()` is never called on them: `kernel`, `lift`, `image_is_sym` and `image_order` do not use `phi_fn`.
  * Each call costs `10 + C[action.GroupWithAction.phi](n,m,r) + C[certificates.restrict_to](m,φ)`.
* **Built-ins:**
  * stats 128; `list(Phi)` `φ+1`; `frozenset(Phi)` `4φ+1`;
  * `sorted(window)`: `w⌈log₂w⌉ + 2w + 1`;
  * `list(range(φ))`: `2φ+2`; `factorial(φ)`: `φ+1`; `x == y`: `λn+1`;
  * line 897: `set(window)` is rebuilt for every u (it sits inside the comprehension's condition), so `n(4w+1+3) + (n+1)`;
  * four `append`.
* **Callees (Σ_ta):**
  * `C[action.GroupWithAction.subgroup](n,m,r1)`, `C[group.PermGroup.known_order_or_none]()`;
  * `(2r1 + 2f)·C[certificates.restrict_to](m,φ)`, `(r1 + 2f)·C[action.GroupWithAction.phi](n,m,r)`;
  * `C[action.GroupWithAction.__init__](n,φ,r1)`, `C[action.GroupWithAction.__init__](n,φ,f)`, `C[action.GroupWithAction.kernel](n,φ,r1)`;
  * `C[certificates.JohnsonData.omega_of](b,t,φ)`;
  * `f·C[perm.is_identity](n)`, `C[group.PermGroup.__init__](n,f)`, `C[perm.alt_gens](φ,φ)`;
  * `3C[action.GroupWithAction.lift](n,φ,f)`, `2C[action.GroupWithAction.lift](n,φ,r1)`, `4C[group.PermGroup.__init__](n,0)`;
  * `C[action.GroupWithAction.image_is_sym](φ,r1)`, `C[action.GroupWithAction.image_order](φ,f)`;
  * `3C[perm.from_cycles](φ,2)`, `3C[perm.inv](n)`, `3C[perm.act_string](n)`, `3C[perm.mul](n)`;
  * `C[group.generated_subcoset](n,4,·)`, `C[perm.identity](n)`, `C[action.Coset.__init__](n)`.
* **The `iso_window` calls:** at most 4 on the window `Ω(Φ)` (lines 859, 875, 884, 890) and 1 on `rest` (line 899). Their own work is `4·W_iw(n,w) + W_iw(n,n−w)`.
* **Bound:**

      W_ta ≤ 636 + 8φ + 18r1 + 32f + w⌈log₂w⌉ + 2w + (17+λ)n + 4nw + Σ_ta + 4·W_iw(n,w) + W_iw(n,n−w)
           ≤ 636 + 8m + 18r1 + 32f + n⌈log₂n⌉ + (19+λ)n + 4n² + Σ_ta + 5·W_iw(n).

* **Solver calls:** at most 5 calls of `Solver.iso`, each made through `iso_window`:
  * ≤ 4 on the w points of `Ω(Φ)`, with group `K^{Ω(Φ)}`, where `K = ker(G1 → Sym(Φ))`;
  * 1 on the `n−w` points of `Ω∖Ω(Φ)`, with group `Aut_top^{rest}`.

### main.Solver.case_2b_structure — W_2b

* **Profile:** outside 211; loops 916 (7,9), 919 While (98,1), 933 (10,8), 934 outer (12,12), 934 inner (8,9), 942 For (9,0), 943 For (13,0), 952 outer (7,11), 952 inner (7,11). Lambdas 945 (12) and 955 (19).
* **Parameters:**
  * `φ = len(Phi) ≤ m`;
  * `r_F = len(Fimg.gens)`;
  * `p_j = len(pts)` in iteration j;
  * p is the final `len(pts)`, with `p ≤ φ`;
  * `r_H` and `r_v` are the generator counts of H and Hv, `≤ r̂ := ρ(φ)` (G4);
  * `o₂ = len(orbs) ≤ p(p−1)`;
  * `c = len(comps) ≤ p`.
* **Loop iteration bounds:**
  * While 919: `np_ = len(pts)` starts at φ. Every iteration that does not break removes v from `pts` (lines 933, 935), and the loop breaks when `np_ ≤ 2`. So there are at most `max(1, φ−1) ≤ φ` iterations.
  * 933: `p_j`. 934 outer: `r_v`. 934 inner: `p_j − 1`.
  * 942 and 943: `o₂` orbitals and `Σ|orb| = p(p−1)` ordered pairs; `orbitals` returns the orbits on the ordered pairs of distinct points.
  * 952: c outer and `Σ|cmp| = p` inner iterations; `components` returns a partition of `range(p)`, cc.py:94–114.
* **Fixed part:**
  * stats 128; `list(a["Phi"])` `18+φ`; the base sets `23m+6`; the lookup 17;
  * line 916: `7(r_F+1) + 9`; `list(Phi)`: `φ+1`; the while loop's own `98(φ+1) + 1`.
* **Per iteration j:**
  * three `len` (3); `factorial(np_)` `p_j+1`;
  * if it continues:
    * `sorted(pts)`: `p_j⌈log₂p_j⌉ + 2p_j + 1`;
    * `pts.index(v)`: `2p_j+1`;
    * line 933: `10(p_j+1) + 8`;
    * line 934: `12(r_v+1) + 12`, plus per generator `8p_j + 9` and the `p_j − 1` calls `pts.index`, each `≤ 2p_j + 1`.
  * In total `≤ 49 + 15p_j + p_j⌈log₂p_j⌉ + 12r_v + r_v(2p_j² + 7p_j + 8)`.
* **After the loop:**
  * Lines 942–944: `9(o₂+1) + 13(p(p−1) + o₂) + (o₂+1) + 7p(p−1) ≤ 43p² + 10`; a key `(u,v)` costs 7 (K3).
  * `list(range(p))`: `2p+2`. The lambda@945 is called p² times (`ClassicalCC.__init__`, cc.py:27), each `12+7`.
  * Line 952 (disc branch): `7(c+1) + 11 + 7(p+c) + 11c ≤ 32p + 18`.
  * The lambda@955 (other branch) is called p² times, each `19 + 2(2p+1) + 7` (two `pts.index` and a lookup).
  * The `fallback` at line 939 is unreachable (A1).
* **Callees (Σ_2b):**
  * `2C[structure.Chooser.check](3) + φ·C[structure.Chooser.check](6)`;
  * `C[structure.Structure.__init__](m,2)`, `r_F·C[certificates.restrict_to](m,φ)`, `C[group.PermGroup.__init__](φ, r_F)`;
  * per iteration j: `C[johnson.orbitals](p_j, r_H)`, `C[group.PermGroup.order](p_j, r_H)`, `C[structure.Chooser.choose](p_j)`, `C[structure.Structure.individualize](m)`, `C[group.PermGroup.point_stabilizer](p_j, r_H)`, `r_v·C[certificates.restrict_to](p_j, p_j−1)`, `C[group.PermGroup.__init__](p_j−1, r_v)`;
  * `2C[cc.ClassicalCC.__init__](p)`, `C[cc.ClassicalCC.canonical_keys](p)`, `C[cc.ClassicalCC.disconnected_off_diagonal_colors](p)`;
  * `C[soj.select_min](≤ p²)`, `C[cc.ClassicalCC.components](p)`, `C[soj.split_by_blocks](m, p)`;
  * `C[cc.ClassicalCC.set_keys]()`, `C[soj.upcc_split_or_johnson](p, m)`.
* **Bound** (`Σ_j ≤ φ` iterations, `p, p_j ≤ φ`):

      W_2b ≤ 526 + 23m + 183φ + 105φ² + 4φ³ + φ²⌈log₂φ⌉ + 7r_F + φ·r̂·(2φ² + 7φ + 20) + Σ_2b
           ≤ 526 + 206m + 105m² + 4m³ + m²⌈log₂m⌉ + 7r_F + m·ρ(m)·(2m² + 7m + 20) + Σ_2b.

* **Solver calls:** none.

### main.Solver.case_3 — W_c3, and `proc@1018` — P_3

* **Profile:** outside 125; loops 978 For (28,0), 980 For (60,0), 984 For (42,7), 1002 For (32,0), 1005 For (49,0), 1012 For (25,0). Genexprs 979 (22), 1004 (22), 1013 (20). `proc@1018`: outside 137; loops 1023 For (12,0), 1026 DictComp (6,11), 1027 ListComp (6,9). `<genexpr@1028>` total 21.
* **Parameters:**
  * `σ = len(strings) ≤ 2`;
  * `M' = C(|Γ∖S|, k) ≤ M` test sets per string;
  * `K_cl = len(classes) ≤ 2M`;
  * the size of an invariant `v_c ≤ 2n+7`. The invariant consists of 3 scalars and two tuples of one entry per iteration of `certificate`'s while loop; each iteration strictly enlarges W ⊆ Ω (certificates.py:307–314), so there are at most n iterations.
  * `D3 = len(keys) ≤ m^k`.
* **Cache hits of `lc.certificate`.** `lc = ax["lc"]` (or `ay["lc"]`) is the `LocalCertificates` object of an `aggregate` miss. That loop visited every k-subset A of `range(m)` and stored it in `lc.certs`, either in `conjugate` (certificates.py:267) or in `certificate` (line 337). Nothing deletes from `lc.certs`.
  * So every `lc.certificate(A)` and `lc0.certificate(A0)` in `case_3` is a hit; `A, A0 ⊆ Γ∖S` are k-subsets.
  * The hit path executes 14 instructions (lines 291–293), plus `frozenset(A)` `4k+1` and two lookups `2(2k+3)`: `C_hit ≤ 8k+18`.
* **Bound on the number of `compare` calls:**
  * For each pair (string, A), loop 984 runs over the bucket of `cert.invariant`, a list of class indices created earlier, and stops at the first success. So it makes at most `|bucket| ≤ K_cl ≤ 2M` calls.
  * Over the `≤ σM' ≤ 2M` pairs: `Γ := #compare ≤ 2M·K_cl ≤ 4M²`.
* **First loop (978/980/984):**
  * Per string: the genexpr `22(m+1)`, the range `m+1`, the memberships `3m`, `sorted` `m⌈log₂m⌉ + 2m + 1`, `combinations` `kM'+1`.
  * Per test set:
    * the cycle of 980 (60), `frozenset` `4k+1`, `C_hit`;
    * `buckets.get` `1+2v_c`; the entry of 984 `42+7`;
    * if not found: `4 + 2v_c + C[perm.identity](n)`;
    * `class_of[...] =` `2k+7`.
  * Per compare iteration: `42 + 2 + C_hit + 128 = 190 + 8k`, plus `C[certificates.LocalCertificates.compare](n,m,k)`.
* **Second loop (1002/1005/1012):**
  * Per test set:
    * the cycle of 1005 (49), `frozenset`, the lookup `2k+7`, `C_hit`;
    * `C[action.GroupWithAction.phi](n,m,r)` and `C[perm.inv](m)`;
    * `sorted(A)`: `k⌈log₂k⌉ + 2k + 1`; `permutations`: `k·k!+1`;
    * loop 1012 with k! iterations, `25(k!+1)`. Per ordering: the genexpr `20(k+1)`, `tuple` `k+1`, the store `2k+3`, and `C[certificates.LocalCertificates.ordered_label](k)`.
  * In total `≤ 55 + 16k + k⌈log₂k⌉ + k!(24k+49) + k!·C[ordered_label](k) + C[phi] + C[perm.inv](m)` per test set.
* **Bound on W_c3:**

      W_c3 ≤ 896 + λn + 112m + 4m⌈log₂m⌉ + M·(544 + 64k + 16n + 2k⌈log₂k⌉ + 2k!(24k+49))
             + Γ·(190 + 8k) + Γ·C[certificates.LocalCertificates.compare](n,m,k)
             + 2M·(C[perm.identity](n) + C[action.GroupWithAction.phi](n,m,r) + C[perm.inv](m)
                   + k!·C[certificates.LocalCertificates.ordered_label](k)),            Γ ≤ 4M².

  Plus `branch`, charged in Section 3.
* **P_3 (`proc@1018`).**
  * Instructions 137; `s == x` `λn+1`; the small lookups 7.
  * `product`: `k·m^k + 1`, and `range(m)` `m+1`.
  * Loop 1023: `12(m^k+1)`, and per tuple `col.get` `2k+3` and `append`.
  * `set(raw)`: elements of size ≤ k+4, `(2k+10)m^k + 1`.
  * `sorted(·, key=canon)`: `D3·C[canon.canon](k+4) + 3(k+4)D3⌈log₂D3⌉ + 2D3 + 1`.
  * Line 1026: `6(D3+1) + 11 + (D3+1) + D3(2k+9)`. Line 1027: `6(m^k+1) + 9 + m^k(2k+9)`.
  * Line 1028: the genexpr `21(D3+1)`, D3 calls `raw.count` each `(k+5)m^k + 1`, and `tuple`.
  * `base`: `≤ 19m+5`. `vertices`: `≤ 13m + 4 + m⌈log₂m⌉`.
  * The bound:

        P_3 ≤ 226 + λn + 33m + m⌈log₂m⌉ + (7k+41)·m^k + (2k+41)·D3 + 3(k+4)·D3⌈log₂D3⌉ + (k+5)·D3·m^k
              + D3·C[canon.canon](k+4) + C[wl.KStructure.__init__](m,k) + C[structure.Chooser.check](D3+3)
              + C[wl.refine_structures](m,k) + C[structure.Structure.__init__](m,2) + C[design.extended_design_lemma](m,k)
            ≤ 226 + λn + 33m + m⌈log₂m⌉ + (9k+82)m^k + 3k(k+4)·m^k⌈log₂m⌉ + (k+5)·m^{2k} + (same callees),

    using `D3 ≤ m^k`.
* **Solver calls:** those of the Γ ≤ 4M² `compare` calls. These are the `iso_window` calls of the solver-call item of `C[certificates.LocalCertificates.compare]`; their strings have letters `(ℓ, 0/1)`, so `λ' = λ+2`. Plus those of `branch`.

### main._chain_search — C_cs, and its generator `rec`

* **Profile:** `_chain_search`: outside 67; loops 1048 (21,0), 1050 (9,0), 1051 SetComp (11,8), 1054 (11,2), 1057 ListComp (13,9), 1074 YieldFrom (13,9). `rec`: outside 28; loops 1064 For (26,0), 1067 For (12,4), 1072 YieldFrom (12,9). `<genexpr@1065>` total 22.
* **Parameters:**
  * `k_G = len(levels)`; `u_i = len(levels[i].trans)`; `σ_i = len(levels[i].gens)`; `S_G = Σσ_i`;
  * `c_i = len(new_fixed[i]) ≤ n`;
  * `U_i = ∏_{j<i} u_j`;
  * Y is the number of values passed out, `Y ≤ g`.
  * Under (A3)/(A4) and G1–G3: `u_i ≥ 2`, `∏u_i = g`, `k_G ≤ log₂g`, and `S_G ≤ g + k_G²`. For `g ≤ 5040` this gives `k_G ≤ 12`.
* **Loop iteration bounds:**
  * 1048 and 1057: `k_G`. 1050: `σ_i`. 1051: `|f| ≤ n`. 1054: `|fixed[0]| ≤ n`. 1064: `u_i`. 1067: `c_i`.
  * The YieldFrom loops: the values passed through.
* **The recursion of `rec`.**
  * `rec(i, ·)` creates at most `u_i` children `rec(i+1, ·)`, and `rec(k_G, ·)` yields once. So there are at most `U_i` invocations at depth i, and at most `U_{k_G} = g` leaves.
  * Each value at depth `k_G` passes through one yield-from per depth `0..k_G−1` and through `_chain_search`'s own.
  * With `u_i ≥ 2`: `Σ_{i<k_G} U_i < g` and `Σ_{i=1}^{k_G} U_i < 2g`.
* **`_chain_search` itself:**
  * Instructions 67.
  * Loop 1048: `22(k_G+1)` including the range, and per i `set(range(n))` `5n+2`.
  * Loop 1050: `9(σ_i+1)` per i.
  * Line 1051: `11(|f|+1) + 8 + 2|f|`, i.e. `≤ 13n+19` per entry, with `S_G` entries.
  * Line 1052: `5n+3`.
  * Loop 1054: `11(n+1) + 2 + λn`.
  * Line 1057: `14(k_G+1) + 9`, and per i a set difference (`6n+1`) and `sorted` (`n⌈log₂n⌉ + 2n + 1`).
  * The YieldFrom at 1074: `13(Y+1) + 9`.
  * Plus `len` 1, `C[group.PermGroup.levels](n,r)` and `C[perm.identity](n)`.
* **One invocation `rec(i, ·)`, `i < k_G`:**
  * Instructions 28; the values view `u_i+1`; loop 1064 `26(u_i+1)`.
  * Per iteration:
    * the genexpr, range and `tuple`: `24n+24`;
    * loop 1067: `12(c_i+1) + 4 + λc_i`;
    * the YieldFrom 1072: `12(Y_child+1) + 9`.
  * So `rec(i) ≤ 55 + u_i(88 + 24n + (12+λ)c_i) + 12·Y_i`.
* **`rec(k_G, ·)`:** 28.
* **Total, with `c_i ≤ n`:**

      C_cs ≤ 151 + 50k_G + 13k_G n + k_G n⌈log₂n⌉ + (16+λ)n + S_G(13n+28)
             + g·(272 + 12k_G + (72+2λ)n) + C[group.PermGroup.levels](n,r) + C[perm.identity](n)
           ≤ 4783 + (2044+λ)n + 12n⌈log₂n⌉ + 444g + (85+2λ)·g·n + C[group.PermGroup.levels](n,r) + C[perm.identity](n)

  The closed form uses `k_G ≤ 12` and `S_G ≤ g+144`. For a user group with a forced prefix (`u_i ≥ 1`, reachable only through `string_isomorphism`), replace `g·(272 + 12k_G + …)` by `g·(41 + 155k_G + k_G(36+λ)n)` and use `k_G ≤ n` and `S_G ≤ k_G(g−1)`. Here `Σ(u_i−1) ≤ ∏u_i − 1` holds for `u_i ≥ 1`.
* **Solver calls:** none.

### main.string_isomorphism

* **Profile:** outside 23.
* **Costs:**
  * `Solver(params)`: `105 + C[soj.SOJParams.__init__]()` if both arguments are None, else ≤ 19;
  * `tuple(x)`, `tuple(y)`: `2(n+1)`;
  * `C[canon.normalize_letters](n, λ_in)`.
* **Bound:** `130 + 2n + C[soj.SOJParams.__init__]() + C[canon.normalize_letters](n, λ_in)`.
* **Solver calls:** one root call `iso(G, x', y')` with int letters (`λ = 1`).

### graph._normalize_edges — C_ne(L)

* **Profile:** outside 10; loop 25 (59,0).
* **Parameters:** L is the number of items of `edges`. A list or a set of size L.
* **Loop iteration bound:** L iterations.
* **Built-ins per edge:** two `int` (2); `min`, `max` (4); `out.add` of a 2-tuple (K3, 7). In total 13.
* **Bound:** `C_ne(L) ≤ 10 + 59(L+1) + 13L = 69 + 72L`. The set returned has `|E| ≤ min(L, N)` elements.

### graph.GraphInstance.__init__ — C_gi(v)

* **Profile:** outside 156; loops 39 DictComp (6,12), 54 ListComp (7,9).
* **Parameters:** v vertices, `N = C(v,2)`.
* **Loop iteration bounds:** both comprehensions run over `self.pairs`, which has N elements.
* **Built-ins:**
  * line 39: `enumerate` `N+1` and N insertions of 2-tuple keys `7N`;
  * two `list(range(v))`: `4v+4`;
  * `factorial(v)`: `v+1`;
  * two imports and a `len`: 3;
  * line 54: N `frozenset` of 2 elements, `9N`;
  * the color lists: `2(v+1)`.
* **Callees:** `C[johnson.subsets_of](v,2)`, `2C[johnson.induced_on_subsets](v, N)`, `2C[perm.from_cycles](v,2)`, `2C[perm.from_cycles](v,v)`, `C[group.PermGroup.__init__](N, 2)` (with `known_order = v!`), `C[johnson.JohnsonStructure.__init__](v, 2, N)`.
* **Bound:** `C_gi(v) ≤ 201 + 30N + 7v + (callees)`.

### graph.GraphInstance.shared

* **Profile:** outside 20.
* **Built-ins:** two dict operations with an int key: 6.
* **Bound:** `≤ 26 + C_gi(v)` on the first call for v; 26 later. The `_shared` cache hits after the first call.

### graph.GraphInstance.string — C_str(L)

* **Profile:** outside 17; loop 73 (38,0).
* **Loop iteration bound:** N iterations, over `self.pairs`.
* **Built-ins per pair:**
  * `(u,v) in E`: 7;
  * without colors: `append` 1;
  * with colors (γ is the maximal size of a color): `sorted` of 2 elements with `key=canon` (`3γ+5` plus 2 canon calls), `tuple` 3, `append` 1.
* **Other costs:** `_normalize_edges(edges, n)`, `C_ne(L)`; `tuple(out)`, `N+1`.
* **Bound:**
  * without colors: `C_str(L) ≤ 125 + 72L + 47N`;
  * with colors: `C_str(L) ≤ 125 + 72L + (55+3γ)N + 2N·C[canon.canon](γ)`.

### graph.GraphInstance.vertex_perm — C_vp(v)

* **Profile:** outside 19; loops 85 For (68,0), 86 ListComp (9,10).
* **Loop iteration bounds:** 85 has v iterations; 86 has v iterations per entry.
* **Built-ins per vertex:**
  * the range `v+1`; the slice 3;
  * twice: `sorted` of 2 elements (7), `tuple` (3), and the index lookup with a 2-tuple key (7);
  * two `set` of 2 elements (18); `&` (13); `len`; `pop`.
* **Bound:** `C_vp(v) ≤ 19 + (v+1) + 68(v+1) + v(10v+90) = 88 + 159v + 10v²`.

### graph.graph_isomorphism — W_gr

* **Profile:** outside 132; loops 115 DictComp (5,9), 124 DictComp (7,9).
* **Parameters:** `L = max(len(edges1), len(edges2))`; v vertices; `N = C(v,2)`.
* **Costs:**
  * `2C_ne(L)` and two `len`.
  * For `v ≤ 2`: the colour comparisons and the dict of ≤ 2 entries, `≤ 44 + 7γ`.
  * For `v ≥ 3`:
    * `shared`: `26 + C_gi(v)`;
    * `2C_str(L)`: `string` normalises the edge set again;
    * `C[canon.normalize_letters](N, 3+2γ)`; the letters are 0/1, or `(bit, (c,c'))` of size `≤ 3+2γ`;
    * `Solver(params)`: `105 + C[soj.SOJParams.__init__]()`;
    * `C_vp(v)`;
    * line 124: `11v + 17`.
* **Bound:**

      W_gr ≤ 758 + 288L + (110+6γ)N + 170v + 10v² + 4N·C[canon.canon](γ) + C_gi(v)
             + C[canon.normalize_letters](N, 3+2γ) + C[soj.SOJParams.__init__]()
           ≤ 959 + 288L + (140+6γ)N + 177v + 10v² + 4N·C[canon.canon](γ)
             + C[canon.normalize_letters](N, 3+2γ) + C[soj.SOJParams.__init__]() + (C_gi callees).

  Without colors, drop γ and the canon terms.
* **Solver calls:** one root call `solver.iso(inst.G, x, y)`.
  * `G = S^{(2)}(V)` acts on `N = C(v,2)` points, with 2 generators and `known_order = v!`.
  * For `v ≥ 5` G carries a `johnson_hint` (m = v, t = 2), which the dispatch uses when `v ≥ ℓ(N)`, i.e. on the `D_hint` path.
  * The letters are ints, so `λ = 1`.

### graph.graph_automorphisms — W_ga

* **Profile:** outside 96; loop 141 ListComp (7,8).
* **Parameters:** `r_A = len(C.group.gens) ≤ ρ(N)` (G4).
* **Costs:**
  * For `v ≤ 2`: `≤ 100 + γ`.
  * Otherwise:
    * `shared`: `26 + C_gi(v)`; `C_ne(L)`; `C_str(L)`;
    * `C[canon.normalize_letters](N, 3+2γ)`; `Solver`: 105;
    * line 141: `7(r_A+1) + 8 + r_A·C_vp(v)`;
    * `C[group.PermGroup.order](N, r_A)`.
* **Bound:**

      W_ga ≤ 436 + 144L + (55+3γ)N + r_A(95 + 159v + 10v²) + C_gi(v) + 2N·C[canon.canon](γ)
             + C[canon.normalize_letters](N, 3+2γ) + C[soj.SOJParams.__init__]() + C[group.PermGroup.order](N, r_A).

* **Solver calls:** one root call `solver.iso(inst.G, x, x)`.

### graph.graph_automorphism_group_order

* **Profile:** outside 8.
* **Bound:** `8 + W_ga`.

### graph.parse_edge_list

Used only by the command line (`__main__.py`); no bound needed.

### The GI → SI reduction, summarised

* For a graph pair on v vertices with at most L edge items each, the own work of `graph_isomorphism`, excluding the root `Solver.iso` call, is at most

      959 + 288L + 140N + 177v + 10v² + C[canon.normalize_letters](N, 1) + C[soj.SOJParams.__init__]()
          + C[johnson.subsets_of](v,2) + 2C[johnson.induced_on_subsets](v,N) + 2C[perm.from_cycles](v,2)
          + 2C[perm.from_cycles](v,v) + C[group.PermGroup.__init__](N,2) + C[johnson.JohnsonStructure.__init__](v,2,N),

  where `N = C(v,2)`.
* The `GraphInstance` part (`C_gi`) is paid once per v per process. `graph_automorphisms` is analogous: `436 + 144L + 55N + r_A(95 + 159v + 10v²) + …`.
* `string` costs `125 + 72L + 47N`.
* In all of this `L ≤` the input length and `|E| ≤ min(L, N)`.

---------------------------------------------------------------------------

## 3. Own work W(node) of every node type

* A **node** is one execution of `Solver._solve(G, x, y, tower)`, with `n = G.n` and `r = len(G.gens) ≤ ρ(n)`.
* `W(node) = D + H`.
  * D is the dispatch part of the `_solve` lemma.
  * H is the own work of the handler it calls, with everything the handler executes outside nested `Solver.iso` calls. This includes the runs of `proc`, `aggregate`, and the own work `W_iw` of every `Solver.iso_window` call made by `top_action` or by `certificates.py`.
* The wrapper of a `Solver.iso` call (`W_iso`, Section 2) is not part of any node.
* All `C[...]` are as in Section 2.

### 3.1 The wrapper and `iso_window`

* `W_iso ≤ 508 + 22r + 36λn + r·C[perm.is_string_automorphism](n,λ) + C[tower.Tower.trivial](n) + C[perm.identity](n) + C[action.Coset.__init__](n)`.
  * If `x ≠ y`: one node `_solve(G,x,y)` (via `_one_iso`, own work 14) and one nested `iso(G,x,x)`.
  * If `x == y` and the cache misses: one node `_solve(G,x,x)`.
* `W_iw(N,L) ≤ 80 + L⌈log₂L⌉ + (2+λ)L + C[action.window_lifter](N,L,r_H) + 2C[action.WindowLifter.restrict_string](L) + C[group.PermGroup.is_trivial]() + C[perm.identity](N) + C[action.Coset.__init__](N) + C[tower.Tower.trivial](N) + C[tower.Tower.restrict](N,L,ℓ) + C[action.WindowLifter.lift_coset](N,L,r_C)`.
  * It makes at most 1 nested `iso` call, on the restriction of H to the window (L points).

### 3.2 Node types

**N1 — Brute force** (`|G| = g ≤ 5040`)

    W ≤ 706 + 5λn + g + 2C_cs + C[group.PermGroup.order](n,r) + C[group.PermGroup.__init__](n,g)
        + C[perm.identity](n) + 2C[action.Coset.__init__](n)
      ≤ 10272 + 889g + (4088+7λ)n + (170+4λ)gn + 24n⌈log₂n⌉ + C[group.PermGroup.order](n,r)
        + 2C[group.PermGroup.levels](n,r) + 3C[perm.identity](n) + C[group.PermGroup.__init__](n,g)
        + 2C[action.Coset.__init__](n).

* `_chain_search` enumerates at most `g = ∏u_i` elements.
* Nested `iso` calls: **none**.

**N2 — Chain rule** (G intransitive, ω orbits, `2 ≤ ω ≤ n`)

    W ≤ 803 + 132ω + 2ω⌈log₂ω⌉ + (1+5λ)n + C[group.PermGroup.order](n,r) + C[group.PermGroup.orbits](n,r)
        + (ω+1)C[perm.identity](n) + C[action.Coset.__init__](n)
        + Σ_{i=1}^{ω} [ C[action.window_lifter](n,n_i,r_i) + 2C[action.WindowLifter.restrict_string](n_i)
          + C[group.PermGroup.is_trivial]() + C[tower.Tower.restrict](n,n_i,ℓ) + C[action.WindowLifter.lift](n,n_i)
          + C[action.WindowLifter.lift_group](n,n_i,r'_i) + C[perm.inv](n) + C[perm.act_string](n) + C[perm.mul](n) ]
      ≤ 803 + (133+5λ)n + 2n⌈log₂n⌉ + (same callees).

* The stage cache only removes the `window_lifter` / `lift_group` terms on a repeated `(G, x)`.
* Nested calls: **at most ω**. Call i is on the orbit Δ_i, with `n_i ≤ n−1` points and `Σ n_i = n`. Its group is the restriction to Δ_i of the stage group `Aut_G^{Δ_1∪…∪Δ_{i−1}}(x)`.

**N3 — Giant** (transitive, `n ≥ 3`, `|G| ≥ n!/2`; `trivial_case` with `is_sym` given)

    W ≤ 1203 + 4λ + 4r + (191+26λ)n + 3C[group.PermGroup.order](n,r) + C[group.PermGroup.orbits](n,r)
        + C[tower.Tower.is_trivial]() + C[action.GroupWithAction.__init__](n,n,r) + Σ_l C[perm.sym_gens](n_l,n)
        + C[group.PermGroup.__init__](n,4n) + C[group.even_subgroup_gens](n,2n) + C[perm.parity](n)
        + C[perm.from_cycles](n,2) + C[perm.mul](n) + C[action.Coset.__init__](n).

* Nested calls: **none**.

**N4 — Strong Luks**

Entered in three ways: `|Gbar| < m^{1+⌊log₂m⌋}`; an unrecognised quotient; or a Johnson quotient on `m_Γ < ℓ(n)` points. Here `m = m_b` blocks, `q = |Gbar|`, and I is the number of coset representatives used.

    W ≤ D_e0 + 503 + (41+n)·I + (2+λn)·S + C[johnson.recognize_johnson](m,r) + C[johnson.recognize_cameron](m,r)
        + C[errors.fallback]() + C[action.GroupWithAction.__init__](n,m,r) + C[action.GroupWithAction.kernel](n,m,r)
        + C[action.GroupWithAction.comb_gamma](n,m,r) + C[action.GroupWithAction._gamma_levels](n,m,r)
        + C[group.PermGroup.coset_reps_prefix](n+m,·;I) + I·(C[perm.inv](n) + C[perm.act_string](n))
        + S·C[perm.mul](n) + C[group.generated_subcoset](n,S,·) + C[action.Coset.__init__](n),

with `I ≤ q`, `S ≤ I` (`S ≤ 1` if `x ≠ y`), and

    D_e0 ≤ 631 + 101n + 3n⌈log₂n⌉ + 3C[group.PermGroup.order](n,r) + C[group.PermGroup.orbits](n,r) + C[tower.Tower.is_trivial]()
           + C[tower.Tower.top_blocks](n,ℓ) + 2C[group.PermGroup.minimal_block_system](n,r)
           + C[group.PermGroup.induced_action](n,r;≤n) + C[tower.Tower.extend](n,ℓ)
           + C[group.PermGroup.induced_action](n,r;m) + C[group.PermGroup.order](m,r) + 33.

* `q` is bounded as follows:
  * `q < m^{1+⌊log₂m⌋}` on the first entry;
  * `q < m^{2+⌊log₂m⌋}`, or `m < 25` and `q ≤ 24!`, on the second;
  * `q ≤ (ℓ(n)−1)!` on the third.
* Nested calls: **`I ≤ q` calls** `iso(N, x, y^{σ^{-1}})`. N is the kernel of the action on the blocks (degree n); the calls stop at the first success if `x ≠ y`.

**N5 — Cameron reduction** (`s_c ≥ 2` coordinates, `s_c ≤ log₂m`)

    W ≤ D_e0 + 580 + (53+m)·I + (2+λn)·S + C[johnson.recognize_johnson](m,r) + C[johnson.recognize_cameron](m,r)
        + C[action.GroupWithAction.__init__](n,m,r) + C[group.PermGroup.__init__](m,ν) + C[group.PermGroup.order](m,ν)
        + C[action.GroupWithAction.preimage](n,m,r,ν) + C[action.GroupWithAction.__init__](m,s_c,r)
        + C[action.GroupWithAction.comb_gamma](m,s_c,r) + C[action.GroupWithAction._gamma_levels](m,s_c,r)
        + C[group.PermGroup.coset_reps_prefix](m+s_c,·;I) + I·(C[action.GroupWithAction.lift](n,m,r)
        + C[perm.inv](n) + C[perm.act_string](n)) + S·C[perm.mul](n) + C[group.generated_subcoset](n,S,·)
        + C[action.Coset.__init__](n),

with `I ≤ s_c! ≤ (log₂m)!`.

* Nested calls: **`I ≤ s_c!` calls** `iso(NG, x, y^{σ^{-1}})`, where `NG = φ^{-1}(Nbar)` has degree n.

**N6 — Johnson case**

Here `|Γ| = m ≥ 10·k_paper(n)`, `k = k_paper(n) ≤ m/10`, `b = C(m,t)` blocks and `M = C(m,k)`.

* **Entry cost:**

      J0 = max(D_hint, D_J) + 30 + C[certificates.JohnsonData.is_primitive](),

  with

      D_hint ≤ 936 + 7n + 3C[group.PermGroup.order](n,r) + C[group.PermGroup.orbits](n,r) + C[tower.Tower.is_trivial]()
               + C[action.GroupWithAction.__init__](n,m,r) + C[certificates.JohnsonData.__init__](n,m,t;n),
      D_J    ≤ D_e0 + 384 + 8r + 9n + r·C[johnson.johnson_phi](b,m,t) + C[johnson.recognize_johnson](b,r)
               + C[action.GroupWithAction.__init__](n,m,r) + C[certificates.JohnsonData.__init__](n,m,t;b).

  (`8m_b ≤ 8n` because `m_b = b ≤ n`.)
* **The branch template.** Write `W_br[P, f_a, W_rec]` for the bound of `branch` (Section 2) with `P_x, P_y ≤ P`:

      W_br[P,f_a,W_rec] ≤ 468 + λn + 22d + 11f_a + (s+1)·P
            + s·(431 + d + 2κ + ρ(n) + C[structure.align](m) + C[action.GroupWithAction.lift](n,m,r) + C[perm.inv](n)
                 + C[perm.act_string](n) + W_rec)
            + s·(54 + 14h* + h*·(C[perm.is_identity](n) + C[action.GroupWithAction.phi](n,m,r)))
            + s²·(960041 + 2κ + 20000·h*·(53 + 22d + 4κ + A_key)) + s³·(1+2κ)(20000 + h*)
            + C[structure.RecordingChooser.__init__]() + C[structure.Structure.aut_gens](m)
            + C[action.GroupWithAction.intersect_image](m,a_x) + C[group.PermGroup.__init__](m,2a_x)
            + C[group.PermGroup.order](m,2a_x) + C[action.GroupWithAction.preimage](n,m,r,2a_x)
            + C[action.GroupWithAction.image_is_sym](m,r) + f_a·C[perm.is_identity](n) + C[group.PermGroup.__init__](n,f_a)
            + C[perm.identity](n) + C[structure.enumerate_runs](ℓ_tr,d;≤s runs) + s·C[perm.mul](n)
            + C[group.generated_subcoset](n,s+1,h*) + 2C[action.Coset.__init__](n),

  * `h* ≤ f_a + s(ρ(n)+1)`. The `_covered` terms (the `s²` and `s³` lines) are present only for `x == y` with pruning.
  * The number of `proc` executions is at most `1 + s` (Lemma R).
  * `C[action.GroupWithAction.preimage]` computes G1, `C[structure.align]` the alignment, and `C[action.GroupWithAction.lift]` the lift of the aligning permutation.

| Sub-case | W(node) | Nested `iso` calls |
|---|---|---|
| **N6a** primitive, `t = 1` (`trivial_case`) | `J0 + W_tc` | none. Unreachable: G would be a giant, which is caught by N3. |
| **N6b** primitive, `t ≥ 2` (`primitive_johnson`) | `J0 + 381 + 36m + W_tw + W_br[max(P_pull, P_edl), 0, 0]` | `≤ s` calls `iso(G1, x, y^{σ^{-1}})`, degree n, `G1 = φ^{-1}(Aut(Sx) ∩ G^φ)`; one if `x ≠ y` after the first success |
| **N6c** imprimitive (`imprimitive_johnson`) | `J0 + 653 + λn + m + A_x + A_y + Q_A·W_iw(n) + H_case` | the `Q_A` certificate calls, plus those of `H_case` |

The quantities in the table:

* `W_tw ≤ 72 + 85m + 78m² + 38m³ + ½m²·b(74+35t+λ)`.
* `P_pull ≤ 59 + 59m + W_tw + C[structure.Chooser.check](3) + C[structure.Structure.__init__](m,2)`.
* `P_edl ≤ 31 + 5m + W_hs + C[structure.Structure.__init__](m,1) + C[design.extended_design_lemma](m,t)`, with

      W_hs ≤ 243 + m + (47+4λ)n + (n+1)⌈log₂(n+1)⌉ + 3λn⌈log₂n⌉ + (11t+53+2λ+2n)·m^t + n·C[canon.canon](λ)
             + C[wl.KStructure.__init__](m,t) + C[structure.Chooser.check](n+3) + C[wl.refine_structures](m,t).

* `A_x` / `A_y`: the `aggregate` bound on a miss, or `4λn+47` on a hit; `A_y = 0` if `y == x`.

      A ≤ 705 + 4λn + 86m + 2m⌈log₂m⌉ + (55+2n+22m)·F + M(157+9k) + M²(65 + F(85+34k+C[perm.mul](n)))
          + M·(C[certificates.LocalCertificates.certificate](n,m,k) + C[certificates.LocalCertificates.conjugate](n,m,k)
               + C[perm.inv](n) + C[perm.identity](n))
          + F·(C[perm.is_identity](n) + 2C[action.GroupWithAction.phi](n,m,r))
          + C[certificates.LocalCertificates.__init__](n) + C[group.PermGroup.__init__](m,F) + C[group.PermGroup.orbits](m,F)
          + F·C[certificates.restrict_to](m,m) + C[certificates.is_giant_on](m,F),

  with `F ≤ M·ρ(n)`. Each of the at most M certificates is charged in full, ignoring orbit pruning.
* `Q_A` is the number of `iso_window` calls of the at most 2M certificate computations: the sum of the solver-call items of `C[certificates.LocalCertificates.certificate]`. Each call has own work `≤ W_iw(n)`.
* The case handlers, with `f_a = len(ax["F_gens"]) ≤ F`:
  * **case 1:** `H_1 = W_br[P_1, f_a, 0]`, with `P_1 ≤ 163 + 4λn + 54m + 3m² + C[structure.Chooser.check](m+5) + C[structure.Structure.__init__](m,m+1)`.
    * Nested: `≤ s` calls `iso(G1,·)` of degree n.
  * **case 2a:** `H_2a = 227 + W_br[P_2a, f_a, 11 + W_ta]`.
    * `P_2a ≤ 115 + 4λn + 23m + C[structure.Chooser.check](3) + C[structure.Structure.__init__](m,2)`.
    * `W_ta ≤ 636 + 8m + 18ρ(n) + 32f_a + n⌈log₂n⌉ + (19+λ)n + 4n² + Σ_ta + 5W_iw(n)`.
    * Nested: per aligned run (at most s), `top_action` makes at most 5 `iso` calls through `iso_window`: at most 4 on `Ω(Φ)` (w points, group `K^{Ω(Φ)}` with `K = ker(G1 → Sym(Φ))`), and 1 on `Ω∖Ω(Φ)` (`n−w` points, group `Aut_top^{rest}`). So **≤ 5s calls**.
  * **case 2b:** `H_2b = W_br[P_2b, f_a, 0]`.
    * `P_2b ≤ 62 + 4λn + W_2b`, with `W_2b ≤ 526 + 206m + 105m² + 4m³ + m²⌈log₂m⌉ + 7F + m·ρ(m)(2m²+7m+20) + Σ_2b`.
    * Nested: `≤ s` calls `iso(G1,·)`.
  * **case 3:** `H_3 = W_c3 + Q_cmp·W_iw(n)|_{λ+2} + W_br[P_3, f_a, 0]`.
    * `W_c3 ≤ 896 + λn + 112m + 4m⌈log₂m⌉ + M(544+64k+16n+2k⌈log₂k⌉+2k!(24k+49)) + Γ(190+8k) + Γ·C[certificates.LocalCertificates.compare](n,m,k) + 2M(C[perm.identity](n) + C[action.GroupWithAction.phi](n,m,r) + C[perm.inv](m) + k!·C[certificates.LocalCertificates.ordered_label](k))`, with `Γ ≤ 4M²`.
    * `P_3 ≤ 226 + λn + 33m + m⌈log₂m⌉ + (9k+82)m^k + 3k(k+4)m^k⌈log₂m⌉ + (k+5)m^{2k} + m^k·C[canon.canon](k+4) + C[wl.KStructure.__init__](m,k) + C[structure.Chooser.check](m^k+3) + C[wl.refine_structures](m,k) + C[structure.Structure.__init__](m,2) + C[design.extended_design_lemma](m,k)`.
    * `Q_cmp` is the number of `iso_window` calls of the `Γ ≤ 4M²` compare calls (the solver-call item of `C[certificates.LocalCertificates.compare]`). The `ordered_label` calls number `2M·k!`: every ordering of every test set of x and y.
    * Nested: `Q_cmp` calls (windows `W_new ⊆ Ω` of a certificate trajectory, groups `it.N`, letters `λ+2`), plus `≤ s` calls `iso(G1,·)`.
* In every imprimitive case there are also the `Q_A` certificate calls of `aggregate`: windows `W_new ⊆ Ω`, groups `N^{W_new}` with N the kernel of `H(W_old) → Sym(A)`.

### 3.3 Closed forms of the dominant terms in n, m, t, k, s

These use `b ≤ n`, `F ≤ Mρ(n)`, `f_a ≤ F`, `h* ≤ F + s(ρ(n)+1)`, `M = C(m,k) ≤ m^k/k!` and `λ ≥ 1`. Every `C[...]` and `W_iw` term above is to be added.

* N6b, EDL branch (per proc run): `O(m^t(t+λ+n)) + C[wl.refine_structures](m,t) + C[design.extended_design_lemma](m,t)`. Explicitly, `P_edl ≤ 274 + 6m + (47+4λ)n + (n+1)⌈log₂(n+1)⌉ + 3λn⌈log₂n⌉ + (11t+53+2λ+2n)m^t + …`. The pullback branch: `P_pull ≤ 131 + 144m + 78m² + 38m³ + ½m²b(74+35t+λ) + …`.
* N6c, aggregate: `A ≤ M²·F·(85 + 34k + C[perm.mul](n)) + (65 + 157 + 9k)M² + (55+2n+22m)F + … ≤ M³ρ(n)(85+34k+C[perm.mul](n)) + …` — cubic in `C(m,k)`. This is the orbit-pruning BFS of lines 765–776, which explores up to M sets with up to F generators for each of the M test sets.
* N6c, case 3: `Γ ≤ 4M²` compare calls. The labelling term is `2M·k!·(24k+49+C[ordered_label](k))`. `proc` costs `(k+5)m^{2k} + (9k+82)m^k + 3k(k+4)m^k⌈log₂m⌉`; the `m^{2k}` comes from `raw.count`.
* The branch, all cases: `(s+1)P + s·(C[align] + C[lift] + C[inv] + C[act_string] + W_rec + 431 + d + 2κ + ρ(n)) + O(s³κ(20000 + F + sρ(n))) + O(s²·20000·(F + sρ(n))(d + κ + A_key))`. The `s³` term is the set union `covered |= orbit` charged per element of both operands (K4).

### 3.4 Values stated in the other modules' files (for substitution; not re-proved here)

* **`johnson_certs.md` §4.**
  * One `certificate` computation makes at most `(J+1)·k! ≤ (n+1)·k!` `iso_window` calls, and a cached one none. So `Q_A ≤ 2M·(n+1)·k!`.
  * One `compare` makes at most `ℓ·k! ≤ (n+1)·k!` calls. So `Q_cmp ≤ 4M²·(n+1)·k!`.
  * The windows are the `W_new ⊆ Ω` of the certificate trajectory, so each call has own work `≤ W_iw(n)`.
* **`group.md` Lemma G.** Every `PermGroup` of degree N keeps at most `γ_N = max(6, λ_N)` generators, with `λ_N ≤ ⌈3N/2⌉ − 1` (Cameron–Solomon–Turull). This is sharper than the `ρ(N) = max(6, ⌊N log₂N⌋)` of Section 1.1, and either may be used for r, `r̄`, `r_K`, `r_A`, `r̂` and in `F ≤ M·ρ(n)`.
* **`structure_cc_wl.md`.**
  * `enumerate_runs` executes `proc` at most `∏ k_d` times, which is the s of Lemma R.
  * Its own work is `≤ 12 + R(123 + 21d)`. This is the term `C[structure.enumerate_runs](ℓ_tr, d; R)`.

---------------------------------------------------------------------------

## 4. Final table

Callees outside main/graph are kept as symbols, and λ ≥ 1. `C_cs`, `W_iw`, `W_tw`, `W_hs`, `W_2b`, `W_ta`, `C_cov`, `C_gi`, `C_ne`, `C_str` and `C_vp` are the bounds of this file.

| function | closed-form bound (one call) |
|---|---|
| main.Params.__init__ | 71 + C[soj.SOJParams.__init__]() |
| main.Params.paper | 86 + 42o + C[soj.SOJParams.__init__]() (o overrides; o = 0 by default) |
| main.Params.small_scale | 610 + 84o + C[soj.SOJParams.small_scale](o) |
| main.Params.__repr__ | diagnostics, not bounded |
| main.Params.luks_threshold | 13 |
| main.Params.enumeration_cap | 15 |
| main.Params.small_quotient | 33 |
| main.Params.k_paper | 18 |
| main.Params.gamma_threshold | 32 |
| main.Params.k_for | 79 |
| main.Solver.__init__ | 105 + C[soj.SOJParams.__init__]() |
| main.Solver.iso (wrapper) | 508 + 22r + 36λn + r·C[perm.is_string_automorphism](n,λ) + C[tower.Tower.trivial](n) + C[perm.identity](n) + C[action.Coset.__init__](n) |
| main.Solver._one_iso | 14 |
| main.Solver._solve (dispatch) | D_bf ≤ 499+Ord; D_cr ≤ 500+Ord+C[orbits]; D_gi ≤ 759+2n+4r+3Ord+…; D_hint ≤ 936+7n+3Ord+…; D_e0 ≤ 631+101n+3n⌈log₂n⌉+3Ord+…; D_J ≤ D_e0+384+8r+9n+… (Section 2) |
| main.Solver.brute_force | 207 + 5λn + g + 2C_cs + C[group.PermGroup.__init__](n,g) + C[perm.identity](n) + 2C[action.Coset.__init__](n) |
| main.Solver.iso_window | W_iw(N,L) ≤ 80 + L⌈log₂L⌉ + (2+λ)L + C[action.window_lifter](N,L,r_H) + 2C[action.WindowLifter.restrict_string](L) + C[group.PermGroup.is_trivial]() + C[perm.identity](N) + C[action.Coset.__init__](N) + C[tower.Tower.trivial](N) + C[tower.Tower.restrict](N,L,ℓ) + C[action.WindowLifter.lift_coset](N,L,r_C) |
| main.Solver.chain_rule | 303 + (133+5λ)n + 2n⌈log₂n⌉ + (n+1)C[perm.identity](n) + C[action.Coset.__init__](n) + Σ_orbits[…] (Section 2) |
| main.Solver.strong_luks | 232 + (41+n)q + (2+λn)q + C[GWA.__init__/kernel/comb_gamma/_gamma_levels](n,m,r) + C[group.PermGroup.coset_reps_prefix](n+m,·;q) + q(C[perm.inv](n)+C[perm.act_string](n)+C[perm.mul](n)) + C[group.generated_subcoset](n,q,·) + C[action.Coset.__init__](n) |
| main.Solver.cameron_reduction | 260 + (53+m)s_c! + (2+λn)s_c! + (callees, Section 2) |
| main.Solver.johnson_case | 30 + C[certificates.JohnsonData.is_primitive]() |
| main.Solver.trivial_case | 448λ + 215λn + Σ_l C[perm.sym_gens](n_l,n) + C[GWA.image_is_sym](m,r) + C[group.PermGroup.__init__](n,4n) + C[group.even_subgroup_gens](n,2n) + C[perm.parity](n) + C[perm.from_cycles](n,2) + C[perm.mul](n) + C[action.Coset.__init__](n) |
| main.Solver.hypergraph_structure | W_hs ≤ 243 + m + (47+4λ)n + (n+1)⌈log₂(n+1)⌉ + 3λn⌈log₂n⌉ + (11t+53+2λ+2n)m^t + n·C[canon.canon](λ) + C[wl.KStructure.__init__](m,t) + C[structure.Chooser.check](n+3) + C[wl.refine_structures](m,t) |
| main.Solver.hypergraph_twin_classes | W_tw ≤ 72 + 85m + 78m² + 38m³ + ½m²·b(74+35t+λ) |
| …hypergraph_twin_classes.<find> | 19m + 10 |
| main.Solver.primitive_johnson | 381 + 36m + W_tw (plus the branch) |
| …primitive_johnson.<largest_twin> | 14 + 36m + W_tw |
| …primitive_johnson.<proc> | 59 + 59m + W_tw + C[structure.Chooser.check](3) + C[structure.Structure.__init__](m,2) |
| …primitive_johnson.<proc2> | 31 + 5m + W_hs + C[structure.Structure.__init__](m,1) + C[design.extended_design_lemma](m,t) |
| main.Solver.branch | 468 + λn + 22d + 11f_a + (s+1)P + s(431 + d + 2κ + ρ(n) + C[structure.align] + C[GWA.lift](n,m,r) + C[perm.inv](n) + C[perm.act_string](n) + W_rec) + Σ_j C_cov + (fixed callees, Section 3) |
| main.Solver._covered | 54 + 14h + 12p + h(C[perm.is_identity](n)+C[GWA.phi](n,m,r)) + p(960029+2κ) + 20000ph(53+22d+4κ+A_key) + (1+2κ)p²(20000+h) |
| main.Solver.imprimitive_johnson | 653 + λn + m (plus aggregate ×2 and the handler) |
| …imprimitive_johnson.<proc@721> | 163 + 4λn + 54m + 3m² + C[structure.Chooser.check](m+5) + C[structure.Structure.__init__](m,m+1) |
| …imprimitive_johnson.<proc@737> | 62 + 4λn + W_2b |
| main.Solver.aggregate | miss: 705 + 4λn + 86m + 2m⌈log₂m⌉ + (55+2n+22m)F + M(157+9k) + M²(65 + F(85+34k+C[perm.mul](n))) + M(C[cert.certificate]+C[cert.conjugate]+C[perm.inv](n)+C[perm.identity](n)) + F(C[perm.is_identity](n)+2C[GWA.phi](n,m,r)) + C[LC.__init__](n) + C[PermGroup.__init__](m,F) + C[PermGroup.orbits](m,F) + F·C[restrict_to](m,m) + C[is_giant_on](m,F), with F ≤ Mρ(n); hit: 4λn + 47 |
| main.Solver.case_2a | 227 (plus the branch) |
| …case_2a.<proc> | 115 + 4λn + 23m + C[structure.Chooser.check](3) + C[structure.Structure.__init__](m,2) |
| …case_2a.<recurse> | 11 + W_ta |
| main.Solver.top_action | W_ta ≤ 636 + 8m + 18r1 + 32f + n⌈log₂n⌉ + (19+λ)n + 4n² + Σ_ta + 4W_iw(n,w) + W_iw(n,n−w) |
| main.Solver.case_2b_structure | W_2b ≤ 526 + 206m + 105m² + 4m³ + m²⌈log₂m⌉ + 7r_F + mρ(m)(2m²+7m+20) + Σ_2b |
| main.Solver.case_3 | 896 + λn + 112m + 4m⌈log₂m⌉ + M(544+64k+16n+2k⌈log₂k⌉+2k!(24k+49)) + 4M²(190+8k+C[cert.compare]) + 2M(C[perm.identity](n)+C[GWA.phi](n,m,r)+C[perm.inv](m)+k!·C[cert.ordered_label](k)) |
| …case_3.<proc@1018> | 226 + λn + 33m + m⌈log₂m⌉ + (9k+82)m^k + 3k(k+4)m^k⌈log₂m⌉ + (k+5)m^{2k} + m^k·C[canon.canon](k+4) + C[wl.KStructure.__init__](m,k) + C[structure.Chooser.check](m^k+3) + C[wl.refine_structures](m,k) + C[structure.Structure.__init__](m,2) + C[design.extended_design_lemma](m,k) |
| main._chain_search (with rec) | C_cs ≤ 4783 + (2044+λ)n + 12n⌈log₂n⌉ + 444g + (85+2λ)gn + C[group.PermGroup.levels](n,r) + C[perm.identity](n) (g ≤ 5040, no forced prefix) |
| main.string_isomorphism | 130 + 2n + C[soj.SOJParams.__init__]() + C[canon.normalize_letters](n,λ_in) |
| graph._normalize_edges | 69 + 72L |
| graph.GraphInstance.__init__ | 201 + 30N + 7v + C[johnson.subsets_of](v,2) + 2C[johnson.induced_on_subsets](v,N) + 2C[perm.from_cycles](v,2) + 2C[perm.from_cycles](v,v) + C[group.PermGroup.__init__](N,2) + C[johnson.JohnsonStructure.__init__](v,2,N) |
| graph.GraphInstance.shared | 26 + C_gi(v) (first call for v), else 26 |
| graph.GraphInstance.string | 125 + 72L + 47N (no colors); 125 + 72L + (55+3γ)N + 2N·C[canon.canon](γ) (colors) |
| graph.GraphInstance.vertex_perm | 88 + 159v + 10v² |
| graph.graph_isomorphism | 959 + 288L + (140+6γ)N + 177v + 10v² + 4N·C[canon.canon](γ) + C[canon.normalize_letters](N,3+2γ) + C[soj.SOJParams.__init__]() + (C_gi callees) |
| graph.graph_automorphisms | 436 + 144L + (55+3γ)N + r_A(95+159v+10v²) + C_gi(v) + 2N·C[canon.canon](γ) + C[canon.normalize_letters](N,3+2γ) + C[soj.SOJParams.__init__]() + C[group.PermGroup.order](N,r_A) |
| graph.graph_automorphism_group_order | 8 + (graph_automorphisms) |
| graph.parse_edge_list | command line only, not bounded |

The node-level bounds W(node) are in Section 3.2.

---------------------------------------------------------------------------

## 5. Profile numbers used

These are the profiles of `babai_gi/_opprofiles.py`, the frozen profiles of the package, which `tests/test_opbounds.py` checks against the code. The format is `(outside, [(line, cycle, entry), …])`. Nested lambdas and generator expressions are given as `(total, loops)`. The single `loops: 1` of a generator expression is its own `for` clause; the bounds by hand are for `_solve.<genexpr@303>` (2 loops) and `<lambda@598>` (1 loop), Lemma P(5).

```python
PROFILES = {
    'main.Params.__init__': (44, []),
    'main.Params.paper': (14, []),
    'main.Params.small_scale': (32, []),
    'main.Params.__repr__': (32, []),
    'main.Params.luks_threshold': (12, []),
    'main.Params.enumeration_cap': (14, []),
    'main.Params.small_quotient': (20, []),
    'main.Params.k_paper': (13, []),
    'main.Params.gamma_threshold': (14, []),
    'main.Params.k_for': (57, []),
    'main.Solver.__init__': (18, []),
    'main.Solver.iso': (212, []),
    'main.Solver._one_iso': (14, []),
    'main.Solver._solve': (499, [(291, 5, 9), (303, 14, 10), (342, 8, 8), (344, 7, 9)]),
    'main.Solver.brute_force': (60, [(367, 0, 10)]),
    'main.Solver.iso_window': (78, []),
    'main.Solver.chain_rule': (54, [(410, 113, 0)]),
    'main.Solver.strong_luks': (61, [(449, 40, 2)]),
    'main.Solver.cameron_reduction': (78, [(481, 52, 2)]),
    'main.Solver.johnson_case': (30, []),
    'main.Solver.trivial_case': (165, [(513, 23, 0), (519, 14, 0), (520, 7, 0), (524, 13, 0), (527, 13, 0)]),
    'main.Solver.hypergraph_structure': (97, [(549, 6, 11), (550, 30, 0), (556, 6, 11), (557, 6, 9)]),
    'main.Solver.hypergraph_twin_classes': (39, [(572, 12, 0), (573, 37, 0), (577, 34, 4), (586, 15, 0)]),
    'main.Solver.hypergraph_twin_classes.<find@566>': (4, [(567, 19, 6)]),
    'main.Solver.primitive_johnson': (110, []),
    'main.Solver.primitive_johnson.<largest_twin@597>': (13, []),
    'main.Solver.primitive_johnson.<proc@604>': (39, []),
    'main.Solver.primitive_johnson.<proc2@611>': (29, []),
    'main.Solver.branch': (138, [(642, 11, 8), (652, 160, 0)]),
    'main.Solver._covered': (19, [(690, 14, 8), (692, 12, 0), (695, 18, 9), (697, 28, 0)]),
    'main.Solver.imprimitive_johnson': (162, []),
    'main.Solver.imprimitive_johnson.<proc@721>': (49, [(726, 29, 0)]),
    'main.Solver.imprimitive_johnson.<proc@737>': (15, []),
    'main.Solver.aggregate': (197, [(759, 86, 0), (767, 16, 5), (769, 47, 0), (785, 11, 8), (789, 8, 9), (791, 19, 9), (793, 14, 8), (796, 8, 8)]),
    'main.Solver.case_2a': (65, []),
    'main.Solver.case_2a.<proc@821>': (45, []),
    'main.Solver.case_2a.<recurse@830>': (11, []),
    'main.Solver.top_action': (348, [(844, 8, 8), (850, 11, 9), (851, 11, 9), (854, 24, 0), (897, 12, 8)]),
    'main.Solver.case_2b_structure': (211, [(916, 7, 9), (919, 98, 1), (933, 10, 8), (934, 12, 12), (934, 8, 9), (942, 9, 0), (943, 13, 0), (952, 7, 11), (952, 7, 11)]),
    'main.Solver.case_3': (125, [(978, 28, 0), (980, 60, 0), (984, 42, 7), (1002, 32, 0), (1005, 49, 0), (1012, 25, 0)]),
    'main.Solver.case_3.<proc@1018>': (137, [(1023, 12, 0), (1026, 6, 11), (1027, 6, 9)]),
    'main._chain_search': (67, [(1048, 21, 0), (1050, 9, 0), (1051, 11, 8), (1054, 11, 2), (1057, 13, 9), (1074, 13, 9)]),
    'main._chain_search.<rec@1059>': (28, [(1064, 26, 0), (1067, 12, 4), (1072, 12, 9)]),
    'main.string_isomorphism': (23, []),
    'graph._normalize_edges': (10, [(25, 59, 0)]),
    'graph.GraphInstance.__init__': (156, [(39, 6, 12), (54, 7, 9)]),
    'graph.GraphInstance.shared': (20, []),
    'graph.GraphInstance.string': (17, [(73, 38, 0)]),
    'graph.GraphInstance.vertex_perm': (19, [(85, 68, 0), (86, 9, 10)]),
    'graph.graph_isomorphism': (132, [(115, 5, 9), (124, 7, 9)]),
    'graph.graph_automorphisms': (96, [(141, 7, 8)]),
    'graph.graph_automorphism_group_order': (8, []),
    'graph.parse_edge_list': (50, [(152, 6, 8), (153, 15, 8), (159, 29, 0)]),
}

# nested lambdas / generator expressions: (total instruction count, number of loops)
NESTED = {
    'main.Solver.iso.<genexpr@237>': (21, 1),
    'main.Solver._solve.<lambda@280>': (3, 0),
    'main.Solver._solve.<genexpr@303>': (27, 2),
    'main.Solver.chain_rule.<lambda@402>': (10, 0),
    'main.Solver.trivial_case.<genexpr@516>': (28, 1),
    'main.Solver.trivial_case.<genexpr@533>': (21, 1),
    'main.Solver.trivial_case.<genexpr@537>': (27, 1),
    'main.Solver.hypergraph_structure.<genexpr@558>': (21, 1),
    'main.Solver.hypergraph_twin_classes.<genexpr@579>': (29, 1),
    'main.Solver.primitive_johnson.<largest_twin@597>.<lambda@598>': (27, 1),
    'main.Solver.branch.<genexpr@651>': (20, 1),
    'main.Solver.branch.<lambda@652>': (8, 0),
    'main.Solver._covered.<genexpr@698>': (21, 1),
    'main.Solver.aggregate.<genexpr@770>': (20, 1),
    'main.Solver.aggregate.<genexpr@787>': (21, 1),
    'main.Solver.aggregate.<genexpr@791>': (21, 1),
    'main.Solver.aggregate.<genexpr@803>': (19, 1),
    'main.Solver.top_action.<lambda@845>': (10, 0),
    'main.Solver.case_2b_structure.<lambda@945>': (12, 0),
    'main.Solver.case_2b_structure.<lambda@955>': (19, 0),
    'main.Solver.case_3.<genexpr@979>': (22, 1),
    'main.Solver.case_3.<genexpr@1004>': (22, 1),
    'main.Solver.case_3.<genexpr@1013>': (20, 1),
    'main.Solver.case_3.<proc@1018>.<genexpr@1028>': (21, 1),
    'main._chain_search.<rec@1059>.<genexpr@1065>': (22, 1),
}
```

---------------------------------------------------------------------------

## 6. What is not proved here, and the assumptions this rests on

1. **(A3) Correctness of `group.py` / `action.py`.** Complete Schreier–Sims, correct `known_order` values, and φ a homomorphism. These are used to count:
   * the `_chain_search` enumeration (`g = ∏u_i ≤ 5040`, `k_G ≤ 12`);
   * the coset representatives in `strong_luks` / `cameron_reduction` (`I = |Gbar| = q`, `I ≤ s_c!`);
   * generator counts, Lemma G4 (`len(H.gens) ≤ max(6, log₂|H|)`).

   They are properties of `group.py` / `action.py` and are not proved here.
2. **(A5) Determinism of `proc`.** It is needed for Lemma R (`enumerate_runs` runs `proc` at most `s = ∏ c_j` times and terminates). It holds because the package has no randomness and its caches return values equal to recomputation. It is not proved for every module that `proc` calls (soj, design, wl, cc).
3. **Parameters left symbolic here; their bounds belong to the documents of those modules:**
   * the number of choices d per run, the choice-object size μ (`κ ≤ 1 + dμ`), and `A_key` (cost of `apply_obj`): soj/design/structure;
   * the number of `iso_window` calls inside one `certificate` / `compare` call, which give `Q_A`, `Q_cmp`: certificates;
   * the candidate counts `c_j` behind `s = ∏ c_j`.
4. **Letter size λ.** The bounds are linear in λ. λ = 1 at the root, and each nesting through `certificates.compare` adds 2 (`colored_string`). A bound on λ along a recursion path, at most `1 + 2·`(number of compare levels), is left to the global proof.
5. **Stdlib Python code** is charged by the built-in rules (K13). This covers `Counter.__eq__`, the `Fraction` constructor and `Counter.__missing__`. The stats f-string formatting is charged 64.
6. **Unreachable code under `Params.paper()` (A1).** This covers every `fallback(...)` and what follows it: lines 333/335 partly, 939–940, and inside `certificates`/`design`/`soj`. It also covers node type N6a (`t = 1` primitive Johnson). N6a would need a primitive group whose Johnson quotient is a giant on the same points; that group is itself a giant and is handled by N3. The bounds above still include `C[errors.fallback]` where the call is evaluated.
7. **Real cost terms, not proof artifacts:**
   * the `M²F` orbit BFS of `aggregate` (≤ M³ρ(n));
   * the `(k+5)m^{2k}` of `raw.count` in case 3;
   * `set(window)` rebuilt per point in `top_action`, line 897 (`4nw`);
   * the `s³κ` term of `_covered`, which comes from K4 (per element of both operands) applied to `covered |= orbit`.

   They are what the code costs in this model. They can be reduced by small code changes; this file does not change the code.
8. **Lemma P** rests on PROOF.md Lemma 1.1, whose hypotheses `tests/test_attribution.py` checks, and on the hand bounds for point 4 and for the two nested code objects with loops.
