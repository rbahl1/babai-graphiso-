# Instruction-count bounds for `babai_gi/johnson.py` and `babai_gi/certificates.py`

Profile numbers are those of `opcount.generate()` (Section 6); line numbers refer to the files of
this repository.
Every bound below is an upper bound on the operations of **one call** in the cost model of
`SPEC.md`. Callees in other modules appear as named symbols `C[module.Qualname](...)`.
Recursion into the solver is never counted. It is listed separately (Section 4).

## 0. Findings

1. **Instruction counts.** The `opcount` profile numbers (Section 6) are sound for these modules without hand corrections (Lemma L, Section 1.3).
2. **Solver calls** come only from `recompute` and `compare` (Section 4).
   * `certificate` makes at most (J+1)·k! calls of `iso_window`.
   * J ≤ n is the number of rounds of its while loop: unconditionally J ≤ n, and J ≤ ⌊n/3⌋ under INV-W.
   * `compare` makes at most ℓ·k! calls, where ℓ ≤ n+1 is the number of rounds of the certificate.
3. **Conditional parts.**
   * |lifts| ≤ k! needs INV-A, which ownwork_gaps.md §5(c) proves from HOM (CORRECTNESS.md, Lemmas 3.3, 4.4, 4.5). Unconditionally |lifts| ≤ m!/(m−k)!.
   * J ≤ ⌊n/3⌋ needs INV-W.
   * The logarithmic generator-count bound of Lemma R needs completeness of group.py's Schreier–Sims. The unconditional bound is max(6, N(N−1)/2).
   * Everything else is unconditional.
4. **Crude spot.** The three union-find structures in `recognize_cameron` use naive linking without union by rank. One `find` is bounded by the number of nodes, which gives the N³-polylog own work of `recognize_cameron`. This is valid, but far from tight.

---------------------------------------------------------------------------------------------

## 1. Conventions

### 1.1 Parameters

**certificates.py** (`JohnsonData` / `LocalCertificates` of a Johnson case):

| symbol | meaning |
|---|---|
| n | `Gw.n` = \|Ω\| |
| m | `Gw.m` = \|Γ\| |
| t | `jd.t` |
| nb | number of standard blocks, `len(jd.blocks) = len(jd.T_of_block)`; nb ≤ n |
| k | \|A\| = `len(A_sorted)` |
| r | \|`Gw.G.gens`\| = \|`Gw.phi_gens`\| (equal, checked in `GroupWithAction.__init__`) |
| r_H | for a `GroupWithAction` H: \|`H.G.gens`\| = \|`H.phi_gens`\| = \|`H.combined_gens`\| |
| r_K, r_N | generator counts of the groups named K and N in the code |
| r̂ | the largest generator count of a group handled in the call |
| λ | \|`lifts`\| of one `kernel_and_lifts` |
| ℓ | `len(cert.iterations)` |
| Λ | Σ_i \|`it_i.lifts`\| |
| R_N | Σ_i \|`it_i.N.gens`\| |
| J | number of `recompute` calls in the while loop of `certificate` |
| B | number of executions of that loop's body |
| w | \|W_new\| |
| E | number of elements of `cert.HA` |

**johnson.py** (the recognisers run on the primitive quotient `Gbar`):

| symbol | meaning |
|---|---|
| N | `Gbar.n`, the number of blocks (called m in `main.py`) |
| r | \|`Gbar.gens`\| |
| L | log2 N |
| ℓ | ⌈log2 N⌉ |
| S | ⌊log_3 N⌋ |

Elsewhere m, t and k are as in the code. Notation: ⌈lg x⌉ := ⌈log2 x⌉ for x ≥ 1, so ⌈lg 1⌉ = 0.

### 1.2 How the cost model is applied

Each instruction counts 1 (Lemma L). On top of that the following *extra* costs are charged. Where the model is ambiguous, the larger reading is used.

| rule | operation | extra cost |
|---|---|---|
| X1 | call of a built-in (function, type or method) | +1, plus X2–X7 |
| X2 | each element produced by `range`, `enumerate`, `zip`, a dict or set (incl. `.items()`, `.values()`), a generator or `combinations` | +1 (itertools: + length of the produced tuple). Often +1 is also charged per element of a list or tuple loop, which is generous. |
| X3 | a built-in consuming an iterable (`tuple`, `list`, `set`, `frozenset`, `dict`, `sorted`, `any`, `all`, `max`, `set.update`) | +1 per element consumed; hashed containers also pay X4 per element |
| X4 | lookup, insertion or deletion with key κ in a dict or set (subscript, `in`, `get`, `setdefault`, `add`, `MAP_ADD`, store) | +1 + 2h(κ): one hashing and one comparison, each bounded by h(κ) |
| X5 | set / frozenset algebra (`&`, `\|`, `\|=`) and comparisons (`<=`, `!=`) | \|a\| + \|b\| + 1 |
|  | tuple / list `==`, `!=`, `<` on flat int sequences | ≤ 1 + min(lengths) |
|  | slice | length + 1 |
|  | list `+` | total length + 1 |
|  | `[x]*L` | L + 1 |
|  | `x in list`, `list.index` | length + 1 |
| X6 | `sorted` of L ints | SORT(L) := L⌈lg L⌉ + 2L + 2 |
|  | `sorted` of containers | (L⌈lg L⌉ comparisons) × (cost of one comparison) + 2L + 2; a key function is charged per call |
| X7 | `factorial(L)`, `comb(L, ·)` | L + 1 |
| X8 | one `self.solver.stats[...] += 1` | +128 (2 × 64, as allowed by SPEC) |
| X9 | an `import` statement inside a function (module already loaded) | +2 |

Hash sizes: h(int) = 1, h(str of length s) = s + 1, h(tuple or frozenset) = 1 + Σ h(elements). Hence
an int key costs 3, a tuple or frozenset of j ints costs 2j + 3, and the key `("kl", tuple of k ints)`
of `kernel_and_lifts` costs 2(k + 5) + 1 = 2k + 11.

### 1.3 Lemma L (own instructions of one call)

**Lemma L.** Let f be a function of these modules and fix one call of f. For each loop ℓ of f, let it_ℓ and en_ℓ be its total iterations and entries during the call; for a comprehension with several `for` clauses, it_ℓ is the number of elements yielded by all its clauses. Then the call executes at most

    outside + Σ_ℓ [ cycle_ℓ · (it_ℓ + en_ℓ) + entry_ℓ · en_ℓ ]

instructions of f's own code object. Here (outside, cycle_ℓ, entry_ℓ) are the numbers of `opcount.profile(f)`.

*Proof.*

1. **The base argument.** This is the argument of the `opcount` docstring and of PROOF.md, Lemma 1.1. Within one level, the only backward jumps are that loop's own. So an instruction of a loop's cycle runs at most once per iteration and once per entry, since the body is executed once per iteration and nested loops are separate levels. Any other instruction of the level runs at most once per entry.
2. **What the argument needs.** It relies on the following properties of the attribution of `opcount.profile` for the loops of both modules. PROOF.md, Lemma 1.1 proves the bound. Its proof uses the hypotheses (H1)–(H3) stated in `tests/test_attribution.py`, and that test checks them on every code object of both modules.
3. **The properties.**
   * **(A1)** Each `for` / comprehension loop's `FOR_ITER`, together with any `EXTENDED_ARG` prefix, is attributed to that loop and lies in its cycle.
   * **(A2)** No instruction attributed to an enclosing level, or to no loop, lies strictly between a loop's `FOR_ITER` and its exit target, i.e. in its body.
   * **(A3)** The only "entry" instructions lying inside a loop body lie on a path that leaves the loop by `return`, `raise` or `break`. Each therefore runs at most once per entry. They are:

     | function | loop | lines | path |
     |---|---|---|---|
     | `recognize_cameron` | For@196 | 361–362 | `return` |
     | `johnson_phi` | For@395 | 397 | `raise` |
     | `recognize_johnson` | For@422 | 427 | `break`, threaded to the outer head |
     | `recognize_johnson` | For@428 | 433 | `return` |
     | `_identify` | For@456 | 547 | `return` |
     | `_identify` | For@491 | 500–501 | `ok = False; break` |
     | `JohnsonData.__init__` | For@63 | 65–66 | `fn = None; break` |

   * **(A4)** For `while` loops, every "entry" instruction precedes the first back-jump target (the first evaluation of the test), or is a backward jump of the enclosing loop on the exit path (`_cameron_candidates` While@138, offset 476); either runs at most once per entry.
4. **Position-less instructions.** Instructions without a source position are prologue (`COPY_FREE_VARS`, `MAKE_CELL`), run once per call, or exception handlers, not executed on normal paths. ∎

**Nested code objects.** `tests/test_attribution.py` checks that no lambda of the two modules has a backward jump and that every generator expression has at most one loop head, its `FOR_ITER`, except the two generator expressions with two loops (third item).
* A lambda executes each of its `total` instructions at most once per call.
* A generator expression with one loop executes at most `total · (L+1)` instructions when L elements are drawn from it. Between two consecutive `FOR_ITER` executions each instruction runs at most once, and there are at most L + 1 `FOR_ITER` executions.
* The two generator expressions with two loops are `recognize_cameron.<genexpr@202>` (the second one on that line, 31 instructions) and `<genexpr@351>` (38 instructions). They are bounded here by hand. For them the bound is `total × (number of FOR_ITER executions of both clauses)`. This is valid because each instruction is controlled by one of the two `FOR_ITER`s and runs at most once per execution of it.

**Duplicate keys.** Where two code objects share a key, `generate()` keeps the last one.

| key | code objects (instructions) | kept by `generate()` |
|---|---|---|
| `Certificate.__init__.<genexpr@146>` | 20 and 19 | 19 |
| `recognize_cameron.<genexpr@202>` | 22 (one loop) and 31 (two loops) | 31 |
| `<parallel@270>.<genexpr@273>` | 26 and 26 | 26 |
| `conjugate.<genexpr@263>` | 20 and 20 | 20 |

The proofs use the count of each individual object.

### 1.4 Named callees

* **Meaning of the symbols.** `C[module.Qualname](params)` is a bound on all operations of one call of that function, including its callees but not solver recursion. The parameters are degree N, generator count r passed, and so on.
* **Monotonicity.** Every such bound is assumed to be nondecreasing in each parameter, so passing upper bounds is allowed.
* **Generator functions.** For `group.PermGroup.coset_reps_prefix` and `group.PermGroup.elements`, the symbol `C[...](N, ·; E)` is the cost of producing E elements and exhausting the generator.
* **`orbits_on`.** `C[group.PermGroup.orbits_on](L, r)` excludes the calls of the `act` argument; `orbitals` charges those itself.
* **`phi` with a fast phi.** `C[action.GroupWithAction.phi](n, m)` includes, when `phi_fn` is set, the call of `phi_fn` / `phi_fn2` bounded in §3.2. The `phi_fn` set by `JohnsonData.__init__` is a function of certificates.py.

### 1.5 Lemma B (stabilizer chains of group.py)

Let P = `PermGroup(N, gens, forced_prefix=F)` with F duplicate-free, after `_build`.

* **(a)** The base points b_i = `levels[i].b` are pairwise distinct. In particular there are at most N levels.
* **(b)** Every element of `levels[i].gens` and every value of `levels[i].trans` lies in ⟨P.gens⟩ and fixes b_0, …, b_{i−1}.
* **(c)** The keys of `levels[i].trans` lie in the orbit of b_i under ⟨`levels[i].gens`⟩.

*Proof* (group.py).
* **Where strong generators come from.** They are added only by `add_strong_gen(h, lo, hi)`, which appends h to levels lo..hi. It is called with (0, j) after `sift(g, 0)` (line 188), and with (i+1, j) after `sift(y, i+1)`, where y = u·s·trans_inv[q] is a Schreier generator of level i (lines 161–166).
* **Induction for (b).** Assume (b) for the current levels. Then y fixes b_0..b_i, since u maps b_i ↦ pt, s maps pt ↦ q and trans_inv[q] maps q ↦ b_i, and all three fix b_0..b_{i−1}.
* **Effect of `sift`.** `sift(g, start)` multiplies by `trans_inv` elements of levels start..j−1, which fix the earlier base points by (b). So its residue h fixes b_start..b_{j−1}, and also b_0..b_{start−1} if g did. Hence h fixes b_0..b_{j−1}, which is (b) for the levels lo..j that receive h.
* **Transversal entries.** They are products `mul(u, s)` of level generators (lines 120–122). This gives (b) for `trans`, and (c).
* **Distinct base points (a).**
  * Prefix levels are created once per element of F (lines 88–90).
  * A new level gets the first point of `rest_order` moved by h (lines 131–139), when j = len(levels). This h fixes all existing base points.
  * `rest_order` excludes F.
  * So the new point is distinct from all earlier base points. ∎

**Consequence B1.** Suppose every generator of P maps a set X ⊆ range(N) onto itself, and b_0, …, b_{j−1} ∈ X. Then |trans_i| ≤ |X| − i for i < j. The reason: by (b), (c) and invariance, the keys lie in X ∖ {b_0..b_{i−1}}.

**Consequence B2.** `coset_reps_prefix(j)` yields ∏_{i<min(j, #levels)} |trans_i| elements, and `elements()` yields ∏_i |trans_i| elements (or 1 if there are no levels). This is read off the recursion `rec` (group.py lines 414–422, 433–440). For a group of degree k both are therefore ≤ k!.

### 1.6 Lemma R (generator counts)

**Lemma R.** For every `PermGroup` P of degree N:
* unconditionally, |P.gens| ≤ max(6, N(N−1)/2);
* if group.py's Schreier–Sims closure yields complete chains, |P.gens| ≤ max(6, ⌊log2 |⟨P.gens⟩|⌋) ≤ max(6, ⌊log2 N!⌋).

*Proof.*
* **Few generators.** The constructor keeps distinct non-identity tuples. If at most 6 remain, the claim holds.
* **Pruning.** Otherwise `_build(prune=True)` replaces `gens` by `essential`. Each essential g had a non-identity sift residue h, and `add_strong_gen(h, 0, j)` then adds the point h[b_j] ∉ trans_j to `trans_j`, or creates a new level.
* **Unconditional count.** So each essential element increases Σ_i (|trans_i| − 1) by at least 1. Transversals never shrink, and the sum is at most Σ_{i<N} (N − 1 − i) = N(N−1)/2 by Lemma B.
* **Count with complete chains.**
  * Every sift in the main loop (line 184) happens with a chain that is complete for ⟨essential so far⟩. The closure has finished (`closure()` returned False), or the order target was reached, after which the loop breaks.
  * So an essential g lies outside ⟨previous essentials⟩, and each step at least doubles the order. ∎

So every generator count in this document is at most ρ := max(6, ⌊log2 (n+m)!⌋) (completeness hypothesis), and at most max(6, (n+m)²/2) unconditionally. Substituting gives bounds in n, m, k alone.

### 1.7 Invariants used by the k! bound and the n/3 bound

**INV-A.** Every H passed together with A_sorted = sorted(A) to `image_on_A`, `affected`, `kernel_and_lifts` or `recompute` satisfies:
* every p ∈ `H.phi_gens` maps A onto A, and
* `H.combined_gens[i] = H.G.gens[i] + (n + p_i[v])_v`. This part holds by construction in action.py.

*Where INV-A comes from.*
* The callers are `certificate` only.
* In `certificate`, H is first `setwise_stabilizer(A)`. That is `Gw.subgroup` of `preimage(gens of S(A)×S(Γ∖A) ∩ G^φ)`, whose generators have φ-images in S(A)×S(Γ∖A) when φ is a homomorphism and `lift` is correct. Both hold by CORRECTNESS.md, Lemma 3.3.
* Afterwards H is `recompute(...)`, which is ≤ H_old if `iso_window` returns cosets inside N (solver correctness; CORRECTNESS.md, Lemma 10.2(b)).

*What INV-A gives.* Under INV-A, every generator of the combined group `comb` preserves n+A. By B1 with X = n + A, then B2: λ ≤ ∏_{i<kA} (k − i) ≤ k!. Without INV-A, use X = n + range(m), which is always invariant because φ-images are permutations of range(m). This gives λ ≤ m!/(m−k)!.

**INV-W.** In `certificate`, every `recompute` returns H_new with H_new.G ≤ H_old.G (solver correctness; CORRECTNESS.md, Lemma 10.2(b)). Unconditional bounds are always given next to the conditional ones.

---------------------------------------------------------------------------------------------

## 2. `babai_gi/johnson.py` (source order)

### johnson.subsets_of

* **Profile.** outside 14; ListComp@38 (cycle 7, entry 9).
* **Assumption.** t ≥ 0. Write B := binom(m, t).
* **Loop.** ListComp@38 runs over `combinations(range(m), t)`. It has exactly B iterations and 1 entry.
* **Instructions.** ≤ 14 + 7(B+1) + 9 = 30 + 7B.
* **Built-ins.**
  * `range`: 1.
  * `combinations`: 1, plus m (it consumes the range), plus B(t+1) produced.
  * `tuple(c)`: B(t+1).
  * Total 2 + m + 2B(t+1).
* **Bound.** **SUB(m,t) ≤ (2t+9)·binom(m,t) + m + 32.**
* **Callers.** graph.py (t = 2) and `johnson_group_gens`.

### johnson.pairs_of

* **Profile.** outside 6.
* **Bound.** 6 + SUB(m,2) ≤ **13·binom(m,2) + m + 38**.
* **Use.** Tests only (no package caller).

### johnson.induced_on_subsets

* **Profile.** outside 15; `<genexpr@46>` (31, 1 loop) over `subsets`; inner `<genexpr@46>` (20, 1 loop) over T.
* **Assumptions.** L := \|subsets\|. Each T is a t-tuple of points of `tau`. `index` maps sorted t-tuples to ints. A missing key raises an exception, which only shortens the call.
* **Instructions.** ≤ 15 + 31(L+1) + L·20(t+1).
* **Built-ins per element.**
  * `sorted` of t ints: SORT(t).
  * `tuple`: t + 1.
  * `index[...]`: 2t + 3.
  * Steps and consumption: t + 2.
  * Total t⌈lg t⌉ + 6t + 8. The outer `tuple` call adds 1.
* **Bound.** **IND(L,t) ≤ L(t⌈lg t⌉ + 26t + 59) + 47 ≤ L(t² + 26t + 59) + 47.**

### johnson.johnson_group_gens

* **Profile.** outside 57; DictComp@52 (6, 11).
* **Loop.** DictComp@52 runs over `enumerate(subs)`: B iterations, 1 entry.
* **Instructions.** 57 + 6(B+1) + 11 = 74 + 6B.
* **Built-ins.**
  * `enumerate` 1, plus B(1 + 2t + 3) for steps and tuple-key insertions.
  * `list(range(m))`: m + 2.
  * Two appends.
* **Callees.**
  * SUB(m,t).
  * IND(B,t) twice.
  * `C[perm.from_cycles](m, 2)` and `C[perm.from_cycles](m, m)`.
* **Bound.** **≤ B(2t⌈lg t⌉ + 56t + 137) + 2m + 205 + C[perm.from_cycles](m,2) + C[perm.from_cycles](m,m)**, with B = binom(m,t).
* **Use.** Tests only.

### johnson.JohnsonStructure.__init__

* **Profile.** outside 21; DictComp@76 (6, 12).
* **Loop.** L := \|T_of_point\|, each a frozenset of ≤ t ints. The DictComp has L iterations and 1 entry.
* **Instructions.** 39 + 6L.
* **Built-ins.** `enumerate` 1, plus L(1 + 2t + 3).
* **Bound.** **JS(L,t) ≤ L(2t+10) + 40.**
* **Callers.** graph.py, `recognize_johnson` (L = N, t = 1), `_identify` (L = N).

### johnson.JohnsonStructure.__repr__, johnson.CameronStructure.__repr__

Diagnostics only (`repr`). No bound needed. Profiles (12) and (16).

### johnson.CameronStructure.__init__

* **Profile.** outside 34.
* **Built-ins.** `comb(k, t)`: k + 1.
* **Bound.** **≤ k + 35.**

### johnson.recognize_hamming

* **Profile.** outside 7.
* **Bound.** 7 + RCAM(N, r; ts = (1,)) (see `recognize_cameron`).
* **Use.** Tests only.

### johnson._cameron_candidates

* **Profile.** outside 20; For@131 (32, 0); While@138 (40, 13); While@141 (11, 6).
* **Small N.** If N < 9, the function returns at line 129. Bound ≤ 20.
* **Setup for N ≥ 9.** Let L = log2 N ≥ 3.16.
* **Passes.** A pass is an iteration of For@131 whose test passes, i.e. c = `iroot(N, s)` satisfies c ≥ 3 and c^s = N.
  * For fixed s, c^s = N has at most one positive integer solution, so there is at most one pass per s.
  * A pass needs 3^s ≤ c^s = N. So the number of passes is P ≤ ⌊log_3 N⌋ − 1 < L.
  * In a pass, s ≥ 2 gives c ≤ √N. Put a := log2 c ≤ L/2 and b := √(2c).
* **Loop While@138** (t = 2, 3, …).
  * It continues while binom(2t+1, t) ≤ c. Since binom(2t+1, t) ≥ binom(2t, t) = Π_{i≤t} (t+i)/i ≥ 2^t, every iteration has 2^t ≤ c, i.e. t ≤ a.
  * Hence the iteration count I_1 satisfies I_1 + 1 ≤ a. If I_1 ≥ 1 then I_1 ≤ ⌊a⌋ − 1; if I_1 = 0 then 1 ≤ a.
  * Each test costs `comb(2t+1, t)` ≤ 2a + 4.
* **Loop While@141** (k from 2t+1).
  * For 2 ≤ t ≤ k − 2, binom(k, t) ≥ binom(k, 2) = k(k−1)/2. An iteration needs binom(k, t) < c, hence (k−1)² < 2c, i.e. k < 1 + b.
  * So the iteration count is I_2 ≤ max(0, b − 2t + 1) ≤ b, and each `comb` evaluated in it or after it costs ≤ 2a + 5 + b.
* **Instructions.**
  * Per pass: 40(I_1+1) + 13 ≤ 53a.
  * Per t-iteration: 11(I_2+1) + 6.
* **Built-ins.**
  * Per pass: 2 + \|ts\| for line 135.
  * Per t-iteration: 1 + \|ts\| (`t in ts`), plus (I_2 + 2)(2a + 5 + b) for `comb`, plus 1 (append).
* **Per t-iteration total.** ≤ 2c + 2ab + 18b + 4a + 29 + \|ts\|.
* **Per pass total.** ≤ 2 + \|ts\| + a(2c + 2ab + 18b + 6a + 86 + \|ts\|).
* **Summing over at most L passes.** Use a ≤ L/2, c ≤ √N and b ≤ √2·N^{1/4}:

      Σ_passes ≤ L·[2 + L√N + 0.71L²N^{1/4} + 12.73L N^{1/4} + 1.5L² + 43L] + |ts|(L + L²/2).

  For ts = None the |ts| terms are 0, because `ts is None` short-circuits.
* **Bound.** The bound CC(N, ts) of one call is in ownwork.md §3.2. It adds to the sum over the passes the fixed part: For@131 and its calls of `iroot`.

### johnson.iroot

* **Profile.** outside 14; While@154 (21, 5).
* **Bound.** In ownwork.md §3.1.

### johnson.recognize_cameron

* **Profile.**
  * outside 52.
  * Loops (cycle, entry):

    | loop | (cycle, entry) | loop | (cycle, entry) | loop | (cycle, entry) |
    |---|---|---|---|---|---|
    | For@193 | (21, 0) | For@249 | (9, 0) | DictComp@309 | (8, 11) |
    | For@196 | (418, 27) | For@250 | (20, 0) | For@311 | (23, 0) |
    | ListComp@199 | (6, 9) | For@256 | (9, 0) | For@313 | (38, 0) |
    | For@200 | (11, 0) | For@257 | (12, 0) | For@336 | (9, 0) |
    | For@208 | (53, 0) | For@276 | (9, 0) | For@337 | (16, 0) |
    | For@211 | (23, 0) | For@277 | (9, 0) | For@339 | (24, 0) |
    | While@217 | (14, 3) | For@278 | (14, 0) | For@344 | (15, 0) |
    | For@219 | (31, 0) | For@281 | (52, 0) | DictComp@350 | (10, 12) |
    | ListComp@228 | (7, 9) | For@291 | (15, 0) | ListComp@361 | (7, 8) |
    | For@241 | (10, 0) | For@297 | (19, 0) | | |
    | For@242 | (9, 0) | For@299 | (9, 0) | | |
    | For@243 | (35, 0) | For@306 | (9, 0) | | |
    | | | For@307 | (7, 0) | | |

  * Inner defs: `find`, `find2`, `find3`, each (4; While (19, 6)); `parallel` (37).
  * Generator expressions and lambdas:

    | object | instructions |
    |---|---|
    | genexpr@202 | 22 and 31 (two loops) |
    | genexpr@225 | 22 |
    | genexpr@252 | 19 |
    | genexpr@253 | 22 |
    | genexpr@259 | 26 |
    | genexpr@273 | 2 × 26 |
    | lambda@293 | 10 |
    | genexpr@294 | 26 |
    | genexpr@315 | 20 |
    | genexpr@347 | 26 |
    | genexpr@351 | 38 (two loops), inner 20 |

* **Assumptions.**
  * `Gbar` is a `PermGroup` of degree N with r generators.
  * `orbs`, if passed, is a list of pairwise disjoint lists of ordered pairs of distinct points with total size ≤ N(N−1). No package caller passes `orbs` (main.py:320 calls `recognize_cameron(Gbar)`). Otherwise `orbs = orbitals(Gbar)`, which partitions the N(N−1) ordered pairs, because `orbits_on` assigns each item to exactly one orbit.

**Global structure.**
* If N < 9, `cands = []` and the function returns before `orbitals`. Bound ≤ 52 + 2 + 20 ≤ 82.
* Otherwise K_c := \|cands\|. A candidate (k, t, s, c) has c^s = N with c ≥ 3, so s ≤ S = ⌊log_3 N⌋.
* For fixed s, the candidates are (c, 1, s, c) and at most one k for each t ≥ 2 with 2^t ≤ binom(2t+1, t) ≤ c. That makes at most ⌊log2 c⌋ ≤ L/s candidates. Hence:

      K_c ≤ Σ_{s=2}^{S} L/s ≤ L(S−1)/2 ≤ LS/2,     Σ_cand s^j ≤ L Σ_{s=2}^{S} s^{j−1} ≤ L·S^j   (j = 1, 2, 3).

* **For@193** (candidates) and **For@196** (orbitals, Q := \|orbs\| ≤ N(N−1) iterations per entry).
  * Instructions: 21(K_c + 1) + K_c[418(Q+1) + 27].
  * Built-ins: `len(o)` once per pair (cand, o).
* **Cheap part.**

      ≤ K_c(419Q + 466) + 21 ≤ LS(210N² + 233) + 21.

**Heavy bodies.**
* For a candidate, put d := t(k−t) (`deg_coord`) and D := s·d (`deg`).
* The body beyond line 197 runs only for orbitals with \|o\| = ND. These are disjoint, so their number is **Q_D ≤ N(N−1)/(ND) < N/D**.
* Facts used below:
  * d ≥ 2: t = 1 gives d = c − 1 ≥ 2; t ≥ 2 gives d ≥ 2(t+1).
  * Hence D ≥ 2s ≥ 4.
  * d ≤ c = binom(k, t): for t = 1, k − 1 < k; for t ≥ 2, binom(k, t) ≥ binom(k, 2) ≥ k²/4 ≥ t(k−t).
  * Hence D ≤ sc ≤ s√N, using c = N^{1/s} ≤ √N.
  * Λ_L := s·c^{s−1} = sN/c ≤ sN/3.
  * λ' := ⌈lg(sN)⌉ ≤ 2ℓ.
* The heavy body splits into phases A–J. For each phase the bound per orbital (instructions from the profile, plus built-ins) is given, and then that bound × N/D.
* A phase's loops are bounded using only checks the code has already passed:

**A (lines 199–203).**
* *Loops.*
  * ListComp@199: N iterations.
  * For@200 over o: ND iterations.
  * genexpr 202a: ≤ N elements.
  * genexpr 202b: Σ_x \|adj[x]\| = \|o\| = ND inner elements, so 2N + ND + 1 `FOR_ITER` executions.
* *Instructions.* 6(N+1) + 9 + 11(ND+1) + 22(N+1) + 31(ND + 2N + 1) = 42ND + 90N + 79.
* *Built-ins.* 10ND + 6N + 4: `set()` ×N, `add` (4 each), `x not in adj[y]` (3 each), the `any` consumption, the steps.
* **A ≤ 52ND + 96N + 83. × N/D: ≤ 76N² + 20.75N.**

**B (local classes, 205–231).** Runs only after line 202 passed, so adj is D-regular and symmetric.
* *Loops.*
  * For@208: N iterations.
  * Per x:
    * For@211 over `sorted(adj[x])`: D iterations.
    * While@217: entries = number of components ≤ D. Iterations = number of pops = number of pushes. Each push is paired with the first assignment of a key of `comp_of` ⊆ adj[x], so there are ≤ D of them.
    * For@219: D iterations per pop, D entries in total.
* *Instructions per x.* 23(D+1) + [14·2D + 3D] + 31(D² + D) + 22(D+1) + 7(s+1) + 9 = 31D² + 107D + 7s + 61.
* *Built-ins per x.*
  * SORT(D).
  * Per y: 4.
  * Per new y: 5.
  * Per pop: 1.
  * Per w: ≤ 13: step, two lookups, the store, two appends.
  * The genexpr `any`: 3D + 2.
  * The frozensets of `local`: 4D + 2s.
  * Two appends.
  * Total ≤ 13D² + D⌈lg D⌉ + 19D + 2s + 7.
* *Total.* B ≤ 53(N+1) + 1 + N(44D² + D⌈lg D⌉ + 126D + 9s + 68). With D⌈lg D⌉ ≤ D² and 9s ≤ 5D:
  **B ≤ N(45D² + 131D + 121) + 54. × N/D: ≤ 45N²D + 161.25N² + 13.5N ≤ 45sN^{2.5} + 161.25N² + 13.5N.**

**C (union-find on (vertex, class), 233–247).** After line 230: every `local[x]` has exactly s classes of size d.
* *Loops.*
  * For@241: N iterations.
  * For@242: Ns iterations.
  * For@243: ND iterations.
* *`find` (Lemma UF).*
  * The parent array is a forest on Ns nodes. Initially parent[i] = i.
  * Linking `parent[ra] = rb` joins two distinct roots: `find` returns a node with parent[a] == a, and path halving changes only non-roots.
  * Path halving replaces a pointer by an ancestor.
  * So the depth stays ≤ Ns − 1, and a call costs ≤ 4 + 19(depth + 1) + 6 ≤ 19Ns + 10.
  * There are 2ND calls.
  * `cls_at[y][x]` exists because x ∈ adj[y] (symmetry) and every element of adj[y] is a key of `cls_at[y]`.
* *Instructions.* 10(N+1) + 9(Ns+N) + 35(ND+Ns).
* *Built-ins.* 4ND + 2Ns + 2N + 3.
* **C ≤ 38N²sD + 59ND + 46Ns + 21N + 13. × N/D: ≤ 38sN³ + 87.25N² + 3.25N.**

**D (groups, layers, 248–254).**
* *Loops.* For@249 and For@250: Ns iterations; Ns `find` calls.
* *Sizes.* G_n := \|groups\| ≤ Ns and Σ\|g\| ≤ Ns, since each pair (x, ci) adds x to one group.
* *Sorting.* `sorted(..., key=sorted)`:
  * key calls: Σ SORT(\|g\|) ≤ Ns(⌈lg N⌉ + 2) + 2G_n;
  * G_n⌈lg G_n⌉ comparisons of lists of length ≤ N, each costing ≤ N + 1.
* *Line 240.* `set(layers)` hashes frozensets: ≤ 2Ns + 4G_n + 1.
* *Instructions.* 9(N+1) + 20(Ns+N) + 19(G_n+1) + 22(G_n+1).
* *Total.*

      D ≤ 19N²s² + Ns(48 + ℓ) + 55G_n + G_n⌈lg G_n⌉(N+1) + 31N + 58 ≤ 19N²s² + Ns(103+ℓ) + Nsλ'(N+1) + 31N + 58.

* **× N/D: ≤ 9.5sN³ + 0.5λ'N³ + N²(59.25 + 0.5ℓ + 0.5λ') + 14.5N.**

**E (layers_of, 255–260).** After line 253: there are Λ_L layers, each of size c, so Σ\|L\| = s·c^s = sN.
* *Loops.* For@256: Λ_L; For@257: sN; genexpr@259: N + 1.
* *Instructions.* 9(Λ_L+1) + 12(sN+Λ_L) + 26(N+1).
* *Built-ins.* Λ_L + 6sN + 7N + 3.
* **E ≤ 22Λ_L + 18sN + 33N + 38 ≤ 26sN + 33N + 38. × N/D: ≤ 21.25N² + 9.5N.**

**F (parallel classes, 262–289).** After line 259: every v lies in exactly s layers.
* *Loops.*
  * For@276: Λ_L.
  * For@277: sN.
  * For@278: sND.
  * For@281: ≤ s·sND iterations and ≤ sND entries.
* *`parallel` calls.* Only for new keys (`tested`), and lj ≠ li, so P_c ≤ min(binom(Λ_L, 2), s²ND).
* *Cost of one `parallel` call.*
  * Instructions: 37 + 2·26(c+1).
  * Built-ins: `L & L2` costs 2c + 1; each element costs \|adj[v]\| + \|L2\| + 4 = D + c + 4.
  * Total ≤ 2c² + 2cD + 62c + 92 ≤ 2(s+1)c² + 62c + 92.
* *All `parallel` calls.* ≤ (Λ_L²/2)·[…] = s²N²(s+1) + 31s²N²/c + 46s²N²/c² ≤ s²N²(s+17).
* *`find2`.* ≤ 2P_c ≤ 2s²ND calls. By Lemma UF on Λ_L nodes, each costs ≤ 19Λ_L + 10.
* *Instructions.* 9(Λ_L+1) + 9(sN+Λ_L) + 14(sND+sN) + 52(s²ND+sND).
* *Built-ins.* 2Λ_L + 5 + sN + 4sND + 18s²ND (incl. `tested.add`, 8 per new key).

      F ≤ 90s²ND + 70sND + 24sN + 20Λ_L + 14 + s²N²(s+17) + 38s²NDΛ_L.

* **× N/D** (with 38s²N²Λ_L = 38s³N³/c ≤ 12.67s³N³):
  **≤ 12.67s³N³ + 0.5s²N³ + 8.5sN³ + 90s²N² + 70sN² + 15.34N² + 3.5N.**

**G (classes, cover, 290–304).**
* *Loops.*
  * For@291: Λ_L iterations, Λ_L `find2` calls.
  * Number of classes Cn ≤ Λ_L.
  * After line 294: \|cls\| = s and Σ\|cl\| = Λ_L, so For@297 has s iterations and For@299 has Λ_L.
  * `cover \|= layers[li]` costs ≤ N + c + 2.
* *Instructions.* 15(Λ_L+1) + 10Cn + 26(Cn+1) + 19(s+1) + 9(Λ_L+s).
* *Total.*

      G ≤ 19Λ_L² + 86Λ_L + Λ_L·c(⌈lg c⌉ + 3) + Λ_L(c+1)⌈lg Λ_L⌉ + Λ_L·N + 31s + 66
        ≤ 3s²N² + sN² + sN(ℓ+32) + 2sNλ' + 31s + 66.

* **× N/D: ≤ 1.5sN³ + 0.5N³ + N²(16 + 0.5ℓ + λ') + 32N.**

**H (class_index, layer_index, class_images, 305–324).**
* *Loops.* For@306: s; For@307: Λ_L; DictComp@309: Λ_L; For@311: r; For@313: ≤ rs; genexpr@315: c each.
* *Instructions.* 9(s+1) + 7(Λ_L+s) + 8(Λ_L+1) + 11 + 23(r+1) + 38(rs+r) + 20rs(c+1) = 15Λ_L + 16s + 51 + 61r + rs(20c + 58).
* *Built-ins.* Λ_L(2c + 8) + s + 2 + rs(7c + 11) + 4r.
* **H ≤ Λ_L(2c+23) + 17s + 53 + 65r + rs(27c+69) ≤ 10sN + 17s + 53 + 65r + rs(27c+69).**
  **× N/D: ≤ 5N² + 21.75N + rN(13.5c + 50.75).**

**I (Gw, kernel, fibers, 325–353).**
* *Loops.*
  * For@336: s − 1.
  * For@337: ≤ Λ_L iterations, with per li `sorted` (SORT(c)) and the slice `L[1:]`.
  * For@339: ≤ sN.
  * `find3` calls: 2sN + N, each ≤ 19N + 10 (Lemma UF on N nodes).
  * For@344: N.
  * F := \|fibers\| ≤ N. `sorted(fib.values())` costs ≤ N⌈lg N⌉(N+1) + 3N + 2.
  * After line 347: DictComp@350 has c iterations (6N + 5c + 1 built-ins).
  * genexpr@351: r_N(c+2) + 1 `FOR_ITER`s and r_N(N + c) inner elements, where r_N := \|`Nk.gens`\|.
* *Instructions.* 9s + 16(Λ_L+s) + 24(sN+Λ_L) + 15(N+1) + 26(F+1) + 10(c+1) + 12 + 38(r_N(c+2)+1) + 20r_N(N+c).
* *Total.*

      I ≤ N²(38s + 19 + ℓ) + sN(63 + ℓ) + N(70 + ℓ) + 26s + 15c + r_N(27N + 64c + 77) + 111.

* **× N/D: ≤ 23.75N³ + 0.25ℓN³ + N²(49 + 0.75ℓ) + N(40.75 + 3.75c) + r_N(6.75N² + 16cN + 19.25N).**
* *Callees per heavy body.*
  * `C[action.GroupWithAction.__init__](N, s, r)`.
  * `C[action.GroupWithAction.kernel](N, s, r)`.
  * `C[group.PermGroup.induced_action](N, r_N; c blocks)`.

**J (353–362).**
* *Instructions.* ListComp@361: 7(Λ_L+1) + 8.
* *Built-ins and own callees.*
  * `factorial(c)`: c + 1.
  * The tuple compare: 3.
  * `list(Nk.gens)`: r_N + 1.
  * `CameronStructure.__init__`: ≤ k + 35, with k ≤ c.
* **J ≤ 11Λ_L + 2c + r_N + 57. × N/D: ≤ 1.84N² + 0.5cN + 0.25r_N N + 14.25N.**
* *Callee.* `C[group.PermGroup.order](c, r_N)` if t = 1, else `recognize_johnson(Nact)` = RJ(c, r_N) (below; Nact has degree c and ≤ r_N generators).

**Sum over the phases (per candidate).**

    HT(s,c) ≤ N³(12.67s³ + 0.5s² + 57.5s + 24.25 + 1.25ℓ) + 45sN^{2.5}
             + N²(90s² + 70s + 493 + 4.75ℓ + 6.75r_N) + N(174 + 4.25c + r(13.5c + 51) + r_N(16c + 19.5)).

**Sum over the candidates.** Use the Σ_cand s^j bounds, K_c ≤ LS/2, c ≤ √N, and 0.5S² ≤ 0.25S³ for S ≥ 2:

    Σ_cand HT ≤ LS·[N³(13S² + 70 + ℓ) + 45N^{2.5} + N²(90S + 317 + 3ℓ + 4r_N) + N(87 + 3√N + r(7√N+26) + r_N(8√N+10))].

**Bound (N ≥ 9).**

    RCAM(N, r; ts) ≤ 75 + CC(N, ts) + ORB(N, r)
        + LS·[N³(13S² + 70 + ℓ) + 45N^{2.5} + N²(90S + 527 + 3ℓ + 4r_N) + N(87 + 3√N + r(7√N+26) + r_N(8√N+10)) + 233]
        + (LS(N−1)/8)·[ C[action.GroupWithAction.__init__](N, S, r) + C[action.GroupWithAction.kernel](N, S, r)
                         + C[group.PermGroup.induced_action](N, r_N; √N) + max(C[group.PermGroup.order](√N, r_N), RJ(√N, r_N)) ].

* The number of heavy bodies is Σ_cand Q_D ≤ K_c(N−1)/4 ≤ LS(N−1)/8.
* r_N is the largest \|`Nk.gens`\| over the heavy bodies. By Lemma R, r_N ≤ max(6, ⌊log2 N!⌋).
* The constant 75 is 52 (outside) + 2 (import) + 21 (final iteration of For@193).
* In N alone (S ≤ L, ℓ ≤ L + 1, N ≥ 9): own work = O(N³ log⁴ N + r N^{1.5} log² N).
* **Solver calls:** none.

### johnson.johnson_phi

* **Profile.** outside 71; For@380 (18, 0); For@385 (67, 0); ListComp@386 (9, 8); For@395 (20, 4); genexpr@396 (20, 1 loop).
* **Parameters.** m = `jh.m`, t = `jh.t`, N := \|`jh.T_of_point`\| = \|img\|.
* **Assumptions.** img is a tuple of length N with values in range(N). The `T_of_point` entries are t-subsets of range(m). `point_of_T` is the inverse map; a missing key raises, which only shortens the call.
* **Loops.**
  * For@380 / For@385: m iterations.
  * ListComp@386: m per gamma.
  * For@395 over `enumerate(T_of)`: N iterations; its 4 entry instructions are the `raise` path.
  * genexpr@396: t elements.
* **Instructions** (t ≥ 2). 71 + 67(m+1) + m(9(m+1)+8) + 20(N+1) + 4 + 20N(t+1) = 9m² + 84m + 162 + N(20t + 40).
* **Built-ins** (t ≥ 2).
  * `[0]*m`: m + 1.
  * Per gamma: m + 18t + 16. This is `others` (m+1), the two slices, concatenations and frozensets (2(6t+2)), two lookups with t-set keys (4t+6), `&` (2t+1), `len`, `tuple(S)`, and the step.
  * `set(phi)` and `len`: 4m + 2.
  * Per p: 7t + 3 (frozenset, steps, comparison).
  * `tuple(phi)`: m + 1.
* **Bound for t = 1.** 113 + 18m + 60N instructions, plus 19m + 10N + 6 built-ins.
* **Bound.** **JP(m,t,N) ≤ 10m² + 18tm + 106m + 27tN + 43N + 168.**
* **Use.** Called once per generator of G (main.py:342), with N = number of blocks = binom(m, t).

### johnson.orbitals

* **Profile.** outside 21; ListComp@404 (20, 11), two clauses; lambda@405 (11).
* **Parameters.** n = G.n, r = \|G.gens\|.
* **Loops.**
  * ListComp@404 yields n (outer) + n² (inner) elements, with 1 entry.
  * The lambda is called by `orbits_on` once per (dequeued item, generator). Each of the L = n(n−1) items is enqueued exactly once (group.py lines 319–333), so there are r·n(n−1) calls.
* **Instructions.** 21 + 20(n² + n + 1) + 11 + 11r·n(n−1).
* **Built-ins.** `range` calls 1 + n, steps n + n². Total n² + 2n + 1.
* **Bound.** **ORB(n,r) ≤ (11r + 21)n² + 22n + 53 + C[group.PermGroup.orbits_on](n(n−1), r)**.
  The symbol excludes the act calls charged here.
* **Callers.**
  * `recognize_johnson` and `recognize_cameron`, on Gbar.
  * main.py `case_2b_structure`, on a group of degree \|Φ\| ≤ m.

### johnson.recognize_johnson

* **Profile.** outside 55; ListComp@418 (8, 9); For@421 (16, 0); For@422 (19, 2); For@428 (18, 4).
* **Trivial case.** N ≤ 1 returns at once.
* **Giant branch.**
  * `Gbar.order()`: `C[group.PermGroup.order](N, r)`.
  * `factorial(N)`: N + 1.
  * `list(Gbar.gens)`: r + 1.
  * ListComp@418: N iterations (6N + 1 built-ins).
  * JS(N, 1) ≤ 12N + 40.
* **Candidates (For@421 / For@422).**
  * For@421: t ∈ [2, N), so N − 2 iterations.
  * For@422, for each t: k runs over [2t+1, N] until the first k with binom(k, t) > N, which breaks.
    * Every k with binom(k, t) ≤ N satisfies k(k−1)/2 ≤ binom(k, t) ≤ N, because 2 ≤ t ≤ k − 2. Hence k < 1 + √(2N).
    * So I_t ≤ max(0, √(2N) − 2t + 1) + 1, and Σ_t I_t ≤ (N − 2) + (√(2N)/2)·√(2N) ≤ 2N.
    * The 2 entry instructions of For@422 are the `break` path, once per entry.
  * `comb(k, t)` costs k + 1.
    * In a non-breaking iteration, k < 1 + √(2N); there are ≤ N of them.
    * In a breaking iteration, k ≤ max(2t+1, 2 + √(2N)); there is one per t.
    * Total ≤ N(2 + √(2N)) + Σ_{t<N}(2t + 3 + √(2N)) ≤ N² + 4N + 2√2·N^{1.5}.
* **For@428.**
  * There are \|cand\| ≤ L candidates: they have distinct t, and 2^t ≤ binom(k, t) = N.
  * `_identify` is called only when `len(orbs) == t`, so **at most once** (the t are distinct).
* **Instructions.** ≤ 55 + 8(N+1) + 9 + 16N + 19·3N + 2N + 18(\|cand\|+1) + 4 = 83N + 18\|cand\| + 94.
* **Built-ins.** ≤ N² + 2.83N^{1.5} + 15N + r + 4 + 2\|cand\|.
* **Bound.**

      RJ(N,r) ≤ 22N² + 3N^{1.5} + 132N + 20L + r + 191 + 11rN(N−1) + ID(N, r, k, t)
                + C[group.PermGroup.order](N, r) + C[group.PermGroup.orbits_on](N(N−1), r)

* **Closed form** (substituting ID with t ≤ L, k ≤ √(3N)):

      RJ(N,r) ≤ 12L²N³ + 63N³ + 87L N^{2.5} + (289 + ℓ + 20r)N² + 3N^{1.5} + (154 + 33L + 65r)N + 202L + r + 360
                + C[group.PermGroup.order](N, r) + C[group.PermGroup.orbits_on](N(N−1), r)
                + L·(C[group.PermGroup.__init__](k, r) + C[group.PermGroup.order](k, r)).

* **Solver calls:** none.

### johnson._identify

* **Profile.**
  * outside 28.
  * Loops:

    | loop | (cycle, entry) | loop | (cycle, entry) |
    |---|---|---|---|
    | For@456 | (132, 9) | For@489 | (24, 0) |
    | ListComp@457 | (6, 8) | For@491 | (42, 4) |
    | For@458 | (10, 0) | For@510 | (25, 0) |
    | For@466 | (39, 0) | For@512 | (21, 0) |
    | For@470 | (15, 0) | For@522 | (31, 0) |
    | For@472 | (19, 0) | For@531 | (21, 0) |
    | For@483 | (58, 0) | For@533 | (28, 0) |

  * Generator expressions:

    | genexpr | @461 | @506 | @514 | @523 | @534 |
    |---|---|---|---|---|---|
    | instructions | 22 | 24 | 27 | 24 | 20 |

* **Parameters.** N = binom(k, t), t ≥ 2, k ≥ 2t+1, r = \|Gbar.gens\|, D := t(k−t). At the only call site \|orbs\| = t, and orbs is the partition into orbitals.
* **Facts.**
  * D ≥ 2(t+1) ≥ 6.
  * k² ≤ 3N, because k(k−1)/2 ≤ N and k ≤ N. Hence D < tk ≤ t√(3N).
  * k/D < 2/t ≤ 1.
  * tN/D = N/(k−t) ≤ N/3.
  * The orbitals passing the degree test (line 461) have \|o\| = ND, so their number is p ≤ (N−1)/D < N/D (and p ≤ t).

**Phase 1 (each of the t orbitals).**
* Instructions: 6(N+1) + 8 + 10(\|o\|+1) + 22(N+1).
* Built-ins: ≤ 5N + 5\|o\| + 4.
* Total ≤ 33N + 15\|o\| + 50. Summed: ≤ t(33N + 50) + 15N(N−1).

**Phase 2 (BFS).**
* For@466: N sources. For each source s:
  * the queue q gets each vertex at most once, so \|q\| ≤ N;
  * For@472 has Σ_p \|adj[p]\| ≤ ND iterations.
* Instructions per source: 15(N+1) + 19(ND+N). Built-ins per source: 2ND + 3N + 5 (list repetition, `max`, steps, appends).
* **≤ 21N²D + 37N² + 59N + 40. × p: ≤ 28N³ + 10N² + 7N.**

**Phase 3 (Lambda).**
* For@483: ≤ N iterations (x; it breaks when \|Lambda\| ≥ k).
* Per x:
  * For@489: D iterations.
  * For@491: ≤ \|classes\| ≤ D iterations per y. The classes are disjoint nonempty sets of neighbours. Its 4 entry instructions are `ok = False; break`.
  * Each iteration with y0 ∈ adj[y] computes two set intersections, cost ≤ 4D + 2.
  * After the check at line 506 there are t classes with Σ\|cl\| = D. So For@512 has D iterations, each running genexpr@514 over range(N) (N + 1 steps; ≤ N insertions).
  * Per class: frozenset, lookup and store, ≤ 8N + 12.
* Instructions per x: 42D² + 27ND + 142D + 46t + 73.
* Built-ins per x: 4D³ + 8D² + D⌈lg D⌉ + 10D + 5ND + 8tN + 12t + 6.
* **≤ 58N + 59 + N(4D³ + 50D² + D⌈lg D⌉ + 152D + 32ND + 8tN + 58t + 79).**
* × p, with 4N²D² ≤ 12t²N³ and 50N²D ≤ 87tN^{2.5}:
  **≤ 12t²N³ + 34.67N³ + 87tN^{2.5} + ℓN² + 194.2N² + 10N.**

**Phase 4 (T_of_point).**
* For@522: N iterations; genexpr@523 over `enumerate(members)` (k elements).
* `set(T_of_point)` costs N(2t + 4) + 2.
* **≤ N(32k + 2t + 64) + 2k + 35. × p: ≤ 44N² + 8N.**

**Phase 5 (phi_gens).**
* For@531: r; For@533: k per g.
* Σ_C \|C\| = tN, since each w lies in exactly t members after Phase 4.
* **≤ 27rtN + 56rk + 52r + 21. × p: ≤ 9rN² + 65rN + 4N.**

**Phase 6.**
* Built-ins and own callees: `factorial(k)`: k + 1; JS(N, t).
* **Own ≤ 42 + k + N(2t + 10). × p: ≤ 3N² + 8N.**
* Callees, ≤ t times in total (p ≤ t): `C[group.PermGroup.__init__](k, r)` + `C[group.PermGroup.order](k, r)`.

**Bound** (outside + For@456: 28 + 132(t+1) + 9).

    ID(N,r,k,t) ≤ 12t²N³ + 63N³ + 87t N^{2.5} + (267 + ℓ + 9r)N² + (22 + 33t + 65r)N + 182t + 169
                  + t·(C[group.PermGroup.__init__](k, r) + C[group.PermGroup.order](k, r)).

**Solver calls:** none.

---------------------------------------------------------------------------------------------

## 3. `babai_gi/certificates.py` (source order)

Common assumptions, which hold for the callers main.py:290–291, 343–344 and `aggregate`:
* `jd.blocks` is a partition of range(n) into nb blocks.
* `jd.T_of_block` lists nb distinct t-subsets of range(m).
* Group elements are tuples that are permutations.
* `jd.Gw` has m = \|Γ\|.

### 3.1 certificates.JohnsonData.__init__

* **Profile.** outside 72; DictComp@55 (6, 12); For@57 (8, 0); For@58 (7, 0); For@63 (11, 4).
* **Loops.**
  * DictComp@55: nb iterations.
  * For@57: nb.
  * For@58: Σ\|blk\| = n in total, nb entries.
  * For@63 over `zip(Gw.G.gens, Gw.phi_gens)`: ≤ r iterations. Its entry instructions are the `fn = None; break` path.
* **Instructions.** 72 + 6(nb+1) + 12 + 8(nb+1) + 7(n+nb) + 11(r+1) + 4 = 113 + 21nb + 7n + 11r.
* **Built-ins.**
  * frozenset-key insertions nb(2t + 4) + 1.
  * Dict stores 4n.
  * The comparisons `fn(g) != p` of m-tuples: r(m + 2) + 1.
  * The import: 2.
  * Total nb(2t+5) + 4n + r(m+2) + 5.
* **Callees.**
  * `_make_fast_phi`: MFP, only if `Gw.phi_fn is None` (always so for the package callers).
  * r calls of the returned function: PF.
  * `C[tower.Tower.trivial](n)` if `tower is None` (never for the package callers).
* **Bound.**

      JD ≤ 118 + 11n + nb(2t+26) + r(m+13) + MFP + r·PF
         ≤ 10m² + 16tm + 100m + 11n + nb(2t+38) + r(m(2t+52) + 63) + 271   [+ C[tower.Tower.trivial](n)].

### 3.2 certificates.JohnsonData._make_fast_phi, phi_fn, phi_fn2

**`_make_fast_phi`.**
* **Profile.** outside 84; For@78 (24, 0); ListComp@83 (9, 9); For@92 (68, 0); ListComp@93 (9, 8).
* **t = 1.**
  * For@78: m iterations, each costing 13 built-ins: a frozenset of 1, `get` with a key of size 1, append, step.
  * ListComp@83: nb iterations (`next(iter(T))`).
  * Total: 126 + 24m + 9nb + 1 + 13m + 3nb ≤ 127 + 37m + 12nb.
* **t ≥ 2.**
  * `m < 2t−1` returns None.
  * Otherwise For@92: m iterations, with ListComp@93 of m iterations inside.
  * Built-ins per gamma: m + 16t + 15 (`others`, two slices/concatenations/frozensets of ≤ t elements, two `get`s with t-set keys, append).
  * Total: 9m² + 85m + 152 + 1 + m(m + 16t + 15).
* **Bound.** **MFP ≤ 10m² + 16tm + 100m + 12nb + 153.**

**`phi_fn(g)`** (t = 1).
* **Profile.** outside 16; genexpr@86 (24) over `reps` (m elements).
* **Built-ins.** `tuple` m + 1, lookups 3m, steps m.
* **Bound.** **PF1 ≤ 29m + 41.**

**`phi_fn2(g)`** (t ≥ 2).
* **Profile.** outside 12; For@103 (37, 0) over `pairs` (m iterations).
* **Built-ins per iteration.** Two int lookups, `&` of two t-sets (2t + 1), `len`, `next(iter())`, append, step: ≤ 2t + 13. `tuple(out)` adds m + 1.
* **Bound.** **PF2 ≤ m(2t + 51) + 50.**

**Combined.** PF := max(PF1, PF2) ≤ m(2t + 51) + 50. This is the cost of `Gw.phi(g)` beyond the dispatch in action.py, once JohnsonData has installed the fast phi.

### 3.3 certificates.JohnsonData.omega_of

* **Profile.** outside 15; For@115 (16, 0).
* **Parameters.** a := \|A\|.
* **Loop.** For@115 over `block_of_T.items()`: ≤ nb iterations.
* **Built-ins.**
  * Per item: step 1, `T <= A` (t + a + 1), `update` call 1.
  * `update` elements: Σ\|B_i\| ≤ n, at 4 each. The blocks of distinct keys are distinct blocks of a partition.
  * `set()`: 1. `frozenset(out)`: 4n + 1.
* **Bound.** **OM(a) ≤ 31 + 16nb + nb(t + a + 3) + 8n + 2 ≤ nb(t + a + 19) + 8n + 33.**
* **Callers.** `colored_string` (a = k), main.py `top_action` (a = \|Φ\| ≤ m).

### 3.4 certificates.JohnsonData.is_primitive

* **Profile.** outside 10.
* **Bound.** Two `len`: **≤ 12.**

### 3.5 certificates.Iteration.__init__

* **Profile.** outside 12.
* **Bound.** **12.**

### 3.6 certificates.Certificate.__init__

* **Profile.** outside 45; genexprs@146 (20 and 19 instructions, 1 loop each) over `iterations`.
* **Parameters.** ℓ := \|iterations\|.
* **Instructions.** ≤ 45 + 20(ℓ+1) + 19(ℓ+1) = 84 + 39ℓ.
* **Built-ins.** `sorted(A)`: SORT(k). The two `tuple`s and their `len` calls: 5ℓ + 2. `len(W)`: 1.
* **Callees.** `it.H_old_A.order()` for each iteration, and `HA.order()`. These groups have degree k.
* **Bound.** **CE(k,ℓ) ≤ 44ℓ + k⌈lg k⌉ + 2k + 89 + Σ_{i≤ℓ} C[group.PermGroup.order](k, r_{A,i}) + C[group.PermGroup.order](k, r_HA).**

### 3.7 certificates.restrict_to

* **Profile.** outside 25; DictComp@151 (6, 12); genexpr@152 (22, 1 loop).
* **Parameters.** L := \|pts\|.
* **Instructions.** 25 + 6(L+1) + 12 + 22(L+1) = 65 + 28L.
* **Built-ins.** `enumerate` and insertions: 4L + 1. `tuple`, lookups, steps: 5L + 1.
* **Bound.** **RT(L) ≤ 37L + 67.**

### 3.8 certificates.is_giant_on

* **Profile.** outside 18.
* **k ≤ 2.** ≤ 18.
* **Otherwise.** `factorial(k)`: k + 1. Callees: `PermGroup(k, gens)` and its `order()`, with g := \|gens\|.
* **Bound.** **IG(k,g) ≤ k + 19 + C[group.PermGroup.__init__](k, g) + C[group.PermGroup.order](k, g).**

### 3.9 certificates.LocalCertificates.__init__

* **Profile.** outside 30.
* **Built-ins.** `tuple(x)`: n + 1.
* **Bound.** **≤ n + 31.**

### 3.10 certificates.LocalCertificates.setwise_stabilizer

* **Profile.** outside 71; ListComp@179 (9, 9).
* **Loop.** ListComp@179 over `range(m)`: m iterations; the `v not in A` lookups cost 3 each.
* **Instructions.** 71 + 9(m+1) + 9 = 89 + 9m.
* **Built-ins.**
  * `sorted(A)`: SORT(k).
  * The ListComp: 4m + 1.
  * List `+` of ≤ 4 permutations: 5.
  * `len` ×2.
  * `factorial(k)`: k + 1. `factorial(m−k)`: m − k + 1.
  * Total k⌈lg k⌉ + 2k + 5m + 12.
* **Gens.** `intersect_image` returns ≤ 8 permutations: ≤ 4 if G^φ is Sym, otherwise `even_subgroup_gens` returns ≤ 2·4.
* **Callees.**
  * `C[perm.sym_gens](k, m)` + `C[perm.sym_gens](m−k, m)`.
  * `C[action.GroupWithAction.intersect_image](n, m, r; 4)`.
  * `C[action.GroupWithAction.image_is_sym](n, m, r)`.
  * `C[action.GroupWithAction.preimage](n, m, r; 8)`.
  * `C[group.PermGroup.order](n, r_pre)`.
  * `C[action.GroupWithAction.subgroup](n, m, r_pre)`, where r_pre = \|H.gens\| of the preimage group, ≤ ρ by Lemma R.
* **Assumption.** G^φ is a giant (else `intersect_image` raises). This holds in the Johnson case.
* **Bound.** **SW ≤ 14m + k⌈lg k⌉ + 2k + 101 + (callees).**

### 3.11 certificates.LocalCertificates.image_on_A

* **Profile.** outside 15; ListComp@188 (7, 9).
* **Loop.** r_H iterations.
* **Instructions.** 31 + 7r_H.
* **Built-ins.** `len` + steps: r_H + 1.
* **Callees.** r_H × RT(k), and `C[group.PermGroup.__init__](k, r_H)`.
* **Bound.** **IOA(r_H) ≤ r_H(37k + 75) + 32 + C[group.PermGroup.__init__](k, r_H).**

### 3.12 certificates.LocalCertificates.affected

* **Profile.** outside 29; For@201 (7, 0); For@202 (8, 0); For@204 (20, 0).
* **Loops.** `PermGroup.orbits()` returns lists partitioning range(n): every point is put in exactly one orbit through `seen` (group.py lines 285–301).
  * For@201: ω_N ≤ n iterations.
  * For@202: Σ\|orb\| = n iterations, ω_N entries.
  * For@204: ω_H ≤ n iterations.
  * Every u has a `norb` entry, so `norb[orb[0]]` never fails.
* **Instructions.** ≤ 29 + 7(ω_N+1) + 8(n+ω_N) + 20(ω_H+1) ≤ 43n + 56.
* **Built-ins.**
  * Stores into `norb`: 4n.
  * Steps: 2n.
  * Per H-orbit: 6.
  * `update`: 4n.
  * `frozenset`: 4n + 1.
  * Total ≤ 20n + 2.
* **Callees.** KL(H, A_sorted), `C[group.PermGroup.orbits](n, r_N)`, `C[group.PermGroup.orbits](n, r_H)`.
* **Bound.** **AFF ≤ 63n + 58 + KL + C[group.PermGroup.orbits](n, r_N) + C[group.PermGroup.orbits](n, r_H).**

### 3.13 certificates.LocalCertificates.kernel_and_lifts

* **Profile.** outside 101; ListComp@215 (7, 9); While@220 (17, 12); ListComp@223 (7, 9); For@225 (27, 0); genexpr@219 (20); genexpr@227 (27).
* **Loops.**
  * ListComp@215 and genexpr@219: k elements each.
  * **While@220:**
    * Variant: kA increases by 1 per iteration, and each iteration requires `levels[kA].b ∈ Aset` = n + A.
    * The forced prefix [n+a for a in A_sorted] is duplicate-free, so by Lemma B(a) the base points are distinct.
    * Hence kA ≤ \|Aset\| = k, and the loop has ≤ k iterations.
  * ListComp@223: r_K iterations, each with a slice of length n.
  * **For@225:** λ = ∏_{i<kA} \|`levels[i].trans`\| iterations (B2).
    * Under INV-A, B1 with X = n + A gives λ ≤ k!/(k−kA)! ≤ k!.
    * Unconditionally, B1 with X = n + range(m) gives λ ≤ m!/(m−k)!.
    * Per iteration: the slice `r[:n]` costs n + 1; genexpr@227 makes k calls `A_sorted.index` (each ≤ k + 1), plus `tuple` and steps.
* **Instructions.** 101 + [7(k+1) + 9] + [17(k+1) + 12] + [7(r_K+1) + 9] + 27(λ+1) + 20(k+1) + 27(k+1)λ = 209 + 44k + 7r_K + λ(27k + 54).
* **Built-ins.**
  * Key tuple: k + 1.
  * `key in H.cache` and the store: 2(2k + 11).
  * `set` of k ints: 5k + 1.
  * While tests: 4(k + 1).
  * Slices: r_K(n + 2).
  * Per lift: n + k² + 3k + 4.
* **Callees.**
  * `C[group.PermGroup.known_order_or_none]`.
  * `C[group.PermGroup.__init__](n+m, r_H; prefix k)`.
  * `C[group.PermGroup.levels](n+m, r_H)`.
  * `C[group.PermGroup.level_group](n+m, r_H)`.
  * `C[group.PermGroup.order](n+m, r_K)`.
  * `C[group.PermGroup.__init__](n, r_K)`.
  * `C[group.PermGroup.coset_reps_prefix](n+m, kA; λ)`.
  * Here r_K = \|K.gens\| ≤ ρ (Lemma R).
* **Cache.** If `key in H.cache` holds, only the outside part runs: ≤ 101 + 5k + 23.
* **Bound.**

      KL ≤ 238 + 59k + r_K(n + 9) + λ(n + k² + 30k + 58) + (callees)
         ≤ 238 + 59k + r̂(n + 9) + k!(n + k² + 30k + 58) + (callees)                [INV-A].

### 3.14 certificates.LocalCertificates.conjugate (with cj, cj_group)

* **Profile.**
  * outside 141.
  * Loops: ListComp@246 (8, 9); DictComp@251 (6, 11); ListComp@252 (7, 8); For@254 (58, 0); For@257 (32, 0); For@260 (12, 0); ListComp@264 (7, 12).
  * Inner defs: `cj` (10); `cj_group` (19; ListComp@243 (8, 9)).
  * Generator expressions: @245 (20) and @263 (20, 20).
* **Parameters.** ℓ = \|cert.iterations\|, λ_i = \|it_i.lifts\|, Λ = Σλ_i, R_N = Σ\|it_i.N.gens\|, r_H = \|cert.H.G.gens\|, r_K = \|cert.K.gens\| (0 if K is None).
* **Loops.**
  * For@254: ℓ iterations.
  * For@257: Λ in total.
  * For@260 over `enumerate(sbar)`: k per lift. `sbar` is a k-tuple built by `kernel_and_lifts`.
  * ListComp@264: λ_i per iteration.
  * `cj` is called r_H + Λ + R_N + r_K times; `cj_group` ℓ + 1 times.
  * genexpr@245: \|W\| ≤ n elements. genexpr@263: \|W_old\| + \|W_new\| ≤ 2n per iteration.
* **Instructions.**

      304 + 18r_H + 13k + ℓ(40n + 197) + Λ(12k + 61) + 18(R_N + r_K) + 20n

  This includes Iteration.__init__ (12ℓ).
* **Built-ins.** k⌈lg k⌉ + 12k + 5n + r_H + R_N + r_K + ℓ(10n + 4) + Λ(3k + 6) + 135.
  * `sorted(A2)`.
  * Frozensets 5 per element.
  * `pos2` and `rho` dict operations.
  * Per lift: `[0]*k`, `enumerate`, `tuple`, appends.
  * Certs store: 2k + 3.
  * Stats: 128.
* **Callees in this module.** IOA(r_{H2} ≤ r_H) and CE(k, ℓ).
* **Bound.**

      CJ ≤ 560 + 2k⌈lg k⌉ + 27k + 25n + r_H(37k + 94) + 19(R_N + r_K) + ℓ(50n + 245) + Λ(15k + 67) + (callees)
         ≤ 560 + 2k⌈lg k⌉ + 27k + 25n + r̂(37k + 19n + 132) + (n+1)(50n + 245) + (n+1)k!(15k + 67) + (callees)

  The second line uses ℓ ≤ n + 1, Λ ≤ ℓk!, R_N ≤ ℓr̂.
* **Callees.**
  * `C[perm.inv](n)`.
  * 2(r_H + Λ + R_N + r_K)·`C[perm.mul](n)`.
  * (ℓ + 2)·`C[group.PermGroup.known_order_or_none]`.
  * `C[action.GroupWithAction.subgroup](n, m, r_H)`.
  * `C[group.PermGroup.__init__](k, r_H)` (in IOA).
  * `C[action.GroupWithAction.phi](n, m)`.
  * Σ_i `C[group.PermGroup.__init__](n, r_{N,i})` + `C[group.PermGroup.__init__](n, r_K)`.
  * Σ_i `C[group.PermGroup.__init__](k, λ_i)`.
  * The orders in CE.
* **Solver calls:** none.

### 3.15 certificates.LocalCertificates.recompute

* **Profile.** outside 67; ListComp@274 (6, 12); For@277 (36, 0).
* **Loops.** λ = \|lifts\| iterations for both. λ ≤ k! under INV-A (§3.13).
* **Instructions.** 67 + 6(λ+1) + 12 + 36(λ+1) + 12 (Iteration) = 133 + 42λ.
* **Built-ins.**
  * Steps: λ.
  * `sorted(W_new)`: SORT(w) with w = \|W_new\| ≤ n.
  * Appends: λ.
  * `list(Hgroup.gens) + [rep]`: 2r_Hg + 3.
* **Callees.**
  * KL(H, A_sorted).
  * `C[group.PermGroup.__init__](k, λ)`.
  * λ·(`C[perm.inv](n)` + `C[perm.act_string](n)` + `C[perm.mul](n)`).
  * `C[group.generated_subcoset](n, π ≤ λ, R)`, where R is the total generator count of the pieces.
  * `C[action.GroupWithAction.subgroup](n, m, r_Hg + 1)`.
* **Solver calls.** **exactly λ** calls `solver.iso_window(N, x, x^{σ^{-1}}, sorted(W_new), jd.tower)`.
  * N = ker(H → S(A)), degree n.
  * Window size w = \|W_new\|.
  * Strings of length n.
* **Bound.** **RC ≤ 139 + 45λ + w⌈lg w⌉ + 2w + 2r_Hg + KL + (callees) ≤ 139 + 45k! + n⌈lg n⌉ + 2n + 2r̂ + KL + (callees)** [INV-A].
* **Cache hit inside `certificate`.**
  * In `certificate`, each `recompute(H, A_sorted, …)` is preceded by `affected(H, A_sorted)` on the same object H. The fallback call is preceded by it as well: the loop exited through `aff <= W`, right after `affected`.
  * That call leaves `H.cache[("kl", tuple(A_sorted))]` set, by line 229 or because it was already there. Nothing removes entries; the only uses of `GroupWithAction.cache` are certificates.py lines 212, 213 and 229.
  * So that KL is a cache hit costing ≤ 5k + 124. The bounds below nevertheless charge the full KL.

### 3.16 certificates.LocalCertificates.certificate

* **Profile.** outside 184; While@301 (58, 1); ListComp@318 (9, 9); ListComp@319 (12, 8).
* **Iteration bound for the while loop.**
  * Every execution of the body either breaks (at most once, the last) or calls `recompute` and replaces W by W ∪ aff with aff ⊄ W, a strict growth.
  * aff ⊆ range(n), because it is a union of `H.G.orbits()`.
  * If \|W\| = n then aff ⊆ W, so the loop breaks.
  * Hence **J ≤ n** recompute calls in the loop, and B ≤ J + 1 ≤ n + 1 body executions.
* **Better bound J ≤ ⌊n/3⌋, under INV-W.**
  * W_i is a union of H_i-orbits. By induction, aff(H_{i−1}) and W_{i−1} are unions of H_{i−1}-orbits, and H_i ≤ H_{i−1}.
  * So aff ∖ W is a nonempty union of H-orbits O with \|O\| > 2\|u^N\| ≥ 2, i.e. \|O\| ≥ 3.
  * Hence \|W\| grows by at least 3 per round.
* **Fallback.** At most one more `recompute`, with W_new = range(n). It is unreachable under `Params.paper()` (CORRECTNESS.md, Theorem B; Lemma 10.3 treats this `fallback`).
* **Instructions.** 184 + 58(B+1) + 1 + 9(n+1) + 9 + 12(r_K+1) + 8 = 58B + 9n + 12r_K + 281.
* **Built-ins.**
  * `frozenset(A)`: 4k + 1.
  * Two `certs` lookups: 2(2k + 3).
  * SORT(k).
  * Per body: `aff <= W` and `W | aff`, ≤ 2n + 1 each, an append, stats → 4n + 131.
  * ListComp@318: 4n + 1.
  * Fallback: import, stats, `frozenset(range(n))`, the comparison, append → 7n + 134.
  * Certs store: 2k + 3.
  * Stats: 128.
* **Own part.** **≤ B(4n + 189) + 20n + 13r_K + k⌈lg k⌉ + 12k + 558.**
* **Callees in this module.**
  * SW once.
  * IOA ≤ B + 2 times.
  * IG ≤ B + 2 times (with g ≤ r_H, resp. g = r_K).
  * AFF ≤ B times.
  * RC ≤ J + 1 times.
  * KL ≤ B + J + 1 ≤ 2J + 2 times.
  * RT(k) r_K times (`Kimgs`).
  * CE(k, ℓ) with ℓ ≤ J + 1.
* **Bound** (all of the above substituted, λ ≤ k!, r_H, r_K ≤ r̂):

      CERT ≤ (J+1)·[ k!(2n + 2k² + 60k + 161) + n⌈lg n⌉ + 69n + r̂(2n + 37k + 95) + 119k + 957 ]
             + r̂(111k + 230) + 3k⌈lg k⌉ + 18k + 20n + 14m + 850 + (callees),     J ≤ n  (J ≤ ⌊n/3⌋ under INV-W).

* **Callees outside the module.**
  * Those of SW, once.
  * (J+3)·[2·`C[group.PermGroup.__init__](k, r̂)` + `C[group.PermGroup.order](k, r̂)`], from IOA and IG.
  * (2J+2)·[`C[group.PermGroup.known_order_or_none]` + `C[group.PermGroup.__init__](n+m, r̂; prefix k)` + `C[group.PermGroup.levels](n+m, r̂)` + `C[group.PermGroup.level_group](n+m, r̂)` + `C[group.PermGroup.order](n+m, r̂)` + `C[group.PermGroup.__init__](n, r̂)` + `C[group.PermGroup.coset_reps_prefix](n+m, k; k!)`], from KL.
    * J + 1 of these calls are in fact cache hits, see §3.15.
  * (J+1)·[`C[group.PermGroup.orbits](n, r̂)` ×2], from AFF.
  * (J+1)·[`C[group.PermGroup.__init__](k, k!)` + k!(`C[perm.inv](n)` + `C[perm.act_string](n)` + `C[perm.mul](n)`) + `C[group.generated_subcoset](n, k!, R)` + `C[action.GroupWithAction.subgroup](n, m, r̂+1)`], from RC.
  * `C[group.PermGroup.pointwise_stabilizer](n, r̂; n)`.
  * r_K·`C[action.GroupWithAction.phi](n, m)`.
  * `C[errors.fallback]`.
  * (J+2)·`C[group.PermGroup.order](k, r̂)`, from CE.
* **Solver calls.** Through RC, ≤ (J+1)·k!; see Section 4.
* **Cached call** (A already in `self.certs`): ≤ 184 + 8k + 10, no solver call.

### 3.17 certificates.LocalCertificates.colored_string

* **Profile.** outside 24; genexpr@344 (29) over range(n).
* **Instructions.** 24 + 29(n+1).
* **Built-ins.** 5n + 2.
* **Callee.** OM(k).
* **Bound.** **CS ≤ 42n + 88 + nb(t + k + 19).**

### 3.18 certificates.LocalCertificates.compare

* **Profile.** outside 197; ListComp@357 (10, 8); ListComp@358 (10, 8); For@359 (7, 0); For@361 (7, 0); For@383 (38, 0); For@387 (59, 0); genexpr@389 (20); genexpr@400 (20).
* **Assumptions.**
  * `other` is a LocalCertificates object of the same `jd`; in `case_3` both come from `aggregate(jd, ·, k)`.
  * \|cert.A\| = \|cert2.A\| = k.
* **Loops.**
  * ListComps 357/358: m iterations each.
  * For@359: k. For@361: m − k.
  * For@383 over `zip(iterations, iterations2)`: ≤ ℓ := \|cert.iterations\| ≤ n + 1.
  * For@387: λ_i ≤ k! lifts per iteration (the lifts were computed under INV-A). Total Λ ≤ ℓk!.
  * genexpr@389: w_i = \|W_new,i\| ≤ n elements per lift. genexpr@400: \|W\| ≤ n.
* **Instructions.** 197 + 2[10(m+1) + 8] + 7(k+1) + 7(m−k+1) + 38(ℓ+1) + 59(Λ + ℓ) + 20Σ_i λ_i(w_i + 1) + 20(\|W\| + 1) ≤ 305 + 27m + 97ℓ + Λ(20n + 79) + 20n.
* **Built-ins.** ≤ 22 + 13m + 3ℓ + ℓ(n⌈lg n⌉ + 2n + 2) + Λ(7n + 4) + 7n.
  * The invariant comparison: tuple of 5 plus two ℓ-tuples, ≤ 2ℓ + 8.
  * `list(range(m))`.
  * The two rest-lists: 8m + 2.
  * zips.
  * `tuple(tau_bar)`.
  * The parity fix: 2m + 4.
  * `sorted(W_new)` per iteration.
  * Per lift: frozenset 5w_i + 1, `!=` ≤ 2n + 1, append, step.
  * Final check: 7n + 2.
* **Callees in this module.** 2·CS (self and `other`).
* **Bound.**

      CMP ≤ 503 + 40m + 111n + 2nb(t + k + 19) + ℓ(n⌈lg n⌉ + 2n + 102) + Λ(27n + 83) + (callees)
          ≤ 503 + 40m + 111n + 2n(t + k + 19) + (n+1)(n⌈lg n⌉ + 2n + 102) + (n+1)k!(27n + 83) + (callees).

* **Callees.**
  * `C[action.GroupWithAction.image_is_sym](n, m, r)`.
  * `C[perm.parity](m)`.
  * `C[action.GroupWithAction.lift](n, m, r)`.
  * Λ·`C[perm.mul](n)`.
  * Λ'·(`C[perm.inv](n)` + `C[perm.act_string](n)` + `C[perm.mul](n)`), where Λ' ≤ Λ is the number of lifts passing the window test.
  * Σ_{i≤ℓ} `C[group.generated_subcoset](n, ≤ λ_i, R_i)`.
  * `C[action.Coset.__init__](n)`.
* **Solver calls.** Λ' ≤ ℓ·k! (Section 4).
* **Early exit.** If the invariants differ, the function returns before any loop: ≤ 197 + 2ℓ + 8.

### 3.19 certificates.LocalCertificates.ordered_label

* **Profile.** outside 36; DictComp@406 (6, 12); For@409 (22, 0); genexprs@407 and @410 (20 each).
* **Assumption.** T is a k-tuple of elements of `cert.A`. The caller (main.py `case_3`) passes images of `permutations(sorted(A), k)`.
* **Loops.**
  * DictComp@406 and genexpr@407: k each.
  * For@409 over `cert.HA.elements()`: E elements. HA is a group of degree k, so E ≤ k! unconditionally by B2.
  * genexpr@410: k per element.
* **Instructions.** 36 + 6(k+1) + 12 + 22(E+1) + 20(k+1) + 20(k+1)E = 96 + 26k + E(20k + 42).
* **Built-ins.** 9k + 2 + E(3k + 3): the tuples, the comparison `q < best` (≤ k + 1), the steps.
* **Bound.** **OL ≤ 98 + 35k + E(23k + 45) + C[group.PermGroup.elements](k, r_HA; E) ≤ 98 + 35k + k!(23k + 45) + C[group.PermGroup.elements](k, r_HA; k!).**

---------------------------------------------------------------------------------------------

## 4. Solver calls (recursion; only the call instructions are in the bounds above)

| caller | call | how many per call of the caller | window | group |
|---|---|---|---|---|
| `recompute(H, A_sorted, W_new, x)` | `self.solver.iso_window(N, x, act_string(x, inv(σ)), sorted(W_new), jd.tower)` | exactly λ = \|lifts\| = \|H^A\| (one per lift). λ ≤ k! under INV-A, ≤ m!/(m−k)! always | \|W_new\| ≤ n | N = ker(H → S(A)) = `PermGroup(n, …)`, degree n |
| `certificate(A)`, round i = 1..J of the while loop | via `recompute` | λ_{i−1} ≤ k! | W_i, with ∅ ⊊ W_1 ⊊ … ⊊ W_J ⊆ Ω; \|W_i\| ≥ i (≥ 3i under INV-W) | N_i = ker(H_{i−1} → S(A)) |
| `certificate(A)`, fallback (unreachable under the paper preset, CORRECTNESS.md Theorem B) | via `recompute` | ≤ k! | Ω (size n) | ker(H_J → S(A)) |
| `certificate(A)` total |  | **≤ (J+1)·k! ≤ (n+1)·k!** (≤ (⌊n/3⌋+1)·k! under INV-W; ≤ J·k! without fallback; 0 if A is cached) |  |  |
| `compare(cert, other, cert2)`, round i = 1..ℓ | `self.solver.iso_window(it.N, x_A, act_string(y_A, inv(π)), sorted(it.W_new), jd.tower)` | ≤ λ_i ≤ k!: one per lift σ whose π = σπ_0 passes the window test | \|W_i\| ≤ n | it.N = N_i, degree n |
| `compare` total |  | **≤ ℓ·k! ≤ (n+1)·k!** (0 if the invariants differ) |  |  |

No other function of the two modules calls the solver. johnson.py makes no solver calls.

---------------------------------------------------------------------------------------------

## 5. Final table

Notation: ⌈lg⌉ = ⌈log2⌉. In certificates.py, r̂ is the largest generator count (≤ ρ = max(6, ⌊log2 (n+m)!⌋) by Lemma R) and J ≤ n (≤ ⌊n/3⌋ under INV-W).

Callees in johnson.py and certificates.py are substituted. "+ ext" stands for the external callees listed in the subsection.

### johnson.py

| function | closed-form bound (one call) |
|---|---|
| `subsets_of(m,t)` | (2t+9)·binom(m,t) + m + 32 |
| `pairs_of(m)` [tests only] | 13·binom(m,2) + m + 38 |
| `induced_on_subsets(L subsets of size t)` | L(t⌈lg t⌉ + 26t + 59) + 47 |
| `johnson_group_gens(m,t)` [tests only] | binom(m,t)(2t⌈lg t⌉ + 56t + 137) + 2m + 205 + 2·C[perm.from_cycles](m, ≤m) |
| `JohnsonStructure.__init__(L points, t)` | L(2t+10) + 40 |
| `JohnsonStructure.__repr__`, `CameronStructure.__repr__` | diagnostics |
| `CameronStructure.__init__` | k + 35 |
| `recognize_hamming` [tests only] | 7 + RCAM(N, r; ts=(1,)) |
| `_cameron_candidates(N, ts)` = CC | N < 9: 20; else bounded in ownwork.md §3.2 |
| `iroot(N, s)` | bounded in ownwork.md §3.1 |
| `recognize_cameron(N, r)` = RCAM | N < 9: 82; else 75 + CC(N,ts) + (11r+21)N² + 22N + 53 + C[group.PermGroup.orbits_on](N(N−1), r) + LS·[N³(13S² + 70 + ℓ) + 45N^{2.5} + N²(90S + 527 + 3ℓ + 4r_N) + N(87 + 3√N + r(7√N+26) + r_N(8√N+10)) + 233] + (LS(N−1)/8)·[C[action.GroupWithAction.__init__](N,S,r) + C[action.GroupWithAction.kernel](N,S,r) + C[group.PermGroup.induced_action](N, r_N; √N) + max(C[group.PermGroup.order](√N, r_N), RJ(√N, r_N))] |
| `johnson_phi(img, jh)` (m, t, N points) | 10m² + 18tm + 106m + 27tN + 43N + 168 |
| `orbitals(G)` (n, r) | (11r+21)n² + 22n + 53 + C[group.PermGroup.orbits_on](n(n−1), r) |
| `recognize_johnson(N, r)` = RJ | 12L²N³ + 63N³ + 87L N^{2.5} + (289 + ℓ + 20r)N² + 3N^{1.5} + (154 + 33L + 65r)N + 202L + r + 360 + C[group.PermGroup.order](N,r) + C[group.PermGroup.orbits_on](N(N−1),r) + L·(C[group.PermGroup.__init__](k,r) + C[group.PermGroup.order](k,r)), with k ≤ √(3N) |
| `_identify(N, r, k, t)` | 12t²N³ + 63N³ + 87t N^{2.5} + (267 + ℓ + 9r)N² + (22 + 33t + 65r)N + 182t + 169 + t·(C[group.PermGroup.__init__](k,r) + C[group.PermGroup.order](k,r)) |

### certificates.py

| function | closed-form bound (one call) |
|---|---|
| `JohnsonData.__init__` | 10m² + 16tm + 100m + 11n + nb(2t+38) + r(m(2t+52) + 63) + 271 [+ C[tower.Tower.trivial](n) if tower is None] |
| `JohnsonData._make_fast_phi` | 10m² + 16tm + 100m + 12nb + 153 |
| `…<phi_fn>` / `…<phi_fn2>` | 29m + 41 / m(2t+51) + 50 |
| `JohnsonData.omega_of(A)`, a = \|A\| | nb(t + a + 19) + 8n + 33 |
| `JohnsonData.is_primitive` | 12 |
| `Iteration.__init__` | 12 |
| `Certificate.__init__` | 44ℓ + k⌈lg k⌉ + 2k + 89 + (ℓ+1)·C[group.PermGroup.order](k, ≤ρ) |
| `restrict_to(p, L pts)` | 37L + 67 |
| `is_giant_on(k, g gens)` | k + 19 + C[group.PermGroup.__init__](k,g) + C[group.PermGroup.order](k,g) |
| `LocalCertificates.__init__` | n + 31 |
| `setwise_stabilizer` | 14m + k⌈lg k⌉ + 2k + 101 + ext (sym_gens ×2, intersect_image(n,m,r;4), image_is_sym, preimage(n,m,r;8), order(n,·), subgroup(n,m,·)) |
| `image_on_A` | r_H(37k+75) + 32 + C[group.PermGroup.__init__](k, r_H) |
| `affected` | 63n + 58 + KL + C[group.PermGroup.orbits](n, r_N) + C[group.PermGroup.orbits](n, r_H) |
| `kernel_and_lifts` = KL | 238 + 59k + r̂(n+9) + k!(n + k² + 30k + 58) + ext (PermGroup(n+m) init/levels/level_group/order, PermGroup(n) init, coset_reps_prefix(n+m, k; ≤k!)) |
| `conjugate` | 560 + 2k⌈lg k⌉ + 27k + 25n + r̂(37k + 19n + 132) + (n+1)(50n + 245) + (n+1)k!(15k + 67) + ext |
| `recompute` | 139 + 45k! + n⌈lg n⌉ + 2n + 2r̂ + KL + ext; **solver: k! calls, window \|W_new\| ≤ n** |
| `certificate` | (J+1)[k!(2n + 2k² + 60k + 161) + n⌈lg n⌉ + 69n + r̂(2n + 37k + 95) + 119k + 957] + r̂(111k + 230) + 3k⌈lg k⌉ + 18k + 20n + 14m + 850 + ext; **solver: ≤ (J+1)k! calls** |
| `colored_string` | 42n + 88 + nb(t + k + 19) |
| `compare` | 503 + 40m + 111n + 2n(t + k + 19) + (n+1)(n⌈lg n⌉ + 2n + 102) + (n+1)k!(27n + 83) + ext; **solver: ≤ ℓk! ≤ (n+1)k! calls** |
| `ordered_label` | 98 + 35k + k!(23k + 45) + C[group.PermGroup.elements](k, ·; ≤ k!) |

### Simplified forms of the central certificate functions

These hold for n, k ≥ 1, with J ≤ n and r̂ ≤ ρ; the form for `certificate` also needs nk ≥ 2. They use 69n + 119k + 957 ≤ 1144nk (n, k ≥ 1, nk ≥ 2) and n⌈lg n⌉ ≤ n².

* `certificate`: ≤ (n+1)k!(2n + 2k² + 60k + 161) + (n+1)(n² + 1144nk + ρ(2n + 37k + 95)) + ρ(111k + 230) + 3k² + 18k + 20n + 14m + 850.
* `kernel_and_lifts`: ≤ k!(n + 31k²+ 58) + ρ(n + 9) + 59k + 238. Here k² + 30k ≤ 31k².
* `compare`: ≤ (n+1)k!(27n + 83) + (n+1)(n² + 2n + 102) + 2n(t + k + 19) + 111n + 40m + 503.
* `conjugate`: ≤ (n+1)k!(15k + 67) + (n+1)(50n + 245) + ρ(37k + 19n + 132) + 2k² + 27k + 25n + 560.
* `ordered_label`: ≤ k!(23k + 45) + 35k + 98 (+ elements).
* `recognize_johnson`: O(N³ log² N) + O(rN²).
* `recognize_cameron`: O(N³ log⁴ N + rN^{1.5} log² N), plus at most LS(N−1)/8 calls of RJ on ≤ √N points.
* `orbitals`: ≤ (11r + 21)n² + 22n + 53 (+ orbits_on).

---------------------------------------------------------------------------------------------

## 6. Profile numbers used (`opcount.generate()`)

Functions and inner `def`s: key → (outside, [(line, cycle, entry), ...]).

```python
PROFILES = {
    'johnson.subsets_of': (14, [(38, 7, 9)]),
    'johnson.pairs_of': (6, []),
    'johnson.induced_on_subsets': (15, []),
    'johnson.johnson_group_gens': (57, [(52, 6, 11)]),
    'johnson.JohnsonStructure.__init__': (21, [(76, 6, 12)]),
    'johnson.JohnsonStructure.__repr__': (12, []),
    'johnson.CameronStructure.__init__': (34, []),
    'johnson.CameronStructure.__repr__': (16, []),
    'johnson.recognize_hamming': (7, []),
    'johnson._cameron_candidates': (20, [(131, 32, 0), (138, 40, 13), (141, 11, 6)]),
    'johnson.iroot': (14, [(154, 21, 5)]),
    'johnson.recognize_cameron': (52, [(193, 21, 0), (196, 418, 27), (199, 6, 9), (200, 11, 0), (208, 53, 0), (211, 23, 0), (217, 14, 3), (219, 31, 0), (228, 7, 9), (241, 10, 0), (242, 9, 0), (243, 35, 0), (249, 9, 0), (250, 20, 0), (256, 9, 0), (257, 12, 0), (276, 9, 0), (277, 9, 0), (278, 14, 0), (281, 52, 0), (291, 15, 0), (297, 19, 0), (299, 9, 0), (306, 9, 0), (307, 7, 0), (309, 8, 11), (311, 23, 0), (313, 38, 0), (336, 9, 0), (337, 16, 0), (339, 24, 0), (344, 15, 0), (350, 10, 12), (361, 7, 8)]),
    'johnson.recognize_cameron.<find@235>': (4, [(236, 19, 6)]),
    'johnson.recognize_cameron.<find2@264>': (4, [(265, 19, 6)]),
    'johnson.recognize_cameron.<parallel@270>': (37, []),
    'johnson.recognize_cameron.<find3@330>': (4, [(331, 19, 6)]),
    'johnson.johnson_phi': (71, [(380, 18, 0), (385, 67, 0), (386, 9, 8), (395, 20, 4)]),
    'johnson.orbitals': (21, [(404, 20, 11)]),
    'johnson.recognize_johnson': (55, [(418, 8, 9), (421, 16, 0), (422, 19, 2), (428, 18, 4)]),
    'johnson._identify': (28, [(456, 132, 9), (457, 6, 8), (458, 10, 0), (466, 39, 0), (470, 15, 0), (472, 19, 0), (483, 58, 0), (489, 24, 0), (491, 42, 4), (510, 25, 0), (512, 21, 0), (522, 31, 0), (531, 21, 0), (533, 28, 0)]),
    'certificates.JohnsonData.__init__': (72, [(55, 6, 12), (57, 8, 0), (58, 7, 0), (63, 11, 4)]),
    'certificates.JohnsonData._make_fast_phi': (84, [(78, 24, 0), (83, 9, 9), (92, 68, 0), (93, 9, 8)]),
    'certificates.JohnsonData._make_fast_phi.<phi_fn@85>': (16, []),
    'certificates.JohnsonData._make_fast_phi.<phi_fn2@101>': (12, [(103, 37, 0)]),
    'certificates.JohnsonData.omega_of': (15, [(115, 16, 0)]),
    'certificates.JohnsonData.is_primitive': (10, []),
    'certificates.Iteration.__init__': (12, []),
    'certificates.Certificate.__init__': (45, []),
    'certificates.restrict_to': (25, [(151, 6, 12)]),
    'certificates.is_giant_on': (18, []),
    'certificates.LocalCertificates.__init__': (30, []),
    'certificates.LocalCertificates.setwise_stabilizer': (71, [(179, 9, 9)]),
    'certificates.LocalCertificates.image_on_A': (15, [(188, 7, 9)]),
    'certificates.LocalCertificates.affected': (29, [(201, 7, 0), (202, 8, 0), (204, 20, 0)]),
    'certificates.LocalCertificates.kernel_and_lifts': (101, [(215, 7, 9), (220, 17, 12), (223, 7, 9), (225, 27, 0)]),
    'certificates.LocalCertificates.conjugate': (141, [(246, 8, 9), (251, 6, 11), (252, 7, 8), (254, 58, 0), (257, 32, 0), (260, 12, 0), (264, 7, 12)]),
    'certificates.LocalCertificates.conjugate.<cj@239>': (10, []),
    'certificates.LocalCertificates.conjugate.<cj_group@242>': (19, [(243, 8, 9)]),
    'certificates.LocalCertificates.recompute': (67, [(274, 6, 12), (277, 36, 0)]),
    'certificates.LocalCertificates.certificate': (184, [(301, 58, 1), (318, 9, 9), (319, 12, 8)]),
    'certificates.LocalCertificates.colored_string': (24, []),
    'certificates.LocalCertificates.compare': (197, [(357, 10, 8), (358, 10, 8), (359, 7, 0), (361, 7, 0), (383, 38, 0), (387, 59, 0)]),
    'certificates.LocalCertificates.ordered_label': (36, [(406, 6, 12), (409, 22, 0)]),
}
```

Nested lambdas and generator expressions, as `generate()` reports them: key → (total, loops). For duplicate keys, see §1.3.

```python
NESTED = {   # key: (total instructions, number of loops)
    'johnson.induced_on_subsets.<genexpr@46>': (31, 1),
    'johnson.induced_on_subsets.<genexpr@46>.<genexpr@46>': (20, 1),
    'johnson.recognize_cameron.<genexpr@202>': (31, 2),
    'johnson.recognize_cameron.<genexpr@225>': (22, 1),
    'johnson.recognize_cameron.<genexpr@252>': (19, 1),
    'johnson.recognize_cameron.<genexpr@253>': (22, 1),
    'johnson.recognize_cameron.<genexpr@259>': (26, 1),
    'johnson.recognize_cameron.<parallel@270>.<genexpr@273>': (26, 1),
    'johnson.recognize_cameron.<lambda@293>': (10, 0),
    'johnson.recognize_cameron.<genexpr@294>': (26, 1),
    'johnson.recognize_cameron.<genexpr@315>': (20, 1),
    'johnson.recognize_cameron.<genexpr@347>': (26, 1),
    'johnson.recognize_cameron.<genexpr@351>': (38, 2),
    'johnson.recognize_cameron.<genexpr@351>.<genexpr@351>': (20, 1),
    'johnson.johnson_phi.<genexpr@396>': (20, 1),
    'johnson.orbitals.<lambda@405>': (11, 0),
    'johnson._identify.<genexpr@461>': (22, 1),
    'johnson._identify.<genexpr@506>': (24, 1),
    'johnson._identify.<genexpr@514>': (27, 1),
    'johnson._identify.<genexpr@523>': (24, 1),
    'johnson._identify.<genexpr@534>': (20, 1),
    'certificates.JohnsonData._make_fast_phi.<phi_fn@85>.<genexpr@86>': (24, 1),
    'certificates.Certificate.__init__.<genexpr@146>': (19, 1),
    'certificates.restrict_to.<genexpr@152>': (22, 1),
    'certificates.LocalCertificates.kernel_and_lifts.<genexpr@219>': (20, 1),
    'certificates.LocalCertificates.kernel_and_lifts.<genexpr@227>': (27, 1),
    'certificates.LocalCertificates.conjugate.<genexpr@245>': (20, 1),
    'certificates.LocalCertificates.conjugate.<genexpr@263>': (20, 1),
    'certificates.LocalCertificates.colored_string.<genexpr@344>': (29, 1),
    'certificates.LocalCertificates.compare.<genexpr@389>': (20, 1),
    'certificates.LocalCertificates.compare.<genexpr@400>': (20, 1),
    'certificates.LocalCertificates.ordered_label.<genexpr@407>': (20, 1),
    'certificates.LocalCertificates.ordered_label.<genexpr@410>': (20, 1),
}
```

---------------------------------------------------------------------------------------------

## 7. Not proved / conditional

1. **|lifts| ≤ k!** (and hence the k! factors in `recompute`, `certificate`, `compare`, `conjugate`, `kernel_and_lifts`) needs **INV-A**.
   * INV-A is a property of `setwise_stabilizer`, `GroupWithAction.preimage`/`lift` and `recompute`. It is not proved in this document; ownwork_gaps.md §5(c) proves it from HOM for `jd.Gw` (CORRECTNESS.md, Lemmas 3.3, 4.4, 4.5).
   * Unconditionally, replace k! by m!/(m−k)! (Lemma B1 with X = n + range(m)).
2. **J ≤ ⌊n/3⌋** needs **INV-W**, which is solver correctness. J ≤ n is unconditional.
3. **Generator counts.**
   * They are kept as parameters (r, r_H, r_K, r_N, r̂).
   * The substitution r̂ ≤ max(6, ⌊log2 (n+m)!⌋) needs the completeness of group.py's Schreier–Sims chains (Lemma R). Unconditionally, use max(6, (n+m)²/2).
   * The degree-n groups that `recompute` builds from solver output satisfy the same lemma; their generator counts are not bounded in this document.
4. **`recognize_cameron`.**
   * The union-find depth bound (Lemma UF: ≤ number of nodes) is crude. A sharper amortized bound for path halving with naive linking would need Tarjan–van Leeuwen; it is not proved here.
   * The number of heavy bodies reaching Phases I and J is only bounded by Q_D ≤ (N−1)/D per candidate. It is not proved that at most one gets there.
5. **The cost model** was applied with the choices of §1.2, generous where SPEC is ambiguous:
   * strings hash at length + 1;
   * equality during hashing is bounded by the probe's hash size;
   * `comb(L, ·)` is charged L + 1.
