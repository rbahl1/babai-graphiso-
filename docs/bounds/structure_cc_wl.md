# Instruction-count bounds for `babai_gi/structure.py`, `babai_gi/wl.py`, `babai_gi/cc.py`

Specification: `SPEC.md` in this directory; the instructions counted are those of the CPython 3.13
bytecode.  Every bound below is the number of operations of
**one call** in the cost model of the specification; callees outside the three modules are left as
named symbols `C[module.Qualname](params)`.

## 0. Summary of results and findings

Main closed forms (all proved below; `lambda(L) = ceil(log2 L)` for `L >= 1`, `lambda(0) = 0`):

| function | closed form (N = number of points, k = arity, m = \|Gamma\|) |
|---|---|
| `wl.refine_structures([X])`, X k-ary on N >= 2 points | `131 + N^k k^k (14 k lambda(N) + 11k + 476) + (4k^2 + 54k + 286) N^(2k+1) lambda(N)` |
| ... number of WL rounds | `<= N^k - c_0 + 1 <= N^k` (`c_0` = number of F2 classes >= number of distinct input colours) |
| ... one WL round | `<= (4k^2 + 54k + 286) N^(k+1) lambda(N)` |
| ... F2 (`to_configuration`) | `<= N^k k^k (11k + 476 + 14 k lambda(N))` |
| ... calls of the chooser's `check` | `1 + rounds <= 1 + N^k`, each `C[check](s) = 53 + s`, `s <= N^k + 7` (already included) |
| `wl.classical_wl` (N >= 2) | `<= (48 lambda(N) + 382) N^5 + (nu+2) N^4 + 12(eta+2)(nu+2) N^2 lambda(N) + (80 + 7nu) N^2 + N^2 (C_cb + C[canon.canon](nu+2)) + 38N + 229` |
| `cc.ClassicalCC.__init__` (int colours) | exactly `N^2` callback calls; `<= 150 + 51N + N^2 (C[color] + 18 + C[canon.canon](1)) + 12 N^2 lambda(N)` |
| `cc.ClassicalCC.components` | `<= 38N^3 + (32 + gamma)N^2 + 57N + 73` |
| `cc.ClassicalCC.disconnected_off_diagonal_colors` | `<= 85 + 12r + 38N^3 + r'(168 + 137N + 79N^2 + N lambda(N))` (int colours) |
| `cc.ClassicalCC.is_uniprimitive` | `<= 135 + 24r + r'(86 + 77N + 51N^2) + 38N^3` |
| `cc.ClassicalCC.canonical_keys` | `<= 207 + 61N + 43N^2 + 278r + 72rN + r^2(197 + 87N + C[canon.canon](10N+10) + (630N + 600) lambda(N))` |
| `structure.Structure.refine` | `<= 291 + (213 + 4 phi) m + 3Jm + m C[f] + m (C[canon](phi) + C[canon](kappa+tau+phi+3)) + m lambda(m) (1.5m + 5 + 6(theta+1)phi + 3(kappa+tau+phi+3)(2 eta'+5))` |
| key size after `r` construction steps (Lemma K) | `<= kappa_root + 6 + sum_i (\|tag_i\| + phi_i + 7)`; in the repository `<= 9 + sum_i (phi_i + 12) <= 9 + r(m + 13)`, height `<= 3r + 3` |
| `structure.align` | `<= 339 + (374 + 17kappa) m + 2m C[canon](kappa) + 2m lambda(m)(2 + 3kappa(2eta+3)) + J(38 + 6t)` + parity/odd-automorphism terms |
| `structure.enumerate_runs` | executions of `proc`: `R <= prod_{d=1}^{D} k_d`; own work `<= 12 + R(123 + 21D)` |

Findings:

* **A. Instruction attribution (`opcount`).**  In CPython 3.13 the `FOR_ITER` of a loop carries the
  source position of the loop's *iterable*, and some instructions (the `PUSH_EXC_INFO` of
  `enumerate_runs`) carry no position.  `opcount` attributes each instruction to the innermost loop
  whose source span contains its position (in a nested comprehension, such as line 27 of
  `ClassicalCC.__init__`, an instruction of the inner comprehension goes to the inner one), and
  places `FOR_ITER` together with its `EXTENDED_ARG` prefixes, the backward jumps and the
  position-less instructions inside a loop by their offset (`PROOF.md`, Lemma 1.1).  The proofs of
  this document use a **range-based profile** (Lemma 0, Section 1.2), computed from the backward
  jumps of the bytecode and sound by a direct argument.
  The `opcount` numbers are listed in every subsection and in Section 6.1 (the format the
  specification asks for); the range-based numbers used in the proofs are in Section 6.2, and
  Section 6.3 gives the function computing them.  For all 98 code objects the two agree:
  73 are identical; in the other 25, `opcount`'s `outside` <= `outside'` and every `cycle` <= the own
  count of the same loop, with equal instruction totals, the difference being the prologue/epilogue
  of comprehensions and the first test of `while` loops, which `opcount` counts once per entry of the
  loop and the range method counts with the enclosing level.  (`enumerate_runs`: `opcount` gives
  `77 + 94R + 17I` for `R` replays and `I` inner iterations, the direct count of Section 2
  gives `12 + 94R + 17I`.)
* **B. `enumerate_runs`.** The bound "proc runs <= 1 + prod k_d" is true but not tight: `proc` runs
  `R <= prod_d k_d` times (the empty product being 1), and the proof does not assume that `proc` is
  deterministic.  Every index sequence is replayed **at most once** (unconditionally); that every
  consistent sequence is replayed at least once holds only for deterministic `proc` (true in the
  repository, but not needed for any bound).
* **C. `wl._summary` with several structures** raises `KeyError` when a signature of `order` does not
  occur in some structure (`d[sg]` in the generator at line 160).  All callers pass one structure, so
  this is latent; the bounds are stated for `S >= 1` structures anyway (with the assumption that the
  call does not fail).
* **D. Frozenset equality in the cost model.**  `c == jcell` (`_normalize`, `refine`) is charged per
  element of both operands, which gives terms `C*J` (number of cells times size of the Johnson cell), at
  most `(m+1)^2/2`.  (CPython returns after a size check; the model does not see that.)
* **E. Unbounded key nesting.** Keys grow by `|tag| + |f(v)| + 7` nodes per refinement step even when
  nothing splits; a bound in terms of m alone is therefore impossible from the code of `structure.py`;
  the bound is given in terms of the number `r` of refinement steps (Lemma K).  The number of steps per
  `proc` run is a property of the callers (`soj.py`, `design.py`, `main.py`).
* No function of the three modules calls the solver (`Solver.iso`, ...): every "solver calls" item is
  empty, except that `enumerate_runs` calls the caller-given `proc`.

## 1. Conventions

### 1.1 The cost model as applied

* Instructions are counted with the range-based profile of Section 1.2 (Lemma 0), which is sound by
  a direct argument; the `opcount` numbers agree with it up to bookkeeping (Finding A).
* **Built-ins.** An O(1) built-in call (`len`, `isinstance`, `list.append`, `hash` of an int, raising
  an exception object without counting its message, ...) costs 1.  A built-in that touches `e`
  elements costs at most `1 + e` (always written `1 + e`).  Constructors of `list`/`tuple` from `L`
  elements: `1 + L`.  Constructors of `set`/`frozenset`/`dict` from `L` elements and `set.update`:
  `1 + sum` of the insertion costs `D(x)` below.  Iterating over a `range`, `enumerate`, `zip`, a
  dict, a dict view, a set or a frozenset costs 1 per element produced (iterating a list or tuple is
  just the `FOR_ITER` instruction).  `product(range(n), repeat=k)` costs `k` per tuple produced (plus
  1 per element of the consumed `range`).  Slicing, tuple/list concatenation and repetition: `1 +`
  length of the result.  `x in list`, `list.index`, `list.count`: `1 +` (number of elements touched)
  times the cost of one `==`.  `sorted`/`list.sort` of `L` items: `L lambda(L)` comparisons, each
  costing the comparison of two keys, plus `2L + 1`, plus `L` calls of the `key` function.
  `math.factorial(s)`: `1 + s`; `math.comb(a, b)`: `1 + b`.  Arithmetic and comparison of ints of any
  size: the instruction only.
* **Strings are atoms of cost 1** (hash and comparison).  All strings that are hashed or compared in
  these modules are literals of the program text (cell-key tags, `canon` tags `"i"`, `"t"`, ...,
  invariant tags, `"choice"`, `"inv"`, `"johnson"`, `"d"`, `"e"`), the longest having 16 characters
  (`"bsoj-twin-blocks"`).  If strings were charged per character, the hashing/comparison terms would
  grow by at most this factor 16.
* **Sizes.** For a value `x` built from atoms (`None`, `bool`, `int`, `str`), `tuple`, `list`,
  `frozenset`/`set` and `structure.Fixed`: `|x| = 1` for an atom, `|x| = 1 + sum |x_i|` for a container
  with elements `x_i`, `|Fixed(v)| = 1 + |v|`.  The height `h(x)` is 0 for an atom and
  `1 + max h(x_i)` for a container (`h(Fixed(v)) = 1 + h(v)`; `h(()) = 1`).  `x` is *set-free* if
  it contains no set/frozenset.
* **Dict/set operations.** A lookup, insertion or deletion with key `x` costs
  `D(x) = 1 + |x| + |x| = 1 + 2|x|` for a set-free key (hash `<= |x|`, Lemma S1, one comparison
  `<= |x|`, Lemma S2), and `D_f(x) = 1 + 3|x|` for a key that is a frozenset of ints compared with a key
  of the same size (`<= |x| + |y| = 2|x|` per the model).  For an int key: `D = 3`.

### 1.2 Counting instructions: Lemma 0 and the sound profile

For a code object, every backward jump (`JUMP_BACKWARD`, `JUMP_BACKWARD_NO_INTERRUPT`) at offset `b`
with target `t` spans the *range* `[t, b]`; ranges with the same target are merged (largest `b`).  An
instruction belongs to the innermost range containing its offset; `outside'` is the number of
instructions in no range and `own(R)` the number of instructions whose innermost range is `R`.  For
every code object of the three modules except `enumerate_runs` (treated directly in its subsection)
the ranges are pairwise nested or disjoint (checked on the listings, function `range_profile` of
Section 6.3).

**Lemma 0.** For such a code object, one call executes at most
`outside' + sum_R own(R) (it(R) + en(R))` instructions, where `it(R)` is the number of executions of
backward jumps of `R` and `en(R)` the number of transfers of control from an offset outside `R` to one
inside `R`.  If `R` is the range of a `for` statement or comprehension generator (its target is the
loop's `FOR_ITER` or the `EXTENDED_ARG` prefixing it), `it(R) <= ` iterations and `en(R) = ` entries of the loop; for a `while` loop
`it(R) <= ` iterations, `en(R) <= ` entries.

*Proof.* Within a frame the offset increases except at backward jumps: calls return to the next
instruction, a generator resumes after its `YIELD_VALUE`, and the exception handlers of these code
objects (comprehension clean-up `SWAP/POP_TOP/RERAISE`, the `StopIteration` conversion of generator
expressions, the `try` of `enumerate_runs`) lie after all ranges and end with `RERAISE`, i.e. leave
the frame (the only exception: `enumerate_runs`).  Let `o` be an instruction and consider two
consecutive executions of `o`.  In between, some backward jump from an offset `b' >= offset(o)` to
`t' <= offset(o)` was executed; its range contains `o`.  If `o` lies in no range this is impossible,
so `o` runs at most once.  Otherwise the jump belongs to the innermost range `R` of `o` (an `it(R)`
event) or to a range containing `R` properly; in the latter case `t' < t(R)` and `b' > b(R)` (equal
targets are merged; different jumps have different offsets), so control was outside `R` and came back
to `o`: an `en(R)` event.  The events of different consecutive pairs lie in disjoint time intervals,
and the first execution of `o` is preceded by an entry (offset 0 is in no range).  For a `for` loop,
each iteration executes at most one backward jump to the `FOR_ITER` (the loop end or one `continue`),
and control enters the range only from the `GET_ITER` before it, once per entry; similarly for
`while` loops.  []

Consequently the bound of a function is `outside' + sum over its loops own (iterations + entries)`
plus built-ins and callees.  For a generator expression (one range, its `FOR_ITER` loop) producing
`E` elements: `outside' + own (E + 1)`; for a lambda: its instruction count per call.  Each
subsection gives both the `opcount` profile and the sound one; only the sound one enters the bounds.
The per-loop numbers of `opcount` agree with the range-based ones up to the placement of
comprehension prologues/epilogues and first `while` tests (Finding A).

### 1.3 Sizes, hashing and comparison

**Lemma S1 (hash).** Hashing `x` touches at most `|x|` nodes.

**Lemma S2 (equality).** For set-free `x, y`, `x == y` / `x != y` costs at most `min(|x|, |y|)`.
*Proof.* Atoms, or atom against container: 1.  Two tuples/lists: one length check, then elements in
order until the first unequal pair (CPython `tuplerichcompare`/`list_richcompare`, identity shortcut
only saves work): `1 + sum_{i <= i*} E(x_i, y_i) <= 1 + sum_i min(|x_i|, |y_i|) <= min(|x|, |y|)` by
induction.  []

**Lemma S3 (ordering).** For set-free `x, y`, `x < y` costs at most
`(min(h(x), h(y)) + 1) min(|x|, |y|)`.
*Proof.* Atoms: 1.  Tuples/lists: `==` on the elements before the first unequal pair `i*`, then
`==` and `<` on that pair (or a length comparison): cost
`<= 1 + sum_{i <= i*} min(|x_i|,|y_i|) + O(x_{i*}, y_{i*}) <= min(|x|,|y|) + (min(h(x_{i*}),h(y_{i*})) + 1) min(|x_{i*}|,|y_{i*}|)`,
and `min(h(x_{i*}), h(y_{i*})) + 1 <= min(h(x), h(y))`, `min(|x_{i*}|,|y_{i*}|) <= min(|x|,|y|)`.  []

**Lemma C (canonical images, `canon.canon`).** For `x` as in 1.1, `|canon(x)| <= 3|x|` and
`h(canon(x)) <= 2h(x) + 1`; `canon(x)` is set-free.
*Proof* (by induction on `canon.py`): `None -> ("n",)` (2 nodes, height 1); `bool`, `int`, `str` ->
`(tag, v)` (3 nodes, height 1); tuple/list/frozenset with elements `x_i` -> `(tag, (canon(x_1), ...))`:
`3 + sum |canon(x_i)| <= 3(1 + sum|x_i|)` nodes, height `2 + max h(canon x_i) <= 2 + 2(h(x) - 1) + 1`;
`Fixed(v) -> ("x", canon(v))`: `2 + 3|v| <= 3|Fixed(v)|` nodes, height `1 + 2h(v) + 1 <= 2h(Fixed(v)) + 1`.  []

Hence one comparison of two canonical images in a sort with `key=_hk` (or `canon`, `_sort_key`) of
objects of size `<= s` and height `<= h` costs at most `Omega(s, h) := (2h + 2) 3s = 6(h+1)s`.
The cost of computing `canon(x)` itself is the callee `C[canon.canon](s)` (`canon.py` is not one of
the three modules); it denotes the maximum over arguments of size `<= s` and is therefore nondecreasing in
`s`.  `C[structure._hk](s) = C[cc._hk](s) = C[wl._sort_key](s) = 5 + C[canon.canon](s)`.

### 1.4 Parameters and assumptions

* `structure.py`: `m = self.m`; a `Structure` satisfies **(S1)**: its cells are non-empty pairwise
  disjoint subsets of `range(m)`; hence `C <= m` cells and `sum |c| <= m`.  (S1) holds for every
  structure built in the repository: the roots in `main.py` partition `range(m)` (`"all"`, `twins/rest`,
  `Phi/rest`, `S/rest`, `orbits/fixed`), `refine`, `soj.split_by_blocks` and `with_johnson` partition
  the cells of a structure satisfying (S1); `__init__` drops empty cells.  `K` = number of distinct keys,
  `kappa`/`eta` = maximal size/height of a key of `self.cells`, `J` = size of the Johnson cell (0 if
  none), `t = jc.t`, `m' = jc.m`.  Keys and values of refinement functions are set-free (they are
  built from strings, ints, `None`, bools and tuples, Lemma K).
* `wl.py`: `N = s.n` (number of points), `k = s.k`, `P = N^k`, `M = k^k` (number of maps
  `[k] -> [k]`), `q = k(k-1)/2`, `S` = number of structures; every structure has the same `N`, `k`
  and `len(colors) = N^k` (true for all callers: they pass one structure built with `N^k` colours).
* `cc.py`: `N = len(vertices)`, `r = len(self.colors)` (`<= N^2`), `r'` = number of off-diagonal
  colours (`<= min(r, N(N-1))`; `<= N - 1` if the configuration is homogeneous and coherent, since then
  every off-diagonal colour has out-valency `>= 1` and the valencies sum to `N`), `gamma`/`eta_g` =
  maximal size/height of a colour value.  In the repository all colours are ints (`gamma = 1`,
  `eta_g = 0`): `design.py:63`, `main.py:944,954`, `soj.py:527` and `induced` (which keeps colours).
* **Callbacks.**  `check` of a chooser: `C[check](s) := max(C[RecordingChooser.check](s),
  C[ReplayChooser.check](s)) = 53 + s` for an invariant of size `s` (Section 2).  Every invariant
  passed to `check` in the repository is set-free (counts, bools, `None`, short strings, tuples of
  them, the WL summaries); Lemma S2 applies.  Other callbacks (`color`, `vertex_color`, `pair_color`,
  `f` of `refine`, `proc` of `enumerate_runs`) are callees whose cost `C[...]` is given by the caller.

### 1.5 Callees outside the three modules

`C[canon.canon](s)`; `C[perm.from_cycles](n, l)` (degree `n`, total cycle length `l`);
`C[perm.parity](n)`; `C[perm.mul](n)`.

## 2. `babai_gi/structure.py`

`Mismatch` has no methods of its own.  Notation of 1.4: `m`, `C`, `K`, `kappa`, `eta`, `J`.

### structure.Fixed.__init__
opcount `(4, [])`; sound `(4, [])`.  No loops, built-ins or callees.  **Bound: 4.**

### structure.Fixed.__eq__
opcount `(15, [])`; sound `(15, [])`.  Built-ins: `isinstance` 1; `other.value == self.value`
costs at most `|self.value| + |other.value|` (Lemma S2, or per element of both operands for sets).
**Bound: `16 + |self.value| + |other.value|`.**

### structure.Fixed.__hash__
opcount/sound `(8, [])`.  `hash(("Fixed", value))`: `1 + |("Fixed", value)| = 3 + |value|` (Lemma S1).
**Bound: `11 + |value|`.**

### structure.Fixed.__repr__
opcount/sound `(9, [])`.  The f-string calls `repr(value)` (cost `1 + rho`, `rho = len(repr(value))`)
and builds a string of `rho + 7` characters (`1 + rho + 7`).  **Bound: `18 + 2 rho`.**  Used only
for diagnostics / error messages (`apply_obj`'s `TypeError` text, not counted).

### structure.Fixed.canon_value
opcount/sound `(4, [])`.  **Bound: 4.**

### structure.apply_obj
opcount `(92, [(70, 8, 9)])`, genexprs `<genexpr@66>`, `<genexpr@68>`: total 21 each;
sound `(101, [(70, 8)])`, genexprs `(11, [(66, 10)])`, `(11, [(68, 10)])`.

Assumption: `obj` is built from `bool`, `int` (`< len(sigma)`), `Fixed`, `str`, `None`, `tuple`,
`frozenset`, `list` (otherwise the `TypeError` exit).  Let `x` have `r` direct elements `o_i`.

* Recursion: every invocation on a container calls `apply_obj` once per direct element (in the
  genexpr / list comprehension), atoms (including `Fixed`) do not recurse; so a call on `x` makes
  exactly one invocation per node of `x`: `|x|` invocations in all.
* Own work of one invocation.  Instructions: `outside' = 101`; the list comprehension (line 70) has
  `r` iterations, 1 entry: `8(r+1)`; the genexpr of line 66/68 produces `r` elements:
  `11 + 10(r+1)`.  Built-ins: at most 7 `isinstance` calls on any path (bool, int, Fixed, str, tuple,
  frozenset, list): 7; `tuple(genexpr)`: `1 + r`; `frozenset(genexpr)`: `1 + sum_i (1 + 3|o_i|)`
  (insertion of an element of size `|o_i|`, hash `|o_i|`, one comparison `<= 2|o_i|`).
  Total own work `<= 108` for an atom, `<= 108 + 21 + 10r + 1 + r + r + 3 sum|o_i| = 130 + 12r + 3 sum|o_i|`
  otherwise (the list case, `108 + 8r + 8`, is smaller).
* **Claim: `C[apply_obj](x) <= (130 + 15 h(x)) |x|`.**  Atoms: `108 <= 130`.  Containers, by
  induction, with `r <= sum |o_i|` and `h(o_i) + 1 <= h(x)`:
  `130 + 12r + 3 sum|o_i| + sum (130 + 15h(o_i))|o_i| <= 130 + sum (145 + 15 h(o_i))|o_i|
  <= 130 + (130 + 15h(x)) sum|o_i| <= (130 + 15h(x))|x|`.

**Bound: `(130 + 15 h(obj)) |obj|`.**  (Caller: `Solver._covered`, on choice sequences.)

### structure.Chooser.choose / structure.Chooser.check
opcount/sound `(3, [])` each; abstract, raise `NotImplementedError` (constructor 1).  **Bound: 4 each.**

### structure.Chooser.choose_index
opcount/sound `(10, [])`.  `list(range(k))`: `2 + k`; callee `self.choose(list of k)`.
**Bound: `12 + k + C[choose](k) <= 116 + k`** (with the bounds 33 / 104 below).  No callers.

### structure.RecordingChooser.__init__
opcount/sound `(8, [])`.  **Bound: 8.**

### structure.RecordingChooser.choose
opcount/sound `(30, [])`.  Built-ins: `len` 1, two `append` 2 (`not candidates`, indexing:
instructions; the `ValueError` exit is an error exit).  **Bound: 33.**

### structure.RecordingChooser.check
opcount/sound `(10, [])`.  `append` 1 (the 2-tuple is built by one instruction, nothing is hashed).
**Bound: 11** (independent of the size of the invariant).

### structure.ReplayChooser.__init__
opcount/sound `(21, [])`.  `list(path)`: `1 + |path|`.  **Bound: `22 + |path|`.**

### structure.ReplayChooser._next_event
opcount/sound `(28, [])`.  `len` 1, `Mismatch(...)` 1.  **Bound: 30.**

### structure.ReplayChooser.choose
opcount/sound `(66, [])`.  Callee `_next_event` (30).  Built-ins: `len(candidates)` twice,
`len(self.taken)`, `len(self.path)`, three `append`, `Mismatch`: 8.  The comparisons are of a
string with a literal and of two ints.  **Bound: 104.**

### structure.ReplayChooser.check
opcount/sound `(22, [])`.  Callee `_next_event` (30); `Mismatch` 1; `ev[1] != invariant` compares a
recorded invariant with the argument (both set-free, 1.4): at most `s = |invariant|` (Lemma S2).
**Bound: `53 + s`.**  Hence `C[check](s) = max(11, 53 + s) = 53 + s` for every chooser of the
package (these are the only two `Chooser` subclasses, `main.py:632`, `structure.py:146`).

### structure.enumerate_runs
opcount `(10, [(145, 65, 2), (156, 17, 12)])`; sound: `outside' = 12`, ranges `[12, 380]` (outer
`while`, target line 146), `[174, 406]` (the `JUMP_BACKWARD_NO_INTERRUPT` at 406 of the `except`
handler back to line 154) and `[286, 334]` (inner `while`, line 157), own counts 70, 7, 17.  The first
two ranges overlap, so Lemma 0 is not used; instead:

*Instruction count.* The generator code has 106 instructions: 12 outside `[12, 406]` (prologue,
`while True` `NOP`, the final `RERAISE`s / `StopIteration` handler, each executed at most once per
generator), 17 in `[286, 334]`, and 77 others.  One pass of the outer loop (one *replay*) starts at
offset 12 and runs forward, either normally to 172 (the `yield` suspends and resumes at the next
instruction) or until an exception at an offset `<= 172` (inside the `try`: `ReplayChooser(...)`
at 24, `proc(ch)` at 42, the `raise` at 122, or an exception thrown in at the `yield`), then the handler
384-406 (or, for a non-`Mismatch`, 384-398 and the final `RERAISE`s, ending the generator), then the
jump to 174, then forward to 380 (back to 12) or to the `return` at 350.  Hence each of the 77
instructions runs at most once per replay; the inner range runs `<= 17 (it + 1)` per replay.

*Inner loop (line 156).* `i` starts at `len(taken) - 1` and decreases by 1 per iteration while
`i >= 0`: at most `len(taken)` iterations.  Let `D` be the number of `("choice", .)` events of
`trace` and `k_1, ..., k_D >= 1` their counts (`RecordingChooser.choose` refuses an empty candidate
list).  **Claim 1: in every replay, `len(taken) <= D` and `counts[d] = k_{d+1}`.**  The events are
consumed in order (`_next_event`); a `choose` either raises `Mismatch` before appending or consumes
a `"choice"` event whose count equals `len(candidates)`, and appends exactly that count; a `check`
either raises or consumes an `"inv"` event.  `Mismatch` raised by `ch` is never caught inside `proc`
(the only `except` clauses of the package are `enumerate_runs`' own and `canon.normalize_letters`'
`TypeError`; a nested `enumerate_runs` inside `proc` would only catch exceptions of its own chooser,
and no `proc` of the repository hands `ch` to the solver).  So after the run, the consumed prefix of
`trace` contains exactly `len(taken)` choice events and `counts` records their counts.  Hence also
`taken[d] = path[d] < k_{d+1}` or `0`: `path[d] = taken'[d] + 1 < counts'[d] = k_{d+1}` by the test at
line 156, so `candidates[idx]` never fails.

**Claim 2 (number of replays): `R <= prod_{d=1}^{D} k_d`.**  Pad every path and every `taken` with
zeros to length `D` and let `Nr(p) = sum_d p_d W_d` with `W_d = prod_{e > d} k_e` (mixed radix,
`0 <= p_d < k_d`, so `0 <= Nr(p) <= prod k_d - 1`).  Replay `s` follows path `p_s`: for
`d < min(len(taken_s), len(p_s))` it takes `p_s[d]`, beyond `len(p_s)` it takes 0; so padded
`taken_s` agrees with padded `p_s` on all `d < len(taken_s)` and is 0 afterwards (no assumption of
determinism of `proc` is needed: a run may stop earlier than the previous one).  The next path is
`p_{s+1} = taken_s[:i] + [taken_s[i] + 1]` with `i < len(taken_s)`, so padded `p_{s+1}` agrees with
padded `p_s` before `i`, exceeds it by 1 at `i`, and is 0 after `i`.  Therefore
`Nr(p_{s+1}) - Nr(p_s) >= W_i - sum_{d > i} (k_d - 1) W_d = W_i - (W_i - 1) = 1` (telescoping
`(k_d - 1) W_d = W_{d-1} - W_d`).  With `Nr(p_1) = Nr([]) = 0` the number of replays is at most
`prod k_d`.  The replays have pairwise different paths, so every choice sequence is replayed (and
yielded) at most once.  If `proc` is deterministic (the same answers give the same calls), the
replays are exactly the leaves of the tree of consistent prefixes, so `R` equals the number of
leaves, `= prod k_d` iff no replay fails before its last choice.  The bound `1 + prod k_d` is
therefore correct but not tight.

*Built-ins per replay:* `ReplayChooser(trace, path)` (callee, `22 + |path| <= 22 + D`, as
`|path| <= len(taken_{s-1}) <= D`), `len(trace)` 1, `Mismatch(...)` 1, `list(ch.chosen)`
`1 + len(chosen) <= 1 + D`, `len(taken)` 1, `taken[:i]` `<= 1 + D`, list concatenation `<= 1 + D`:
`<= 29 + 4D` including the constructor.

Callees: `proc(ch)` once per replay (its cost, including the chooser calls it makes, is the caller's
`C[proc]`).  Solver calls: none (only through `proc`).

**Bound (own work): `12 + R (77 + 17(D + 1) + 29 + 4D) = 12 + R(123 + 21D)`, `R <= prod_{d=1}^D k_d`,
plus `sum over the R replays of C[proc]`.**  The work per replay is `123 + 21D`.

### structure.JohnsonCell.__init__ / structure.JohnsonCell.invariant
opcount/sound `(8, [])` each.  **Bound: 8 each.**

### Lemma K (sizes of cell keys)
Every key of a `Structure` is created either by the caller of a *root* construction
(`Structure(m, cells)`, `coloring_structure`) or from a key `k` of a structure by a *construction
step*: `refine(f, tag)` (also via `individualize`, `mark`) gives `(k, tag, f(v))`; `split_cell` and
`soj.split_by_blocks` give `(k, tag)`; `with_johnson` keeps `k`; every construction ends with
`_normalize`, which replaces each key `k'` by `(k', len(c))` and the key of the Johnson cell by
`((k', len(c)), "johnson", m', t')`.  Let `S_0` be a root whose keys have size `<= kappa_root` and
height `<= eta_root`, and `S_i` the result of the `i`-th step applied to `S_{i-1}`, with a tag of size
`|tag_i|`, height `h(tag_i)` (0 if none) and values `f(v)` of size `<= phi_i`, height `<= theta_i`
(0 if none).  Then every key of `S_r` satisfies

`kappa(S_r) <= kappa_root + 6 + sum_{i=1}^{r} (|tag_i| + phi_i + 7)`,
`eta(S_r) <= max(eta_root + 2, max_i h(tag_i), max_i theta_i) + 3r`.

*Proof.* The root's normalisation adds 2 nodes (and 4 more for a Johnson cell), 1 (2) to the height.
A step builds a tuple of `k`, the tag and the value (`+1 + |tag_i| + phi_i` nodes, height
`1 + max(...)`) and normalises (`+2`, `+4` for the Johnson cell; height `+1`, `+1`).  []

*In the repository:* roots have `kappa_root <= 3` (`"all"`, `"twins"`, `"rest"`, `"Phi"`, `"S"`,
`"fixed"`, `("orb", n)`), `eta_root <= 1`; tags have `<= 5` nodes and height `<= 2`
(`("bsoj-dl", depth, i)`, `(("upcc-fb", depth), step)`, ...); values are ints, bools, `None`,
`(twsize, deg)` (3 nodes) or, in `soj._individualize_v2`, a tuple of `<= |V2|` ints (`|V2| <= m`:
the points of `V2` are distinct vertices or pairwise disjoint blocks of vertices), height `<= 1`.  So
`phi_i <= m + 1` and **`kappa(S_r) <= 9 + sum_i (phi_i + 12) <= 9 + r(m + 13)`,
`eta(S_r) <= 3r + 3`**, where `r` is the number of construction steps since the root (every `proc`
starts from its own root).  `r` itself is a property of the callers (Finding E).

### structure.Structure.__init__
opcount `(21, [(183, 14, 12)])`; sound `(33, [(183, 14)])`.

Let `L0 = len(cells)` (argument) and assume (S1) for the non-empty input cells (`sum |c| <= m`).
Loop 183 (list comprehension over `cells`): `L0` iterations, 1 entry: `14(L0 + 1)`.  Built-ins:
`frozenset(c)` per non-empty cell, `<= 1 + 3|c|` (int insertions): `<= L0 + 3m`.  Callee:
`self._normalize()` with `C <= L0` cells, input keys of size `<= kappa_in`, height `<= eta_in`.

**Bound: `47 + 15 L0 + 3m + C[_normalize](C, kappa_in, eta_in, J)`.**  Callers: `L0 <= m + 1` in
the repository (`refine`, `split_by_blocks`, `with_johnson`: `L0 = C <= m`; roots: 2 cells or
orbits + fixed).

### structure.Structure._normalize
opcount `(89, [(190, 12, 12), (194, 12, 0), (198, 7, 9)])`, `<lambda@197>` 18; sound
`(110, [(190, 12), (194, 12), (198, 7)])`, `<lambda@197>` `(18, [])`.

`C = len(self.cells)`; keys of `self.cells` have size `<= kappa_in`, height `<= eta_in`; so the keys
`(k, len(c))` of `cells` have size `s := kappa_in + 2`, height `<= eta_in + 1`.
* Loop 190: `C` iterations: `12(C+1)`; `len(c)`: `C`.
* Loop 194 (only with a Johnson cell `jcell`, `J = |jcell|`): `12(C+1)`; `enumerate` `1 + C`;
  `c == jcell` costs `1 + |c| + J` each: `<= C + m + CJ`.
* `sorted(range(len(cells)), key=lambda)`: `len` 1, `range` `1 + C`; `C` lambda calls, each 18
  instructions + `_hk((k, len))` (`5 + C[canon.canon](s)`) + `sorted(cell)`
  (`|c| lambda(|c|) + 2|c| + 1`, int comparisons; sum over cells `<= m lambda(m) + 2m + C`);
  `C lambda(C)` comparisons of the pairs `(canon(key), sorted cell)`, each at most
  `Omega_N := 4 + 1.5m + 3s(2 eta_in + 5)`: if the canonical keys differ, `1 + 3s + Omega(s, eta_in+1)
  = 1 + 3s(2 eta_in + 5)` (Lemmas S2, S3, C); if they are equal, the keys are equal (`canon` is
  injective), hence the two cells have equal size `s_c <= m/2` (disjoint) and the sorted lists cost
  `<= 1 + 3s + (1 + s_c) + 2(1 + s_c) <= 4 + 3s + 1.5m`; plus `2C + 1`.
* Loop 198: `7(C+1)`.  `order.index(jc)`: `1 + C`.

Sum: instructions `110 + 12(C+1) + 12(C+1) + 7(C+1) + 18C = 141 + 49C`; built-ins
`C + (1 + 2C + m + CJ) + (2 + C) + C(5 + C[canon](s)) + (m lambda(m) + 2m + C) + C lambda(C) Omega_N + (2C + 1) + (1 + C)`.

**Bound: `146 + 62C + 3m + m lambda(m) + CJ + C C[canon.canon](kappa_in + 2) + C lambda(C) (4 + 1.5m + 3(kappa_in + 2)(2 eta_in + 5))`**
(the term `CJ` only with a Johnson cell).

### structure.Structure.cell_of
opcount `(12, [(207, 10, 0), (208, 6, 0)])`; sound `(12, [(207, 10), (208, 6)])`.
Loop 207: `C` iterations, 1 entry; loop 208: `sum |c| <= m` iterations, `C` entries.  Built-ins:
`enumerate` `1 + C`; frozenset iteration `m`; `d[v] = i` `3m`.
**Bound: `12 + 10(C+1) + 6(m + C) + 1 + C + 4m = 23 + 17C + 10m <= 23 + 27m`.**

### structure.Structure.key_of_vertex
opcount `(10, [(214, 8, 0), (215, 6, 0)])`; sound `(10, [(214, 8), (215, 6)])`.  Same loops;
built-ins: frozenset iteration `m`, `d[v] = k` (int key) `3m`.
**Bound: `10 + 8(C+1) + 6(m + C) + 4m = 18 + 14C + 10m <= 18 + 24m`.**

### structure.Structure.invariant
opcount `(26, [])`, `<genexpr@220>` 24; sound `(26, [])`, `<genexpr@220>` `(10, [(220, 14)])`.
The genexpr produces `C` pairs `(canon(k), len(c))`: `10 + 14(C+1)` plus per element `_hk(k)`
(`5 + C[canon](kappa)`) and `len` (1).  `sorted`: `C lambda(C)` comparisons of pairs of size
`<= 3 kappa + 2`, each `<= 1 + 3kappa(2 eta + 3)` (canonical keys differ: `1 + 3kappa + 6(eta+1)kappa`;
equal: `1 + 3kappa + 2`), plus `2C + 1`; `tuple(...)` `1 + C`; `self.johnson.invariant()` 8; the
tuple concatenation `1 + C + 1`.
**Bound: `62 + 24C + C C[canon.canon](kappa) + C lambda(C) (1 + 3 kappa (2 eta + 3))`.**  The result
has size `<= 5 + C(3 kappa + 2)` and is set-free.

### structure.Structure.max_cell_size
opcount `(10, [])`, genexpr 20; sound `(10, [])`, genexpr `(10, [(224, 10)])`.  `max` over the
genexpr: `1 + C`; `len` per cell: `C`.  **Bound: `10 + 10 + 10(C+1) + 1 + 2C = 31 + 12C`.**  No callers.

### structure.Structure.is_trivial
opcount/sound `(16, [])`; `len` 1.  **Bound: 17.**  No callers in the package (only `tests/`).

### structure.Structure.refine
opcount `(51, [(235, 34, 0), (237, 15, 0), (239, 15, 0), (246, 12, 0)])`; sound
`(51, [(235, 34), (237, 15), (239, 15), (246, 12)])`.

Parameters: `C` cells of `self`, `C'` cells of the result (`C <= C' <= m`, (S1)), keys of `self` of
size `<= kappa`, height `<= eta`; `tau = |tag|`, `h_tau = h(tag)`; values `f(v)` set-free of size
`<= phi`, height `<= theta`; `C[f]` the cost of one call of `f`; `J` = size of the Johnson cell of
`self` (0 if none).  Let `g_c` be the number of distinct values of `f` on cell `c`
(`sum_c g_c = C'`).
* Loops: 235 over `self.cells` (`C` iterations, 1 entry): `34(C+1)`; 237 over `c` (`sum|c| <= m`
  iterations, `C` entries): `15(m + C)`; 239 over the sorted groups (`C'` iterations, `C` entries):
  `15(C' + C)`; 246 over `enumerate(new)` (`C'` iterations, `<= 1` entry): `12(C'+1)`.
* Per vertex: `f(v)` (`C[f]`), `groups.setdefault(f(v), [])` (`D <= 1 + 2phi`), `append` 1, set
  iteration 1: `m(3 + 2phi) + m C[f]`.
* Per cell: `sorted(groups, key=_hk)`: dict iteration `g_c`, `g_c` calls of `_hk`
  (`5 + C[canon](phi)`), `g_c lambda(g_c)` comparisons of canonical images, each
  `<= Omega(phi, theta) = 6(theta+1)phi`, `2g_c + 1`; `len(groups)` 1; with a Johnson cell,
  `c == jc_set` `<= 1 + |c| + J`.  Sum: `8C' + C' C[canon](phi) + 6(theta+1)phi C' lambda(C') + 2C`
  (`sum g_c lambda(g_c) <= C' lambda(C')`), plus `C + m + CJ`.
* Per new cell: `groups[fv]` (`1 + 2phi`), `frozenset(...)` (`1 + 3|group|`), `append` 1:
  `C'(3 + 2phi) + 3m`.
* Loop 246 (only with a Johnson cell): `enumerate` `1 + C'`, `c == jc_set` `<= C' + m + C'J`.
* Callee: `Structure(self.m, new, johnson, jcell)`: `L0 = C'`, input keys `(k, tag, f(v))` of size
  `<= kappa_in := kappa + tau + phi + 1`, height `<= eta' := max(eta, h_tau, theta) + 1`; Johnson
  cell of size `J' <= J`.

Own work: `97 + 64C + 27C' + 15m + m(6 + 2phi) + m C[f] + C'(11 + 2phi) + 2C + C' C[canon](phi)
+ 6(theta+1)phi C' lambda(C') + [1 + C + 2C' + 2m + (C + C')J]`.  Adding
`C[__init__] <= 47 + 15C' + 3m + C[_normalize](C', kappa_in, eta', J')`:

**Bound: `291 + 67C + (117 + 2phi)C' + (29 + 2phi)m + m lambda(m) + m C[f] + C' (C[canon](phi) + C[canon](kappa+tau+phi+3)) + (C + 2C')J
+ C' lambda(C') (6(theta+1)phi + 4 + 1.5m + 3(kappa+tau+phi+3)(2 eta' + 5))`.**
Closed form (`C <= C' <= m`): **`C[refine] <= 291 + (213 + 4phi) m + 3Jm + m C[f] + m (C[canon](phi) + C[canon](kappa+tau+phi+3))
+ m lambda(m) (1.5m + 5 + 6(theta+1)phi + 3(kappa+tau+phi+3)(2 eta' + 5))`.**
The keys of the result: size `<= kappa + tau + phi + 7`, height `<= eta' + 2` (Lemma K).

### structure.Structure.individualize
opcount `(12, [])`, `<lambda@254>` 10; sound the same.  Callee `refine(lambda, tag)` with
`C[f] = 10`, `phi = 1`, `theta = 0`.
**Bound: `12 + C[refine](C[f]=10, phi=1, theta=0) <= 303 + 227m + 3Jm + m (C[canon](1) + C[canon](kappa+tau+4))
+ m lambda(m)(1.5m + 11 + 3(kappa+tau+4)(2eta'+5))`,** `eta' = max(eta, h_tau) + 1`.

### structure.Structure.mark
opcount `(16, [])`, `<lambda@258>` 10; sound the same.  `frozenset(S)`: `1 + 3|S|`; the lambda's
`u in S` is an int lookup (3): `C[f] = 13`, `phi = 1`, `theta = 0`.
**Bound: `17 + 3|S| + C[refine](C[f]=13, phi=1, theta=0) <= 308 + 3|S| + 230m + 3Jm + m (C[canon](1) + C[canon](kappa+tau+4))
+ m lambda(m)(1.5m + 11 + 3(kappa+tau+4)(2eta'+5))`.**

### structure.Structure.split_cell
opcount `(63, [(266, 18, 0), (276, 12, 0)])`; sound `(63, [(266, 18), (276, 12)])`.  No callers in
the package.  Parameters: `B = len(blocks)`, `m_b = sum |b|`, `C_n = C - 1 + B` cells passed on.
Loops: 266 `B` iterations: `18(B+1)`; 276 `C_n` iterations: `12(C_n + 1)`.  Built-ins:
`list(self.cells)` `1 + C`; `del new[i]` `<= 1 + C`; `set()` 1; per block `frozenset(b)`
`1 + 3|b|`, `covered |= fb` `<= 1 + m + |b|` (both operands), `append` 1; `covered != c`
`<= 1 + 2m`; Johnson: `enumerate` `1 + C_n`, `cc == jset` `<= C_n + m + C_n J`.  Callee
`Structure(...)` with `L0 = C_n`, keys `(k, tag)` of size `<= kappa + tau + 1`.
**Bound: `98 + 2C + 14C_n + B(21 + m) + 4m_b + 3m + C_n J + C[__init__](C_n, kappa+tau+1, max(eta,h_tau)+1, J)`.**

### structure.Structure.with_johnson
opcount/sound `(11, [])`.  `list(self.cells)` `1 + C`; callee `Structure(...)` with `L0 = C`, keys
of size `<= kappa`, height `<= eta`, Johnson cell of size `J = |cell|`.
**Bound: `12 + C + C[__init__](C, kappa, eta, J) <= 205 + 78C + 6m + m lambda(m) + CJ + C C[canon](kappa+2)
+ C lambda(C)(4 + 1.5m + 3(kappa+2)(2eta+5))`.**

### structure.Structure.aut_gens
opcount `(25, [(290, 15, 0), (292, 136, 0), (303, 12, 8), (306, 10, 0), (311, 22, 0), (313, 7, 0)])`;
sound `(28, [(290, 15), (292, 141), (303, 12), (306, 10), (311, 22), (313, 7)])`.

For a key class `j` (`K` classes) let `n_j` be its number of cells and `s_j` their common size
(equal keys have equal second component `len(c)`, Lemma K; `sum n_j = C`, `sum n_j s_j <= m`,
`sum_j s_j <= m`), `K_2 = #{j : n_j >= 2} <= C/2`.
* Loops: 290 over `enumerate(self.cells)`: `15(C+1)`; 292 over `by_key.items()`: `141(K+1)`; for
  `n_j >= 2`: 303 (`n_j` iterations) `12(n_j+1)`, 306 (`zip` of two cells, `s_j` iterations)
  `10(s_j+1)`; for `n_j > 2`: 311 (`n_j` iterations) `22(n_j+1)`, 313 (`n_j` entries of `s_j`
  iterations) `7 n_j (s_j + 1)`.  Sum `<= 184 + 56C + 141K + 44K_2 + 17m`.
* Built-ins: `enumerate` `1 + C`; `setdefault` + `append` `C(2 + 2kappa)`; `items()` `1 + K`; per
  class `sorted(first)` `s_j lambda(s_j) + 2s_j + 1`, two `len`, slice `first[:2]` 3, `<= 2` appends
  or one `extend` (3), two `len(idxs)`: `<= mlambda(m) + 2m + 10K` in all; per class with
  `n_j >= 2`: `n_j` sorts of cells, `list(range(m))` `2 + 2m`, `zip` `1 + s_j`, `tuple(p)` `1 + m`,
  `append` 1: `<= m lambda(m) + 2m + C + K_2(5 + 3m) + m`; per class with `n_j > 2`:
  `list(range(m))` `2 + 2m`, `range(len(lists))` `2 + n_j`, per cell `len` + `zip` `2 + s_j`,
  `tuple(p)`, `append`: `<= K_2(6 + 3m) + 3C + m`.
* Callees: per non-Johnson class with `s_j >= 2`: `C[perm.from_cycles](m, 2)` and, if `s_j > 2`,
  `C[perm.from_cycles](m, s_j)`; for the Johnson class `C[_johnson_cell_gens](m, jc)`.
* Number of generators returned: `<= 2` (cell or Johnson generators) `+ 2` (cell permutations) per
  class: `G <= 4K`.

**Bound: `186 + (63 + 2kappa)C + 152K + 55K_2 + 23m + 2m lambda(m) + 6m K_2 + sum_j [C[perm.from_cycles](m,2) + C[perm.from_cycles](m,s_j)] + C[_johnson_cell_gens]`
`<= 186 + (266 + 2kappa) m + 3m^2 + 2m lambda(m) + 2K max_s C[perm.from_cycles](m, s) + C[_johnson_cell_gens]`.**

### structure.Structure.aut_order
opcount `(26, [(322, 15, 0), (324, 49, 0)])`; sound `(26, [(322, 15), (324, 49)])`.  Used only by
tests.  Loops: `15(C+1)`, `49(K+1)`.  Built-ins: `enumerate` `1 + C`, `setdefault` + `append`
`C(2 + 2kappa)`, `items()` `1 + K`, per class `len`, `factorial(s_j)` `1 + s_j` (or
`factorial(m')` `1 + m'` for the Johnson class), two `len(idxs)`, `factorial(n_j)` `1 + n_j`.
**Bound: `92 + (19 + 2kappa)C + 55K + m + m'`.**

### structure.Structure.has_odd_automorphism
opcount `(17, [(335, 15, 0), (337, 62, 2)])`; sound `(19, [(335, 15), (337, 62)])`.  No callers.
Built-ins as in `aut_order` without factorials; `comb(m'-2, t-1)` `<= 1 + t` (at most once).
**Bound: `99 + (18 + 2kappa)C + 65K + t`.**

### structure.Structure.odd_automorphism
opcount `(8, [(350, 9, 4)])`; sound `(12, [(350, 9)])`.  Loop over the `G <= 4K` generators of
`aut_gens()` (callee), each `parity(g)` (`C[perm.parity](m)`).
**Bound: `12 + 9(G+1) + C[aut_gens] + G C[perm.parity](m) <= 21 + 36K + C[aut_gens] + 4K C[perm.parity](m)`.**

### structure._johnson_cell_gens
opcount `(60, [(360, 6, 11), (367, 23, 0), (369, 18, 0)])`, `<genexpr@370>` 20; sound
`(71, [(360, 6), (367, 23), (369, 18)])`, `<genexpr@370>` `(11, [(370, 9)])`.

Parameters: `J = len(jc.labels)` (the Johnson cell), `t = jc.t`, `m' = jc.m`.  Assumption (as
guaranteed by `soj.bipartite_split_or_johnson`): `labels` maps the `J` vertices bijectively onto the
`t`-subsets of `range(m')`, vertices `< m`.
* Loop 360 (dict comprehension, `J` iterations): `6(J+1)`; `labels.items()` `1 + J`; insertions
  of frozenset keys of size `t + 1`: `J(4 + 3t)`.
* `lam_gens`: `<= 2` permutations (`from_cycles(m', [[0,1]])`, `list(range(m'))` `2 + 2m'`,
  `from_cycles(m', [list])`), 2 appends.
* Loop 367 (`<= 2` iterations): `23 * 3`; per iteration `list(range(m))` `2 + 2m`, loop 369
  (`J` iterations) `18(J+1)`, `labels.items()` `1 + J`, per vertex the genexpr (`t` elements:
  `11 + 9(t+1)`), `frozenset(...)` `1 + 3t`, the lookup `label_to_vertex[...]` `D_f = 4 + 3t`;
  `tuple(p)` `1 + m`, `append` 1.

**Bound: `197 + 2m' + 6m + J(99 + 33t) + C[perm.from_cycles](m', 2) + C[perm.from_cycles](m', m')`.**

### structure.align
opcount `(94, [(386, 15, 0), (388, 15, 0), (393, 26, 0), (397, 98, 0), (406, 8, 11), (407, 20, 0), (413, 9, 0)])`,
`<genexpr@415>` 18; sound `(98, [(386, 15), (388, 15), (393, 26), (397, 105), (406, 8), (407, 20), (413, 9)])`,
`<genexpr@415>` `(10, [(415, 8)])`.

Parameters: `C = max(C_A, C_B)`, `K`, `kappa`, `eta` (maxima over A, B), `J`, `t` of the Johnson
cells.  If the invariants differ the function returns after computing them (cost
`<= 98 + C[inv](A) + C[inv](B) + 5 + C(3kappa + 2)`, smaller than the bound below).  Otherwise
`C_A = C_B` (one invariant entry per cell) and the keys have the same sizes.
* Loops: 386, 388 (`C` iterations each): `30(C+1)`; 393 over the keys of `byA` (`K`):
  `26(K+1)`; 397 over `zip(ia, ib)` (`n_j` per key, `C` in all, `K` entries): `105(C + K)`; the
  Johnson branch runs for at most one cell (`a == A.johnson_cell`): 406 (`J` iterations)
  `8(J+1)`, 407 (`J`) `20(J+1)`; 413 (`s` per non-Johnson cell, `<= m` in all, `<= C` entries):
  `9(m + C)`; genexpr 415 (`m` elements): `10 + 8(m+1)`.
* Built-ins: the two invariants (callees) and their comparison `<= 5 + C(3kappa + 2)` (Lemma S2);
  two `enumerate` `2 + 2C`; `setdefault` + `append` `2C(2 + 2kappa)`; `set(byA)`, `set(byB)`
  `2(1 + K + K(1 + 2kappa))`, their comparison `<= 1 + K(1 + 2kappa) + K`; `[-1] * m` `1 + m`;
  per key `byA[k]`, `byB[k]` `2(1 + 2kappa)`, two `len`, `zip` `1 + n_j`; per cell two `len`;
  Johnson: two `items()` `2 + 2J`, `J` insertions and `J` lookups of frozenset keys `2J(4 + 3t)`;
  per non-Johnson cell two `sorted` and a `zip`: `<= 2m lambda(m) + 5m + 3C` in all; `any`
  `1 + m`; `tuple(p)` `1 + m`.
* Callees: `A.invariant()`, `B.invariant()`; if `need_even` and `sigma` is odd: `C[perm.parity](m)`,
  `B.odd_automorphism()`, `C[perm.mul](m)`.

**Bound: `215 + 158C + 7C kappa + 143K + 10K kappa + 25m + 2m lambda(m) + J(38 + 6t) + C[Structure.invariant](A) + C[Structure.invariant](B)
+ [C[perm.parity](m) + C[Structure.odd_automorphism](B) + C[perm.mul](m)]`.**  Substituting the
invariant bound and `K <= C <= m`:
**`C[align] <= 339 + (374 + 17kappa) m + 2m C[canon.canon](kappa) + 2m lambda(m)(2 + 3kappa(2eta+3)) + J(38 + 6t) + [need_even terms]`.**

### structure._hk
opcount/sound `(5, [])`.  **Bound: `5 + C[canon.canon](|x|)`.**

### structure.coloring_structure
opcount `(21, [(433, 13, 0), (435, 11, 12)])`; sound `(33, [(433, 13), (435, 11)])`.  No callers.
`G` = number of colours, `gamma` their maximal size.  Loops `13(m+1)`, `11(G+1)`; `range(m)`
`1 + m`; `setdefault` + `append` `m(2 + 2gamma)`; `items()` `1 + G`; `frozenset(vs)` `G + 3m`.
Callee `Structure(m, ...)` with `L0 = G`, keys `(tag, colour)` of size `1 + tau + gamma`.
**Bound: `59 + (19 + 2gamma)m + 13G + C[__init__](G, 1 + tau + gamma, 1 + max(h_tau, eta_g), 0)`.**

## 3. `babai_gi/wl.py`

Notation (1.4): `N = s.n` points, arity `k`, `P = N^k`, `M = k^k`, `q = k(k-1)/2`, `S` structures,
`lambda = lambda(N)`.  Colours stored in a `KStructure` are ints.

### wl.KStructure.__init__
opcount/sound `(27, [])`.  If `ncolors is None`: `max(colors)` `1 + L` (`L = len(colors)`).
**Bound: 27 if `ncolors` is given (every caller in the package), `28 + L` otherwise.**

### wl.KStructure.index
opcount `(12, [(43, 8, 0)])`; sound `(12, [(43, 8)])`.  Loop over `tup`: `l = len(tup)`
iterations, 1 entry.  **Bound: `12 + 8(l + 1) = 20 + 8l`** (`= 20 + 8k` in every call of the package).

### wl.KStructure.color
opcount/sound `(9, [])`; callee `index(tup)`.  **Bound: `29 + 8 len(tup)`.**

### wl.KStructure.vertex_color
opcount/sound `(13, [])`; `(v,) * k` `1 + k`; callee `index` (`20 + 8k`).  **Bound: `34 + 9k`.**
Used only by tests.

### wl.KStructure.prefix_vertex_coloring
opcount `(21, [(57, 17, 9)])`; sound `(30, [(57, 17)])`.  Assumption `l = len(prefix) <= k`.
Loop 57 over `range(N)`: `N` iterations, 1 entry.  Built-ins: `len` 1, `range` `1 + N`; per
iteration `tuple(prefix)` `1 + l`, `(v,) * rest` `1 + rest`, concatenation `1 + k`, callee
`index` `20 + 8k` (`l + rest = k`).
**Bound: `30 + 17(N+1) + 1 + (1 + N) + N(23 + 10k) = 49 + 41N + 10kN`.**

### wl.KStructure.prefix_pair_coloring
opcount/sound `(39, [])`; `tuple(prefix)` `1 + l`, `len` 1.  **Bound: `41 + l`.**

### wl.KStructure.prefix_pair_coloring.<c@67>
opcount/sound `(17, [])`.  Assumption `l <= k - 1` (callers: `l <= k - 2`), so the index tuple has
length `l + 1 + rest = k`.  `pre + (u,)` `2 + l`, `(v,) * rest` `1 + rest`, concatenation `1 + k`,
callee `index` `20 + 8k`.  **Bound: `40 + 10k`** per call (the callback of `ClassicalCC(C, c2)` in
`design.py` and of `design_lemma` in `soj.py`).

### wl.structure_from_function
opcount `(31, [(82, 7, 8), (85, 10, 0)])`; sound `(39, [(82, 7), (85, 10)])`.  No callers.  Loops
82 (over `product`, `P` iterations) and 85 (over `raw`, `P`): `17(P+1)`; `product` `1 + kP`,
`range` `1 + N`; `P` calls of `f`; `r not in indexer` and the insertion `2(1 + 2phi)` per tuple
(`phi` = maximal size of a value of `f`, set-free); `KStructure` 27.
**Bound: `85 + N + P(19 + k + 4phi) + P C[f]`.**

### wl.finalize_raw
opcount `(25, [(94, 7, 0), (97, 24, 0), (98, 6, 8)])`; sound `(28, [(94, 7), (97, 29), (98, 6)])`.
No callers.  `R_i = len(indexer)`, raw colours of size `<= phi`, height `<= theta`.  `sorted` over
`indexer.keys()`: `1 + R_i`, `R_i (5 + C[canon](phi))`, `6(theta+1)phi R_i lambda(R_i) + 2R_i + 1`;
loop 94 `7(R_i+1)`, `enumerate` `1 + R_i`, stores `R_i(1 + 2phi)`; loop 97 (`S` structures)
`29(S+1)`; per structure loop 98 `6(P+1)`, lookups `P(1 + 2phi)`, `KStructure` 27, `len` 1, `append` 1.
**Bound: `67 + R_i(17 + 2phi + C[canon](phi)) + 6(theta+1) phi R_i lambda(R_i) + S(64 + P(7 + 2phi))`.**

### wl._sort_key
opcount/sound `(5, [])`.  **Bound: `5 + C[canon.canon](|x|)`.**

### wl._all_maps
opcount `(15, [(109, 7, 9)])`; sound `(24, [(109, 7)])`.  The list comprehension iterates over
`product(range(k), repeat=k)`: `M = k^k` iterations, each tuple of length `k`.  `product` `1 + kM`,
`range` `1 + k`, `tuple(m)` `M(1 + k)`.  **Bound: `24 + 7(M+1) + 1 + kM + 1 + k + M(1 + k) = 33 + k + 8M + 2kM`.**

### wl.to_configuration
opcount `(59, [(125, 26, 0), (129, 36, 0), (131, 12, 0), (132, 12, 0), (135, 16, 0), (137, 10, 0), (145, 8, 0), (149, 19, 15), (149, 7, 9)])`;
sound `(77, [(125, 26), (129, 36), (131, 12), (132, 12), (135, 16), (137, 10), (145, 8), (149, 25), (149, 7)])`
(the two line-149 entries are the outer and the inner comprehension).

Loops and iteration counts (per call):
* 125 over `structures`: `S` iterations, 1 entry.
* 129 over `product(range(N), repeat=k)`: `P` iterations per entry, `S` entries.
* 131 over `range(k)`: `k` per tuple (`SPk` in all), `SP` entries.
* 132 over `range(i+1, k)`: `k - 1 - i` iterations, so `q` per tuple (`SPq`), `SPk` entries.
* 135 over `maps` (`_all_maps(k)`, `M` elements): `SPM` iterations, `SP` entries.
* 137 over `m` (`k` elements): `SPMk` iterations, `SPM` entries.
* 145 over `enumerate(order)`: `R = len(order)` iterations, where `R` = number of distinct
  signatures `<= SP`; 1 entry.
* 149 (outer) over `zip(structures, sigs_per)`: `S`; 149 (inner) over `sigs`: `P` per entry, `S` entries.

Instructions: `77 + 26(S+1) + 36(SP+S) + 12(SPk+SP) + 12(SPq+SPk) + 16(SPM+SP) + 10(SPMk+SPM) + 8(R+1) + 25(S+1) + 7(SP+S)`.

Signatures: `sig = (tuple(rho), tuple(sub))` with `|rho| = q`, `|sub| = M`: size
`sigma = q + M + 3`, height 2, set-free; one comparison in the sort `<= 3 sigma` (Lemma S3), one dict
operation `1 + 2 sigma`.

Built-ins per tuple: `product` `k`; `range(k)` `1 + k`; the `k` ranges of line 132 `k + q`;
`rho.append` `q`; `sub.append` `M`; `tuple(rho)` `1 + q`; `tuple(sub)` `1 + M`; `sigs.append` 1;
`setdefault` `1 + 2sigma`; the lookup `all_sigs[sg]` at line 149 `1 + 2sigma`.  Per structure:
`range(N)` + `product` + `append` `N + 3`; at line 149 `zip` step, `KStructure` (27), `len` : 29.
After the loops: `zip` 2, `keys()` `1 + R`, `sorted` `3 sigma R lambda(R) + 2R + 1`, `enumerate`
`1 + R`, stores `R(1 + 2sigma)`.

Callees: `_all_maps(k)` (`33 + k + 8M + 2kM`); `_summary(order, sigs_per)` (below, with
`sigma_x = sigma`); `trace(("F2", summary))` = `C[check](5 + S(R+1))` (the invariant has
`5 + S(R+1)` nodes).

Collected:

**`C_F2 = 277 + 186S + SN + SP(10Mk + 36M + 23q + 27k + 116) + SR(12 + 2sigma) + R(3q + 3M + 23) + 3 sigma R lambda(R) + k + 8M + 2kM`.**

For `S = 1` (all callers), `R <= P`: `C_F2 <= P(10Mk + 41M + 28q + 27k + 157) + 3 sigma P lambda(P) + 2kM + 8M + k + N + 463`.
Closed form for `N >= 2`, `k >= 1` (using `q <= M/2`, `k <= M`, `1 <= M`, `lambda(P) <= k lambda(N)`,
`3sigma <= 13.5M`, `P >= 2`, and `2kM + 8M + k + N + 463 <= PM(k + 237)`):
**`C_F2 <= N^k k^k (11k + 476 + 14 k lambda(N))`.**
For `k = 2`: `C_F2 <= 483N^2 + 48N^2 lambda(N) + N + 513`.

### wl._summary
opcount `(18, [(156, 23, 0), (158, 13, 0)])`, `<genexpr@160>` 20; sound `(18, [(156, 23), (158, 13)])`,
`<genexpr@160>` `(11, [(160, 9)])`.

Parameters: `S = len(sigs_per)`, `P = len(sigs)`, `R = len(order)`, signatures set-free of size
`<= sigma_x`.  Loops: 156 over `sigs_per` (`S`): `23(S+1)`; 158 over `sigs` (`P` per entry, `S`
entries): `13(SP + S)`; the genexpr (`R` elements per structure): `S(11 + 9(R+1))`.  Built-ins:
`d.get` + store per signature `2(1 + 2sigma_x)`; per structure `R` lookups `d[sg]` `R(1 + 2sigma_x)`,
`tuple(genexpr)` `1 + R`, `append` 1; `tuple(order)` `1 + R`, `hash` `2 + R sigma_x`,
`tuple(counts)` `1 + S`.  (For `S >= 2`, `d[sg]` raises `KeyError` if `sg` does not occur in
that structure: Finding C.)
**Bound: `45 + 59S + SP(15 + 4sigma_x) + SR(11 + 2sigma_x) + R(1 + sigma_x)`;** the result has
`3 + S(R+1)` nodes.

### wl.weisfeiler_leman
opcount `(29, [(172, 67, 1), (177, 38, 0), (180, 10, 9), (182, 43, 0), (183, 11, 9), (185, 22, 0), (193, 9, 0), (197, 19, 14), (197, 7, 9)])`,
`<genexpr@186>` 28; sound `(44, [(173, 76), (177, 44), (180, 10), (182, 49), (183, 11), (185, 22), (193, 9), (197, 25), (197, 7)])`,
`<genexpr@186>` `(11, [(186, 17)])` (the `while` range starts at line 173).

**Number of rounds.**  Let `R_r` be `len(order)` in round `r` (the number of distinct new colours,
over all structures) and `R_0 = cur[0].ncolors` at the first round.  The new colour of a tuple is
the rank of `sig = (colors[idx], rows)`, which contains the old colour; hence equal new colours imply
equal old colours and `R_r >= ` (number of distinct old colours).  Every structure of `new` gets
`ncolors = len(order)`, which is exactly the number of distinct colour values (all ranks
`0..len(order)-1` occur).  So for `r >= 2` the test of line 198 compares `R_r` with `R_{r-1}`, and
for `r = 1` with `R_0`; when the input's `ncolors` is exact (it is: the input comes from
`to_configuration`, whose `ncolors = len(order)` is the number of distinct colours), every round
that does not stop has `R_r >= R_{r-1} + 1`.  As `R_r <= SP` (number of tuples) and `R_0 >= 1`
(if `SP >= 1`), the number of rounds is
**`rho <= SP - c_0 + 1 <= SP`**, `c_0 = R_0` (for `refine_structures`: `c_0` = number of F2
classes `>=` number of distinct input colours, because F2 refines the input through the identity
map).  If `ncolors` were not exact the bound would be `SP + 1`; with `max_rounds`,
`rho <= max_rounds`.

**One round.**  Loops (per round): 177 over `cur` (`S`); 180 `range(k)` (`k` per structure); 182
over `enumerate(product(...))` (`P` per structure); 183 `range(k)` (`k` per tuple); 185 `range(N)`
(`N` per tuple); the genexpr `k` elements per (tuple, z); 193 over `enumerate(order)` (`R`); 197
outer `S`, inner `P` per structure.  Instructions per round:
`76 + 44(S+1) + 10S(k+1) + 49(SP+S) + 11SP(k+1) + 22SP(N+1) + SPN(28 + 17k) + 9(R+1) + 25(S+1) + 7(SP+S)`
(the `76` is the `while` range's own count per round; its entry adds one more 76 per call).

Signatures: `sig = (colors[idx], tuple(rows))`, `rows` = `N` tuples of `k` ints: size
`tau = N(k+1) + 3`, height 3, set-free: one sort comparison `<= 4tau`, one dict operation `1 + 2tau`;
`rows.sort()` compares `k`-tuples of ints: `<= 2(k+1)` each (Lemma S3).

Built-ins per tuple: `enumerate` + `product` `1 + k`; `range(k)` `1 + k`; `range(N)` `1 + N`; per `z`:
`range(k)` `1 + k`, `tuple(genexpr)` `1 + k`, `append` 1; `rows.sort()` `2(k+1) N lambda(N) + 2N + 1`;
`tuple(rows)` `1 + N`; `sigs.append` 1; `setdefault` `1 + 2tau`; lookup at line 197 `1 + 2tau`.
Per structure: `range(k)` `1 + k`; `range(N)`, `product`, `enumerate` `3 + N`; `append` 1; `zip`
step, `KStructure`, `len`: 29.  Per round: `zip` 2, `keys()` `1 + R`, `sorted`
`4tau R lambda(R) + 2R + 1`, `enumerate` `1 + R`, stores `R(1 + 2tau)`, `len(order)` 1.  Callees per
round: `_summary` (`sigma_x = tau`) and `trace(("WL", rounds, summary))` = `C[check](6 + S(R+1))`.

Collected:
**`W = SP(136 + 13k + 65N + 27Nk + 2(k+1) N lambda(N)) + S(229 + 11k + N) + 264 + R(15 + 3tau) + SR(12 + 2tau) + 4 tau R lambda(R)`**
per round, and **`C_WL <= 121 + S + rho * max_round W`** (outside 44, the `while` entry 76,
`list(structures)` `1 + S`).

For `S = 1`, `R <= P`: `W <= P(178 + 13k + 70N + 32Nk + 2(k+1)N lambda + 4(Nk + N + 3) lambda(P)) + 493 + 11k + N`.
With `lambda(P) <= k lambda`, `N >= 2` (so `N lambda >= 2`, `P >= 2`): `12k lambda <= 6kN lambda`,
`32Nk + 70N <= (32k + 70) N lambda`, `13k + 178 <= (6.5k + 89) N lambda`,
`493 + 11k + N <= P N lambda (124.5 + 3k)`:
**`W <= (4k^2 + 54k + 286) N^(k+1) lambda(N)`** and
**`C_WL <= 122 + (4k^2 + 54k + 286) N^(2k+1) lambda(N)`** (`rho <= N^k`).
For `k = 2`: `W <= N^2(204 + 134N + 30N lambda + 24 lambda) + 515 + N`, `rho <= N^2`.

### wl.refine_structures
opcount/sound `(9, [])`.  Callees `to_configuration(structures, trace)` and
`weisfeiler_leman(..., trace=trace)`; `trace` is a chooser's `check` (`C[check](s) = 53 + s`,
already substituted above) or `None`.  For one structure on `N >= 2` points:
**`C[refine_structures] <= 9 + C_F2 + C_WL <= 131 + N^k k^k (14 k lambda(N) + 11k + 476) + (4k^2 + 54k + 286) N^(2k+1) lambda(N)`.**
For `k = 2`: `C <= 644 + N + 998N^2 + 48N^2 lambda + N^3 + 204N^4 + 24N^4 lambda + 134N^5 + 30N^5 lambda <= (48 lambda(N) + 382) N^5`.
Calls of `check`: `1 + rho <= 1 + N^k`.  (Call sites: `main.hypergraph_structure` (`N = m`, `k = t`),
`main.case_3` (`N = m`, `k = P.k_for(n, m)`), `soj.bipartite_split_or_johnson` (`N = |V2|`,
`k = d <= 6 ceil(l)`), `classical_wl` (`k = 2`).)

### wl.classical_wl
opcount `(74, [(215, 9, 0), (216, 27, 0), (222, 6, 11), (223, 6, 9)])`, `<genexpr@225>` 21; sound
`(94, [(215, 9), (216, 27), (222, 6), (223, 6)])`, `<genexpr@225>` `(11, [(225, 10)])`.

Parameters: `N` points; colour values of `vertex_color` / `pair_color` set-free of size `<= nu`,
height `<= eta`; `raw` entries `("d", .)` / `("e", .)` have size `<= nu + 2`, height `<= eta + 1`;
`K = len(keys) <= N^2` distinct raw colours.  Loops: 215 (`N`) `9(N+1)`, 216 (`N` per entry, `N`
entries) `27(N^2 + N)`, 222 (`K`) `6(K+1)`, 223 (`N^2`) `6(N^2+1)`, genexpr (`K` elements)
`11 + 10(K+1)`.  Callbacks: `N` calls of `vertex_color`, `N(N-1)` of `pair_color`.  Built-ins:
ranges `1 + 2N + N^2`; `raw.append` `N^2`; `set(raw)` `1 + N^2(2nu + 5)`; `sorted(..., key=_sort_key)`
`K(5 + C[canon](nu+2)) + 6(eta+2)(nu+2) K lambda(K) + 2K + 1` (Lemma C); `enumerate` `1 + K`;
insertions `K(2nu + 5)`; lookups `idx[r]` `N^2(2nu + 5)`; `len` 1; `KStructure` 27; trace:
`raw.count(kk)` for each key `K(1 + N^2(nu + 2))` (Lemma S2), `tuple(...)` twice `2 + 2K`,
`hash(tuple(keys))` `2 + K(nu + 2)`, `C[check](K + 4) = 57 + K`.  Callee
`refine_structures([X], trace)` with `k = 2`.

**Bound: `229 + 38N + (45 + 4nu)N^2 + (35 + 3nu)K + K C[canon.canon](nu + 2) + 6(eta+2)(nu+2) K lambda(K) + (nu + 2) K N^2
+ N C[vertex_color] + N(N-1) C[pair_color] + C[refine_structures](N, k=2)`.**
Closed form (`K <= N^2`, `lambda(K) <= 2 lambda(N)`, `N >= 2`):
**`C[classical_wl] <= (48 lambda(N) + 382) N^5 + (nu + 2) N^4 + 12(eta+2)(nu+2) N^2 lambda(N) + (80 + 7nu) N^2 + N^2 (C_cb + C[canon.canon](nu+2)) + 38N + 229`,**
`C_cb = max(C[vertex_color], C[pair_color])`.  The term `(nu+2)N^4` is the quadratic
`raw.count` of the trace.  (Caller `soj.bipartite_split_or_johnson`: `vcol` returns
`("v1", canon(key))` / `("v2", col, canon(key))`, so `nu <= 3 kappa + 3` (height `<= 2 eta + 2`) with `kappa`, `eta` the key
size and height of `base` (Lemma C); `pcol` values have `<= 3` nodes.)

## 4. `babai_gi/cc.py`

Notation (1.4): `N` vertices, `r = len(self.colors) <= N^2`, `r'` off-diagonal colours, colour
values set-free of size `<= gamma`, height `<= eta_g` (`gamma = 1`, `eta_g = 0` for every
`ClassicalCC` of the repository).  A comparison `x == color` of two colours costs the instruction
plus at most `gamma` (Lemma S2); it is charged as `+gamma` (an over-count of 1 for ints).

### cc.ClassicalCC.__init__
opcount `(70, [(27, 6, 12), (27, 7, 11), (28, 9, 9), (29, 6, 12), (31, 8, 0)])`; sound
`(106, [(27, 14), (27, 7), (28, 9), (29, 6), (31, 8)])` (line 27: outer, inner comprehension).

* Loops: 27 outer over `V` (`N` iterations, 1 entry) `14(N+1)`; 27 inner over `V` (`N` per entry,
  `N` entries) `7(N^2 + N)`; 28 `range(N)` `9(N+1)`; 29 `enumerate(V)` `6(N+1)`; 31 over the rows
  `8(N+1)`.
* **Callback calls: exactly `N^2`** (`color(u, v)` once for every `(u, v)` in `V x V`), each
  `C[color]`.
* Built-ins: `list(vertices)` `1 + N`; `len` 1; `range` `1 + N`; `enumerate` `1 + N`; `pos[v] = i`
  `3N` (vertices are ints); `set()` 1; `cols.update(row)` `N` calls, `N^2(1 + 2gamma)` insertions;
  `sorted(cols, key=_hk)` with `r` colours: `r(5 + C[canon](gamma)) + 6(eta_g+1) gamma r lambda(r)
  + 2r + 1`, set iteration `r`.

**Bound: `150 + 51N + (8 + 2gamma) N^2 + N^2 C[color] + r(8 + C[canon.canon](gamma)) + 6(eta_g+1) gamma r lambda(r)`.**
Int colours, `r <= N^2`: **`<= 150 + 51N + N^2 (C[color] + 18 + C[canon.canon](1)) + 12 N^2 lambda(N)`.**
Callers: `design.py:63` (`color` = `prefix_pair_coloring` closure, `40 + 10k`), `main.py:944,954`
(`color_of` lookups), `soj.py:527` (`Xc.color`, `45`), `induced` (18).

### cc.ClassicalCC.key
opcount/sound `(11, [])`.  With keys: one lookup `D = 1 + 2gamma`.  **Bound: `12 + 2gamma`.**

### cc.ClassicalCC.set_keys
opcount/sound `(4, [])`.  **Bound: 4.**

### cc.ClassicalCC.vertex_classes
opcount `(16, [(48, 13, 0)])`; sound `(16, [(48, 13)])`.  No callers.  Loop over `enumerate(V)`
(`N`): `13(N+1)`; `defaultdict` 1, `enumerate` `1 + N`, `d[vcol]` + `append` `N(2 + 2gamma)`,
`dict(d)` `<= 1 + N(1 + 2gamma)`.  **Bound: `32 + (17 + 4gamma)N`.**

### cc.ClassicalCC.is_homogeneous
opcount/sound `(10, [])`.  `set(self.vcol)` `1 + N(1 + 2gamma)`, `len` 1.  **Bound: `12 + (1 + 2gamma)N`.**

### cc.ClassicalCC.diagonal_colors
opcount/sound `(6, [])`.  **Bound: `7 + (1 + 2gamma)N`.**  Returns a set of `<= N` colours.

### cc.ClassicalCC.off_diagonal_colors
opcount `(14, [(60, 9, 9)])`; sound `(23, [(60, 9)])`.  Callee `diagonal_colors`; loop over
`self.colors` (`r`): `9(r+1)`, `col not in d` `r(1 + 2gamma)`.
**Bound: `39 + (10 + 2gamma) r + (1 + 2gamma) N`.**  Returns the `r'` off-diagonal colours.

### cc.ClassicalCC.paired
opcount `(20, [(66, 10, 0), (67, 22, 0)])`; sound `(20, [(66, 10), (67, 22)])`.
First call (`self._paired is None`): loops `10(N+1)` and `22(N^2 + N)`, ranges `1 + 2N + N^2`,
`col not in p` `N^2(1 + 2gamma)`, `<= r` insertions, the final lookup.
**Bound (first call): `31 + 34N + 23N^2 + (N^2 + r + 1)(1 + 2gamma)`; later calls: `21 + 2gamma`**
(`_paired` is assigned only in `__init__` (to `None`) and here (to a dict), so after the first call
the cache is always hit).

### cc.ClassicalCC.out_neighbors
opcount `(17, [(76, 11, 9)])`; sound `(26, [(76, 11)])`.  No callers.
**Bound: `26 + 11(N+1) + (1 + N) + gamma N = 38 + (12 + gamma)N`.**

### cc.ClassicalCC.in_neighbors
opcount `(12, [(79, 14, 9)])`; sound `(21, [(79, 14)])`.
**Bound: `21 + 14(N+1) + (1 + N) + gamma N = 36 + (15 + gamma)N`.**

### cc.ClassicalCC.out_degree
opcount `(16, [])`, `<genexpr@82>` 22; sound `(16, [])`, `<genexpr@82>` `(11, [(82, 11)])`.  The
genexpr runs over the `N` entries of the row: `11 + 11(N+1)` plus `gamma N` for the comparisons;
`sum` `1 + N`.  **Bound: `39 + (12 + gamma)N`.**

### cc.ClassicalCC.constituent_vertex_classes
opcount `(16, [(87, 10, 0), (88, 29, 0)])`; sound `(16, [(87, 10), (88, 29)])`.  No callers.
Loops `10(N+1)`, `29(N^2 + N)`; ranges `1 + 2N + N^2`; comparisons `gamma N^2`; two `set()` 2;
`<= 2N^2` insertions of colours `2N^2(1 + 2gamma)`.  **Bound: `29 + 41N + (32 + 5gamma)N^2`.**

### cc.ClassicalCC.components
opcount `(39, [(104, 15, 0), (106, 30, 0), (112, 12, 0)])`, `<find@98>` `(4, [(99, 19, 6)])`;
sound `(39, [(104, 15), (106, 30), (112, 12)])`, `<find@98>` `(10, [(100, 19)])`.

* `find(x)`: the `while` loop follows parent pointers.  `parent` always encodes a forest on
  `range(N)`: initially all roots; a union sets `parent[ri] = rj` for two *different roots* `ri`,
  `rj` (so no cycle is created); path halving sets `parent[x]` to its grandparent (an ancestor).
  Each iteration replaces `x` by its former grandparent, so the depth of `x` decreases by `>= 1`:
  at most `N - 1` iterations.  `C[find] <= 10 + 19N` (Lemma 0: `10 + 19(it + 1)`).
* Loops: 104 `range(N)` `15(N+1)`; 106 `range(N)` per row (`N^2` iterations, `N` entries)
  `30(N^2 + N)`; 112 `range(N)` `12(N+1)`.
* `find` is called twice per arc `(i, j)`, `i != j`, of colour `color` (`E <= N(N-1)` arcs) and
  `N` times at the end: `2E + N` calls.
* Built-ins: `list(range(N))` `2 + 2N`; the ranges `2 + 3N + N^2`; comparisons `gamma N^2`;
  `defaultdict` 1; `groups[find(i)].append(i)` `4N`; `list(groups.values())` `<= 2 + N`.

**Bound: `73 + 67N + (31 + gamma)N^2 + (2E + N)(10 + 19N) <= 38N^3 + (32 + gamma)N^2 + 57N + 73`.**

### cc.ClassicalCC.effective_vertices
opcount `(15, [(118, 15, 0), (120, 19, 0)])`; sound `(15, [(118, 15), (120, 19)])`.
Loops `15(N+1)`, `19(N^2 + N)`; `set()` 1; ranges `1 + 2N + N^2`; comparisons `gamma N^2`;
`out.add` twice per matching pair `<= 6N^2`; `sorted(out)` (`<= N` ints) `N lambda(N) + 2N + 1`.
**Bound: `33 + 38N + (26 + gamma)N^2 + N lambda(N)`.**

### cc.ClassicalCC.is_clique
opcount/sound `(16, [])`.  Callees `is_homogeneous`, `off_diagonal_colors`; `len` 1.
**Bound: `68 + 2(1 + 2gamma)N + (10 + 2gamma) r`.**

### cc.ClassicalCC.disconnected_off_diagonal_colors
opcount `(12, [(133, 34, 0)])`, `<genexpr@135>` 25; sound `(12, [(133, 34)])`, `<genexpr@135>`
`(11, [(135, 14)])`.

Loop 133 over the `r'` off-diagonal colours: `34(r'+1)`.  Per colour `col` (with `E_col` arcs of
colour `col`; `sum_col E_col <= N(N-1)` since every off-diagonal pair has one colour):
`effective_vertices` (callee), `set(...)` `1 + 3N`, `components` (callee, `<= N` components with
`sum |cmp| = N`), the genexpr `11 + 14(N+1)`, `effset.intersection(cmp)` per component
`1 + |effset| + 3|cmp|` (`<= N^2 + 4N` in all), `sum` `1 + N`, `append` 1.  Callee
`off_diagonal_colors` once.  Summing, with the bounds of `components` (`73 + 67N + (31+gamma)N^2 +
(2E_col + N)(10 + 19N)`) and `effective_vertices`:

**Bound: `85 + (10 + 2gamma) r + (1 + 2gamma)N + r'(168 + 137N + (77 + 2gamma)N^2 + N lambda(N)) + 38N^3 - 18N^2 - 20N`;**
for int colours **`<= 85 + 12r + 38N^3 + r'(168 + 137N + 79N^2 + N lambda(N))`**, i.e. `O(N^4)`
in general (`r' <= N(N-1)`) and `O(N^3)` for homogeneous coherent input (`r' <= N - 1`).

### cc.ClassicalCC.is_primitive
opcount `(14, [(144, 12, 2)])`; sound `(16, [(144, 12)])`.  Callees `is_homogeneous`,
`off_diagonal_colors`, `components` for each of the `<= r'` off-diagonal colours (early exit
possible), `len` 1 each.
**Bound: `79 + 2(1 + 2gamma)N + (10 + 2gamma)r + r'(86 + 77N + (50 + gamma)N^2) + 38N^3 - 18N^2 - 20N`;**
int colours: **`<= 79 + 12r + r'(86 + 77N + 51N^2) + 38N^3`.**

### cc.ClassicalCC.is_uniprimitive
opcount/sound `(16, [])`.  Callees `is_primitive`, `off_diagonal_colors`; `len` 1.
**Bound (int colours): `<= 135 + 24r + r'(86 + 77N + 51N^2) + 38N^3`.**

### cc.ClassicalCC.induced
opcount/sound `(26, [])`, `<lambda@157>` `(12, [])`.  `N' = len(subset)`; assumption
`subset` `<= self.vertices` (the `pos` lookups succeed).  `list(subset)` `1 + N'`; the colour
callback is the lambda: 12 instructions + two int lookups (6): `C[color] = 18`; callee
`ClassicalCC(sub, lambda, keys)` with `N'` vertices and `r'' <= min(r, N'^2)` colours.
**Bound: `177 + 52N' + (26 + 2gamma)N'^2 + r''(8 + C[canon.canon](gamma)) + 6(eta_g+1) gamma r'' lambda(r'')`.**

### cc.ClassicalCC.strong_twin_classes
opcount `(42, [(176, 20, 0), (179, 62, 0), (186, 26, 4), (195, 15, 0)])`, `<find@170>`
`(4, [(171, 19, 6)])`; sound `(42, [(176, 20), (179, 66), (186, 26), (195, 15)])`, `<find@170>`
`(10, [(172, 19)])`.  Only reached through `largest_twin_class_size`, which has no callers.
Loops: 176 `N`; 179 over `range(i+1, N)`: `<= N(N-1)/2` iterations in all, `<= N` entries; 186
over `range(N)`: `<= N` per entry, `<= N(N-1)/2` entries; 195 `N`.  `find` (`<= 10 + 19N`, same
forest argument) is called `<= 2N + 4 * N(N-1)/2 <= 2N^2` times.  Built-ins: ranges and
comparisons `<= 6 + 9N + (1 + gamma)N^2 + (1/2 + gamma)N^3`.
**Bound: `<= 83 + 64N + (54 + gamma)N^2 + (51.5 + gamma)N^3`.**

### cc.ClassicalCC.largest_twin_class_size
opcount `(11, [])`, genexpr 19; sound `(11, [])`, `<genexpr@200>` `(10, [(200, 9)])`.  No callers.
**Bound: `31 + 11N + C[strong_twin_classes]`.**

### cc.ClassicalCC.canonical_keys
opcount `(41, [(218, 9, 0), (219, 13, 0), (222, 21, 0), (224, 21, 0), (229, 23, 0), (232, 50, 1), (234, 32, 0), (239, 8, 11), (240, 8, 8)])`,
`<genexpr@235>` 28; sound `(49, [(218, 9), (219, 13), (222, 21), (224, 21), (229, 23), (233, 62), (234, 32), (239, 8), (240, 8)])`,
`<genexpr@235>` `(11, [(235, 17)])`.

Only caller: `main.case_2b_structure`, int colours (`gamma = 1`); the bound is stated for `gamma = 1`.
`r` = number of colours (= `len(rep)` = `len(cols)`), `pi_c = |p[col]| <= N` (one entry per `z`).

**Rounds.**  `new[col]` has `key[col]` as first component, so the partition of the colours by `new`
refines the one by `key`, and `len(uniq) >= d := len(set(key.values()))`.  If the loop does not stop,
`len(uniq) > d`, and `key := comp` has exactly `len(uniq)` distinct values (every element of `uniq` is
some `new[col]`).  So `d` increases strictly in every round that does not stop, `1 <= d <= r`:
**`W <= r` rounds** (more precisely `r - d_1 + 1`).

Sizes: initial keys `(bool, int, int)` (4 nodes, height 1), later ints; an item
`(key[a], key[b], v)` has `<= 10` nodes, height `<= 2`: comparison `<= 30`; `new[col]` has
`<= 10 + 10N` nodes, height `<= 4`: one dict operation `21 + 20N`, one comparison of canonical images
`Omega(10 + 10N, 4) = 300(1 + N)`; `u = len(uniq) <= r`.

* Instructions (sound profile): `164 + 22N + 13N^2 + 65r + 21rN + 110W + 76Wr + 17WrN`
  (loops 218: `N`; 219: `N^2`, `N` entries; 222: `r`; 224: `N` per colour; 229: `r`; `while`: `W`;
  234: `r` per round; 239: `u` per round; 240: `r` per round; the genexpr `pi_c` elements per
  (round, colour), `sum_c pi_c <= rN`).
* Set-up built-ins: ranges `1 + 2N + N^2`; `rep.setdefault` `3N^2`; `rep.items()` `1 + r`; per colour
  `defaultdict`, `range` `2 + N`, the counts `cnt[(a,b)] += 1` `14N`, `dict(cnt)` `1 + 7N`, `p[col]=` 3;
  `diagonal_colors` `7 + 3N`; per colour of loop 229: three lookups 9, `out_degree` `39 + 13N`,
  `in_neighbors` `36 + 16N`, `len` 1.  Sum `9 + 5N + 4N^2 + 92r + 51rN`.
* `paired`: first call `34 + 34N + 26N^2 + 3r`, later `23` each (counted in the round terms).
* Per round: per colour `items()` `1 + pi_c`, the genexpr's lookups `6pi_c`, `sorted(items)`
  `30 pi_c lambda(pi_c) + 2pi_c + 1`, three lookups 9, `paired` 23, `tuple(items)` `1 + pi_c`; then
  `values()`, `set(...)` `1 + r(21 + 20N)`, `sorted(..., key=_hk)`
  `u(5 + C[canon](10N+10)) + 300(1+N) u lambda(u) + 2u + 1`, `enumerate` + insertions
  `1 + u(22 + 20N)`, `comp` `r(24 + 20N)`, `set(key.values())` `2 + 10r`, `len` 2.  Sum per round
  `<= 8 + 91r + 50rN + 30rN lambda(N) + u(30 + 20N + C[canon](10N+10)) + 300(1 + N) u lambda(u)`.

**Bound: `207 + 61N + 43N^2 + 160r + 72rN + W [118 + 167r + 67rN + 30 rN lambda(N) + u(30 + 20N + C[canon.canon](10N+10)) + 300(1+N) u lambda(u)]`;**
with `W, u <= r <= N^2`, `lambda(u) <= 2 lambda(N)`:
**`<= 207 + 61N + 43N^2 + 278r + 72rN + r^2 (197 + 87N + C[canon.canon](10N + 10) + (630N + 600) lambda(N))`.**

### cc._hk
opcount/sound `(5, [])`.  **Bound: `5 + C[canon.canon](|x|)`.**

### cc.cc_from_pair_coloring
opcount/sound `(5, [])`.  No callers.  **Bound: `5 + C[ClassicalCC.__init__](N, C[c])`.**

## 5. Final table (closed forms, in-module callees substituted)

Symbols: `lambda = lambda(.)` = `ceil(log2 .)`; `Cc(s) = C[canon.canon](s)`; `FC(n,l) = C[perm.from_cycles](n,l)`;
`PAR(n) = C[perm.parity](n)`; `MUL(n) = C[perm.mul](n)`; caller-given callbacks `C[f]`, `C[color]`,
`C[proc]`, ...  Parameters as in the subsections (`m`, `C`, `C'`, `K`, `kappa`, `eta`, `J`, `t`, `m'`
for structures; `N`, `k`, `P = N^k`, `M = k^k`, `S` for WL; `N`, `r`, `r'`, `gamma` for configurations).
Every function: solver calls none.

| function | bound for one call |
|---|---|
| `structure.Fixed.__init__` | 4 |
| `structure.Fixed.__eq__` | `16 + \|value\| + \|other.value\|` |
| `structure.Fixed.__hash__` | `11 + \|value\|` |
| `structure.Fixed.__repr__` | `18 + 2 len(repr(value))` (diagnostics only) |
| `structure.Fixed.canon_value` | 4 |
| `structure.apply_obj` | `(130 + 15 h(obj)) \|obj\|` (`\|obj\|` recursive invocations) |
| `structure.Chooser.choose`, `.check` | 4 each |
| `structure.Chooser.choose_index` | `116 + k` (no callers) |
| `structure.RecordingChooser.__init__` | 8 |
| `structure.RecordingChooser.choose` | 33 |
| `structure.RecordingChooser.check` | 11 |
| `structure.ReplayChooser.__init__` | `22 + \|path\|` |
| `structure.ReplayChooser._next_event` | 30 |
| `structure.ReplayChooser.choose` | 104 |
| `structure.ReplayChooser.check` | `53 + \|invariant\|` |
| `structure.enumerate_runs` | `12 + R(123 + 21D) + sum_runs C[proc]`, `R <= prod_{d<=D} k_d` |
| `structure.JohnsonCell.__init__`, `.invariant` | 8 each |
| `structure.Structure.__init__` | `47 + 15L0 + 3m + C[_normalize]` `<= 193 + 77L0 + 6m + m lambda(m) + L0 J + L0 Cc(kappa_in+2) + L0 lambda(L0)(4 + 1.5m + 3(kappa_in+2)(2eta_in+5))` |
| `structure.Structure._normalize` | `146 + 62C + 3m + m lambda(m) + CJ + C Cc(kappa_in+2) + C lambda(C)(4 + 1.5m + 3(kappa_in+2)(2eta_in+5))` |
| `structure.Structure.cell_of` | `23 + 17C + 10m <= 23 + 27m` |
| `structure.Structure.key_of_vertex` | `18 + 14C + 10m <= 18 + 24m` |
| `structure.Structure.invariant` | `62 + 24C + C Cc(kappa) + C lambda(C)(1 + 3kappa(2eta+3))` |
| `structure.Structure.max_cell_size` | `31 + 12C` (no callers) |
| `structure.Structure.is_trivial` | 17 (tests only) |
| `structure.Structure.refine` | `291 + (213 + 4phi)m + 3Jm + m C[f] + m(Cc(phi) + Cc(kappa+tau+phi+3)) + m lambda(m)(1.5m + 5 + 6(theta+1)phi + 3(kappa+tau+phi+3)(2eta'+5))`, `eta' = max(eta, h(tag), theta) + 1` |
| `structure.Structure.individualize` | `303 + 227m + 3Jm + m(Cc(1) + Cc(kappa+tau+4)) + m lambda(m)(1.5m + 11 + 3(kappa+tau+4)(2eta'+5))` |
| `structure.Structure.mark` | `308 + 3\|S\| + 230m + 3Jm + m(Cc(1) + Cc(kappa+tau+4)) + m lambda(m)(1.5m + 11 + 3(kappa+tau+4)(2eta'+5))` |
| `structure.Structure.split_cell` | `98 + 2C + 14C_n + B(21 + m) + 4m_b + 3m + C_n J + C[__init__](C_n, kappa+tau+1)` (no callers) |
| `structure.Structure.with_johnson` | `205 + 78C + 6m + m lambda(m) + CJ + C Cc(kappa+2) + C lambda(C)(4 + 1.5m + 3(kappa+2)(2eta+5))` |
| `structure.Structure.aut_gens` | `186 + (266 + 2kappa)m + 3m^2 + 2m lambda(m) + 2K max_s FC(m, s) + [197 + 2m' + 6m + J(99 + 33t) + FC(m',2) + FC(m',m')]`; returns `<= 4K` generators |
| `structure.Structure.aut_order` | `92 + (19 + 2kappa)C + 55K + m + m'` (tests only) |
| `structure.Structure.has_odd_automorphism` | `99 + (18 + 2kappa)C + 65K + t` (no callers) |
| `structure.Structure.odd_automorphism` | `21 + 36K + C[aut_gens] + 4K PAR(m)` |
| `structure._johnson_cell_gens` | `197 + 2m' + 6m + J(99 + 33t) + FC(m',2) + FC(m',m')` |
| `structure.align` | `339 + (374 + 17kappa)m + 2m Cc(kappa) + 2m lambda(m)(2 + 3kappa(2eta+3)) + J(38 + 6t)` `+ [PAR(m) + MUL(m) + C[odd_automorphism](B)]` if `need_even` |
| `structure._hk` | `5 + Cc(\|x\|)` |
| `structure.coloring_structure` | `59 + (19 + 2gamma)m + 13G + C[__init__](G, 1 + tau + gamma)` (no callers) |
| `wl.KStructure.__init__` | 27 (`28 + len(colors)` if `ncolors is None`) |
| `wl.KStructure.index` | `20 + 8 len(tup)` |
| `wl.KStructure.color` | `29 + 8 len(tup)` |
| `wl.KStructure.vertex_color` | `34 + 9k` (tests only) |
| `wl.KStructure.prefix_vertex_coloring` | `49 + 41N + 10kN` |
| `wl.KStructure.prefix_pair_coloring` | `41 + len(prefix)` |
| `wl.KStructure.prefix_pair_coloring.<c@67>` | `40 + 10k` per call |
| `wl.structure_from_function` | `85 + N + P(19 + k + 4phi) + P C[f]` (no callers) |
| `wl.finalize_raw` | `67 + R_i(17 + 2phi + Cc(phi)) + 6(theta+1)phi R_i lambda(R_i) + S(64 + P(7 + 2phi))` (no callers) |
| `wl._sort_key` | `5 + Cc(\|x\|)` |
| `wl._all_maps` | `33 + k + 8k^k + 2k^(k+1)` |
| `wl.to_configuration` | `277 + 186S + SN + SP(10Mk + 36M + 23q + 27k + 116) + SR(12 + 2sigma) + R(3q + 3M + 23) + 3sigma R lambda(R) + k + 8M + 2kM`; `S = 1`, `N >= 2`: `<= N^k k^k (11k + 476 + 14k lambda(N))` |
| `wl._summary` | `45 + 59S + SP(15 + 4sigma_x) + SR(11 + 2sigma_x) + R(1 + sigma_x)` |
| `wl.weisfeiler_leman` | `121 + S + rho W`, `rho <= SP - c_0 + 1`, `W` as in Section 3; `S = 1`, `N >= 2`: `<= 122 + (4k^2 + 54k + 286) N^(2k+1) lambda(N)` |
| `wl.refine_structures` | `S = 1`, `N >= 2`: `131 + N^k k^k (14k lambda(N) + 11k + 476) + (4k^2 + 54k + 286) N^(2k+1) lambda(N)`; `k = 2`: `(48 lambda(N) + 382) N^5` |
| `wl.classical_wl` | `(48 lambda(N) + 382)N^5 + (nu+2)N^4 + 12(eta+2)(nu+2)N^2 lambda(N) + (80 + 7nu)N^2 + N^2(C_cb + Cc(nu+2)) + 38N + 229` |
| `cc.ClassicalCC.__init__` | `150 + 51N + (8 + 2gamma)N^2 + N^2 C[color] + r(8 + Cc(gamma)) + 6(eta_g+1)gamma r lambda(r)` (`N^2` callback calls) |
| `cc.ClassicalCC.key` | `12 + 2gamma` |
| `cc.ClassicalCC.set_keys` | 4 |
| `cc.ClassicalCC.vertex_classes` | `32 + (17 + 4gamma)N` (no callers) |
| `cc.ClassicalCC.is_homogeneous` | `12 + (1 + 2gamma)N` |
| `cc.ClassicalCC.diagonal_colors` | `7 + (1 + 2gamma)N` |
| `cc.ClassicalCC.off_diagonal_colors` | `39 + (10 + 2gamma)r + (1 + 2gamma)N` |
| `cc.ClassicalCC.paired` | first call `31 + 34N + 23N^2 + (N^2 + r + 1)(1 + 2gamma)`, later `21 + 2gamma` |
| `cc.ClassicalCC.out_neighbors` | `38 + (12 + gamma)N` (no callers) |
| `cc.ClassicalCC.in_neighbors` | `36 + (15 + gamma)N` |
| `cc.ClassicalCC.out_degree` | `39 + (12 + gamma)N` |
| `cc.ClassicalCC.constituent_vertex_classes` | `29 + 41N + (32 + 5gamma)N^2` (no callers) |
| `cc.ClassicalCC.components` | `73 + 67N + (31 + gamma)N^2 + (2E + N)(10 + 19N) <= 38N^3 + (32 + gamma)N^2 + 57N + 73` |
| `cc.ClassicalCC.components.<find@98>` | `10 + 19N` |
| `cc.ClassicalCC.effective_vertices` | `33 + 38N + (26 + gamma)N^2 + N lambda(N)` |
| `cc.ClassicalCC.is_clique` | `68 + 2(1 + 2gamma)N + (10 + 2gamma)r` |
| `cc.ClassicalCC.disconnected_off_diagonal_colors` | `85 + (10 + 2gamma)r + (1 + 2gamma)N + r'(168 + 137N + (77 + 2gamma)N^2 + N lambda(N)) + 38N^3 - 18N^2 - 20N` |
| `cc.ClassicalCC.is_primitive` | `79 + 2(1 + 2gamma)N + (10 + 2gamma)r + r'(86 + 77N + (50 + gamma)N^2) + 38N^3 - 18N^2 - 20N` |
| `cc.ClassicalCC.is_uniprimitive` | int colours: `135 + 24r + r'(86 + 77N + 51N^2) + 38N^3` |
| `cc.ClassicalCC.induced` | `177 + 52N' + (26 + 2gamma)N'^2 + r''(8 + Cc(gamma)) + 6(eta_g+1)gamma r'' lambda(r'')` |
| `cc.ClassicalCC.strong_twin_classes` | `83 + 64N + (54 + gamma)N^2 + (51.5 + gamma)N^3` (only via an uncalled function) |
| `cc.ClassicalCC.strong_twin_classes.<find@170>` | `10 + 19N` |
| `cc.ClassicalCC.largest_twin_class_size` | `31 + 11N + C[strong_twin_classes]` (no callers) |
| `cc.ClassicalCC.canonical_keys` | int colours: `207 + 61N + 43N^2 + 278r + 72rN + r^2(197 + 87N + Cc(10N+10) + (630N + 600) lambda(N))` |
| `cc._hk` | `5 + Cc(\|x\|)` |
| `cc.cc_from_pair_coloring` | `5 + C[ClassicalCC.__init__]` (no callers) |

Functions not reached by the solver (no bound needed by the specification, bounds given anyway):
used only by tests: `Structure.aut_order`, `Structure.is_trivial`, `KStructure.vertex_color`;
diagnostics: `Fixed.__repr__`; no callers at all: `Chooser.choose_index`, `Structure.max_cell_size`,
`Structure.split_cell`, `Structure.has_odd_automorphism`, `coloring_structure`,
`structure_from_function`, `finalize_raw`, `ClassicalCC.vertex_classes`, `.out_neighbors`,
`.constituent_vertex_classes`, `.strong_twin_classes`, `.largest_twin_class_size`,
`cc_from_pair_coloring`.

## 6. Profile numbers

### 6.1 `opcount.generate()`, as required by the specification
Functions and inner `def`s (`<find@98>`, `<find@170>`, `<c@67>`): `(outside, [(line, cycle, entry), ...])`;
generator expressions and lambdas: the dict `{"total": ..., "loops": ...}` exactly as `generate()`
returns it.

```python
OPCOUNT_PROFILES = {'structure.Fixed.__init__': (4, []),
 'structure.Fixed.__eq__': (15, []),
 'structure.Fixed.__hash__': (8, []),
 'structure.Fixed.__repr__': (9, []),
 'structure.Fixed.canon_value': (4, []),
 'structure.apply_obj': (92, [(70, 8, 9)]),
 'structure.apply_obj.<genexpr@66>': {'total': 21, 'loops': 1},
 'structure.apply_obj.<genexpr@68>': {'total': 21, 'loops': 1},
 'structure.Chooser.choose': (3, []),
 'structure.Chooser.check': (3, []),
 'structure.Chooser.choose_index': (10, []),
 'structure.RecordingChooser.__init__': (8, []),
 'structure.RecordingChooser.choose': (30, []),
 'structure.RecordingChooser.check': (10, []),
 'structure.ReplayChooser.__init__': (21, []),
 'structure.ReplayChooser._next_event': (28, []),
 'structure.ReplayChooser.choose': (66, []),
 'structure.ReplayChooser.check': (22, []),
 'structure.enumerate_runs': (10, [(145, 65, 2), (156, 17, 12)]),
 'structure.JohnsonCell.__init__': (8, []),
 'structure.JohnsonCell.invariant': (8, []),
 'structure.Structure.__init__': (21, [(183, 14, 12)]),
 'structure.Structure._normalize': (89, [(190, 12, 12), (194, 12, 0), (198, 7, 9)]),
 'structure.Structure._normalize.<lambda@197>': {'total': 18, 'loops': 0},
 'structure.Structure.cell_of': (12, [(207, 10, 0), (208, 6, 0)]),
 'structure.Structure.key_of_vertex': (10, [(214, 8, 0), (215, 6, 0)]),
 'structure.Structure.invariant': (26, []),
 'structure.Structure.invariant.<genexpr@220>': {'total': 24, 'loops': 1},
 'structure.Structure.max_cell_size': (10, []),
 'structure.Structure.max_cell_size.<genexpr@224>': {'total': 20, 'loops': 1},
 'structure.Structure.is_trivial': (16, []),
 'structure.Structure.refine': (51, [(235, 34, 0), (237, 15, 0), (239, 15, 0), (246, 12, 0)]),
 'structure.Structure.individualize': (12, []),
 'structure.Structure.individualize.<lambda@254>': {'total': 10, 'loops': 0},
 'structure.Structure.mark': (16, []),
 'structure.Structure.mark.<lambda@258>': {'total': 10, 'loops': 0},
 'structure.Structure.split_cell': (63, [(266, 18, 0), (276, 12, 0)]),
 'structure.Structure.with_johnson': (11, []),
 'structure.Structure.aut_gens': (25,
                                  [(290, 15, 0), (292, 136, 0), (303, 12, 8), (306, 10, 0), (311, 22, 0), (313, 7, 0)]),
 'structure.Structure.aut_order': (26, [(322, 15, 0), (324, 49, 0)]),
 'structure.Structure.has_odd_automorphism': (17, [(335, 15, 0), (337, 62, 2)]),
 'structure.Structure.odd_automorphism': (8, [(350, 9, 4)]),
 'structure._johnson_cell_gens': (60, [(360, 6, 11), (367, 23, 0), (369, 18, 0)]),
 'structure._johnson_cell_gens.<genexpr@370>': {'total': 20, 'loops': 1},
 'structure.align': (94,
                     [(386, 15, 0), (388, 15, 0), (393, 26, 0), (397, 98, 0), (406, 8, 11), (407, 20, 0), (413, 9, 0)]),
 'structure.align.<genexpr@415>': {'total': 18, 'loops': 1},
 'structure._hk': (5, []),
 'structure.coloring_structure': (21, [(433, 13, 0), (435, 11, 12)]),
 'wl.KStructure.__init__': (27, []),
 'wl.KStructure.index': (12, [(43, 8, 0)]),
 'wl.KStructure.color': (9, []),
 'wl.KStructure.vertex_color': (13, []),
 'wl.KStructure.prefix_vertex_coloring': (21, [(57, 17, 9)]),
 'wl.KStructure.prefix_pair_coloring': (39, []),
 'wl.KStructure.prefix_pair_coloring.<c@67>': (17, []),
 'wl.structure_from_function': (31, [(82, 7, 8), (85, 10, 0)]),
 'wl.finalize_raw': (25, [(94, 7, 0), (97, 24, 0), (98, 6, 8)]),
 'wl._sort_key': (5, []),
 'wl._all_maps': (15, [(109, 7, 9)]),
 'wl.to_configuration': (59,
                         [(125, 26, 0),
                          (129, 36, 0),
                          (131, 12, 0),
                          (132, 12, 0),
                          (135, 16, 0),
                          (137, 10, 0),
                          (145, 8, 0),
                          (149, 19, 15),
                          (149, 7, 9)]),
 'wl._summary': (18, [(156, 23, 0), (158, 13, 0)]),
 'wl._summary.<genexpr@160>': {'total': 20, 'loops': 1},
 'wl.weisfeiler_leman': (29,
                         [(172, 67, 1),
                          (177, 38, 0),
                          (180, 10, 9),
                          (182, 43, 0),
                          (183, 11, 9),
                          (185, 22, 0),
                          (193, 9, 0),
                          (197, 19, 14),
                          (197, 7, 9)]),
 'wl.weisfeiler_leman.<genexpr@186>': {'total': 28, 'loops': 1},
 'wl.refine_structures': (9, []),
 'wl.classical_wl': (74, [(215, 9, 0), (216, 27, 0), (222, 6, 11), (223, 6, 9)]),
 'wl.classical_wl.<genexpr@225>': {'total': 21, 'loops': 1},
 'cc.ClassicalCC.__init__': (70, [(27, 6, 12), (27, 7, 11), (28, 9, 9), (29, 6, 12), (31, 8, 0)]),
 'cc.ClassicalCC.key': (11, []),
 'cc.ClassicalCC.set_keys': (4, []),
 'cc.ClassicalCC.vertex_classes': (16, [(48, 13, 0)]),
 'cc.ClassicalCC.is_homogeneous': (10, []),
 'cc.ClassicalCC.diagonal_colors': (6, []),
 'cc.ClassicalCC.off_diagonal_colors': (14, [(60, 9, 9)]),
 'cc.ClassicalCC.paired': (20, [(66, 10, 0), (67, 22, 0)]),
 'cc.ClassicalCC.out_neighbors': (17, [(76, 11, 9)]),
 'cc.ClassicalCC.in_neighbors': (12, [(79, 14, 9)]),
 'cc.ClassicalCC.out_degree': (16, []),
 'cc.ClassicalCC.out_degree.<genexpr@82>': {'total': 22, 'loops': 1},
 'cc.ClassicalCC.constituent_vertex_classes': (16, [(87, 10, 0), (88, 29, 0)]),
 'cc.ClassicalCC.components': (39, [(104, 15, 0), (106, 30, 0), (112, 12, 0)]),
 'cc.ClassicalCC.components.<find@98>': (4, [(99, 19, 6)]),
 'cc.ClassicalCC.effective_vertices': (15, [(118, 15, 0), (120, 19, 0)]),
 'cc.ClassicalCC.is_clique': (16, []),
 'cc.ClassicalCC.disconnected_off_diagonal_colors': (12, [(133, 34, 0)]),
 'cc.ClassicalCC.disconnected_off_diagonal_colors.<genexpr@135>': {'total': 25, 'loops': 1},
 'cc.ClassicalCC.is_primitive': (14, [(144, 12, 2)]),
 'cc.ClassicalCC.is_uniprimitive': (16, []),
 'cc.ClassicalCC.induced': (26, []),
 'cc.ClassicalCC.induced.<lambda@157>': {'total': 12, 'loops': 0},
 'cc.ClassicalCC.strong_twin_classes': (42, [(176, 20, 0), (179, 62, 0), (186, 26, 4), (195, 15, 0)]),
 'cc.ClassicalCC.strong_twin_classes.<find@170>': (4, [(171, 19, 6)]),
 'cc.ClassicalCC.largest_twin_class_size': (11, []),
 'cc.ClassicalCC.largest_twin_class_size.<genexpr@200>': {'total': 19, 'loops': 1},
 'cc.ClassicalCC.canonical_keys': (41,
                                   [(218, 9, 0),
                                    (219, 13, 0),
                                    (222, 21, 0),
                                    (224, 21, 0),
                                    (229, 23, 0),
                                    (232, 50, 1),
                                    (234, 32, 0),
                                    (239, 8, 11),
                                    (240, 8, 8)]),
 'cc.ClassicalCC.canonical_keys.<genexpr@235>': {'total': 28, 'loops': 1},
 'cc._hk': (5, []),
 'cc.cc_from_pair_coloring': (5, [])}
```

### 6.2 Range-based profiles used in the proofs (Lemma 0)
`(outside', [(line of the range target, own), ...])` for every code object, keyed like 6.1.
`structure.enumerate_runs` has overlapping ranges and is counted directly (Section 2).

```python
RANGE_PROFILES = {'structure.Fixed.__init__': (4, []),
 'structure.Fixed.__eq__': (15, []),
 'structure.Fixed.__hash__': (8, []),
 'structure.Fixed.__repr__': (9, []),
 'structure.Fixed.canon_value': (4, []),
 'structure.apply_obj': (101, [(70, 8)]),
 'structure.apply_obj.<genexpr@66>': (11, [(66, 10)]),
 'structure.apply_obj.<genexpr@68>': (11, [(68, 10)]),
 'structure.Chooser.choose': (3, []),
 'structure.Chooser.check': (3, []),
 'structure.Chooser.choose_index': (10, []),
 'structure.RecordingChooser.__init__': (8, []),
 'structure.RecordingChooser.choose': (30, []),
 'structure.RecordingChooser.check': (10, []),
 'structure.ReplayChooser.__init__': (21, []),
 'structure.ReplayChooser._next_event': (28, []),
 'structure.ReplayChooser.choose': (66, []),
 'structure.ReplayChooser.check': (22, []),
 'structure.enumerate_runs': (12, [(146, 70), (154, 7), (157, 17)]),
 'structure.JohnsonCell.__init__': (8, []),
 'structure.JohnsonCell.invariant': (8, []),
 'structure.Structure.__init__': (33, [(183, 14)]),
 'structure.Structure._normalize': (110, [(190, 12), (194, 12), (198, 7)]),
 'structure.Structure._normalize.<lambda@197>': (18, []),
 'structure.Structure.cell_of': (12, [(207, 10), (208, 6)]),
 'structure.Structure.key_of_vertex': (10, [(214, 8), (215, 6)]),
 'structure.Structure.invariant': (26, []),
 'structure.Structure.invariant.<genexpr@220>': (10, [(220, 14)]),
 'structure.Structure.max_cell_size': (10, []),
 'structure.Structure.max_cell_size.<genexpr@224>': (10, [(224, 10)]),
 'structure.Structure.is_trivial': (16, []),
 'structure.Structure.refine': (51, [(235, 34), (237, 15), (239, 15), (246, 12)]),
 'structure.Structure.individualize': (12, []),
 'structure.Structure.individualize.<lambda@254>': (10, []),
 'structure.Structure.mark': (16, []),
 'structure.Structure.mark.<lambda@258>': (10, []),
 'structure.Structure.split_cell': (63, [(266, 18), (276, 12)]),
 'structure.Structure.with_johnson': (11, []),
 'structure.Structure.aut_gens': (28, [(290, 15), (292, 141), (303, 12), (306, 10), (311, 22), (313, 7)]),
 'structure.Structure.aut_order': (26, [(322, 15), (324, 49)]),
 'structure.Structure.has_odd_automorphism': (19, [(335, 15), (337, 62)]),
 'structure.Structure.odd_automorphism': (12, [(350, 9)]),
 'structure._johnson_cell_gens': (71, [(360, 6), (367, 23), (369, 18)]),
 'structure._johnson_cell_gens.<genexpr@370>': (11, [(370, 9)]),
 'structure.align': (98, [(386, 15), (388, 15), (393, 26), (397, 105), (406, 8), (407, 20), (413, 9)]),
 'structure.align.<genexpr@415>': (10, [(415, 8)]),
 'structure._hk': (5, []),
 'structure.coloring_structure': (33, [(433, 13), (435, 11)]),
 'wl.KStructure.__init__': (27, []),
 'wl.KStructure.index': (12, [(43, 8)]),
 'wl.KStructure.color': (9, []),
 'wl.KStructure.vertex_color': (13, []),
 'wl.KStructure.prefix_vertex_coloring': (30, [(57, 17)]),
 'wl.KStructure.prefix_pair_coloring': (39, []),
 'wl.KStructure.prefix_pair_coloring.<c@67>': (17, []),
 'wl.structure_from_function': (39, [(82, 7), (85, 10)]),
 'wl.finalize_raw': (28, [(94, 7), (97, 29), (98, 6)]),
 'wl._sort_key': (5, []),
 'wl._all_maps': (24, [(109, 7)]),
 'wl.to_configuration': (77,
                         [(125, 26),
                          (129, 36),
                          (131, 12),
                          (132, 12),
                          (135, 16),
                          (137, 10),
                          (145, 8),
                          (149, 25),
                          (149, 7)]),
 'wl._summary': (18, [(156, 23), (158, 13)]),
 'wl._summary.<genexpr@160>': (11, [(160, 9)]),
 'wl.weisfeiler_leman': (44,
                         [(173, 76),
                          (177, 44),
                          (180, 10),
                          (182, 49),
                          (183, 11),
                          (185, 22),
                          (193, 9),
                          (197, 25),
                          (197, 7)]),
 'wl.weisfeiler_leman.<genexpr@186>': (11, [(186, 17)]),
 'wl.refine_structures': (9, []),
 'wl.classical_wl': (94, [(215, 9), (216, 27), (222, 6), (223, 6)]),
 'wl.classical_wl.<genexpr@225>': (11, [(225, 10)]),
 'cc.ClassicalCC.__init__': (106, [(27, 14), (27, 7), (28, 9), (29, 6), (31, 8)]),
 'cc.ClassicalCC.key': (11, []),
 'cc.ClassicalCC.set_keys': (4, []),
 'cc.ClassicalCC.vertex_classes': (16, [(48, 13)]),
 'cc.ClassicalCC.is_homogeneous': (10, []),
 'cc.ClassicalCC.diagonal_colors': (6, []),
 'cc.ClassicalCC.off_diagonal_colors': (23, [(60, 9)]),
 'cc.ClassicalCC.paired': (20, [(66, 10), (67, 22)]),
 'cc.ClassicalCC.out_neighbors': (26, [(76, 11)]),
 'cc.ClassicalCC.in_neighbors': (21, [(79, 14)]),
 'cc.ClassicalCC.out_degree': (16, []),
 'cc.ClassicalCC.out_degree.<genexpr@82>': (11, [(82, 11)]),
 'cc.ClassicalCC.constituent_vertex_classes': (16, [(87, 10), (88, 29)]),
 'cc.ClassicalCC.components': (39, [(104, 15), (106, 30), (112, 12)]),
 'cc.ClassicalCC.components.<find@98>': (10, [(100, 19)]),
 'cc.ClassicalCC.effective_vertices': (15, [(118, 15), (120, 19)]),
 'cc.ClassicalCC.is_clique': (16, []),
 'cc.ClassicalCC.disconnected_off_diagonal_colors': (12, [(133, 34)]),
 'cc.ClassicalCC.disconnected_off_diagonal_colors.<genexpr@135>': (11, [(135, 14)]),
 'cc.ClassicalCC.is_primitive': (16, [(144, 12)]),
 'cc.ClassicalCC.is_uniprimitive': (16, []),
 'cc.ClassicalCC.induced': (26, []),
 'cc.ClassicalCC.induced.<lambda@157>': (12, []),
 'cc.ClassicalCC.strong_twin_classes': (42, [(176, 20), (179, 66), (186, 26), (195, 15)]),
 'cc.ClassicalCC.strong_twin_classes.<find@170>': (10, [(172, 19)]),
 'cc.ClassicalCC.largest_twin_class_size': (11, []),
 'cc.ClassicalCC.largest_twin_class_size.<genexpr@200>': (10, [(200, 9)]),
 'cc.ClassicalCC.canonical_keys': (49,
                                   [(218, 9),
                                    (219, 13),
                                    (222, 21),
                                    (224, 21),
                                    (229, 23),
                                    (233, 62),
                                    (234, 32),
                                    (239, 8),
                                    (240, 8)]),
 'cc.ClassicalCC.canonical_keys.<genexpr@235>': (11, [(235, 17)]),
 'cc._hk': (5, []),
 'cc.cc_from_pair_coloring': (5, [])}
```

### 6.3 The function computing the range-based profiles

```python
import dis

def range_profile(code):
    """(outside', [(line of target, own), ...]): every JUMP_BACKWARD* at offset b with target t
    spans [t, b]; ranges with equal targets are merged; an instruction belongs to the innermost
    range containing its offset (ranges must be nested, else 'nested' is False)."""
    ins = list(dis.get_instructions(code))
    byt = {}
    for i in ins:
        if i.opname.startswith("JUMP_BACKWARD"):
            byt[i.argval] = max(byt.get(i.argval, -1), i.offset)
    ranges = sorted(byt.items())
    nested = all(b < c or d < a or (a <= c and d <= b) or (c <= a and b <= d)
                 for a, b in ranges for c, d in ranges)
    def inner(off):
        best = None
        for a, b in ranges:
            if a <= off <= b and (best is None or (best[0] <= a and b <= best[1])):
                best = (a, b)
        return best
    own = {r: 0 for r in ranges}
    outside = 0
    for i in ins:
        r = inner(i.offset)
        if r is None:
            outside += 1
        else:
            own[r] += 1
    first = {i.offset: i for i in ins}
    return outside, [(first[a].positions.lineno, own[(a, b)]) for (a, b) in ranges], nested
```

Applied to `f.__code__` of every function/method and, recursively, to the nested code objects in
`co_consts`; `nested` is `True` for all of them except `structure.enumerate_runs`.

## 7. What is not proved / caveats

* **Lemma 0** rests on structural facts about the CPython 3.13 bytecode of these code objects, read
  off the listings (`dis`): the backward-jump ranges are nested (computed), exception handlers of
  these functions end with `RERAISE` except the one of `enumerate_runs` (inspected), and the only
  entry into a `for`-loop range is from the `GET_ITER` before it.  These are properties of the
  compiler, not proved from the language definition.
* `canon.canon` is not in the three modules: its cost is left as `C[canon.canon](s)`; only the sizes and
  heights of its results (Lemma C) are proved here, because they determine the comparison costs.
* Strings are charged as atoms (1.1); per-character charging multiplies hashing/comparison terms by
  at most 16.
* The union-find `find` is bounded by the trivial `N - 1` iterations per call (no amortised
  analysis); `components` is therefore `O(N^3)` rather than `O(N^2 log N)`.
* `disconnected_off_diagonal_colors`, `is_primitive`: `r' <= N - 1` needs a homogeneous coherent
  configuration (a property of the caller's input); without it only `r' <= N(N-1)` is used.
* Key sizes (Lemma K) are bounded in terms of the number `r` of construction steps since the root;
  a bound on `r` per `proc` run depends on the callers (`soj.py`, `design.py`, `main.py`).
* `wl._summary` (and so `to_configuration`/`weisfeiler_leman` with a `trace`) raises `KeyError` for
  `S >= 2` structures whose signature sets differ; all callers use `S = 1`.
* The frozenset-equality terms (`C J`) follow the model's "per element of both operands"; CPython
  stops after a size check.
* `enumerate_runs`: the bound `R <= prod k_d` holds for arbitrary (also nondeterministic) `proc`; it
  assumes that `proc` does not catch `Mismatch` exceptions raised by its chooser (true in the
  repository: the only `except` clauses of the package are in `enumerate_runs` and
  `canon.normalize_letters` (`TypeError`)).
