# Cost model and method of the per-function bounds

This document (SPEC) states the cost model and the method of the per-function operation
bounds for `babai_gi` (Babai's String Isomorphism) in `docs/bounds/`.

## Purpose

For every function and method of `babai_gi`, the documents in `docs/bounds/` prove an
explicit upper bound on the number of **operations** executed by **one call**, in terms of
size parameters of its arguments.  These bounds are the "own work" part of a time bound of
the form `a 2^{b log^3 n}` for the whole solver.  Each bound is a **mathematical proof from
the code**, not a measurement.

## Cost model

This is the model of `babai_gi/opcount.py`; `PROOF.md` Part I (§1–§2) states the same
model.  One operation is:

* the execution of one CPython 3.13 bytecode instruction of the package
  (`dis.get_instructions`); an instruction counts one also when it handles a number
  of items fixed by the program text (building or unpacking a 3-tuple, one step of
  `zip` or `enumerate`);
* an arithmetic operation or comparison of `int` / `Fraction` (any size: group orders
  are big integers): the instruction that performs it, cost 1;
* a dict/set lookup, insertion or deletion: 1 plus the cost of hashing the key and of
  the `==` comparisons it makes (**one comparison is counted per lookup**, plus the
  hashing; hashing or comparing a tuple / frozenset costs one per element it touches,
  recursively for nested containers; ints cost 1);
* a built-in whose work grows with its data costs **one per element it touches** in
  addition to its call instruction: constructors of containers from an iterable
  (`list`, `tuple`, `dict`, `set`, `frozenset`), `sorted` (`L ceil(log2 L)` comparisons,
  each costing the comparison of its keys, plus `2L + 1`; a `key=` function is called
  `L` times), `sum`, `max`, `min`, `any`, `all`, `map`, `zip`, `enumerate`,
  `range` iteration (per element consumed), `x in list`, `list.index`, `list.count`,
  list repetition, slicing, `list.extend`, `list.pop(0)`, `deque` operations (1),
  set/frozenset algebra and comparison (per element of both operands), equality /
  ordering of tuples and lists (per element compared), `str`/`repr`, `itertools`
  generators (per element produced, times the length of the produced tuple),
  `math.factorial(L)` and `math.comb` (count `L` multiplications),
  `str.join`, `.items()/.keys()/.values()` iteration (per element);
* a call of a Python function of the package: its call instructions are part of the
  caller's count; the callee's operations are charged by the callee's bound.

Not counted: the text of exception messages on error exits, and the diagnostic counters
`Solver.stats` and `soj.STATS` beyond the following.  Their `+= 1` instructions are counted
as ordinary instructions, and the hashing done by the `Counter` is charged 1 + the length of
the key string; the documents bound this charge by 64.

## Method

For a function `f`, `opcount.profile(f)` gives `outside`, the number of its instructions
outside every loop, and for every loop `(line, kind, cycle, entry)`.  By Lemma 1.1
(`PROOF.md` §2; the docstring of `babai_gi/opcount.py` states the same count), one call
executes at most

    outside + sum over loops [ cycle * (iterations + entries) + entry * entries ]

of its own instructions, where `iterations` and `entries` are the total numbers of
iterations and entries of that loop during the call (an inner loop is entered once
per iteration of the enclosing loop).  Inner functions / lambdas / generator
expressions are separate code objects (`opcount.generate()` lists them as
`func.<name@line>`; a lambda or genexpr executes each instruction at most once per
call / per element).  The bound of a call is this count plus the built-in costs and the
callees' bounds.

Every loop has an iteration bound **with a proof from the code**: which collection it
ranges over and why that collection is at most so large; for a `while` loop, a variant.
For recursion inside a module, the number of recursive invocations is bounded with a
proof.  For caches (`aut_cache`, `_levels` built lazily, `lifter_cache`, `H.cache`, ...),
a bound may always charge the full uncached cost (an upper bound); a bound that relies on
a cache hit proves that hit.

## Exclusions

* Operations executed inside calls of `Solver.iso` (and of `Solver.iso_window`,
  `chain_rule`, `strong_luks`, `branch`, ... reached only through them) are the
  recursion and are **not** part of the own work.  When a function calls back into the
  solver (`self.solver.iso_window(...)`), its bound counts only the call instructions, and
  the call (with its argument sizes) is listed in a separate "solver calls" item of the
  function's lemma.
* Functions used only by tests, the CLI or diagnostics are listed without a bound.

## Parameters

The bounds use explicit size parameters: `N` = degree of a permutation group (length of
its permutations), `r` = number of generators passed, `L` = length of a list argument,
`m`, `k`, `t`, `d` as in the code.  Every assumption on the inputs that a bound uses is
stated (e.g. "every generator is a tuple of length N", "|gens| <= r"), and where it is not
evident it is checked for the callers in the repository.  Where possible, a bound is valid
for all parameter values ≥ 1 (or ≥ 2) and has explicit integer coefficients.
Simplifications such as `N^2 + 3N + 5 <= 9 N^2` (N >= 1) are used in the final closed
forms, and the place where each is used is stated.

## Form of the per-module documents

1. A short section with the conventions of the document (parameters, assumptions).
2. One subsection per function, in source order:
   `### module.Qualname` — the profile numbers used (`outside`, loops), the iteration
   bound of every loop with its proof, the built-in costs, the callees (with the parameter
   values passed), the solver calls (if any), and the resulting bound, first as an
   expression, then as a closed form.
3. A final table: function -> closed-form bound (with the callees' bounds substituted
   for callees inside the document's modules; callees outside these modules are left as
   named symbols `C[module.Qualname](params)`).
4. A list of the profile numbers used, as a Python dict literal
   `{"module.Qualname": (outside, [(line, cycle, entry), ...]), ...}`, so that a test can
   check them against `opcount.generate()`.

A bound is exact where this is cheap and generous where precision would cost pages; every
inequality in it is true.  Anything that is not proved is marked as such.
