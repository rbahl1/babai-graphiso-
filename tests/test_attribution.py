"""The hypotheses of PROOF.md Lemma 1.1, checked on every code object of the package.

Lemma 1.1 bounds the instructions of one call by its profile.  Its proof uses three
properties of the attribution computed by ``opcount.attribution``:

(H1) every backward jump belongs to a loop (``regions``);
(H2) an instruction in the range ``[target, jump]`` of a backward jump of loop ``J`` is
     attributed to ``J`` or to a loop nested in ``J``; if it is attributed to the
     entry part of a loop ``L`` (not its cycle), then ``J`` strictly encloses ``L``;
(H3) every exception handler lies after the code it protects (also checked on lambdas and
     generator expressions);

and, for the nested code objects that ``opcount`` profiles by their total, that a lambda
has no backward jump and a generator expression has one loop head, its ``FOR_ITER``.
The cases where these fail are listed in ``EXCEPTIONS`` with the place where they are
bounded by hand; the test fails if the list is not exactly the set of failures.
"""

import dis
import importlib
import inspect
import types

from babai_gi import opcount

MODULES = opcount.MODULES + ("canon", "tower")

EXCEPTIONS = {
    # (H1): the exit jump of the ``except TypeError`` path runs at most once per call
    ("canon.normalize_letters", "H1"): "docs/bounds/group.md, Lemma R",
    # (H2): handler stubs of two comprehensions inside the range of the ``yield from``;
    # they end in RERAISE and run at most once per call
    ("main._chain_search", "H2"): "docs/bounds/main.md, Lemma P(4)",
    # nested code objects with loops, bounded by hand
    ("johnson.recognize_cameron.<genexpr@202>", "nested"): "docs/bounds/johnson_certs.md, §1.3",
    ("johnson.recognize_cameron.<genexpr@351>", "nested"): "docs/bounds/johnson_certs.md, §1.3",
    ("main.Solver._solve.<genexpr@303>", "nested"): "docs/bounds/main.md, Lemma P(5)",
    ("main.Solver.primitive_johnson.<largest_twin@597>.<lambda@598>", "nested"):
        "docs/bounds/main.md, Lemma P(5)",
}


def _encloses(a, b) -> bool:
    return a is b or (opcount._contains(a.span, b.span[0]) and opcount._contains(a.span, b.span[1]))


def _failures(code: types.CodeType):
    instrs, loops, owner, regions = opcount.attribution(code)
    out = set()
    jumps = []
    for ins in instrs:
        if ins.opname.startswith("JUMP_BACKWARD"):
            owners = [lp for lp in loops if (ins.argval, ins.offset) in regions.get(id(lp), ())]
            if not owners:
                out.add("H1")
            else:
                jumps.append((ins.argval, ins.offset, owners[0]))
    for ins, lp in zip(instrs, owner):
        cycle = lp is not None and any(a <= ins.offset <= b for a, b in regions.get(id(lp), ()))
        for t, j, J in jumps:
            if not t <= ins.offset <= j:
                continue
            if lp is None or not _encloses(J, lp) or (not cycle and J is lp):
                out.add("H2")
    if not _handlers_after(code):
        out.add("H3")
    return out


def _handlers_after(code: types.CodeType) -> bool:
    return all(entry.target >= entry.end for entry in dis.Bytecode(code).exception_entries)


def _nested_ok(code: types.CodeType) -> bool:
    instrs = list(dis.get_instructions(code))
    index = {ins.offset: i for i, ins in enumerate(instrs)}
    heads = set()
    for ins in instrs:
        if ins.opname.startswith("JUMP_BACKWARD"):
            i = index[ins.argval]
            while instrs[i].opname == "EXTENDED_ARG":
                i += 1
            heads.add(i)
    if code.co_name == "<lambda>":
        return not heads
    return len(heads) <= 1 and all(instrs[i].opname == "FOR_ITER" for i in heads)


def _functions(mod):
    for obj in vars(mod).values():
        if inspect.isfunction(obj) and obj.__module__ == mod.__name__:
            yield obj.__qualname__, obj.__code__
        elif inspect.isclass(obj) and obj.__module__ == mod.__name__:
            for member in vars(obj).values():
                f = member.fget if isinstance(member, property) else member
                if isinstance(f, (staticmethod, classmethod)):
                    f = f.__func__
                if inspect.isfunction(f):
                    yield f.__qualname__, f.__code__


def _walk(code: types.CodeType, key: str, found: dict) -> None:
    if code.co_name.startswith("<"):
        if not _nested_ok(code):
            found[(key, "nested")] = True
        if not _handlers_after(code):
            found[(key, "H3")] = True
    else:
        for what in _failures(code):
            found[(key, what)] = True
    for const in code.co_consts:
        if isinstance(const, types.CodeType):
            _walk(const, f"{key}.<{const.co_name.strip('<>')}@{const.co_firstlineno}>", found)


def test_attribution_hypotheses_hold_except_the_listed_cases():
    found: dict = {}
    for name in MODULES:
        mod = importlib.import_module(f"babai_gi.{name}")
        for qual, code in _functions(mod):
            _walk(code, f"{name}.{qual}", found)
    assert set(found) == set(EXCEPTIONS)
