"""Region profiles of soj.py, design.py and johnson.iroot (docs/bounds/soj.md, Lemma 1.1').

docs/bounds/soj.md §0.2 bounds the instructions of one call of a code object by its
*region profile*.  Every backward jump J (``JUMP_BACKWARD*``) with target t defines the
region [t, offset(J)].  The regions with a common target form a group (one loop, or one
generator clause of a comprehension) whose span is [t, max offset(J)].  Every
instruction is counted in the innermost span that contains its offset (the group's
``cycle'``), or in ``outside'`` if no span contains it.  Lemma 1.1' then gives

    own instructions of one call <= outside' + sum over groups L of cycle'_L * P_L,

where P_L is the number of executions of L's target instruction.

This module recomputes the region profile of every code object of ``soj.py`` and
``design.py`` (functions, methods and nested code objects) and of ``johnson.iroot``,
checks the hypotheses of Lemma 1.1' on each of them, and compares the numbers with the
frozen table ``REGION_PROFILES``, which is the table of soj.md §4.2.  soj.md §0.2 and
§4.2 cite this test.  The hypotheses are:

(R1) the only instructions that transfer control to a smaller offset are the
     ``JUMP_BACKWARD*`` instructions;
(R2) the group spans are laminar (nested or disjoint);
(R3) every backward jump lies in the span of its own group and in no span nested in it;
(R4) no jump from outside a span lands inside the span other than at its target t;
(R5) every exception handler lies after the code it protects, outside every span, and is
     a straight run of instructions ending in ``RERAISE``;
(R6) the source contains no ``try``, ``with``, ``yield`` or ``await``.

By (R5) and (R6), a handler of a function runs only while an exception propagates out
of the call, and a handler of a generator expression runs at most once, when the
generator is closed.  The test also checks that the region profile and the profile of
``opcount.generate()`` have the same total, the number of instructions of the code object.
"""

import ast
import dis
import importlib
import inspect
import textwrap
import types

from babai_gi import johnson, opcount

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

FORBIDDEN_NODES = (ast.Try, ast.TryStar, ast.With, ast.AsyncWith, ast.Yield, ast.YieldFrom, ast.Await,
                   ast.AsyncFunctionDef, ast.AsyncFor)


class Regions:
    """The groups of backward jumps of one code object and the innermost span of each offset."""

    def __init__(self, code: types.CodeType) -> None:
        self.code = code
        self.instrs = list(dis.get_instructions(code))
        jumps = {}
        for ins in self.instrs:
            if ins.opname.startswith("JUMP_BACKWARD"):
                jumps.setdefault(ins.argval, []).append(ins.offset)
        self.jumps = jumps                                     # target -> offsets of its jumps
        self.spans = {t: (t, max(js)) for t, js in jumps.items()}

    def innermost(self, offset):
        """The target of the innermost span containing ``offset``, or None."""
        inside = [t for t, (a, b) in self.spans.items() if a <= offset <= b]
        return min(inside, key=lambda t: self.spans[t][1] - self.spans[t][0]) if inside else None

    def profile(self):
        """(outside', [(line of the target instruction, cycle'), ...]) in the order of the targets."""
        outside = 0
        cycle = {t: 0 for t in self.spans}
        for ins in self.instrs:
            t = self.innermost(ins.offset)
            if t is None:
                outside += 1
            else:
                cycle[t] += 1
        line = {ins.offset: ins.positions.lineno for ins in self.instrs}
        return outside, [(line[t], cycle[t]) for t in sorted(self.spans)]

    def violations(self):
        """The hypotheses (R1)-(R5) that fail, with the offending offsets."""
        out = []
        for ins in self.instrs:
            if ins.opcode in dis.hasjump and not ins.opname.startswith("JUMP_BACKWARD"):
                if ins.argval <= ins.offset:
                    out.append(("R1", ins.offset, ins.opname))
        spans = sorted(self.spans.values())
        for i, (a0, a1) in enumerate(spans):
            for b0, b1 in spans[i + 1:]:
                if b0 <= a1 and b1 > a1:                       # overlapping, not nested
                    out.append(("R2", (a0, a1), (b0, b1)))
        for t, offsets in self.jumps.items():
            for j in offsets:
                if self.innermost(j) != t:
                    out.append(("R3", t, j))
        for ins in self.instrs:
            if ins.opcode in dis.hasjump:
                for t, (a, b) in self.spans.items():
                    if a < ins.argval <= b and not a <= ins.offset <= b:
                        out.append(("R4", ins.offset, ins.argval, t))
        index = {ins.offset: n for n, ins in enumerate(self.instrs)}
        for entry in dis.Bytecode(self.code).exception_entries:
            if entry.target < entry.end:
                out.append(("R5", "handler before protected code", entry.target))
            n = index[entry.target]
            while True:
                ins = self.instrs[n]
                if self.innermost(ins.offset) is not None:
                    out.append(("R5", "handler inside a span", ins.offset))
                if ins.opname == "RERAISE":
                    break
                if ins.opcode in dis.hasjump or ins.opname.startswith(("RETURN", "YIELD")):
                    out.append(("R5", "handler is not straight", ins.offset))
                    break
                n += 1
        return out


def _top_level(mod):
    """(qualname, function) for the functions and methods defined in ``mod``, in source order."""
    out = []
    for obj in vars(mod).values():
        if inspect.isfunction(obj) and obj.__module__ == mod.__name__:
            out.append(obj)
        elif inspect.isclass(obj) and obj.__module__ == mod.__name__:
            for member in vars(obj).values():
                f = member.fget if isinstance(member, property) else member
                if isinstance(f, (staticmethod, classmethod)):
                    f = f.__func__
                if inspect.isfunction(f):
                    out.append(f)
    out.sort(key=lambda f: f.__code__.co_firstlineno)
    return [(f.__qualname__, f) for f in out]


def _walk(code: types.CodeType, key: str):
    yield key, code
    for const in code.co_consts:
        if isinstance(const, types.CodeType):
            yield from _walk(const, f"{key}.<{const.co_name.strip('<>')}@{const.co_firstlineno}>")


def _functions():
    """(module-qualified name, function) for every function covered by REGION_PROFILES."""
    out = []
    for name in ("soj", "design"):
        mod = importlib.import_module(f"babai_gi.{name}")
        out += [(f"{name}.{qual}", f) for qual, f in _top_level(mod)]
    out.append(("johnson.iroot", johnson.iroot))
    return out


def _code_objects():
    """(key, code) for every code object; a repeated key gets the suffix #2, #3, ..."""
    out = {}
    for key, f in _functions():
        for k, code in _walk(f.__code__, key):
            unique, n = k, 2
            while unique in out:
                unique, n = f"{k}#{n}", n + 1
            out[unique] = code
    return out


def test_sources_have_no_try_with_yield_or_await():
    for name in ("soj", "design"):
        tree = ast.parse(inspect.getsource(importlib.import_module(f"babai_gi.{name}")))
        assert not [type(node).__name__ for node in ast.walk(tree) if isinstance(node, FORBIDDEN_NODES)]
    tree = ast.parse(textwrap.dedent(inspect.getsource(johnson.iroot)))
    assert not [type(node).__name__ for node in ast.walk(tree) if isinstance(node, FORBIDDEN_NODES)]


def test_hypotheses_of_lemma_1_1_prime():
    failures = {key: Regions(code).violations() for key, code in _code_objects().items()}
    assert {key: v for key, v in failures.items() if v} == {}


def test_region_profiles_match_the_frozen_table():
    current = {key: Regions(code).profile() for key, code in _code_objects().items()}
    assert set(current) == set(REGION_PROFILES), sorted(set(current) ^ set(REGION_PROFILES))
    changed = {key: current[key] for key in current if current[key] != REGION_PROFILES[key]}
    assert changed == {}


def test_totals_agree_with_opcount():
    generated = opcount.generate()
    codes = _code_objects()
    shared = {key.split("#")[0] for key in codes if "#" in key}   # one opcount entry for several codes
    for key, code in codes.items():
        n = len(list(dis.get_instructions(code)))
        outside, groups = Regions(code).profile()
        assert outside + sum(c for _, c in groups) == n
        prof = generated.get(key)
        if prof is None or key.split("#")[0] in shared:
            continue
        if "total" in prof:
            assert prof["total"] == n, key
        else:
            assert prof["outside"] + sum(c + e for _, _, c, e in prof["loops"]) == n, key
