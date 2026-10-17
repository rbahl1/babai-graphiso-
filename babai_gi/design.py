"""The Design Lemma and the Extended Design Lemma on Gamma
(Babai Thm. 6.1.1, Procedure Split-or-UPCC; Thm. 7.3.3; HBD Prop. 4 and
Sec. 5.1).

``extended_design_lemma`` takes the k-WL-refined k-ary coherent configuration
X of a canonical k-ary relational structure on Gamma (relative strong symmetry
defect >= 1/2 for the guarantee), searches the prefixes of the Design Lemma
(HBD Prop. 4), and returns a canonical Structure on Gamma relative to the
choices made:

  (a) a coloring with no alpha-dominant class, or
  (b) a dominant class C with a non-clique homogeneous classical coherent
      configuration X'' on C:
        - imprimitive: C is equipartitioned by the components of a disconnected
          constituent (Babai Split-or-UPCC line 08),
        - uniprimitive: UPCC Split-or-Johnson (Babai Sec. 7, HBD 5.2) gives a
          colored alpha-partition of C or a Johnson scheme on >= alpha|C| vertices.

Multiplicative cost: |Gamma|^{k-1} (prefix) times the cost of Split-or-Johnson.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, List

from .errors import fallback

from .cc import ClassicalCC
from .soj import (STATS, SOJParams, design_lemma, individualize_until, select_min, split_by_blocks,
                  upcc_split_or_johnson)
from .structure import Chooser, Structure
from .wl import KStructure


def extended_design_lemma(X: KStructure, base: Structure, alpha: float, chooser: Chooser,
                          params: SOJParams, vertices: List[int] = None) -> Structure:
    """Babai Thm. 7.3.3.  ``X`` is a refined k-ary configuration on range(m); the
    structure is built relative to ``base`` (which may already color Gamma)."""
    m = X.n
    STATS["extended_design_lemma"] += 1
    if vertices is None:
        vertices = list(range(m))
    res = design_lemma(X, alpha, chooser)
    chooser.check(("edl", res is not None, None if res is None else (len(res[0]), res[1])))
    if res is None:
        # unreachable when the hypotheses of the Design Lemma hold (HBD Prop. 5.1; CORRECTNESS.md)
        fallback(params.allow_fallbacks, "Design Lemma failed (HBD Prop. 5.1)")
        STATS["edl_fallback"] += 1
        return individualize_until(base, vertices, alpha * len(vertices), chooser, "edl-fb")
    tup, kind, col1 = res
    for i, v in enumerate(tup):
        base = base.individualize(v, ("edl-ind", i))
    base = base.refine(lambda v: col1[v], "edl-col")
    if kind == "a":
        STATS["edl_coloring"] += 1
        return base
    groups: Dict[int, List[int]] = {}
    for v, c in enumerate(col1):
        groups.setdefault(c, []).append(v)
    C = sorted(max(groups.values(), key=len))
    c2 = X.prefix_pair_coloring(tup)
    cc = ClassicalCC(C, c2)
    disc = cc.disconnected_off_diagonal_colors()
    chooser.check(("edl-disc", len(disc), len(cc.colors)))
    if disc:
        STATS["edl_equipartition"] += 1
        col = select_min(disc, cc.key, chooser)
        comps = cc.components(col)
        blocks = [[cc.vertices[i] for i in cmp] for cmp in comps]
        return split_by_blocks(base, C, blocks, "edl-comp")
    if not cc.is_uniprimitive():
        # cannot happen (kind 'b' guarantees a non-clique homogeneous configuration)
        fallback(params.allow_fallbacks, "Extended Design Lemma: configuration on C not uniprimitive")
        STATS["edl_fallback2"] += 1
        return individualize_until(base, C, alpha * len(C), chooser, "edl-fb2")
    STATS["edl_upcc"] += 1
    # Babai Thm. 7.3.3: Split-or-Johnson on C with beta = alpha m / |C| (in [alpha, 1)),
    # so that the cells it returns inside C have at most alpha m points and a Johnson
    # scheme it returns has at least alpha m points
    return upcc_split_or_johnson(cc, Fraction(alpha) * m / len(C), base, chooser, params)
