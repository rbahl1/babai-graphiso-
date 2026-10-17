"""A canonical, value-faithful total order on the objects used as colours, keys and
letters.

The procedures of the algorithm must be *canonical*: a decision may depend on the
values of colours, keys and letters, but not on how those values happen to be
represented (Babai Def. 4.0.2).  Python's ``repr`` is not suitable for that: equal
values can print differently (``1`` and ``True``; two equal frozensets whose
elements were inserted in different orders), and distinct values can print alike
(two different objects of a class without ``__repr__``).  ``canon`` maps a value to
a nested tuple of ``(tag, payload)`` pairs that depends only on the value:

* equal values have equal images, and distinct values have distinct images, for
  the types used in this package: ``None``, ``bool``, ``int``, ``str``, ``tuple``,
  ``list``, ``frozenset``/``set`` (sorted by the canonical order of their
  elements) and ``structure.Fixed``;
* any two images are comparable (tags are strings and are compared first), so
  ``sorted(..., key=canon)`` is a total order that is the same for every
  representation of the same values.

``bool`` is treated as its integer value, because ``True == 1`` in Python and the
two must therefore behave identically.
"""

from __future__ import annotations

from typing import Any, Tuple


def canon(obj: Any) -> Tuple:
    """The canonical encoding of ``obj`` (see the module docstring)."""
    if obj is None:
        return ("n",)
    if isinstance(obj, bool):
        return ("i", int(obj))
    if isinstance(obj, int):
        return ("i", obj)
    if isinstance(obj, str):
        return ("s", obj)
    if isinstance(obj, tuple):
        return ("t", tuple(canon(o) for o in obj))
    if isinstance(obj, list):
        return ("l", tuple(canon(o) for o in obj))
    if isinstance(obj, (frozenset, set)):
        return ("f", tuple(sorted(canon(o) for o in obj)))
    value = getattr(obj, "canon_value", None)
    if value is not None:
        return ("x", canon(value()))
    raise TypeError(f"no canonical encoding for {type(obj).__name__}")


def normalize_letters(x, y):
    """Re-encode two strings over an arbitrary hashable alphabet as tuples of integers.

    Equal letters (in Python's ``==`` sense) get equal codes and different letters
    different codes; the codes are assigned in the canonical order of the letters
    that occur in ``x`` or ``y``, ties of the canonical order (impossible for the
    types handled by :func:`canon`) being impossible because ``canon`` is injective
    on them.  Letters of other types are numbered in order of first occurrence in
    ``x`` then ``y``, which is the same for both strings, so the map is still a
    bijection between the alphabets that is applied identically to ``x`` and
    ``y``; that is all String Isomorphism needs."""
    letters = []
    seen = {}
    for s in (x, y):
        for a in s:
            if a not in seen:
                seen[a] = len(letters)
                letters.append(a)
    try:
        order = sorted(letters, key=canon)
    except TypeError:
        order = letters
    code = {a: i for i, a in enumerate(order)}
    return tuple(code[a] for a in x), tuple(code[a] for a in y)
