"""The exception raised when a step that the papers' theorems rule out is reached.

Under the papers' parameters (``Params.paper()``) every such step is unreachable
(``CORRECTNESS.md`` gives the proof for each one), so the exception is never raised;
it replaces the exact but exponential fallbacks of the small-scale preset, so that
the operation bound of ``PROOF.md`` does not depend on them.  Under
``Params.small_scale()`` (used by the tests, below the papers' thresholds, where
the theorems do not apply) the fallbacks are allowed and are exact.
"""

from __future__ import annotations


class TheoremViolation(RuntimeError):
    """A situation excluded by a theorem of the papers was reached."""


def fallback(allowed: bool, what: str) -> None:
    """Allow an exact fallback (``allowed``) or raise ``TheoremViolation``."""
    if not allowed:
        raise TheoremViolation(what)
