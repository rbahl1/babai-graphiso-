"""The instruction profiles used by the per-function bounds (docs/bounds/, PROOF.md Part I)
are frozen in babai_gi/_opprofiles.py; a change of the code that changes a profile must be
accompanied by a re-check of the affected bounds and a regeneration of the file
(``python -m babai_gi.opcount``)."""
from babai_gi import opcount
from babai_gi._opprofiles import PROFILES


def test_frozen_profiles_match_the_code():
    current = opcount.generate()
    assert set(current) == set(PROFILES), sorted(set(current) ^ set(PROFILES))[:10]
    changed = [k for k in current if current[k] != PROFILES[k]]
    assert not changed, changed[:10]
