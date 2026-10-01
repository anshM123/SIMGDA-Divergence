"""Check that lean/DMSolutions/LastIterate/Defs.lean contains the definitions of the pull-request file
verbatim, and that Solution.lean and CheckAnswer.lean state `divergence_for_p_lt_half` verbatim.

The reference file lean/reference/LastIterateConvergence.pr3675.lean is the file
FormalConjectures/Arxiv/1905.10899/LastIterateConvergence.lean at the head d80f089b of
formal-conjectures pull request 3675 (git blob a352fef41e5ec8a4ae7d8f2d07340712497f46f1).

Usage (from the repository root): python scripts/check_verbatim.py
"""
import hashlib
import os
import sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ref_path = os.path.join(root, "lean", "reference", "LastIterateConvergence.pr3675.lean")
raw = open(ref_path, "rb").read()
blob = hashlib.sha1(b"blob %d\0" % len(raw) + raw).hexdigest()
ref = raw.decode("utf-8")
d = os.path.join(root, "lean", "DMSolutions", "LastIterate")
defs = open(os.path.join(d, "Defs.lean"), encoding="utf-8").read()
sol = open(os.path.join(d, "Solution.lean"), encoding="utf-8").read()
chk = open(os.path.join(d, "CheckAnswer.lean"), encoding="utf-8").read()

ok = blob == "a352fef41e5ec8a4ae7d8f2d07340712497f46f1"
print("reference git blob:", blob, "OK" if ok else "MISMATCH")
starts = ["variable (n m : ℕ)", "abbrev E_n", "abbrev F_m", "abbrev Z_space", "noncomputable def toProd",
          "structure State", "noncomputable def F_operator", "noncomputable def IsSaddlePoint",
          "noncomputable def step", "noncomputable def coefficients_schedule\n",
          "noncomputable def coefficients_schedule_p"]
for s in starts:
    i = ref.find(s)
    j = ref.find("\n\n", i)
    good = i >= 0 and ref[i:j] in defs
    ok &= good
    print(f"{s.strip():45s} verbatim in Defs.lean: {good}")
i = ref.find("theorem divergence_for_p_lt_half")
j = ref.find(":= by", i)
stmt = ref[i + len("theorem divergence_for_p_lt_half"):j]
for name, txt in [("Solution.lean", sol), ("CheckAnswer.lean", chk)]:
    good = stmt in txt
    ok &= good
    print(f"statement of divergence_for_p_lt_half verbatim in {name}: {good}")
print("ALL OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
