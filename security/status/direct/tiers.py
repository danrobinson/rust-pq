"""Tiers of the direct proof at the three points (imports direct_bounds.py; NOT machine-checked)."""
from direct_bounds import *
rows = []
for P, (qf, qs) in PTS.items():
    lin = Fr(2*qf + C0, 2**128); coll = Fr((Qtot(qf, qs, L) + 2)**2, 2**257)
    out = {}
    out['A  direct II + full-log tape, n=qf+2qs+2, prod form'] = lin + coll + reuseSum_prod(63, 12, 14, qf + 2*qs + 2)
    out['A\' direct II + full-log tape, n=qf+qs+2, prod form'] = lin + coll + reuseSum_prod(63, 12, 14, qf + qs + 2)
    out['B  direct II + full-log tape, n=qf+2qs+2, Stirling form'] = lin + coll + reuseSum_exact(63, 12, 14, qf + 2*qs + 2)
    out['B\' direct II + full-log tape, n=qf+qs+2, Stirling form'] = lin + coll + reuseSum_exact(63, 12, 14, qf + qs + 2)
    out['C  direct II + two-colour tape (targets only)'] = lin + coll + cover_targets_only(qf + 1, qs, qf)
    print(P)
    for k, v in out.items(): print(f"   {k:<58} 2^{lg(v):7.2f}")
# sensitivity: P64 bound as qs varies (qf = 2^64), tier C and B'
print("P64-type, qf=2^64, varying qs:  tier B'  /  tier C  / floor")
for e in (48, 52, 56, 60, 62, 64, 66):
    qf, qs = 2**64, 2**e
    lin = Fr(2*qf + C0, 2**128); coll = Fr((Qtot(qf, qs, L) + 2)**2, 2**257)
    b = lin + coll + reuseSum_exact(63, 12, 14, qf + qs + 2)
    c = lin + coll + cover_targets_only(qf + 1, qs, qf)
    pre, it = generic(qf, qs)
    print(f"   qs=2^{e}: 2^{lg(b):7.2f}  2^{lg(c):7.2f}  2^{log2(pre+it):7.2f}")
