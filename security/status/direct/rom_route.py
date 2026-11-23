"""The ROM-reduction route (DIRECT.md section 10): VCVio's three-oracle bound at qh = qf, plus the
error of the Merkle-Damgard simulation hop, at P20/P40/P64.  Exact rational arithmetic; logs only
for printing.  NOT machine-checked.

Transcribed definitions (VCVio, .tools/VCVio-upstream):
  securityBound p card c r qh qs   HashSig/SLHDSA/Security/Target.lean:243
      = (qh+1) * wTCB(h,a,k, qs, qh, qs/card) + (c*qh + (r+1)*V) / card
  weightedTargetCoverBound h a k qs qw w   VCVio/CryptoFoundations/HardnessAssumptions/KeyedHash/Covering.lean:896
      = sum_{r<=k} sum_{r1<=r} C(qs, r-r1) C(qw, r1) surj(k,r) w^r1 2^(-h r) 2^(-a k)
  V = verifyInternalQueryBound p = 1 + (k(a+1)+1) + d (len (w-1) + 1 + h')   GeneralSchemeQueryBound.lean:39
SLH-DSA-SHA2-128s: n=16, h=63, d=7, h'=9, a=12, k=14, w=16, len=35, m=30.
"""
from fractions import Fraction as Fr
from math import log2, comb, factorial

def lg(x):
    x = Fr(x)
    if x == 0: return float('-inf')
    return log2(x.numerator) - log2(x.denominator)

h, a, k, d, hp, w, ln = 63, 12, 14, 7, 9, 16, 35
V = 1 + (k * (a + 1) + 1) + d * (ln * (w - 1) + 1 + hp)
Y = 2**128

def surj(kk, r):
    return sum((-1)**j * comb(r, j) * (r - j)**kk for j in range(r + 1))

def wTCB(qs, qw, wt):
    tot = Fr(0)
    for r in range(k + 1):
        sr = surj(k, r)
        for r1 in range(r + 1):
            tot += Fr(comb(qs, r - r1) * comb(qw, r1) * sr) * Fr(wt)**r1 * Fr(1, 2**(h*r)) * Fr(1, 2**(a*k))
    return tot

def securityBound(qh, qs, c=2, r=1):
    cov = (qh + 1) * wTCB(qs, qh, Fr(qs, Y))
    lin = Fr(c * qh + (r + 1) * V, Y)
    return cov, lin

# ---- the hop error ----
x = (2**26 + 56) // 64            # message blocks at l = 2^26
def QcAll(qf, qs): return qf + (qs + 1) * (2**25 + 2 * x)   # Ideal/Realize/FinalCore.lean:33
def qOPrf(qs): return 17920 + qs * 182784
def Qall(qf, qs): return QcAll(qf, qs) + 2 * qOPrf(qs)      # every cell of the real run (over-count)

def hop(qf, qs):
    Q = Qall(qf, qs)
    coll = Fr((Q + 1)**2, 2**254)          # collisions, back-links, IV hits, 256-bit guesses (fully fresh samples)
    eroot = Fr(qs, Y)                      # E_root: some signer inner digest X_i has X_i[0..16) = PK.root
    return coll, eroot

points = {"P20": (2**60, 2**20), "P40": (2**64, 2**40), "P64": (2**64, 2**64)}
tight8 = {"P20": [77, 132, 63], "P40": [63, 94, 59], "P64": [45, 46, 39]}
print(f"V = {V}")
for name, (qf, qs) in points.items():
    cov, lin = securityBound(qf, qs)
    coll, eroot = hop(qf, qs)
    tot = cov + lin + coll + eroot
    t8 = sum(Fr(1, 2**e) for e in tight8[name])
    print(f"{name}: qf=2^{lg(qf):.0f} qs=2^{lg(qs):.0f}")
    print(f"   coverage (qh+1)wTCB   2^{lg(cov):.3f}")
    print(f"   2(qh+V)/|Y|           2^{lg(lin):.3f}")
    print(f"   hop: collisions       2^{lg(coll):.3f}   (Q_all = 2^{lg(Qall(qf, qs)):.2f})")
    print(f"   hop: E_root qs/|Y|    2^{lg(eroot):.3f}")
    print(f"   securityBound alone   2^{lg(cov + lin):.3f}")
    print(f"   TOTAL                 2^{lg(tot):.3f}")
    print(f"   tight8 (proved)       2^{lg(t8):.3f}   gain {lg(t8) - lg(tot):.2f} bits")
    # alternative simulator that precomputes each signing query's H_msg (qh = qf + qs, no E_root)
    cov2, lin2 = securityBound(qf + qs, qs)
    print(f"   alt sim (qh=qf+qs)    2^{lg(cov2 + lin2 + coll):.3f}")
    # the form provable in Lean with surj(14,r) <= r^14 (Direct/RomNumerics.lean)
    covb = Fr(0)
    for r in range(k + 1):
        for r1 in range(r + 1):
            covb += Fr(comb(qs, r - r1) * comb(qf, r1) * r**14) * Fr(qs, Y)**r1 * Fr(1, 2**(h*r)) * Fr(1, 2**(a*k))
    covb *= (qf + 1)
    print(f"   coverage, surj<=r^14  2^{lg(covb):.3f};  total with it 2^{lg(covb + lin + coll + eroot):.3f}")
