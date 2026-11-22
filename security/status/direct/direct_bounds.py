"""Evaluate the current closed bound (suf_ideal_closed_tight8) term by term, the generic-attack
floor, and the predicted bound of the planned direct ideal-model proof, at P20/P40/P64.

Definitions transcribed from the Lean sources (security/...):
  QlinT8        Ideal/Realize/FinalTight8.lean:303
  polyP8        Ideal/Realize/FinalTight8.lean:179   polyP8 = polyP7 + 3(Qc+40N+1)
  polyP7        Ideal/Realize/FinalTight7.lean:203   polyP7 = polyP + 14(20N+1)
  polyP         Ideal/Compose128.lean:319
  QcAll         Ideal/Realize/FinalCore.lean:33
  NAll          Ideal/Realize/FinalCore.lean:37, qOPrf_128s Ideal/Realize/PrfReal.lean:328
  ellB          Ideal/Realize/FinalCore.lean:40
  epsItsrF      Ideal/ComposeFinal.lean:77 (headline args: qP=qf, cP=2qs, q=qf, qc=itsrQc qs, Lc=itsrLc l)
  itsrQc        Ideal/Realize/Itsr.lean:42/44  (= 269824 + 2007386 qs)
  itsrLc        Ideal/Realize/ItsrBound.lean:427 / Itsr.lean:51 (= max 11 ((l+56)/64+1))
  reuseSum      Ideal/Inst/Itsr128.lean:139 (sum over (j, c:[k]->[n]) with c i != j of
                2^(-h |im c|) 2^(-a k)); closed form n * sum_r S(k,r) (n-1)_r 2^(-h r) 2^(-a k)
  reuseSum_le_prod Ideal/Inst/ItsrNumeric.lean: n 2^(-ak) prod_{i<k} (i + n/2^h)  (the form the Lean
                numerics use)
Exact rational arithmetic; logs only for printing.  NOT machine-checked.
"""
from fractions import Fraction as Fr
from math import log2, comb, factorial

def lg(x):
    x = Fr(x)
    if x == 0: return float('-inf')
    # log2 of a Fraction without float overflow
    return log2(x.numerator) - log2(x.denominator)

# ---------- Lean definitions ----------
def x_of(l): return (l + 56) // 64
def QcAll(qf, qs, l): return qf + (qs + 1) * (2**25 + 2 * x_of(l))
def qOPrf(qs): return 17920 + qs * 182784
def NAll(qs): return max(2**81, qOPrf(qs))
def ellB(l): return (l + 63) // 64
def polyP(Qc, N, qs, l):
    return ((Qc + N)**2 + (Qc + qs * (l + 1) + 2)**2 + 18 * (2*Qc + 22*N + 21)**2
            + 18 * (2*Qc + 22*N + 9)**2 + 78*Qc + 1433*N + 47)
def polyP7(Qc, N, qs, l): return polyP(Qc, N, qs, l) + 14 * (20*N + 1)
def polyP8(Qc, N, qs, l): return polyP7(Qc, N, qs, l) + 3 * (Qc + 40*N + 1)
def QlinT8(qf, qs, l):
    x = x_of(l)
    return 27*qf + qs*(16771392 + 14*x) + 29487855 + 13*x
def itsrQc(qs): return 269824 + qs * 2007386
def itsrLc(l): return max(11, x_of(l) + 1)

def stirling2(n, k):
    S = [[0]*(k+1) for _ in range(n+1)]; S[0][0] = 1
    for i in range(1, n+1):
        for j in range(1, min(i, k)+1):
            S[i][j] = j*S[i-1][j] + S[i-1][j-1]
    return S[n][k]
S14 = [stirling2(14, r) for r in range(15)]

def falling(n, r):
    p = 1
    for i in range(r): p *= (n - i)
    return p

def reuseSum_exact(h, a, k, n):
    """closed form of reuseSum h a k n (Itsr128.lean:139)."""
    tot = Fr(0)
    for r in range(1, k+1):
        tot += Fr(stirling2(k, r) * falling(n-1, r), 2**(h*r))
    return n * tot / 2**(a*k)

def reuseSum_prod(h, a, k, n):
    """reuseSum_le_prod: n 2^-ak prod_{i<k}(i + n/2^h)."""
    p = Fr(1)
    for i in range(k): p *= (i + Fr(n, 2**h))
    return n * p / 2**(a*k)

def epsItsrF_parts(qP, cP, q, qc, Lc, qs, l, exact=True):
    n = qP + cP + 2*(qs+1)
    Ia = reuseSum_exact(63, 12, 14, n) if exact else reuseSum_prod(63, 12, 14, n)
    Ib = Fr((q + qc*Lc + (qs+1)*(x_of(l)+3))**2, 2**256)
    return n, Ia, Ib

# ---------- points (caps of the tight8 numeric theorems, FinalTight8.lean:528-582) ----------
L = 2**26
PTS = {'P20': (2**60, 2**20), 'P40': (2**64, 2**40), 'P64': (2**64, 2**64)}

def current(qf, qs, l):
    x = x_of(l)
    n, Ia, Ib = epsItsrF_parts(qf, 2*qs, qf, itsrQc(qs), itsrLc(l), qs, l, exact=True)
    _, Ia_prod, _ = epsItsrF_parts(qf, 2*qs, qf, itsrQc(qs), itsrLc(l), qs, l, exact=False)
    Qc, N = QcAll(qf, qs, l), NAll(qs)
    lin = QlinT8(qf, qs, l)
    parts_lin = {'27*qf': 27*qf, 'qs*16771392 (re-signing hashing)': qs*16771392,
                 'qs*14x (message blocks)': qs*14*x, 'one-off 29487855+13x': 29487855 + 13*x}
    assert sum(parts_lin.values()) == lin
    P8 = polyP8(Qc, N, qs, ellB(l))
    parts_poly = {'(Qc+N)^2': (Qc+N)**2, '(Qc+qs(l+1)+2)^2': (Qc+qs*(ellB(l)+1)+2)**2,
                  '18(2Qc+22N+21)^2 + 18(2Qc+22N+9)^2 (T_len/T_k internal CVs, L12)':
                      18*(2*Qc+22*N+21)**2 + 18*(2*Qc+22*N+9)**2,
                  'linear rest': P8 - (Qc+N)**2 - (Qc+qs*(ellB(l)+1)+2)**2
                                 - 18*(2*Qc+22*N+21)**2 - 18*(2*Qc+22*N+9)**2}
    return dict(n=n, Ia=Ia, Ia_prod=Ia_prod, Ib=Ib, lin=Fr(lin, 2**128), parts_lin=parts_lin,
                poly=Fr(P8, 2**256), parts_poly=parts_poly, Qc=Qc, N=N)

# ---------- generic attack floor ----------
def p_cover(qs, h=63, a=12, k=14, tail=80):
    """P[a fresh uniform digest is covered by qs independent uniform target digests]
    (TIGHT.md 1.3, p(qs)).  gamma = number of targets on the candidate's FORS key,
    gamma ~ Bin(qs, 2^-h); given gamma, each of the k indices is covered w.p. 1-(1-2^-a)^gamma.
    Terms g > tail are negligible (< 2^-300).  (1-2^-h)^(qs-g) is replaced by exp(-qs 2^-h)
    (relative error < 2^-50 for g <= tail)."""
    from math import exp
    p = Fr(1, 2**h)
    tot = Fr(0)
    for g in range(1, min(tail, qs) + 1):
        tot += comb(qs, g) * p**g * (1 - (1 - Fr(1, 2**a))**g)**k
    return float(tot) * exp(-qs / 2**h)

def generic(qf, qs):
    pre = qf / 2.0**128               # SK.seed exhaustive search (one PRF-shaped query per guess)
    itsr = qf * p_cover(qs)           # FORS few-time forgery
    return pre, itsr

# ---------- predicted direct bound ----------
# compression cells, lazy table, distinct cells (upper bounds), from the Lean counts:
#   keygenHashes 269824 (Reduction/Instance128sV2.lean:60) + 9 extra blocks per T_len (2^9 of them)
#   + 2^9*35 secret reads (PRF cells) + 1 midstate cell
#   signHashes 2007385 (:63) + 9*3585 T_len extra + 3 T_k extra + signReads 182784
#   (Reduction/Resources.lean:349) + H_msg (x+3) + PRF_msg (x+4)
#   verifyHashes 3928 (Reduction/TcrMemo.lean:704) + 9*7 + 3 + (x+3)
def Qtot(qf, qs, l):
    x = x_of(l)
    Kc = 269824 + 9*512 + 512*35 + 1
    Sc = 2007385 + 9*3585 + 3 + 182784 + (x+3) + (x+4)
    Vc = 3928 + 63 + 3 + (x+3)
    return qf + Kc + qs*Sc + Vc

C0 = 3928 + 259 + 64    # verification last cells (Hit) + forged secret/chain values (HiddenEq) + seed/IV events

def cover_targets_only(ncand, qs, qf):
    """union bound: candidate cB cells x assignments of the 14 indices to target ordinals;
    effective coverers qs*(1+qf/2^128) (pre-queried targets, see plan 2.6)."""
    s = Fr(qs) * (1 + Fr(qf, 2**128))
    tot = Fr(0)
    for r in range(1, 15):
        tot += S14[r] * s**r / Fr(2)**(63*r)
    return ncand * tot / Fr(2)**168

def direct(qf, qs, l, c=2, itsr='targets'):
    lin = Fr(c*qf + C0, 2**128)
    if itsr == 'targets':
        cov = cover_targets_only(qf + 1, qs, qf)
    elif itsr == 'fulllog':   # fallback: existing tape lemma, every cB cell a coverer, n = qf + qs + 1
        cov = reuseSum_exact(63, 12, 14, qf + qs + 1)
    elif itsr == 'fulllog_prod':
        cov = reuseSum_prod(63, 12, 14, qf + qs + 1)
    Q = Qtot(qf, qs, l)
    coll = Fr((Q + 2)**2, 2**257)
    return lin, cov, coll

def show(name, v): print(f"    {name:<62} 2^{lg(v):8.2f}")

if __name__ == '__main__':
    for P, (qf, qs) in PTS.items():
        cu = current(qf, qs, L)
        tot_cur = cu['Ia'] + cu['Ib'] + cu['lin'] + cu['poly']
        print(f"\n=== {P}: qf = 2^{lg(qf):.0f}, qs = 2^{lg(qs):.0f}, l = 2^26 (x = {x_of(L)})")
        print("  current bound (suf_ideal_closed_tight8, unrounded):")
        print(f"    ITSR n = qf + 2qs + 2(qs+1) = 2^{lg(cu['n']):.2f}")
        show("I.a reuseSum exact (Stirling closed form)", cu['Ia'])
        show("I.a reuseSum_le_prod (form used in the Lean numerics)", cu['Ia_prod'])
        show("I.b (q + qc*Lc + (qs+1)(x+3))^2 / 2^256", cu['Ib'])
        show("II  QlinT8 / 2^128", cu['lin'])
        for k, v in cu['parts_lin'].items(): show("      " + k, Fr(v, 2**128))
        show("III polyP8 / 2^256", cu['poly'])
        for k, v in cu['parts_poly'].items(): show("      " + k, Fr(v, 2**256))
        show("TOTAL current (I.a exact)", tot_cur)
        show("TOTAL current (I.a prod form)", tot_cur - cu['Ia'] + cu['Ia_prod'])
        pre, it = generic(qf, qs)
        print("  generic attacks (lower bound on any true bound):")
        show("SK.seed search qf/2^128", Fr(pre))
        show("FORS/ITSR qf*p(qs)", Fr(it) if it > 0 else Fr(0))
        show("floor (sum)", Fr(pre + it))
        print("  predicted direct bound, c=2 (plan 3):")
        lin, cov, coll = direct(qf, qs, L)
        show("(2qf + C0)/2^128", lin); show("(qf+1)*cover_targets(qs)", cov)
        show("(Qtot+2)^2/2^257", coll); show("TOTAL direct", lin + cov + coll)
        print(f"    Qtot = 2^{lg(Qtot(qf, qs, L)):.2f}")
        lin1, _, _ = direct(qf, qs, L, c=1)
        show("TOTAL direct, refined c=1", lin1 + cov + coll)
        for mode in ('fulllog', 'fulllog_prod'):
            l2, c2, k2 = direct(qf, qs, L, itsr=mode)
            show(f"fallback: direct leg II + ITSR {mode} (n=qf+qs+1)", l2 + c2 + k2)
            show(f"   of which ITSR {mode}", c2)
        print(f"  gain current -> direct: {lg(tot_cur) - lg(lin + cov + coll):.2f} bits;"
              f" direct vs floor: {lg(lin + cov + coll) - log2(pre + it):.2f} bits")
