"""
The explicit constant c* in the theorem
    "for every x ≥ 4 the interval [x, x + c*·√x·log x] contains a prime"
for the test function F(y) = Σ c_j e^{-π b_j y²}.  Derivation: proof.org.

Everything in Arb balls. ↑ = upper bound, ↓ = lower bound.
Part 1: norms of F (independent of x).  Part 2: the x-dependent terms as explicit functions of L = log x:
  [L0, 1000] covered by Arb balls (the result holds for every L in a ball),
  L ≥ 1000: crude decreasing bounds (proof.org section 4.2).
"""

import sys
from fractions import Fraction

import numpy as np
from certify import PI, GaussSum, lower, upper
from flint import arb

q = lambda f: arb(f.numerator) / f.denominator
up = lambda v: upper(v)
M_PRIMES = 15  # fixed split parameter in the prime part (section 3.5(a))
PSI_C = arb("4.3")  # lemma (L1)
PSI_D = arb("17.2")  # lemma (L2)


def abs_moment1(G, L, X):
    """↑ ∫_L^X |y·G(y)| dy and ↑ ∫_L^X (y-L)|G(y)| dy, over segments where G has constant sign."""
    m1, m1s = arb(0), arb(0)
    for lo, hi, s in G.segments(L, X):
        u, v = q(lo), q(hi)
        I1 = arb(0)
        for a, b in zip(G.a, G.beta):
            I1 += a * ((-PI * b * u * u).exp() - (-PI * b * v * v).exp()) / (2 * PI * b)
        I0 = G.prim(u, v)
        if s == 0:
            sup = abs(G.enclose(u, v))
            w = v - u
            m1 += sup * v * w
            m1s += sup * (v - q(L)) * w
        else:
            m1 += abs(I1)
            m1s += abs(I1 - q(L) * I0)
    return m1, m1s


def tail_y_bound(G, X):
    """↑ ∫_X^∞ y|G(y)| dy ≤ Σ |a_j| e^{-πβ_j X²}/(2πβ_j)."""
    return sum(
        (abs(a) * (-PI * b * X * X).exp() / (2 * PI * b) for a, b in zip(G.a, G.beta)),
        arb(0),
    )


def sup_abs(G, L, X, n=20000):
    """↑ sup_{[L,X]} |G|, by intervals on a grid."""
    best = arb(0)
    for i in range(n):
        lo, hi = L + (X - L) * Fraction(i, n), L + (X - L) * Fraction(i + 1, n)
        best = best.max(
            upper(abs(G.enclose(q(lo), q(hi))))
        )  # max of the exact upper ends
    return best


def norms(path):
    bs, cs = np.load(path)
    b = [arb(float(v)) for v in bs]
    c = [arb(float(v)) for v in cs]
    F = GaussSum(c, b)
    Fh = GaussSum([cj / bj.sqrt() for cj, bj in zip(c, b)], [1 / bj for bj in b])
    dF = GaussSum([-2 * PI * bj * cj for cj, bj in zip(c, b)], b)  # F'(y)  = y·dF(y)
    dFh = GaussSum(
        [-2 * PI * cj / bj.sqrt() / bj for cj, bj in zip(c, b)], [1 / bj for bj in b]
    )  # F̂'(t) = t·dFh(t)
    X = Fraction(int(np.ceil(np.sqrt(80 / (np.pi * bs.min())))))
    T = Fraction(int(np.ceil(np.sqrt(80 * bs.max() / np.pi))))
    n = dict(bmax=max(b, key=lambda v: float(v.mid())))
    n["F0"] = sum(c, arb(0))
    n["sumc"] = sum((abs(v) for v in c), arb(0))  # ≥ ||F||_∞
    n["sumcb"] = sum((abs(cj) * bj for cj, bj in zip(c, b)), arb(0))
    n["S"] = sum(
        (abs(cj) / bj.sqrt() for cj, bj in zip(c, b)), arb(0)
    )  # ≥ ||F̂||_∞, = ∫|y F'| ↑
    L1h, _, _ = F.integrals(Fraction(0), X)
    n["L1"] = up(2 * L1h)
    _, Tp, _ = Fh.integrals(Fraction(1), T)
    n["Tplus"] = up(2 * Tp)  # ∫_{|t|>1} (F̂)_+
    n["TM"] = up(2 * Fh.tail_abs_bound(arb(M_PRIMES)))  # ∫_{|t|>M} |F̂|
    tv, _ = abs_moment1(dFh, Fraction(1), T)
    n["TV"] = up(tv + tail_y_bound(dFh, q(T)))
    dl1, _ = abs_moment1(dF, Fraction(0), X)
    n["dF1"] = up(2 * dl1 + 2 * tail_y_bound(dF, q(X)))
    _, lg = abs_moment1(F, Fraction(1), X)
    n["logF"] = up(2 * lg + 2 * tail_y_bound(F, q(X)))
    n["supFh"] = up(
        sup_abs(Fh, Fraction(0), T) + n["S"] * (-PI * q(T) ** 2 / n["bmax"]).exp()
    )
    return n


def x_terms(n, L):
    """All terms depending on x = e^L (↑), for c ∈ [1/2, 1]. Numbering as in proof.org section 3.
    L may be an Arb ball; the result then bounds the terms for ALL L in the ball. The formulas avoid
    subtracting close quantities (e.g. V − U), so that the enclosure stays tight on wide balls."""
    S, bmax, M = n["S"], n["bmax"], arb(M_PRIMES)
    sx = (L / 2).exp()  # √x
    r = L / sx  # a_max = x·√(1+r)
    D = L / (4 * PI * sx)  # Δ ≤ D   (Δ = log(1+cL/√x)/4π)
    lD = (1 / D).log()  # Δ·log(1/Δ) is increasing for Δ < 1/e
    la = L + (1 + r).log() / 2  # log a_max
    t = {}
    t["eps1"] = PI * D**2 / 2 * n["sumcb"] / n["F0"]
    t["eta"] = (PI * D * (M + 2)).exp() * (1 + 1 / sx) - 1
    t["E_zero"] = (
        2 * PI * (arb("0.15") * D * S + (arb("0.15") * D * lD + 3 * D) * n["dF1"])
    )
    t["E_Gamma"] = (D / L) * (
        (arb("21.2") + PI * lD) * n["sumc"]
        + (PI / 2 + 2 * D) * n["L1"]
        + (PSI_C + lD) * n["dF1"]
        + 2 * S
    )
    # prime powers k ≥ 2: U = x e^{-θ}, V = a_max e^{θ}
    Mp = (bmax * (2 * L.log() + 25) / PI).sqrt()  # e^{-πM'²/b_max} = e^{-25}/L²
    th = 2 * PI * D * Mp
    logV = la + th
    sqU = sx * (-th / 2).exp()
    VmU_2sqU = (
        sx
        * (th / 2).exp()
        * ((r / ((1 + r).sqrt() + 1)) * th.exp() + 2 * th.sinh())
        / 2
    )  # (V−U)/(2√U)
    kmax = logV / arb(2).log()
    t["M'"] = Mp
    t["PP_in"] = n["supFh"] * logV / (2 * sqU) * kmax * (1 + VmU_2sqU)
    Lae = 1 + la
    cnt_over_sqrt = arb(1).exp().sqrt() * (
        (arb(1).exp()).sqrt() * (1 + r) ** (arb(1) / 4)
        + Lae
        / arb(2).log()
        * arb(1).exp() ** (arb(1) / 3)
        * (1 + r) ** (arb(1) / 6)
        * (-L / 6).exp()
    )
    t["PP_out"] = S * (-PI * Mp**2 / bmax).exp() * Lae / 2 * cnt_over_sqrt
    # tails |log(n/a)| > 1, the second prime term, the log π term  (§3.5(c))
    K = 1 / (4 * PI * D**2 * bmax)
    logN = (arb(1).exp() * (la.exp()) + 1).log()
    t["E_far"] = (
        S
        * (-K).exp()
        * (logN.exp() * (1 + logN.exp() / (K - 2)) + la.exp() * la + 2 + PI.log())
    )
    return t


def tail_bounds(n, L):
    """Crude bounds for the small terms when L ≥ 1000 (proof.org §4.2). Each has the form
    P(L)e^{-L/2} (P a polynomial of degree ≤ 4 with non-negative coefficients, so decreasing for L > 8),
    C·(L+2)/L² or e^{3L − e^L/(2L²)}·C; all decrease for L ≥ 1000."""
    S, s0, d1, l1, sig = n["S"], n["sumc"], n["dF1"], n["L1"], n["supFh"]
    e = (-L / 2).exp()
    EZ = L / 2 * e * (arb("0.15") * S + (arb("0.075") * L + 3) * d1)
    EG = (
        e
        / (4 * PI)
        * (
            (arb("21.2") + PI * L / 2) * s0
            + (PI / 2 + 1) * l1
            + (arb("4.3") + L / 2) * d1
            + 2 * S
        )
    )
    PPin = arb("1.5") * sig * (L + 1) ** 2 * (1 + L + 2 * L * L) * e
    one = arb(1).exp()
    PPout = (
        S
        * (-25 * arb(1)).exp()
        * (L + 2)
        / L**2
        * one.sqrt()
        / 2
        * ((2 * one).sqrt() + 1)
    )
    Efar = S * 200 * (3 * L - L.exp() / (2 * L * L)).exp()
    return EZ + EG + PPin + PPout + Efar


def main(path, L1=1000, h=arb("0.05")):
    n = norms(path)
    L0 = (arb(4) * arb(10) ** 18).log().lower()  # L0 ≤ log(4·10^18)
    t0 = x_terms(n, L0)
    small = lambda t: t["E_zero"] + t["E_Gamma"] + t["PP_in"] + t["PP_out"] + t["E_far"]
    base = n["logF"] + 8 * n["TV"]

    # (1) cover [L0, L1] by balls of width h; the result holds for every L in a ball.
    #     Collect the max of ε1, η and the small terms over all balls.
    e1m, etm, smm, k, lo = arb(0), arb(0), arb(0), 0, L0
    while lo < L1:
        hi = lo + h
        tb = x_terms(n, arb((lo + hi) / 2, h / 2 * (1 + arb("1e-30"))))
        e1m, etm, smm = (
            e1m.max(upper(tb["eps1"])),
            etm.max(upper(tb["eta"])),
            smm.max(upper(small(tb))),
        )
        lo = hi
        k += 1
    # L ≥ L1: ε1, η increase with D and 1/√x, which decrease for L > 2  ⇒  ≤ the values at L1 ≤ the max above
    tL1 = x_terms(n, arb(L1))
    assert tL1["eps1"] < e1m and tL1["eta"] < etm

    num = (
        n["F0"] * (1 - e1m)
        - 4 * (1 + etm) * n["Tplus"]
        - 4 * (arb(1).exp().sqrt() - 1) * (1 + etm) * n["TM"]
    )
    Jstar = lower(num / n["L1"])
    thr = (2 - arb("0.001") * Jstar) * n[
        "L1"
    ]  # condition: base + small < thr  (⇔ K/L̄1 < 2 − 0.001J*)
    cstar = upper(1 / Jstar)

    print(f"file: {path}")
    print("Norms (independent of x):")
    for kk in ["F0", "L1", "Tplus", "TM", "TV", "dF1", "logF", "supFh", "sumc", "S"]:
        print(f"  {kk:8s} {n[kk].str(10)}")
    print(f"Terms at x0 = 4e18 (L0 = {L0.str(6)}), for orientation:")
    for kk, v in t0.items():
        print(f"  {kk:8s} {v.str(6)}")
    print(
        f"Maxima over the {k} balls covering [L0, {L1}]:  ε1 ≤ {e1m.str(4)},  η ≤ {etm.str(4)},  small terms ≤ {smm.str(6)}"
    )
    print(f"  (precisely: small terms ≤ {smm.str(15)})")
    print(f"  J* ↓        = {Jstar.str(12)}")
    ratio = upper((base + smm) / n["L1"])
    print(
        f"  K/||F||_1 ↑ = {ratio.str(8)}   condition: < {(2 - arb('0.001') * Jstar).str(8)}"
    )
    ok = base + smm < thr
    print(f"  [L0, {L1}]: {'OK' if ok else 'FAIL'}")
    # (2) the tail L ≥ L1: the bounds decrease, so the value at L1 suffices
    tb = upper(tail_bounds(n, arb(L1)))
    ok2 = base + tb < thr
    print(f"  L ≥ {L1}: small terms ≤ {tb.str(6)}: {'OK' if ok2 else 'FAIL'}")
    # check: the crude bounds really are ≥ x_terms at a few points L ≥ L1
    for L in [arb(L1), arb(2000), arb(10) ** 4, arb(10) ** 5]:
        assert small(x_terms(n, L)) < tail_bounds(n, L), L
    ok_all = ok and ok2
    print(
        f"RESULT: {'CONDITION HOLDS for all x ≥ 4e18' if ok_all else 'FAIL'}  ⇒  c* = 1/J* ≤ {cstar.str(10)}"
    )
    print(f"  max log x/√x = 2/e < c*: {(2 / arb(1).exp() < cstar)}")
    return Jstar, cstar


if __name__ == "__main__":
    main(sys.argv[1])
