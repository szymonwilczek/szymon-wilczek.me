"""
Rigorous certificate of the lower bound C^+(A) >= J_A(F) for F(x) = Σ c_j e^{-π b_j x²}.

The floats (b_j, c_j) in the .npy file are taken as EXACT (dyadic) rationals: they define F.
All arithmetic is in Arb balls (python-flint):

  * F(0) = Σ c_j                                  - exact (a ball),
  * ||F||_1  - UPPER BOUND,
  * ∫_{|t|>1} (F̂)_+ - UPPER BOUND,
  ⇒ J = (F(0) - A·tail) / L1 - LOWER BOUND.

F̂(t) = Σ c_j b_j^{-1/2} e^{-π t²/b_j} is also a sum of Gaussians, so the GaussSum class handles
both functions. Integrals of Gaussians are in closed form via erf/erfc.

Root isolation: recursive subdivision of [L, X]; on an interval I we compute G(I) in mean-value
form G(m) + G'(I)(I - m). If 0 ∉ G(I), the sign is constant. If 0 ∉ G'(I), G is monotone with
at most one root; bisection narrows it to an interval of width < eps, on which
∫|G| ≤ eps·sup|G|.
"""

import sys
from fractions import Fraction

import numpy as np
from flint import arb, ctx

ctx.prec = 256
PI = arb.pi()


def A_from(s):
    return (
        arb(Fraction(s).numerator) / arb(Fraction(s).denominator)
        if "/" in s
        else arb(s)
    )


class GaussSum:
    """G(x) = Σ a_j e^{-π β_j x²}, a_j, β_j Arb balls."""

    def __init__(self, a, beta):
        self.a, self.beta = a, beta

    def g(self, x, d=0):
        s = arb(0)
        for a, b in zip(self.a, self.beta):
            e = (-PI * b * x * x).exp()
            if d == 0:
                s += a * e
            elif d == 1:
                s += a * (-2 * PI * b * x) * e
            else:
                s += a * (4 * PI * PI * b * b * x * x - 2 * PI * b) * e
        return s

    def enclose(self, lo, hi, d=0):
        """Enclosure of G^{(d)} on [lo, hi] (mean-value form)."""
        m = (lo + hi) / 2
        I = arb(m, (hi - lo) / 2)  # the ball [lo, hi]
        return self.g(m, d) + self.g(I, d + 1) * (I - m)

    def prim(self, u, v):
        """∫_u^v G exactly (a ball); v=None means +∞."""
        s = arb(0)
        for a, b in zip(self.a, self.beta):
            r = (PI * b).sqrt()
            if v is None:
                s += a / (2 * b.sqrt()) * (r * u).erfc()
            else:
                s += a / (2 * b.sqrt()) * ((r * v).erf() - (r * u).erf())
        return s

    def tail_abs_bound(self, X):
        """Upper bound ∫_X^∞ |G| ≤ Σ |a_j| ∫_X^∞ e^{-πβx²}."""
        s = arb(0)
        for a, b in zip(self.a, self.beta):
            s += abs(a) / (2 * b.sqrt()) * ((PI * b).sqrt() * X).erfc()
        return s

    def segments(self, L, X, eps=Fraction(1, 10**12), init=4000):
        """Returns a list of (lo, hi, sign), sign ∈ {+1, -1, 0}; 0 = enclosure of a root (width < eps)."""
        out, stack = [], []
        grid = [L + (X - L) * Fraction(i, init) for i in range(init + 1)]
        stack = list(zip(grid[:-1], grid[1:]))[::-1]
        ev = lambda q: self.g(arb(q.numerator) / arb(q.denominator))
        while stack:
            lo, hi = stack.pop()
            alo, ahi = (
                arb(lo.numerator) / lo.denominator,
                arb(hi.numerator) / hi.denominator,
            )
            G = self.enclose(alo, ahi)
            if G > 0 or G < 0:
                out.append((lo, hi, 1 if G > 0 else -1))
                continue
            D = self.enclose(alo, ahi, 1)
            if D > 0 or D < 0:  # monotone: ≤ 1 root
                glo, ghi = ev(lo), ev(hi)
                if (glo > 0 and ghi > 0) or (glo < 0 and ghi < 0):
                    out.append((lo, hi, 1 if glo > 0 else -1))
                    continue
                if not ((glo > 0 and ghi < 0) or (glo < 0 and ghi > 0)):
                    # sign at an endpoint undecided: subdivide further
                    if hi - lo < eps:
                        out.append((lo, hi, 0))
                        continue
                    mid = (lo + hi) / 2
                    stack += [(mid, hi), (lo, mid)]
                    continue
                s_lo = 1 if glo > 0 else -1
                a_, b_ = lo, hi
                while b_ - a_ >= eps:
                    mid = (a_ + b_) / 2
                    gm = ev(mid)
                    if (gm > 0 and s_lo > 0) or (gm < 0 and s_lo < 0):
                        a_ = mid
                    elif (gm > 0 and s_lo < 0) or (gm < 0 and s_lo > 0):
                        b_ = mid
                    else:
                        break
                # [lo, a_] sign s_lo, [a_, b_] root, [b_, hi] sign -s_lo
                if a_ > lo:
                    out.append((lo, a_, s_lo))
                out.append((a_, b_, 0))
                if hi > b_:
                    out.append((b_, hi, -s_lo))
                continue
            if hi - lo < eps:
                out.append((lo, hi, 0))
                continue
            mid = (lo + hi) / 2
            stack += [(mid, hi), (lo, mid)]
        return out

    def integrals(self, L, X):
        """(upper bound of ∫_L^∞ |G|, upper bound of ∫_L^∞ G_+, number of roots)."""
        q = lambda f: arb(f.numerator) / f.denominator
        absI, posI, nroots = arb(0), arb(0), 0
        for lo, hi, s in self.segments(L, X):
            if s == 0:
                nroots += 1
                sup = abs(self.enclose(q(lo), q(hi)))
                w = q(hi) - q(lo)
                absI += sup * w
                posI += sup * w
            else:
                v = self.prim(q(lo), q(hi))
                absI += abs(v)
                if s > 0:
                    posI += v
        t = self.tail_abs_bound(q(X))
        return absI + t, posI + t, nroots


def upper(x):  # right end of the ball, exact (rounded up), an arb of radius 0
    return x.upper()


def lower(x):  # left end of the ball, exact (rounded down)
    return x.lower()


def certify(path, A_str):
    bs, cs = np.load(path)
    b = [arb(float(v)) for v in bs]  # exact dyadic rationals
    c = [arb(float(v)) for v in cs]
    F = GaussSum(c, b)
    Fh = GaussSum([cj / bj.sqrt() for cj, bj in zip(c, b)], [1 / bj for bj in b])
    X = Fraction(int(np.ceil(np.sqrt(80 / (np.pi * bs.min())))))
    T = Fraction(int(np.ceil(np.sqrt(80 * bs.max() / np.pi))))
    A = A_from(A_str)
    F0 = sum(c, arb(0))
    l1_half, _, r1 = F.integrals(Fraction(0), X)
    _, tail_half, r2 = Fh.integrals(Fraction(1), T)
    L1 = 2 * l1_half
    tail = 2 * tail_half
    L1u, tailu = upper(L1), upper(tail)
    Jlow = (F0 - A * tailu) / L1u
    print(f"file: {path}   A = {A_str}")
    print(f"  F(0)               = {F0.str(15)}")
    print(f"  ||F||_1      ≤ {L1u.str(15)}   (roots of F on [0,X]: {r1})")
    print(f"  ∫(F̂)_+ |t|>1 ≤ {tailu.str(15)}   (roots of F̂ on [1,T]: {r2})")
    print(f"  ⇒  C^+(A) ≥ J ≥ {lower(Jlow).str(12)}")
    print(f"  ⇒  1/J ≤ {upper(1 / arb(lower(Jlow))).str(12)}")
    return lower(Jlow)


if __name__ == "__main__":
    certify(sys.argv[1], sys.argv[2])
