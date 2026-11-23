"""
Independent recomputation of the norms from explicit_constant.py by a DIFFERENT method (mpmath, 50 digits):
roots from a dense grid + findroot, integrals by mpmath.quad between roots,
F̂ and derivatives evaluated directly from the formula, without the code in certify.py.
Not rigorous: it is there to catch bugs in the code, not to prove anything.
"""

import sys

import mpmath as mp
import numpy as np

mp.mp.dps = 50


def main(path):
    bs, cs = np.load(path)
    b = [mp.mpf(float(v)) for v in bs]
    c = [mp.mpf(float(v)) for v in cs]
    F = lambda y: mp.fsum(cj * mp.exp(-mp.pi * bj * y * y) for cj, bj in zip(c, b))
    dF = lambda y: mp.fsum(
        -2 * mp.pi * bj * cj * y * mp.exp(-mp.pi * bj * y * y) for cj, bj in zip(c, b)
    )
    Fh = lambda t: mp.fsum(
        cj / mp.sqrt(bj) * mp.exp(-mp.pi * t * t / bj) for cj, bj in zip(c, b)
    )
    dFh = lambda t: mp.fsum(
        -2 * mp.pi * t * cj / bj ** mp.mpf(1.5) * mp.exp(-mp.pi * t * t / bj)
        for cj, bj in zip(c, b)
    )

    def roots(g, lo, hi, n=6000):
        xs = [lo + (hi - lo) * mp.mpf(i) / n for i in range(n + 1)]
        vs = [g(x) for x in xs]
        r = []
        for i in range(n):
            if vs[i] == 0:
                r.append(xs[i])
            elif vs[i] * vs[i + 1] < 0:
                r.append(mp.findroot(g, (xs[i], xs[i + 1]), solver="anderson"))
        return r

    def int_abs(g, lo, hi, w=lambda y: 1, pos=False):
        pts = [lo] + roots(g, lo, hi) + [hi]
        tot = mp.mpf(0)
        for u, v in zip(pts[:-1], pts[1:]):
            val = mp.quad(lambda y: w(y) * g(y), [u, v])
            if pos:
                tot += max(val, 0) if g((u + v) / 2) > 0 else 0
            else:
                tot += abs(val)
        return tot

    Y, T = 30, 40
    r = {}
    r["F0"] = F(0)
    r["L1"] = 2 * int_abs(F, mp.mpf(0), Y)
    r["Tplus"] = 2 * int_abs(Fh, mp.mpf(1), T, pos=True)
    r["TV"] = int_abs(dFh, mp.mpf(1), T)
    r["dF1"] = 2 * int_abs(dF, mp.mpf(0), Y)
    r["logF"] = 2 * int_abs(
        F, mp.mpf(1), Y, w=lambda y: mp.log(y)
    )  # exactly ||log+|y| F||_1
    ts = [mp.mpf(i) / 2000 * T for i in range(2001)]
    r["supFh"] = max(abs(Fh(t)) for t in ts)
    J = (r["F0"] - 4 * r["Tplus"]) / r["L1"]
    small = (
        mp.mpf("0.000741269") + mp.mpf("0.00135710") + mp.mpf("0.000582881")
    )  # E_zero+E_Γ+PP_in at x0
    K = (r["logF"] + 8 * r["TV"] + small) / r["L1"]
    for k, v in r.items():
        print(f"  {k:6s} {mp.nstr(v, 12)}")
    print(f"  J (no ε1, η)   = {mp.nstr(J, 12)}   1/J = {mp.nstr(1 / J, 12)}")
    print(f"  K/||F||_1      = {mp.nstr(K, 10)}   (exact log y instead of y-1)")


if __name__ == "__main__":
    main(sys.argv[1])
