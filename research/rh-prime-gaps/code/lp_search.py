"""
Search for a test function for C^+(A) by linear programming.

Basis: F(x) = Σ_j c_j e^{-π b_j x²},  F̂(t) = Σ_j c_j b_j^{-1/2} e^{-π t²/b_j}.
For fixed widths b_j the problem
    max F(0) - A ∫_{|t|>1} (F̂)_+   subject to  ||F||_1 ≤ 1
is convex in c, and linear after discretising the integrals (LP, HiGHS).
The LP result is only a candidate: the functional is then evaluated precisely in mpmath
(functional.GaussSum), because the discretisation can overestimate.
"""

import sys

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, identity, vstack


def solve(A, bs, nx=4000, nt=4000):
    bs = np.asarray(bs, float)
    # truncation points chosen so that the tails e^{-π b x²}, e^{-π t²/b} are < e^{-45}
    X = np.sqrt(45 / (np.pi * bs.min()))
    T = np.sqrt(45 * bs.max() / np.pi)
    m = len(bs)
    x = np.linspace(0, X, nx)
    t = np.linspace(1, T, nt)
    wx = np.full(nx, x[1] - x[0])
    wx[[0, -1]] /= 2
    wt = np.full(nt, t[1] - t[0])
    wt[[0, -1]] /= 2
    Fx = np.exp(-np.pi * np.outer(x**2, bs))  # nx × m
    Ft = np.exp(-np.pi * np.outer(t**2, 1 / bs)) / np.sqrt(bs)  # nt × m
    # variables: c (m, free), u (nx, ≥0) ≥ |F(x_i)|, s (nt, ≥0) ≥ F̂(t_k)
    cost = np.concatenate([-np.ones(m), np.zeros(nx), 2 * A * wt])  # min -F(0) + A·2∫s
    Ix, It = identity(nx, format="csr"), identity(nt, format="csr")
    Zxt, Ztx = csr_matrix((nx, nt)), csr_matrix((nt, nx))
    A_ub = vstack(
        [
            hstack([csr_matrix(Fx), -Ix, Zxt]),  #  F(x) - u ≤ 0
            hstack([csr_matrix(-Fx), -Ix, Zxt]),  # -F(x) - u ≤ 0
            hstack([csr_matrix(Ft), Ztx, -It]),  #  F̂(t) - s ≤ 0
            hstack(
                [csr_matrix((1, m)), csr_matrix(2 * wx), csr_matrix((1, nt))]
            ),  # 2∫u ≤ 1
        ]
    ).tocsr()
    b_ub = np.concatenate([np.zeros(2 * nx + nt), [1.0]])
    bounds = [(None, None)] * m + [(0, None)] * (nx + nt)
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if res.status != 0:
        raise RuntimeError(res.message)
    return res.x[:m], -res.fun


if __name__ == "__main__":
    A = float(eval(sys.argv[1])) if len(sys.argv) > 1 else 4.0
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    lo, hi = (float(v) for v in sys.argv[3:5]) if len(sys.argv) > 4 else (0.3, 12.0)
    bs = np.geomspace(lo, hi, m)
    c, val = solve(A, bs)
    print(
        f"A={A:.5f} m={m} b∈[{lo},{hi}]  LP ≈ {val:.6f}  max|c|={np.abs(c).max():.3g}",
        flush=True,
    )
    np.save(f"cand_A{A:.4f}_m{m}_{lo}_{hi}.npy", np.vstack([bs, c]))
    import mpmath as mp
    from functional import GaussSum

    F = GaussSum([(mp.mpf(cj), 0, mp.pi * mp.mpf(bj)) for bj, cj in zip(bs, c)])
    X = float(np.sqrt(60 / (np.pi * lo)))
    T = float(np.sqrt(60 * hi / np.pi))
    J, info = F.functional(A, X=X, T=T)
    print(
        f"   mpmath: J = {mp.nstr(J, 10)}  1/J = {mp.nstr(1 / J, 8)}  {dict((k, mp.nstr(v, 8)) for k, v in info.items())}",
        flush=True,
    )
