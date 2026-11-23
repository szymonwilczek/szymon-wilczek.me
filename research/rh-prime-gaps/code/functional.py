"""
The Carneiro–Milinovich–Soundararajan functional:

    J_A(F) = ( F(0) - A * ∫_{|t|>1} (F̂(t))_+ dt ) / ||F||_1,
    C^+(A) = sup_F J_A(F).

Convention: F̂(t) = ∫ F(x) e^{-2πixt} dx.

Two classes of functions:
  * GaussSum - F(x) = Σ c_j x^{2k_j} e^{-b_j x^2}   (CMS (4.11), the CPdL form p(x²)e^{-πx²})
  * DilatedH - F(x) = H(x/λ), H(x) = cos(2πx)/(1-16x²)  (CMS section 6, the explicit version)
"""

from __future__ import annotations

from dataclasses import dataclass

import mpmath as mp

mp.mp.dps = 30


def _sign_changes(f, a, b, n):
    """Roots of f on [a, b]: sample n points, then refine by bisection/Anderson."""
    xs = [a + (b - a) * mp.mpf(i) / n for i in range(n + 1)]
    vals = [f(x) for x in xs]
    roots = []
    for x0, x1, v0, v1 in zip(xs, xs[1:], vals, vals[1:]):
        if v0 == 0:
            roots.append(x0)
        elif v0 * v1 < 0:
            roots.append(mp.findroot(f, (x0, x1), solver="anderson"))
    return roots


def integrate_abs(f, a, b, n=4000):
    pts = [mp.mpf(a)] + _sign_changes(f, a, b, n) + [mp.mpf(b)]
    return sum(abs(mp.quad(f, [u, v])) for u, v in zip(pts, pts[1:]) if v > u)


def integrate_pos(f, a, b, n=4000):
    pts = [mp.mpf(a)] + _sign_changes(f, a, b, n) + [mp.mpf(b)]
    total = mp.mpf(0)
    for u, v in zip(pts, pts[1:]):
        if v <= u:
            continue
        if f((u + v) / 2) > 0:
            total += mp.quad(f, [u, v])
    return total


@dataclass
class GaussSum:
    terms: list  # (c, k, b): c * x^(2k) * exp(-b x^2)

    def __call__(self, x):
        x = mp.mpf(x)
        return sum(
            mp.mpf(c) * x ** (2 * k) * mp.e ** (-mp.mpf(b) * x * x)
            for c, k, b in self.terms
        )

    def hat(self, t):
        # FT[x^{2k} e^{-bx²}](t) = (-1)^k (4b)^{-k} H_{2k}(s) e^{-s²} sqrt(π/b),  s = πt/√b
        t = mp.mpf(t)
        out = mp.mpf(0)
        for c, k, b in self.terms:
            b = mp.mpf(b)
            s = mp.pi * t / mp.sqrt(b)
            out += (
                mp.mpf(c)
                * (-1) ** k
                * (4 * b) ** (-k)
                * mp.hermite(2 * k, s)
                * mp.e ** (-s * s)
                * mp.sqrt(mp.pi / b)
            )
        return out

    def functional(self, A, X=12, T=12):
        l1 = 2 * integrate_abs(self, 0, X)
        tail = 2 * integrate_pos(self.hat, 1, T)
        return (self(0) - mp.mpf(A) * tail) / l1, {
            "F0": self(0),
            "L1": l1,
            "tail+": tail,
        }


@dataclass
class DilatedH:
    lam: float

    def __call__(self, x):
        y = mp.mpf(x) / self.lam
        if abs(1 - 16 * y * y) < mp.mpf(10) ** -20:  # removable singularity at y = ±1/4
            return mp.pi / 4
        return mp.cos(2 * mp.pi * y) / (1 - 16 * y * y)

    def hat(self, t):
        u = mp.mpf(self.lam) * t
        return (
            mp.mpf(self.lam) * mp.pi / 4 * mp.cos(mp.pi * u / 2)
            if abs(u) <= 1
            else mp.mpf(0)
        )

    def functional(self, A, X=400):
        lam = mp.mpf(self.lam)
        # ||H||_1: numerical integration with nodes at the zeros of cos(2πx) (x = 1/4 + m/2, m ≥ 1)
        nodes = [mp.mpf(0)] + [mp.mpf(1) / 4 + mp.mpf(m) / 2 for m in range(1, 2 * X)]
        h = lambda y: (
            mp.cos(2 * mp.pi * y) / (1 - 16 * y * y)
            if abs(1 - 16 * y * y) > 1e-25
            else mp.pi / 4
        )
        l1H = 2 * sum(abs(mp.quad(h, [u, v])) for u, v in zip(nodes, nodes[1:]))
        # tail: |H(y)| ~ 1/(16 y²) → remainder ≈ (2/π)·∫ 1/(16y²) dy using the mean of |cos|
        l1H += 2 * (2 / mp.pi) / (16 * nodes[-1])
        l1 = lam * l1H
        tail = 1 - mp.sin(mp.pi * lam / 2)  # ∫_{|t|>1} F̂ = 1 - sin(πλ/2), F̂ ≥ 0
        return (1 - mp.mpf(A) * tail) / l1, {
            "F0": 1,
            "L1": l1,
            "tail+": tail,
            "c0": 1 / l1H,
        }
