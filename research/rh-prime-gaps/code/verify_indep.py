"""Independent check of a candidate: F̂ by quadrature of F (not the formula), integrals on a dense grid (Simpson)."""

import sys

import numpy as np
from scipy.integrate import simpson

bs, c = np.load(sys.argv[1])
A = float(eval(sys.argv[2]))
F = lambda x: np.exp(-np.pi * np.outer(np.atleast_1d(x) ** 2, bs)) @ c
X = np.sqrt(60 / (np.pi * bs.min()))
T = np.sqrt(60 * bs.max() / np.pi)
x = np.linspace(0, X, 400_001)
Fx = F(x)
L1 = 2 * simpson(np.abs(Fx), x=x)
t = np.linspace(1, T, 40_001)
# F̂(t) = 2∫_0^∞ F(x) cos(2πxt) dx, quadrature on the x grid (in blocks, to save memory)
xs = np.linspace(0, X, 60_001)
Fxs = F(xs)
Fh = np.concatenate(
    [
        2 * simpson(Fxs * np.cos(2 * np.pi * np.outer(tb, xs)), x=xs, axis=1)
        for tb in np.array_split(t, 80)
    ]
)
Fh_formula = (np.exp(-np.pi * np.outer(t**2, 1 / bs)) / np.sqrt(bs)) @ c
tail = 2 * simpson(np.maximum(Fh, 0), x=t)
print(
    f"F(0)={F(0)[0]:.9f} L1={L1:.9f} tail+={tail:.9f}  max|F̂_num-F̂_formula|={np.abs(Fh - Fh_formula).max():.2e}"
)
print(f"J = {(F(0)[0] - A * tail) / L1:.9f}   1/J = {L1 / (F(0)[0] - A * tail):.7f}")
print(
    "sign changes of F on [0,X]:",
    np.sum(np.diff(np.sign(Fx)) != 0),
    "  F̂ on [1,T]:",
    np.sum(np.diff(np.sign(Fh)) != 0),
)
