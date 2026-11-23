"""Reproduces known values from CMS (2019)."""

import mpmath as mp
from functional import DilatedH, GaussSum

# CMS (4.11), A = 36/11 → expected 1.1943...
F411 = GaussSum(
    [(-4.8, 1, 3.3), (1.5, 1, 7.4), (520, 12, 9.7), (1.3, 0, 2.8), (0.18, 0, 2)]
)
J, info = F411.functional(mp.mpf(36) / 11)
print(
    "CMS (4.11), A=36/11:  J =",
    mp.nstr(J, 10),
    " 1/J =",
    mp.nstr(1 / J, 10),
    {k: mp.nstr(v, 8) for k, v in info.items()},
)

# FT check: F̂(0) = ∫F
print(
    "   check F̂(0) vs ∫F:",
    mp.nstr(F411.hat(0), 12),
    mp.nstr(2 * mp.quad(F411, [0, 12]), 12),
)

# H with λ = 0.9, A = 4 → expected J = 1.1405..., ||F||_1 = 0.83337, c0 = 1.07995
J, info = DilatedH(0.9).functional(4)
print(
    "H(x/0.9), A=4:        J =",
    mp.nstr(J, 10),
    " 1/J =",
    mp.nstr(1 / J, 10),
    {k: mp.nstr(v, 8) for k, v in info.items()},
)

# optimal λ for H at A=4 → expected λ=0.892422, J=1.141186
lam = mp.findroot(
    lambda l: mp.diff(lambda m: DilatedH(m).functional(4, X=100)[0], l), 0.89
)
J, _ = DilatedH(lam).functional(4)
print(
    "H optimal λ, A=4:     λ =",
    mp.nstr(lam, 8),
    " J =",
    mp.nstr(J, 10),
    " 1/J =",
    mp.nstr(1 / J, 10),
)

# CMS (4.11) at A = 4 (for comparison with the explicit version)
J, _ = F411.functional(4)
print("CMS (4.11), A=4:      J =", mp.nstr(J, 10), " 1/J =", mp.nstr(1 / J, 10))
