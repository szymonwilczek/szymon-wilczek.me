"""
Check of the digamma lemmas (analytic proof: proof.org, section 1).

  (L1) |Re ψ(1/4 + it)| ≤ 4.3 + log(1 + 4|t|)          for t ∈ R
  (L2) |ψ'(1/4 + it)|   ≤ min(17.2, 1/t² + π/(2|t|))   [ψ'(1/4) = π² + 8G < 17.2]

Interval check (Arb): t ∈ [0, TMAX] covered by balls; on each ball acb.digamma gives
an enclosure, compared with a lower bound for the right-hand side.
This does NOT replace the proof (which covers all of R); it is an independent confirmation.
"""

from flint import acb, arb, ctx

ctx.prec = 80
TMAX, N = 200, 200000
quarter = arb(1) / 4
G = arb("0.915965594177219015054603514932384110774")
psi1_q = arb.pi() ** 2 + 8 * G
print("ψ'(1/4) =", psi1_q, " (< 17.2:", psi1_q < arb("17.2"), ")")
print("ψ(1/4)  =", quarter.digamma())

bad1 = bad2 = 0
worst1 = worst2 = -1e9
for i in range(N):
    lo, hi = arb(TMAX) * i / N, arb(TMAX) * (i + 1) / N
    t = (lo + hi) / 2
    tb = arb(t.mid(), ((hi - lo) / 2).mid() * (1 + arb("1e-15")))  # a ball ⊇ [lo, hi]
    z = acb(quarter, tb)
    re = abs(z.digamma().real)
    rhs1 = arb("4.3") + (1 + 4 * lo).log()  # smallest RHS on the ball
    if not (re < rhs1):
        bad1 += 1
    worst1 = max(worst1, float((re - rhs1).mid()))
    # ψ' = derivative of digamma: acb.polygamma(1, z)
    p1 = abs(z.polygamma(1))
    rhs2 = (
        arb("17.2")
        if lo == 0
        else min(arb("17.2"), 1 / (hi * hi) + arb.pi() / (2 * hi))
    )
    if not (p1 < rhs2):
        # split the ball into 1000 parts (the enclosure overestimates on a wide ball)
        for k in range(1000):
            l2, h2 = lo + (hi - lo) * k / 1000, lo + (hi - lo) * (k + 1) / 1000
            z2 = acb(
                quarter,
                arb(((l2 + h2) / 2).mid(), ((h2 - l2) / 2).mid() * (1 + arb("1e-15"))),
            )
            r2 = (
                arb("17.2")
                if l2 == 0
                else min(arb("17.2"), 1 / (h2 * h2) + arb.pi() / (2 * h2))
            )
            q2 = abs(z2.polygamma(1))
            if not (q2 < r2):
                bad2 += 1
                print("  violation:", l2.str(6), h2.str(6), q2.str(10), r2.str(10))
            worst2 = max(worst2, float((q2 - r2).mid()))
    else:
        worst2 = max(worst2, float((p1 - rhs2).mid()))
print(f"(L1): {bad1} violations on {N} balls, max(LHS-RHS) = {worst1:.4f}")
print(f"(L2): {bad2} violations on {N} balls, max(LHS-RHS) = {worst2:.4f}")
