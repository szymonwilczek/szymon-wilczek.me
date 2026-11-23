import RhGaps.Explicit

/-!
  Main theorem (proof.org): under RH, for every `x ≥ 4` the interval
  `[x, x + c*·√x·log x]` contains a prime, `c* = 0.8511525827`.
  Large `x`: `explicit_formula_bound` (a theorem in `Explicit.lean`) + CMS section 6.3 + section 3.6.
  Small `x`: the axiom `oliveira_e_silva` + the argument of section 2.
-/

open Real

namespace RhGaps

/-- **EXTERNAL (axiom).** Oliveira e Silva–Herzog–Pardi 2014:
  `p_{n+1} − p_n < log² p_n` for `11 ≤ p_n ≤ 4·10¹⁸`. -/
axiom oliveira_e_silva (p : ℕ) (hp : p.Prime) (h11 : 11 ≤ p) (hp4 : (p : ℝ) ≤ 4 * 10 ^ 18) :
    ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < p + log p ^ 2

/-! ### Conclusion of section 3.6 -/

theorem large_x (hRH : RiemannHypothesis) {x : ℝ} (hx : 4 * 10 ^ 18 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + cstar * √x * log x := by
  by_contra hno
  obtain ⟨hc1, hc2⟩ := cstar_bounds
  have hEF := explicit_formula_bound hRH x cstar hx hc1 hc2 hno
  obtain ⟨hY0, hY, hell⟩ := cms_63 hx hc1 hc2
  have hL := log_ge_42 hx
  have hJ : (0 : ℝ) < Jstar := by unfold Jstar; norm_num
  have hcJ : 1 ≤ cstar * Jstar := by unfold cstar Jstar; norm_num
  have hK : Kbar < 2 - Jstar / 1000 := by unfold Kbar Jstar; norm_num
  -- (cL/2 − 0.001)·J* ≤ Y·J* ≤ L/2 − 2 + K̄,  and cJ* ≥ 1
  have h1 : (cstar * log x / 2 - 1 / 1000) * Jstar ≤ Yq x cstar * Jstar :=
    mul_le_mul_of_nonneg_right hY hJ.le
  have h2 : log x / 2 ≤ cstar * Jstar * (log x / 2) := by nlinarith
  nlinarith

/-! ### Small `x`: section 2 -/

lemma lower_prod {x s l : ℝ} (_hs : 0 ≤ s) (hl : 0 ≤ l) (hsx : s ^ 2 ≤ x) (hlx : l ≤ log x) :
    cstar * s * l ≤ cstar * √x * log x := by
  have hsx' : s ≤ √x := Real.le_sqrt_of_sq_le hsx
  have hc : 0 ≤ cstar := by unfold cstar; norm_num
  apply mul_le_mul (mul_le_mul_of_nonneg_left hsx' hc) hlx hl (by positivity)

lemma log_four_gt {x : ℝ} (hx : 4 ≤ x) : 1.386 ≤ log x := by
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hx
  linarith

lemma log_seven_gt {x : ℝ} (hx : 7 ≤ x) : 1.8 ≤ log x := by
  have h7 : 1.8 ≤ log 7 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h5 : exp 1.8 ^ 5 = exp 1 ^ 9 := by
      rw [← Real.exp_natCast_mul, Real.exp_one_pow]; norm_num
    have h9 : exp 1 ^ 9 < 7 ^ 5 := by
      calc exp 1 ^ 9 < 2.7182818286 ^ 9 := by gcongr; exact e_lt
        _ < 7 ^ 5 := by norm_num
    rw [← h5] at h9
    exact (pow_lt_pow_iff_left₀ (exp_pos _).le (by norm_num) (by norm_num)).mp h9 |>.le
  exact h7.trans (Real.log_le_log (by norm_num) hx)

theorem small_x {x : ℝ} (hx : 4 ≤ x) (hx' : x < 4 * 10 ^ 18) :
    ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + cstar * √x * log x := by
  have hc : 0 ≤ cstar := by unfold cstar; norm_num
  rcases le_or_gt x 5 with h5 | h5
  · refine ⟨5, by norm_num, by exact_mod_cast h5, ?_⟩
    have := lower_prod (s := 2) (l := 1.386) (by norm_num) (by norm_num) (by linarith)
      (log_four_gt hx)
    have : cstar * 2 * 1.386 ≥ 1 := by unfold cstar; norm_num
    push_cast; linarith
  rcases le_or_gt x 7 with h7 | h7
  · refine ⟨7, by norm_num, by exact_mod_cast h7, ?_⟩
    have := lower_prod (s := 2.236) (l := 1.386) (by norm_num) (by norm_num) (by nlinarith)
      (log_four_gt hx)
    have : cstar * 2.236 * 1.386 ≥ 2 := by unfold cstar; norm_num
    push_cast; linarith
  rcases le_or_gt x 11 with h11 | h11
  · refine ⟨11, by norm_num, by exact_mod_cast h11, ?_⟩
    have := lower_prod (s := 2.6457) (l := 1.8) (by norm_num) (by norm_num) (by nlinarith)
      (log_seven_gt h7.le)
    have : cstar * 2.6457 * 1.8 ≥ 4 := by unfold cstar; norm_num
    push_cast; linarith
  -- 11 < x < 4·10¹⁸: the largest prime p ≤ ⌊x⌋ and the next one q (OeS)
  set m := ⌊x⌋₊ with hm
  have hx0 : 0 ≤ x := by linarith
  have hm11 : 11 ≤ m := by
    rw [hm, Nat.le_floor_iff hx0]; push_cast; linarith
  set p := Nat.findGreatest Nat.Prime m with hp
  have hpP : p.Prime := Nat.findGreatest_spec hm11 (by norm_num : Nat.Prime 11)
  have hp11 : 11 ≤ p := Nat.le_findGreatest hm11 (by norm_num)
  have hpm : p ≤ m := Nat.findGreatest_le m
  have hpx : (p : ℝ) ≤ x := (Nat.cast_le.mpr hpm).trans (Nat.floor_le hx0)
  obtain ⟨q, hqP, hpq, hqlt⟩ := oliveira_e_silva p hpP hp11 (by linarith)
  have hmq : m < q := by
    by_contra hcon
    rw [Nat.not_lt] at hcon
    exact Nat.findGreatest_is_greatest hpq hcon hqP
  have hxq : x ≤ q := by
    have := Nat.lt_floor_add_one x
    have : (m : ℝ) + 1 ≤ q := by exact_mod_cast hmq
    linarith
  refine ⟨q, hqP, hxq, ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
  have hlogp : log p ≤ log x := Real.log_le_log hp0 hpx
  have hlogp0 : 0 ≤ log p := Real.log_nonneg (by exact_mod_cast hpP.one_lt.le)
  have hlogx0 : 0 ≤ log x := Real.log_nonneg (by linarith)
  -- log² x ≤ c*·√x·log x, since log x ≤ (2/e)√x ≤ c*√x
  have h2e := log_le_two_div_e_mul_sqrt (by linarith : 0 < x)
  have hce : 2 / exp 1 ≤ cstar := by
    rw [div_le_iff₀ (exp_pos 1)]; have := e_gt; unfold cstar at *; nlinarith
  have hsq : log x ≤ cstar * √x := h2e.trans (by gcongr)
  have : log p ^ 2 ≤ cstar * √x * log x := by nlinarith
  linarith

/-- **Main theorem.** Under RH: for every `x ≥ 4` the interval `[x, x + 0.8511525827·√x·log x]`
  contains a prime. -/
theorem main (hRH : RiemannHypothesis) (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + cstar * √x * log x := by
  rcases lt_or_ge x (4 * 10 ^ 18) with h | h
  · exact small_x hx h
  · exact large_x hRH h

end RhGaps
