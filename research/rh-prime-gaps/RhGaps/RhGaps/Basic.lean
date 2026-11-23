import Mathlib

/-!
  Elementary lemmas used in the proof (proof.org).
  Everything here is fully proved, with no axioms.
-/

open Real MeasureTheory

namespace RhGaps

/-- `log(1+s) ≥ s/(1+s)`, gives `|I_j|⁻¹ ≤ 2πΔ(√x_j + 1)` -/
lemma div_one_add_le_log {s : ℝ} (hs : 0 ≤ s) : s / (1 + s) ≤ log (1 + s) := by
  have h1 : 0 < 1 + s := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  have e : (1 + s)⁻¹ - 1 = -(s / (1 + s)) := by field_simp; ring
  linarith

/-- section 3.2: `e^s - 1 ≤ 2s` for `0 ≤ s ≤ 1`. -/
lemma exp_sub_one_le_two_mul {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : exp s - 1 ≤ 2 * s := by
  have := Real.abs_exp_sub_one_le (x := s) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  exact (le_abs_self _).trans this

/-- section 2: `log x ≤ (2/e)·√x` for `x > 0`. -/
lemma log_le_two_div_e_mul_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ 2 / exp 1 * √x := by
  have hs : 0 < √x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (div_pos hs (exp_pos 1))
  rw [Real.log_div hs.ne' (exp_pos 1).ne', Real.log_exp] at h
  have e1 : log x = 2 * log √x := by rw [Real.log_sqrt hx.le]; ring
  have e2 : 2 / exp 1 * √x = 2 * (√x / exp 1) := by ring
  rw [e1, e2]; linarith

/-- (TV), part 1: value at a point <= mean + oscillation. -/
lemma le_avg_add_osc {G : ℝ → ℝ} {a b ω s : ℝ} (hab : a < b)
    (hG : IntervalIntegrable G volume a b)
    (hosc : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, G u - G v ≤ ω)
    (hs : s ∈ Set.Icc a b) :
    G s ≤ (∫ u in a..b, G u) / (b - a) + ω := by
  have h := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hG
    (fun v hv => show G s - ω ≤ G v by linarith [hosc s hs v hv])
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  have hba : 0 < b - a := by linarith
  have : G s - ω ≤ (∫ u in a..b, G u) / (b - a) := by
    rw [le_div_iff₀ hba]; linarith
  linarith

end RhGaps
