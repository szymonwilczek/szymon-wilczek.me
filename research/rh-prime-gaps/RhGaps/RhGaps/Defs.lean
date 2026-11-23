import Mathlib
import RhGaps.Basic

/-!
  Shared definitions (proof.org section 3) and the CMS section 6.3 inequalities, fully proved.
-/

open Real

namespace RhGaps
/-- `J* = 1.17487747839`; PROVED in `Explicit.lean`: `J*·L̄₁ ≤ F(0) − ε − 4(1+η̄)T₊ − …`. -/
noncomputable def Jstar : ℝ := 117487747839 / 10 ^ 11
/-- `K̄ = 1.3048608`; PROVED in `Explicit.lean`: `Λ̄_F + Esm + 8·TV ≤ K̄·L̄₁`. -/
noncomputable def Kbar : ℝ := 13048608 / 10 ^ 7
/-- The constant of the theorem (`1/J*` rounded up). -/
noncomputable def cstar : ℝ := 8511525827 / 10 ^ 10

/-- `r = c·L/√x`, `x' = x(1+r)`. -/
noncomputable def rr (x c : ℝ) : ℝ := c * log x / √x
/-- `2πΔ = ½·log(1 + r)`. -/
noncomputable def tpd (x c : ℝ) : ℝ := log (1 + rr x c) / 2
/-- `Y = 2πΔ·√a`, `a = √(x x') = x·√(1+r)`. -/
noncomputable def Yq (x c : ℝ) : ℝ := tpd x c * √(x * √(1 + rr x c))
/-- `log(1/(2πΔ))`. -/
noncomputable def ell (x c : ℝ) : ℝ := log (1 / tpd x c)

/-! ### Auxiliary numerical bounds -/

lemma e_lt : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
lemma e_gt : 2.7182818283 < exp 1 := Real.exp_one_gt_d9

lemma log_le_div_e {y : ℝ} (hy : 0 < y) : log y ≤ y / exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy (exp_pos 1))
  rw [Real.log_div hy.ne' (exp_pos 1).ne', Real.log_exp] at h
  linarith

lemma cstar_bounds : 1 / 2 ≤ cstar ∧ cstar ≤ 1 := by unfold cstar; constructor <;> norm_num

lemma exp_two_lt : exp 2 < 7.39 := by
  have : exp 2 = exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
  rw [this]
  calc exp 1 ^ 2 < 2.7182818286 ^ 2 := by gcongr; exact e_lt
    _ < 7.39 := by norm_num

lemma exp_two_gt : 7.38 < exp 2 := by
  have : exp 2 = exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
  rw [this]
  calc (7.38 : ℝ) < 2.7182818283 ^ 2 := by norm_num
    _ < exp 1 ^ 2 := by gcongr; exact e_gt

/-- `log x ≥ 42` for `x ≥ 4·10¹⁸`. -/
lemma log_ge_42 {x : ℝ} (hx : 4 * 10 ^ 18 ≤ x) : 42 ≤ log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [Real.le_log_iff_exp_le hx0]
  have : exp 42 = exp 1 ^ 42 := by rw [Real.exp_one_pow]; norm_num
  rw [this]
  calc exp 1 ^ 42 ≤ 2.7182818286 ^ 42 := by gcongr; exact e_lt.le
    _ ≤ 4 * 10 ^ 18 := by norm_num
    _ ≤ x := hx

/-- `(log x)²/√x ≤ 1/1000` for `x ≥ 4·10¹⁸` (via `log x = 8 log x^{1/8} ≤ 8x^{1/8}/e`). -/
lemma logsq_div_sqrt_small {x : ℝ} (hx : 4 * 10 ^ 18 ≤ x) : log x ^ 2 / √x ≤ 1 / 1000 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  set q := √x with hq
  set w := √q with hw
  set s := √w with hs
  have hq0 : 0 < q := Real.sqrt_pos.mpr hx0
  have hw0 : 0 < w := Real.sqrt_pos.mpr hq0
  have hs0 : 0 < s := Real.sqrt_pos.mpr hw0
  have hq2 : q * q = x := Real.mul_self_sqrt hx0.le
  have hw2 : w * w = q := Real.mul_self_sqrt hq0.le
  have hs2 : s * s = w := Real.mul_self_sqrt hw0.le
  have hL : log x = 8 * log s := by
    have h1 : log q = log x / 2 := Real.log_sqrt hx0.le
    have h2 : log w = log q / 2 := Real.log_sqrt hq0.le
    have h3 : log s = log w / 2 := Real.log_sqrt hw0.le
    linarith
  have hqb : 2 * 10 ^ 9 ≤ q := by
    rw [hq, Real.le_sqrt (by norm_num) hx0.le]; linarith
  have hwb : 44721 ≤ w := by
    rw [hw, Real.le_sqrt (by norm_num) hq0.le]; linarith
  have hlogs := log_le_div_e hs0
  have hlogs0 : 0 ≤ log s := by
    apply Real.log_nonneg
    nlinarith
  have he := e_gt
  -- log x ≤ 8 s / e ≤ 8 s / 2.718
  have h1 : log x ≤ 8 * s / 2.718 := by
    have : s / exp 1 ≤ s / 2.718 :=
      div_le_div_of_nonneg_left hs0.le (by norm_num) (by linarith)
    have e8 : 8 * s / 2.718 = 8 * (s / 2.718) := by ring
    rw [hL, e8]; linarith
  have hlx0 : 0 ≤ log x := by rw [hL]; positivity
  have h2 : log x ^ 2 ≤ (8 * s / 2.718) ^ 2 := by gcongr
  rw [div_le_iff₀ hq0]
  calc log x ^ 2 ≤ (8 * s / 2.718) ^ 2 := h2
    _ = 64 / 2.718 ^ 2 * w := by rw [← hs2]; ring
    _ ≤ 1 / 1000 * q := by
        rw [← hw2]
        have : (64 / 2.718 ^ 2 : ℝ) ≤ 1 / 1000 * 44721 := by norm_num
        nlinarith

/-! ### The CMS section 6.3 inequalities (proof.org section 3.6, here formally) -/

lemma cms_63 {x c : ℝ} (hx : 4 * 10 ^ 18 ≤ x) (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 1) :
    0 ≤ Yq x c ∧ c * log x / 2 - 1 / 1000 ≤ Yq x c ∧ ell x c ≤ log x / 2 - 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hL42 := log_ge_42 hx
  set L := log x with hLdef
  have hsmall := logsq_div_sqrt_small hx
  rw [← hLdef] at hsmall
  have hLs : L / √x ≤ 1 / 1000 := by
    calc L / √x ≤ L ^ 2 / √x := by
          apply div_le_div_of_nonneg_right _ hsx.le; nlinarith
      _ ≤ _ := hsmall
  set r := rr x c with hr
  have hr_def : r = c * L / √x := rfl
  have hr0 : 0 < r := by rw [hr_def]; positivity
  have hr1 : r ≤ 1 / 1000 := by
    rw [hr_def, mul_div_assoc]
    calc c * (L / √x) ≤ 1 * (L / √x) := by gcongr
      _ ≤ _ := by linarith
  have hrlow : L / (2 * √x) ≤ r := by
    rw [hr_def, div_le_div_iff₀ (by positivity) hsx]
    have := mul_nonneg (by linarith : 0 ≤ 2 * c - 1) (mul_pos (by linarith : (0:ℝ) < L) hsx).le
    nlinarith
  -- 2πΔ ≥ ½·r/(1+r)
  have hlog := div_one_add_le_log hr0.le
  have htpd : r / (1 + r) / 2 ≤ tpd x c := by
    unfold tpd; rw [← hr]; linarith
  have hrr : r * (1 - r) ≤ r / (1 + r) := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_pos (mul_pos hr0 hr0) hr0
    nlinarith
  have htpd0 : 0 < tpd x c := lt_of_lt_of_le (by positivity) htpd
  -- √a ≥ √x
  have hsa : √x ≤ √(x * √(1 + r)) := by
    apply Real.sqrt_le_sqrt
    have : 1 ≤ √(1 + r) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    nlinarith
  refine ⟨by unfold Yq; rw [← hr]; positivity, ?_, ?_⟩
  · -- Y ≥ ½·r(1−r)·√x = cL/2 − cLr/2 ≥ cL/2 − 1/2000
    unfold Yq; rw [← hr]
    have hcL : r * √x = c * L := by rw [hr_def]; field_simp
    have hY1 : r * (1 - r) / 2 * √x ≤ tpd x c * √(x * √(1 + r)) := by
      apply mul_le_mul (by linarith) hsa hsx.le htpd0.le
    have hY2 : r * (1 - r) / 2 * √x = c * L / 2 - c * L * r / 2 := by
      have : r * (1 - r) / 2 * √x = (r * √x) * (1 - r) / 2 := by ring
      rw [this, hcL]; ring
    have hcLr : c * L * r ≤ 1 / 1000 := by
      have : c * L * r ≤ 1 * L * (L / √x) := by
        rw [hr_def, mul_div_assoc]
        apply mul_le_mul (by nlinarith) (mul_le_of_le_one_left (by positivity) hc2)
          (by positivity) (by positivity)
      have h' : 1 * L * (L / √x) = L ^ 2 / √x := by ring
      linarith
    linarith
  · -- log(1/2πΔ) ≤ log((401 / 100)·√x/L) = L/2 + log((401 / 100)/L) ≤ L/2 − 2
    unfold ell
    have ht0 : 0 ≤ L / √x := by positivity
    have hrlow' : L / √x / 2 ≤ r := by
      have : L / (2 * √x) = L / √x / 2 := by rw [div_div, mul_comm]
      linarith
    have hprod : L / √x / 2 * (999 / 1000) ≤ r * (1 - r) :=
      mul_le_mul hrlow' (by linarith) (by norm_num) hr0.le
    have hlow : L / √x / (401 / 100) ≤ tpd x c := by linarith
    have hLpos : 0 < L := by linarith
    have h1 : 1 / tpd x c ≤ (401 / 100) * √x / L := by
      have := one_div_le_one_div_of_le (by positivity) hlow
      have e : 1 / (L / √x / (401 / 100)) = (401 / 100) * √x / L := by field_simp
      linarith
    have h2 : log (1 / tpd x c) ≤ log ((401 / 100) * √x / L) :=
      Real.log_le_log (by positivity) h1
    have h3 : log ((401 / 100) * √x / L) = L / 2 + log ((401 / 100) / L) := by
      rw [show (401 / 100) * √x / L = √x * ((401 / 100) / L) by ring,
        Real.log_mul hsx.ne' (by positivity), Real.log_sqrt hx0.le]
    have h4 : log ((401 / 100) / L) ≤ -2 := by
      rw [Real.log_le_iff_le_exp (by positivity), Real.exp_neg, div_le_iff₀ hLpos]
      have := exp_two_lt
      rw [inv_mul_eq_div, le_div_iff₀ (exp_pos 2)]
      nlinarith
    linarith


end RhGaps
