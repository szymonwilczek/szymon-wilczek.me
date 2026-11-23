import RhGaps.Coeffs
import RhGaps.Defs
import RhGaps.PrimeIntervals

/-!
  section 3.1-section 3.6 of proof.org.

  Three kinds of assumptions:
  * `explicit_formula_core`: the Guinand–Weil explicit formula under RH plus the bounds of section 3.3 (zeros),
    section 3.4 (the Γ term), section 3.5(b)-(c) (prime powers, tails), summed into the constant `Esm` (Arb sweep, section 4);
    the right-hand side keeps the EXPLICIT sum over primes `Pplus + Pminus`;
  * `cert_*`: five numbers about the concrete function `F`/`F̂` (defined here from the exact
    coefficients), computed in Arb (`code/explicit_constant.py`, `norms`);
  * `montgomery_vaughan` (in `PrimeIntervals.lean`).

  Proved here: the left-hand side `2πf(i/2)(√a+1/√a) ≥ Y(F(0) − ε)`, the whole sum over
  primes of section 3.5(a) (upward and downward chains, the split τ ≤ 15 / τ > 15, the TV lemma),
  the values `F(0)`, `Σ|cⱼ|bⱼ`, the bounds for `log x/√x`, `2πΔ`, `η`, `ε₁`, and the arithmetic
  leading to `Y·J* ≤ log(1/2πΔ) + K̄`, from which `Main.lean` derives the contradiction.
-/

open Real MeasureTheory

namespace RhGaps

/-! ### The test function (exact coefficients from `Coeffs.lean`) -/

/-- The pairs `(bⱼ, cⱼ)`. -/
def pairs : List (ℚ × ℚ) := List.zip bL cL

/-- `F(y) = Σ cⱼ exp(−π bⱼ y²)`. -/
noncomputable def F (y : ℝ) : ℝ := (pairs.map fun p => (p.2 : ℝ) * exp (-π * p.1 * y ^ 2)).sum

/-- `F̂(t) = Σ cⱼ/√bⱼ · exp(−π t²/bⱼ)` (the Fourier transform of `F`). -/
noncomputable def Fhat (t : ℝ) : ℝ :=
  (pairs.map fun p => (p.2 : ℝ) / √(p.1 : ℝ) * exp (-π * t ^ 2 / p.1)).sum

/-- `F(0) = Σ cⱼ`. -/
def F0q : ℚ := (pairs.map (·.2)).sum
/-- `Σ |cⱼ| bⱼ`. -/
def sumcb : ℚ := (pairs.map fun p => |p.2| * p.1).sum
/-- `Σ cⱼ exp(bⱼ s)`; at `s = (2πΔ)²/(16π)` this is `2π f(i/2)/(2πΔ)`. -/
noncomputable def fhalf (s : ℝ) : ℝ := (pairs.map fun p => (p.2 : ℝ) * exp (p.1 * s)).sum

lemma pairs_b : ∀ p ∈ pairs, 0 < p.1 ∧ p.1 ≤ 20 := by unfold pairs bL cL; norm_num
lemma F0q_ge : (1280406781754427 / 10 ^ 15 : ℚ) ≤ F0q := by unfold F0q pairs bL cL; norm_num
lemma sumcb_le : sumcb ≤ 388953 := by unfold sumcb pairs bL cL; norm_num

lemma Fhat_continuous : Continuous Fhat := by
  unfold Fhat
  exact continuous_list_sum _ fun p _ => by fun_prop

lemma Fhat_neg (t : ℝ) : Fhat (-t) = Fhat t := by simp only [Fhat, neg_sq]

/-! ### Certificate constants (the Arb `norms` output, rounded up) -/

/-- `‖F‖₁ ≤ 0.999984860856146`. -/
noncomputable def L1bar : ℝ := 999984860856146 / 10 ^ 15
/-- `‖log⁺|y|·F‖₁ ≤ 0.0102305235484304`. -/
noncomputable def logFbar : ℝ := 102305235484304 / 10 ^ 16
/-- `∫₁^∞ (F̂)₊ ≤ 0.0131933850413233` (half of `T₊`). -/
noncomputable def TpHalf : ℝ := 131933850413233 / 10 ^ 16
/-- `∫₁₅^∞ |F̂| ≤ 5·10⁻¹⁸` (half of `T_M`). -/
noncomputable def TMhalf : ℝ := 5 / 10 ^ 18
/-- `Var(F̂; [1, ∞)) ≤ 0.161488554532486`. -/
noncomputable def TVbar : ℝ := 161488554532486 / 10 ^ 15
/-- `E_Z + E_Γ + PP_in + PP_out + E_far ≤ 0.0027019632` for all `x ≥ 4·10¹⁸` (§4). -/
noncomputable def Esm : ℝ := 27019632 / 10 ^ 10
/-- `η̄`: `|I_j|⁻¹ ≤ Y(1+η̄)` when `τ(x_j) ≤ 15`. -/
noncomputable def etab : ℝ := 85 / 10 ^ 9

/-! ### Arb certificates: EXTERNAL (axioms about a concrete function) -/

/-- Arb: `‖F‖₁`. -/
axiom cert_L1 : (∫ y, |F y|) ≤ L1bar
/-- Arb: `‖log⁺|y| F‖₁` (computed as `2∫₁^∞ (y−1)|F|`). -/
axiom cert_logF : (∫ y, max (log |y|) 0 * |F y|) ≤ logFbar
/-- Arb: `∫₁^t (F̂)₊ ≤ T₊/2` for every `t ≥ 1`. -/
axiom cert_Tplus : ∀ t : ℝ, 1 ≤ t → (∫ u in (1 : ℝ)..t, max (Fhat u) 0) ≤ TpHalf
/-- Arb: `∫₁₅^t |F̂| ≤ T_M/2` for every `t ≥ 15`. -/
axiom cert_TM : ∀ t : ℝ, 15 ≤ t → (∫ u in (15 : ℝ)..t, |Fhat u|) ≤ TMhalf
/-- Arb: `Var(F̂; [1,∞)) = ∫₁^∞ |F̂'| ≤ TV`. -/
axiom cert_TV : eVariationOn Fhat (Set.Ici 1) ≤ ENNReal.ofReal TVbar

/-! ### The analytic core -/

/-- `a = √(x x') = x√(1+r)`. -/
noncomputable def aa (x c : ℝ) : ℝ := x * √(1 + rr x c)
/-- `τ(y) = log(y/a)/(2πΔ)`. -/
noncomputable def tau (x c y : ℝ) : ℝ := log (y / aa x c) / tpd x c

/-- Primes with `x' < p ≤ ae` (the upward side of §3.5(a)). -/
noncomputable def Pplus (x c : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x * (1 + rr x c)⌋₊ ⌊aa x c * exp 1⌋₊).filter Nat.Prime,
    log p / √p * max (Fhat (tau x c p)) 0

/-- Primes with `a/e ≤ p < x` (the downward side of §3.5(a)). -/
noncomputable def Pminus (x c : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ico ⌈aa x c / exp 1⌉₊ ⌈x⌉₊).filter Nat.Prime,
    log p / √p * max (Fhat (tau x c p)) 0

/-- **EXTERNAL (axiom).** proof.org section 3.1 - section 3.5 without section 3.5(a): the Guinand–Weil
  explicit formula (MV Thm. 5.12) for `h(z) = ΔF(Δz)a^{iz}` under RH, `2πΔ = tpd`, after taking
  real parts and `F̂ ≤ (F̂)₊`:
    `2π f(i/2)(√a + 1/√a) ≤ Z + E_π + E_Γ + P`,
  where `2π f(i/2) = 2πΔ·Σ cⱼ e^{π bⱼ Δ²/4}`, `Z ≤ log(1/2πΔ)‖F‖₁ + ‖log⁺|y|F‖₁ + E_Z` (§3.3,
  Trudgian), `E_Γ` (section 3.4, the ψ lemmas), the powers `p^k` and `|log(n/a)| > 1` (section 3.5(b)-(c)); their sum
  is ≤ `Esm` for every `x ≥ 4·10¹⁸` (Arb sweep, section 4). What remains are the primes
  with `a/e ≤ p ≤ ae`; by assumption there are none in `[x, x']`. -/
axiom explicit_formula_core (hRH : RiemannHypothesis) (x c : ℝ) (hx : 4 * 10 ^ 18 ≤ x)
    (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 1)
    (hno : ¬ ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + c * √x * log x) :
    tpd x c * (√(aa x c) + 1 / √(aa x c)) * fhalf (tpd x c ^ 2 / (16 * π))
      ≤ ell x c * (∫ y, |F y|) + (∫ y, max (log |y|) 0 * |F y|) + Esm
        + Pplus x c + Pminus x c

/-! ### Numerical bounds in `x` -/

lemma log_x0_le : log (4 * 10 ^ 18) ≤ 42.9 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : exp 42.9 = exp 1 ^ 42 * exp 0.9 := by
    rw [Real.exp_one_pow, ← Real.exp_add]; norm_num
  have h2 := Real.quadratic_le_exp_of_nonneg (x := 0.9) (by norm_num)
  have h3 : (2.7182818283 : ℝ) ^ 42 ≤ exp 1 ^ 42 := by gcongr; exact e_gt.le
  rw [h1]
  calc (4 * 10 ^ 18 : ℝ) ≤ 2.7182818283 ^ 42 * (1 + 0.9 + 0.9 ^ 2 / 2) := by norm_num
    _ ≤ exp 1 ^ 42 * exp 0.9 := by gcongr

/-- `log x/√x ≤ 2.245·10⁻⁸` for `x ≥ 4·10¹⁸` (precisely `≈ 2.1416·10⁻⁸` at `x₀`). -/
lemma L_div_sqrt_le {x : ℝ} (hx : 4 * 10 ^ 18 ≤ x) : log x / √x ≤ 2245 / 10 ^ 11 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hq : 2 * 10 ^ 9 ≤ √x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
  set q := √x with hqdef
  have hq0 : 0 < q := by linarith
  have hlx : log x = 2 * log q := by rw [hqdef, Real.log_sqrt hx0.le]; ring
  have h1 : log q = log (2 * 10 ^ 9) + log (q / (2 * 10 ^ 9)) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have h2 : log (q / (2 * 10 ^ 9)) ≤ q / (2 * 10 ^ 9) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : log (2 * 10 ^ 9) = log (4 * 10 ^ 18) / 2 := by
    rw [show (4 * 10 ^ 18 : ℝ) = (2 * 10 ^ 9) ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h4 := log_x0_le
  rw [div_le_iff₀ hq0]
  linarith

/-- Basic facts about the parameters of §3 for `x ≥ 4·10¹⁸`, `c ∈ [½, 1]`. -/
lemma params {x c : ℝ} (hx : 4 * 10 ^ 18 ≤ x) (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 1) :
    0 < rr x c ∧ rr x c ≤ 2245 / 10 ^ 11 ∧ 0 < tpd x c ∧ tpd x c ≤ 11225 / 10 ^ 12
      ∧ x ≤ aa x c ∧ aa x c ≤ 2 * x ∧ 2 * 10 ^ 9 ≤ √(aa x c)
      ∧ tau x c (x * (1 + rr x c)) = 1 ∧ tau x c x = -1
      ∧ x * (1 + rr x c) = x + c * √x * log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hL := log_ge_42 hx
  have hLs := L_div_sqrt_le hx
  have hr0 : 0 < rr x c := by unfold rr; have : 0 < c := by linarith
                              positivity
  have hr1 : rr x c ≤ 2245 / 10 ^ 11 := by
    unfold rr
    rw [mul_div_assoc]
    calc c * (log x / √x) ≤ 1 * (log x / √x) := by gcongr
      _ ≤ _ := by linarith
  set r := rr x c with hr
  have hlog1 : log (1 + r) ≤ r := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + r); linarith
  have hlog0 : 0 < log (1 + r) := Real.log_pos (by linarith)
  have hT0 : 0 < tpd x c := by unfold tpd; rw [← hr]; linarith
  have hT1 : tpd x c ≤ 11225 / 10 ^ 12 := by unfold tpd; rw [← hr]; linarith
  have hs1 : 1 ≤ √(1 + r) := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hs2 : √(1 + r) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hs0 : 0 < √(1 + r) := by linarith
  have ha1 : x ≤ aa x c := by unfold aa; rw [← hr]; nlinarith
  have ha2 : aa x c ≤ 2 * x := by unfold aa; rw [← hr]; nlinarith
  have hsa : 2 * 10 ^ 9 ≤ √(aa x c) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hlogs : log √(1 + r) = tpd x c := by
    rw [Real.log_sqrt (by linarith)]; unfold tpd; rw [← hr]
  refine ⟨hr0, hr1, hT0, hT1, ha1, ha2, hsa, ?_, ?_, ?_⟩
  · unfold tau
    have e : x * (1 + r) / aa x c = √(1 + r) := by
      unfold aa; rw [← hr]
      rw [mul_div_mul_left _ _ hx0.ne', Real.div_sqrt]
    rw [e, hlogs, div_self hT0.ne']
  · unfold tau
    have e : x / aa x c = (√(1 + r))⁻¹ := by
      unfold aa; rw [← hr]; field_simp
    rw [e, Real.log_inv, hlogs, neg_div, div_self hT0.ne']
  · rw [hr]; unfold rr
    field_simp
    linear_combination (-(c * log x)) * Real.mul_self_sqrt hx0.le

/-! ### The left-hand side, §3.2 -/

lemma fhalf_list (l : List (ℚ × ℚ)) (hl : ∀ p ∈ l, 0 < p.1 ∧ p.1 ≤ 20) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ 1 / 40) :
    (((l.map (·.2)).sum : ℚ) : ℝ) - 2 * s * (((l.map fun p => |p.2| * p.1).sum : ℚ) : ℝ)
      ≤ (l.map fun p => (p.2 : ℝ) * exp (p.1 * s)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
    have ih' := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    obtain ⟨hb0, hb⟩ := hl p List.mem_cons_self
    have hb0' : (0 : ℝ) < p.1 := by exact_mod_cast hb0
    have hb' : (p.1 : ℝ) ≤ 20 := by exact_mod_cast hb
    have hbs0 : 0 ≤ (p.1 : ℝ) * s := by positivity
    have hbs1 : (p.1 : ℝ) * s ≤ 1 := by nlinarith
    have he1 := exp_sub_one_le_two_mul hbs0 hbs1
    have he0 : 1 ≤ exp ((p.1 : ℝ) * s) := Real.one_le_exp hbs0
    have hca : 0 ≤ (p.2 : ℝ) + |(p.2 : ℝ)| := by linarith [neg_abs_le (p.2 : ℝ)]
    have h1 : -(|(p.2 : ℝ)| * (exp (p.1 * s) - 1)) ≤ (p.2 : ℝ) * (exp (p.1 * s) - 1) := by
      nlinarith [mul_nonneg hca (by linarith : 0 ≤ exp ((p.1 : ℝ) * s) - 1)]
    have h2 : |(p.2 : ℝ)| * (exp (p.1 * s) - 1) ≤ |(p.2 : ℝ)| * (2 * (p.1 * s)) :=
      mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
    have key : (p.2 : ℝ) - 2 * s * (|(p.2 : ℝ)| * p.1) ≤ (p.2 : ℝ) * exp (p.1 * s) := by
      nlinarith
    linarith

lemma fhalf_ge {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 40) :
    (F0q : ℝ) - 2 * s * (sumcb : ℝ) ≤ fhalf s :=
  fhalf_list pairs pairs_b hs0 hs

/-! ### Chains of intervals `(u, u+√u]` -/

/-- `x_k = f^k(s)`, `f(y) = y + √y`. -/
noncomputable def upc (s : ℝ) (k : ℕ) : ℝ := (fun y => y + √y)^[k] s

lemma upc_succ (s : ℝ) (k : ℕ) : upc s (k + 1) = upc s k + √(upc s k) :=
  Function.iterate_succ_apply' _ _ _

lemma upc_mono (s : ℝ) : Monotone (upc s) :=
  monotone_nat_of_le_succ fun k => by rw [upc_succ]; linarith [Real.sqrt_nonneg (upc s k)]

lemma upc_ge {s : ℝ} (hs : 1 ≤ s) (k : ℕ) : s + k ≤ upc s k := by
  induction k with
  | zero => simp [upc]
  | succ k ih =>
    rw [upc_succ]; push_cast
    have : 1 ≤ √(upc s k) := Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    linarith

/-- The inverse of `f`: `dn(w) + √dn(w) = w`. -/
noncomputable def dn (w : ℝ) : ℝ := ((√(4 * w + 1) - 1) / 2) ^ 2

lemma dn_nonneg (w : ℝ) : 0 ≤ dn w := sq_nonneg _

lemma dn_add {w : ℝ} (hw : 0 ≤ w) : dn w + √(dn w) = w := by
  have hq : 1 ≤ √(4 * w + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hq2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 * w + 1)
  unfold dn
  rw [Real.sqrt_sq (by linarith)]
  nlinarith

lemma dn_iter_nonneg {w : ℝ} (hw : 0 ≤ w) : ∀ n, 0 ≤ dn^[n] w
  | 0 => hw
  | n + 1 => by rw [Function.iterate_succ_apply']; exact dn_nonneg _

lemma upc_dn {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : upc (dn^[n] y) n = y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold upc at ih ⊢
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
      dn_add (dn_iter_nonneg hy n), ih]

/-! ### Integrals and variation of `F̂` -/

lemma Gp_cont : Continuous fun u => max (Fhat u) 0 := Fhat_continuous.max continuous_const

lemma sum_int (t : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (∫ u in (t k)..(t (k + 1)), max (Fhat u) 0)
      = ∫ u in (t 0)..(t n), max (Fhat u) 0 :=
  intervalIntegral.sum_integral_adjacent_intervals fun _ _ => Gp_cont.intervalIntegrable _ _

lemma sum_int_tail (t : ℕ → ℝ) (ht : Monotone t) (M : ℝ) (n : ℕ) :
    ∑ k ∈ (Finset.range n).filter (fun k => M < t k), (∫ u in (t k)..(t (k + 1)), max (Fhat u) 0)
      ≤ ∫ u in M..(max M (t n)), max (Fhat u) 0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg (le_max_left _ _) fun u _ => le_max_right _ _
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.sum_insert (by simp)]
      have e1 : max M (t n) = t n := max_eq_right h.le
      have e2 : max M (t (n + 1)) = t (n + 1) := max_eq_right (h.le.trans (ht n.le_succ))
      rw [e1] at ih
      have hadd := intervalIntegral.integral_add_adjacent_intervals (a := M) (b := t n)
        (c := t (n + 1)) (Gp_cont.intervalIntegrable (μ := volume) _ _)
        (Gp_cont.intervalIntegrable (μ := volume) _ _)
      rw [e2]
      linarith
    · refine ih.trans ?_
      apply intervalIntegral.integral_mono_interval le_rfl (le_max_left _ _)
        (max_le_max le_rfl (ht n.le_succ))
      · exact Filter.Eventually.of_forall fun u => le_max_right _ _
      · exact Gp_cont.intervalIntegrable _ _

lemma TVbar_nonneg : 0 ≤ TVbar := by unfold TVbar; norm_num

lemma var_le {s t : ℝ} (hs : 1 ≤ s) :
    eVariationOn Fhat (Set.Icc s t) ≠ ⊤ ∧ (eVariationOn Fhat (Set.Icc s t)).toReal ≤ TVbar := by
  have hsub : Set.Icc s t ⊆ Set.Ici 1 := fun u hu => Set.mem_Ici.mpr (le_trans hs hu.1)
  have hm : eVariationOn Fhat (Set.Icc s t) ≤ ENNReal.ofReal TVbar :=
    (eVariationOn.mono Fhat hsub).trans cert_TV
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm, ?_⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rwa [ENNReal.toReal_ofReal TVbar_nonneg] at this

lemma var_neg_le {s t : ℝ} (ht : t ≤ -1) :
    eVariationOn Fhat (Set.Icc s t) ≠ ⊤ ∧ (eVariationOn Fhat (Set.Icc s t)).toReal ≤ TVbar := by
  have e : eVariationOn Fhat (Set.Icc s t) = eVariationOn Fhat (Set.Icc (-t) (-s)) := by
    have hf : Fhat = Fhat ∘ Neg.neg := funext fun u => (Fhat_neg u).symm
    conv_lhs => rw [hf]
    rw [eVariationOn.comp_eq_of_antitoneOn Fhat Neg.neg (fun _ _ _ _ h => neg_le_neg h),
      Set.image_neg_eq_neg, Set.neg_Icc]
  rw [e]; exact var_le (by linarith)

lemma int_neg {s : ℝ} :
    ∫ u in s..(-1), max (Fhat u) 0 = ∫ u in (1 : ℝ)..(-s), max (Fhat u) 0 := by
  have := intervalIntegral.integral_comp_neg (a := s) (b := -1) (fun u => max (Fhat u) 0)
  simp only [Fhat_neg, neg_neg] at this
  exact this

/-! ### section 3.5(a): both sides -/

lemma inv_len {a T u : ℝ} (ha : 0 < a) (hT : 0 < T) (hu : 0 < u) :
    1 / (log ((u + √u) / a) / T - log (u / a) / T) ≤ T * (√u + 1) := by
  have h := inv_length_le (a := a) (Δ := T / (2 * π)) (u := u) ha (by positivity) hu
  have e : 2 * π * (T / (2 * π)) = T := by field_simp
  rwa [e] at h

lemma tau_mono {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    StrictMonoOn (fun y => log (y / a) / T) (Set.Ici (exp 2)) := by
  intro u hu v hv huv
  have hu0 : 0 < u := (exp_pos 2).trans_le hu
  exact div_lt_div_of_pos_right
    (Real.log_lt_log (div_pos hu0 ha) (div_lt_div_of_pos_right huv ha)) hT

lemma term_nonneg (p : ℕ) (g : ℝ) : 0 ≤ log p / √p * max g 0 := by
  rcases Nat.eq_zero_or_pos p with h | h
  · subst h; simp
  · exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (Real.sqrt_nonneg _))
      (le_max_right _ _)

/-- **Upward side**: `Σ_{x' < p ≤ ae} ≤ 4(Y(1+η̄)·T₊/2 + 2Y·T_M/2 + TV)`. -/
theorem upward_side {a T xp : ℝ} (ha : 0 < a) (hT : 0 < T) (hT1 : T ≤ 11225 / 10 ^ 12)
    (hsa : 2 * 10 ^ 9 ≤ √a) (hxp : exp 2 ≤ xp) (hτ1 : log (xp / a) / T = 1) :
    ∑ p ∈ (Finset.Ioc ⌊xp⌋₊ ⌊a * exp 1⌋₊).filter Nat.Prime,
        log p / √p * max (Fhat (log (p / a) / T)) 0
      ≤ 4 * (T * √a * (1 + etab) * TpHalf + 2 * (T * √a) * TMhalf + TVbar) := by
  classical
  set τ : ℝ → ℝ := fun y => log (y / a) / T with hτdef
  have hτ : StrictMonoOn τ (Set.Ici (exp 2)) := tau_mono ha hT
  have he2 : (1 : ℝ) ≤ exp 2 := Real.one_le_exp (by norm_num)
  have hex : ∃ n, a * exp 1 ≤ upc xp n := by
    refine ⟨⌈a * exp 1⌉₊, ?_⟩
    have := upc_ge (by linarith : 1 ≤ xp) ⌈a * exp 1⌉₊
    have := Nat.le_ceil (a * exp 1)
    linarith
  set n := Nat.find hex with hn_def
  have hn : a * exp 1 ≤ upc xp n := Nat.find_spec hex
  have hlt : ∀ k < n, upc xp k < a * exp 1 := fun k hk => lt_of_not_ge (Nat.find_min hex hk)
  set x := upc xp with hxdef
  have hx0 : x 0 = xp := rfl
  have hxe : ∀ k, exp 2 ≤ x k := fun k => hxp.trans (upc_mono xp (Nat.zero_le k))
  have hxpos : ∀ k, 0 < x k := fun k => (exp_pos 2).trans_le (hxe k)
  set Y := T * √a with hY
  have hsa0 : 0 < √a := by linarith
  have hY0 : 0 < Y := mul_pos hT hsa0
  have hTY : T ≤ Y * (5 / 10 ^ 10) := by
    rw [hY]; nlinarith
  set B : ℕ → ℝ := fun k => Y * (1 + etab) + if 15 < τ (x k) then 2 * Y else 0 with hBdef
  have hB : ∀ k < n, 1 / (τ (x (k + 1)) - τ (x k)) ≤ B k := by
    intro k hk
    have h1 := inv_len ha hT (hxpos k)
    simp only [hτdef]
    rw [show x (k + 1) = x k + √(x k) from upc_succ xp k]
    refine h1.trans ?_
    simp only [hBdef]
    split_ifs with h15
    · -- τ > 15: `x_k < ae`, so `√x_k ≤ √a·√e ≤ 2√a`
      have hxa : √(x k) ≤ 2 * √a := by
        have h := Real.sqrt_le_sqrt (hlt k hk).le
        rw [Real.sqrt_mul ha.le] at h
        have he : √(exp 1) ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; linarith [e_lt]
        nlinarith
      have : etab ≥ 0 := by unfold etab; norm_num
      nlinarith
    · -- τ ≤ 15: `√x_k ≤ √a·e^{7.5T} ≤ √a(1 + 7.5T + (7.5T)²)`
      rw [not_lt] at h15
      have hlog : log (x k / a) ≤ 15 * T := by
        have := (div_le_iff₀ hT).mp h15; linarith
      have hxk : x k ≤ a * exp (15 * T) := by
        have := (Real.log_le_iff_le_exp (div_pos (hxpos k) ha)).mp hlog
        rwa [div_le_iff₀ ha, mul_comm] at this
      have hsq : √(x k) ≤ √a * exp (15 / 2 * T) := by
        have h := Real.sqrt_le_sqrt hxk
        rw [Real.sqrt_mul ha.le] at h
        have : √(exp (15 * T)) = exp (15 / 2 * T) := by
          rw [show 15 * T = 15 / 2 * T + 15 / 2 * T by ring, Real.exp_add,
            Real.sqrt_mul_self (exp_pos _).le]
        rwa [this] at h
      have hs : |15 / 2 * T| ≤ 1 := by rw [abs_of_pos (by positivity)]; linarith
      have hexp := Real.abs_exp_sub_one_sub_id_le hs
      have hexp' : exp (15 / 2 * T) ≤ 1 + 15 / 2 * T + (15 / 2 * T) ^ 2 := by
        have := le_abs_self (exp (15 / 2 * T) - 1 - 15 / 2 * T); linarith
      have hTT : 15 / 2 * T + (15 / 2 * T) ^ 2 ≤ 8420 / 10 ^ 11 := by nlinarith
      have : Y * (1 + etab) + 0 = Y + Y * etab := by ring
      rw [this]
      unfold etab
      have h2 : T * (√(x k) + 1) ≤ Y * (1 + 15 / 2 * T + (15 / 2 * T) ^ 2) + T := by
        rw [hY]; nlinarith
      nlinarith
  -- lemma (TV) + MV
  have hτ0 : τ (x 0) = 1 := hτ1
  have hvar := var_le (s := τ (x 0)) (t := τ (x n)) (by rw [hτ0])
  have hmain := primes_upward x (upc_succ xp) (by rw [hx0]; exact hxp) τ hτ Fhat Fhat_continuous
    n hvar.1 B hB
  -- the sum over the set in the statement ⊆ the sum from `primes_upward`
  have hsub : (Finset.Ioc ⌊xp⌋₊ ⌊a * exp 1⌋₊).filter Nat.Prime
      ⊆ (Finset.Ioc ⌊x 0⌋₊ ⌊x n⌋₊).filter Nat.Prime := by
    apply Finset.filter_subset_filter
    rw [hx0]
    exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_le_floor hn)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => term_nonneg p (Fhat (τ p)))
  -- Σ B_k ∫ = Y(1+η̄) Σ∫ + 2Y Σ_{τ>15} ∫
  have ht_mono : Monotone fun k => τ (x k) := fun i j hij =>
    hτ.monotoneOn (Set.mem_Ici.mpr (hxe i)) (Set.mem_Ici.mpr (hxe j)) (upc_mono xp hij)
  have hsplit : ∑ k ∈ Finset.range n, B k * (∫ u in (τ (x k))..(τ (x (k + 1))), max (Fhat u) 0)
      = Y * (1 + etab) * (∫ u in (τ (x 0))..(τ (x n)), max (Fhat u) 0)
        + 2 * Y * ∑ k ∈ (Finset.range n).filter (fun k => 15 < τ (x k)),
            (∫ u in (τ (x k))..(τ (x (k + 1))), max (Fhat u) 0) := by
    simp only [hBdef, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_int (fun k => τ (x k)) n]
  have hI1 : (∫ u in (τ (x 0))..(τ (x n)), max (Fhat u) 0) ≤ TpHalf := by
    rw [hτ0]
    exact cert_Tplus _ (hτ0 ▸ ht_mono (Nat.zero_le n))
  have hI2 : ∑ k ∈ (Finset.range n).filter (fun k => 15 < τ (x k)),
      (∫ u in (τ (x k))..(τ (x (k + 1))), max (Fhat u) 0) ≤ TMhalf := by
    refine (sum_int_tail (fun k => τ (x k)) ht_mono 15 n).trans ?_
    refine le_trans ?_ (cert_TM (max 15 (τ (x n))) (le_max_left _ _))
    apply intervalIntegral.integral_mono_on (le_max_left _ _)
      (Gp_cont.intervalIntegrable _ _) (Fhat_continuous.abs.intervalIntegrable _ _)
    exact fun u _ => max_le (le_abs_self _) (abs_nonneg _)
  have hY1 : 0 ≤ Y * (1 + etab) := by unfold etab; positivity
  calc _ ≤ _ := hle
    _ ≤ _ := hmain
    _ ≤ _ := by
        rw [hsplit]
        have := mul_le_mul_of_nonneg_left hI1 hY1
        have := mul_le_mul_of_nonneg_left hI2 (by positivity : (0 : ℝ) ≤ 2 * Y)
        linarith [hvar.2]

/-- **Downward side**: `Σ_{a/e ≤ p < x} ≤ 4(Y(1+η̄)·T₊/2 + TV)`. -/
theorem downward_side {a T x : ℝ} (ha : 0 < a) (hT : 0 < T) (hsa : 2 * 10 ^ 9 ≤ √a)
    (hxa : x ≤ a) (hax : a / exp 1 ≤ x) (hτ1 : log (x / a) / T = -1) :
    ∑ p ∈ (Finset.Ico ⌈a / exp 1⌉₊ ⌈x⌉₊).filter Nat.Prime,
        log p / √p * max (Fhat (log (p / a) / T)) 0
      ≤ 4 * (T * √a * (1 + etab) * TpHalf + TVbar) := by
  classical
  set τ : ℝ → ℝ := fun y => log (y / a) / T with hτdef
  have hτ : StrictMonoOn τ (Set.Ici (exp 2)) := tau_mono ha hT
  have hsa0 : 0 < √a := by linarith
  have ha4 : 4 * 10 ^ 18 ≤ a := by
    have := Real.sq_sqrt ha.le; nlinarith
  have hae : 100 ≤ a / exp 1 := by
    rw [le_div_iff₀ (exp_pos 1)]; linarith [e_lt]
  have hx0 : 0 ≤ x := by linarith
  -- n: the first downward step below a/e
  have hex : ∃ n, dn^[n] x < a / exp 1 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hdec : ∀ n : ℕ, dn^[n] x ≤ x - n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h1 := dn_add (dn_iter_nonneg hx0 n)
        have h2 := hcon (n + 1)
        rw [Function.iterate_succ_apply'] at h2
        have : 1 ≤ √(dn (dn^[n] x)) := Real.one_le_sqrt.mpr (by linarith)
        push_cast; linarith
    have h1 := hdec (⌈x⌉₊ + 1)
    have h2 := hcon (⌈x⌉₊ + 1)
    have h3 := Nat.le_ceil x
    push_cast at h1
    linarith
  set n := Nat.find hex with hn_def
  have hn : dn^[n] x < a / exp 1 := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    have := hn; rw [h0] at this; simp at this; linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hw : a / exp 1 ≤ dn^[m] x := le_of_not_gt (Nat.find_min hex (by omega))
  set s := dn^[n] x with hsdef
  have hs_eq : s + √s = dn^[m] x := by
    rw [hsdef, hm, Function.iterate_succ_apply']
    exact dn_add (dn_iter_nonneg hx0 m)
  have hs0 : 0 ≤ s := dn_iter_nonneg hx0 n
  have hs2 : exp 2 ≤ s := by
    have h1 : √s ≤ (s + 1) / 2 := by
      nlinarith [Real.sq_sqrt hs0, sq_nonneg (√s - 1)]
    linarith [exp_two_lt]
  -- the upward chain from s ends exactly at x
  set xc := upc s with hxcdef
  have hxn : xc n = x := upc_dn hx0 n
  have hxe : ∀ k, exp 2 ≤ xc k := fun k => hs2.trans (upc_mono s (Nat.zero_le k))
  have hxpos : ∀ k, 0 < xc k := fun k => (exp_pos 2).trans_le (hxe k)
  set Y := T * √a with hY
  have hY0 : 0 < Y := mul_pos hT hsa0
  have hTY : T ≤ Y * (5 / 10 ^ 10) := by rw [hY]; nlinarith
  have hB : ∀ k < n, 1 / (τ (xc (k + 1)) - τ (xc k)) ≤ Y * (1 + etab) := by
    intro k hk
    have h1 := inv_len ha hT (hxpos k)
    simp only [hτdef]
    rw [show xc (k + 1) = xc k + √(xc k) from upc_succ s k]
    refine h1.trans ?_
    have hxk : xc k ≤ a := calc
      xc k ≤ xc n := upc_mono s hk.le
      _ = x := hxn
      _ ≤ a := hxa
    have : √(xc k) ≤ √a := Real.sqrt_le_sqrt hxk
    unfold etab
    rw [hY] at hTY ⊢
    nlinarith
  have hτn : τ (xc n) = -1 := by rw [hxn]; exact hτ1
  have hτs : τ (xc 0) ≤ -1 := by
    rw [← hτn]
    exact hτ.monotoneOn (Set.mem_Ici.mpr (hxe 0)) (Set.mem_Ici.mpr (hxe n))
      (upc_mono s (Nat.zero_le n))
  have hvar := var_neg_le (s := τ (xc 0)) (le_of_eq hτn)
  have hmain := primes_upward xc (upc_succ s) hs2 τ hτ Fhat Fhat_continuous n hvar.1
    (fun _ => Y * (1 + etab)) hB
  have hsub : (Finset.Ico ⌈a / exp 1⌉₊ ⌈x⌉₊).filter Nat.Prime
      ⊆ (Finset.Ioc ⌊xc 0⌋₊ ⌊xc n⌋₊).filter Nat.Prime := by
    apply Finset.filter_subset_filter
    intro p hp
    rw [Finset.mem_Ico] at hp
    rw [Finset.mem_Ioc, hxn]
    have hp1 : a / exp 1 ≤ p := Nat.ceil_le.mp hp.1
    have hp2 : (p : ℝ) < x := Nat.lt_ceil.mp hp.2
    refine ⟨(Nat.floor_lt hs0).mpr ?_, Nat.le_floor hp2.le⟩
    show s < p
    linarith
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => term_nonneg p (Fhat (τ p)))
  have hI : (∫ u in (τ (xc 0))..(τ (xc n)), max (Fhat u) 0) ≤ TpHalf := by
    rw [hτn, int_neg]
    exact cert_Tplus _ (by linarith)
  have hY1 : 0 ≤ Y * (1 + etab) := by unfold etab; positivity
  calc _ ≤ _ := hle
    _ ≤ _ := hmain
    _ ≤ _ := by
        rw [← Finset.mul_sum, sum_int (fun k => τ (xc k)) n]
        have := mul_le_mul_of_nonneg_left hI hY1
        linarith [hvar.2]

/-! ### section 3.6: assembly; what used to be an axiom is now a theorem -/

/-- `Y·J* ≤ log(1/2πΔ) + K̄` if `[x, x + c√x log x]` contains no prime. -/
theorem explicit_formula_bound (hRH : RiemannHypothesis) (x c : ℝ) (hx : 4 * 10 ^ 18 ≤ x)
    (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 1)
    (hno : ¬ ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + c * √x * log x) :
    Yq x c * Jstar ≤ ell x c + Kbar := by
  have core := explicit_formula_core hRH x c hx hc1 hc2 hno
  obtain ⟨hr0, hr1, hT0, hT1, ha1, ha2, hsa, hτp, hτm, hxp⟩ := params hx hc1 hc2
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  set T := tpd x c with hT
  set a := aa x c with haa
  have ha0 : 0 < a := by linarith
  have hY : Yq x c = T * √a := rfl
  -- section 3.5(a)
  have hup : Pplus x c ≤ 4 * (T * √a * (1 + etab) * TpHalf + 2 * (T * √a) * TMhalf + TVbar) := by
    unfold Pplus
    have : x ≤ x * (1 + rr x c) := by nlinarith
    exact upward_side ha0 hT0 hT1 hsa (by linarith [exp_two_lt]) hτp
  have hdn : Pminus x c ≤ 4 * (T * √a * (1 + etab) * TpHalf + TVbar) := by
    unfold Pminus
    refine downward_side ha0 hT0 hsa ha1 ?_ hτm
    have := e_gt
    have : a ≤ x * exp 1 := by nlinarith
    rw [div_le_iff₀ (exp_pos 1)]; linarith
  -- section 3.2: the left-hand side
  set s := T ^ 2 / (16 * π) with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 / 40 := by
    rw [hs, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have hf := fhalf_ge hs0 hs1
  have hF0 := (Rat.cast_le (K := ℝ)).mpr F0q_ge
  push_cast at hF0
  have hscb : (sumcb : ℝ) ≤ 388953 := by exact_mod_cast sumcb_le
  have hscb0 : (0 : ℝ) ≤ sumcb := by
    have : (0 : ℚ) ≤ sumcb := by unfold sumcb pairs bL cL; norm_num
    exact_mod_cast this
  have heps : 2 * s * sumcb ≤ 21 / 10 ^ 13 := by
    have h2s : 2 * s ≤ T ^ 2 / 24 := by
      rw [hs]
      have := Real.pi_gt_three
      rw [show 2 * (T ^ 2 / (16 * π)) = T ^ 2 / (8 * π) by ring]
      exact div_le_div_of_nonneg_left (sq_nonneg T) (by norm_num) (by linarith)
    have hT2 : T ^ 2 ≤ (11225 / 10 ^ 12) ^ 2 := by gcongr
    calc 2 * s * sumcb ≤ T ^ 2 / 24 * 388953 :=
          mul_le_mul h2s hscb hscb0 (by positivity)
      _ ≤ (11225 / 10 ^ 12) ^ 2 / 24 * 388953 := by gcongr
      _ ≤ 21 / 10 ^ 13 := by norm_num
  have hfpos : 0 ≤ fhalf s := by linarith
  have hsa0 : 0 < √a := by linarith
  have hLS : T * √a * (1280406781754427 / 10 ^ 15 - 21 / 10 ^ 13)
      ≤ T * (√a + 1 / √a) * fhalf s := by
    have h1 : T * √a * (1280406781754427 / 10 ^ 15 - 21 / 10 ^ 13) ≤ T * √a * fhalf s :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 0 ≤ T * (1 / √a) * fhalf s := by positivity
    nlinarith
  -- `log(1/2πΔ) ≥ 0`, `‖F‖₁ ≤ L̄₁`
  have hell0 : 0 ≤ ell x c := by
    unfold ell
    apply Real.log_nonneg
    rw [← hT, le_div_iff₀ hT0]; linarith
  have hL1 := mul_le_mul_of_nonneg_left cert_L1 hell0
  have hlg := cert_logF
  -- linear in `Y = T√a` and `ell`
  rw [hY]
  have hY0 : 0 ≤ T * √a := by positivity
  unfold Jstar Kbar
  unfold L1bar at hL1
  unfold logFbar at hlg
  unfold etab TpHalf TMhalf TVbar at hup
  unfold etab TpHalf TVbar at hdn
  unfold Esm at core
  nlinarith

end RhGaps
