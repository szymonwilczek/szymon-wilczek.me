import RhGaps.Variation

/-!
  section 3.5(a) of proof.org, the NEW element compared with CMS: the sum over primes,
  covered by intervals (u, u+√u], Montgomery–Vaughan on each, then the (TV) lemma.
  The only axiom: (MV).
-/

open Real MeasureTheory

namespace RhGaps

/-- **(MV)** Montgomery–Vaughan 1973, Thm. 2: `π(u+y) − π(u) < 2y/log y` for `u, y > 1`.
  EXTERNAL (axiom). -/
axiom montgomery_vaughan (u y : ℝ) (hu : 1 < u) (hy : 1 < y) :
    (((Finset.Ioc ⌊u⌋₊ ⌊u + y⌋₊).filter Nat.Prime).card : ℝ) < 2 * y / log y

/-- Primes in `(u, u+√u]`. -/
noncomputable def primesIn (u : ℝ) : Finset ℕ := (Finset.Ioc ⌊u⌋₊ ⌊u + √u⌋₊).filter Nat.Prime

lemma mem_primesIn {u : ℝ} (hu : 0 ≤ u) {p : ℕ} (hp : p ∈ primesIn u) :
    u < p ∧ (p : ℝ) ≤ u + √u := by
  simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨h1, h2⟩, -⟩ := hp
  exact ⟨(Nat.floor_lt hu).mp h1, (Nat.le_floor_iff (by positivity)).mp h2⟩

/-- The weight `log p/√p` decreases for `p ≥ e²`. -/
lemma weight_le {u p : ℝ} (hu : exp 2 ≤ u) (hp : u ≤ p) : log p / √p ≤ log u / √u := by
  have hu0 : 0 < u := lt_of_lt_of_le (exp_pos 2) hu
  have hp0 : 0 < p := lt_of_lt_of_le hu0 hp
  have he : exp 1 ≤ √u := by
    rw [show exp 1 = √(exp 2) by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, Real.sqrt_mul_self (exp_pos 1).le]]
    exact Real.sqrt_le_sqrt hu
  have hpu : √u ≤ √p := Real.sqrt_le_sqrt hp
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
    (Set.mem_Ici.mpr (he.trans hpu)) hpu
  simp only at h
  have ep : log p / √p = 2 * (log √p / √p) := by rw [Real.log_sqrt hp0.le]; ring
  have eu : log u / √u = 2 * (log √u / √u) := by rw [Real.log_sqrt hu0.le]; ring
  rw [ep, eu]; linarith

/-- One interval: `Σ_{p∈(u,u+√u]} (log p/√p)·g(p) ≤ 4·M`, when `0 ≤ g ≤ M`. -/
theorem one_interval {u : ℝ} (hu : exp 2 ≤ u) (g : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg0 : ∀ p ∈ primesIn u, 0 ≤ g p) (hg : ∀ p ∈ primesIn u, g p ≤ M) :
    ∑ p ∈ primesIn u, log p / √p * g p ≤ 4 * M := by
  have hu0 : 0 < u := lt_of_lt_of_le (exp_pos 2) hu
  have he2 : (1 : ℝ) < exp 2 := by
    have := Real.add_one_lt_exp (x := 2) (by norm_num); linarith
  have hu1 : 1 < u := lt_of_lt_of_le he2 hu
  have hsu : 0 < √u := Real.sqrt_pos.mpr hu0
  have hsu1 : 1 < √u := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hu1
  have hlog : 0 < log u := Real.log_pos hu1
  have hw0 : 0 ≤ log u / √u := (div_pos hlog hsu).le
  have term : ∀ p ∈ primesIn u, log p / √p * g p ≤ log u / √u * M := by
    intro p hp
    have hpu := (mem_primesIn hu0.le hp).1
    have hp0 : (0 : ℝ) < p := hu0.trans hpu
    have hwp : 0 ≤ log p / √p :=
      div_nonneg (Real.log_nonneg (hu1.le.trans hpu.le)) (Real.sqrt_nonneg _)
    exact mul_le_mul (weight_le hu hpu.le) (hg p hp) (hg0 p hp) hw0
  have hcard := montgomery_vaughan u √u hu1 hsu1
  have hls : log √u = log u / 2 := by rw [Real.log_sqrt hu0.le]
  rw [hls] at hcard
  calc ∑ p ∈ primesIn u, log p / √p * g p
      ≤ ∑ _p ∈ primesIn u, log u / √u * M := Finset.sum_le_sum term
    _ = ((primesIn u).card : ℝ) * (log u / √u * M) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * √u / (log u / 2)) * (log u / √u * M) := by
        apply mul_le_mul_of_nonneg_right hcard.le (mul_nonneg hw0 hM)
    _ = 4 * M := by field_simp; ring

/-- The sum over adjacent intervals `(⌊x_j⌋, ⌊x_{j+1}⌋]` = the sum over `(⌊x_0⌋, ⌊x_n⌋]`. -/
lemma sum_chain (f : ℕ → ℝ) (x : ℕ → ℝ) (hx : Monotone x) (_hx0 : 0 ≤ x 0) (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ p ∈ Finset.Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, f p
      = ∑ p ∈ Finset.Ioc ⌊x 0⌋₊ ⌊x n⌋₊, f p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact Finset.sum_Ioc_consecutive f (Nat.floor_le_floor (hx (Nat.zero_le n)))
      (Nat.floor_le_floor (hx (Nat.le_succ n)))

/-- **section 3.5(a), upward side**, fully formalised (with the MV axiom).
  Chain `x_{j+1} = x_j + √x_j`, `x_0 ≥ e²`; τ strictly increasing on `[e², ∞)`; `B_j ≥ |I_j|⁻¹`, where
  `I_j = [τ(x_j), τ(x_{j+1})]`. Then
    `Σ_{p∈(x_0,x_n]} (log p/√p)·Ĥ(τ p)₊ ≤ 4·Σ_j B_j ∫_{I_j} Ĥ₊ + 4·Var(Ĥ; [τ x_0, τ x_n])`. -/
theorem primes_upward (x : ℕ → ℝ) (hstep : ∀ j, x (j + 1) = x j + √(x j))
    (hx0 : exp 2 ≤ x 0) (τ : ℝ → ℝ) (hτ : StrictMonoOn τ (Set.Ici (exp 2)))
    (H : ℝ → ℝ) (hH : Continuous H) (n : ℕ)
    (hvar : eVariationOn H (Set.Icc (τ (x 0)) (τ (x n))) ≠ ⊤)
    (B : ℕ → ℝ) (hB : ∀ j < n, 1 / (τ (x (j + 1)) - τ (x j)) ≤ B j) :
    ∑ p ∈ (Finset.Ioc ⌊x 0⌋₊ ⌊x n⌋₊).filter Nat.Prime, log p / √p * max (H (τ p)) 0
      ≤ 4 * ((∑ j ∈ Finset.range n, B j * (∫ u in (τ (x j))..(τ (x (j + 1))), max (H u) 0))
        + (eVariationOn H (Set.Icc (τ (x 0)) (τ (x n)))).toReal) := by
  have he2 : (0 : ℝ) < exp 2 := exp_pos 2
  have hmono : Monotone x := monotone_nat_of_le_succ fun j => by
    rw [hstep j]; linarith [Real.sqrt_nonneg (x j)]
  have hxe : ∀ j, exp 2 ≤ x j := fun j => hx0.trans (hmono (Nat.zero_le j))
  have hxpos : ∀ j, 0 < x j := fun j => he2.trans_le (hxe j)
  have hxs : StrictMono x := strictMono_nat_of_lt_succ fun j => by
    rw [hstep j]; linarith [Real.sqrt_pos.mpr (hxpos j)]
  set t : ℕ → ℝ := fun j => τ (x j) with htdef
  have ht : StrictMono t := fun i j hij => hτ (Set.mem_Ici.mpr (hxe i)) (Set.mem_Ici.mpr (hxe j)) (hxs hij)
  -- G = Ĥ₊ attains its maximum on each I_j
  set G : ℝ → ℝ := fun u => max (H u) 0 with hG
  have hGc : Continuous G := hH.max continuous_const
  have hmax : ∀ j, ∃ s ∈ Set.Icc (t j) (t (j + 1)), ∀ v ∈ Set.Icc (t j) (t (j + 1)), G v ≤ G s :=
    fun j => by
      obtain ⟨s, hs, h⟩ := isCompact_Icc.exists_isMaxOn
        (Set.nonempty_Icc.mpr (ht (Nat.lt_succ_self j)).le) hGc.continuousOn
      exact ⟨s, hs, fun v hv => h hv⟩
  choose s hs hsmax using hmax
  -- (1) split the sum into intervals
  have hsplit := sum_chain (fun p => if p.Prime then log p / √p * G (τ p) else 0) x hmono
    (hxpos 0).le n
  simp only [← Finset.sum_filter] at hsplit
  rw [← hsplit]
  -- (2) each interval ≤ 4·G(s_j)
  have hint : ∀ j ∈ Finset.range n,
      ∑ p ∈ (Finset.Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊).filter Nat.Prime, log p / √p * G (τ p)
        ≤ 4 * G (s j) := by
    intro j _
    have e : (Finset.Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊).filter Nat.Prime = primesIn (x j) := by
      rw [primesIn, hstep j]
    rw [e]
    apply one_interval (hxe j) (fun p => G (τ p)) (G (s j)) (le_max_right _ _)
      (fun p _ => le_max_right _ _)
    intro p hp
    obtain ⟨h1, h2⟩ := mem_primesIn (hxpos j).le hp
    apply hsmax j
    rw [← hstep j] at h2
    have hp2 : exp 2 ≤ (p : ℝ) := (hxe j).trans h1.le
    exact ⟨hτ.monotoneOn (Set.mem_Ici.mpr (hxe j)) (Set.mem_Ici.mpr hp2) h1.le,
      hτ.monotoneOn (Set.mem_Ici.mpr hp2) (Set.mem_Ici.mpr (hxe (j + 1))) h2⟩
  -- (3) lemma (TV)
  have htv := tv_covering H hH t ht n hvar B hB s hs
  calc _ ≤ ∑ j ∈ Finset.range n, 4 * G (s j) := Finset.sum_le_sum hint
    _ = 4 * ∑ j ∈ Finset.range n, G (s j) := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- The bound `|I_j|⁻¹ ≤ 2πΔ(√x_j + 1)` for `τ(y) = log(y/a)/(2πΔ)`, `x_{j+1} = x_j + √x_j`. -/
lemma inv_length_le {a Δ u : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hu : 0 < u) :
    1 / (log ((u + √u) / a) / (2 * π * Δ) - log (u / a) / (2 * π * Δ))
      ≤ 2 * π * Δ * (√u + 1) := by
  have hsu : 0 < √u := Real.sqrt_pos.mpr hu
  have hc : 0 < 2 * π * Δ := by positivity
  have hdiff : log ((u + √u) / a) - log (u / a) = log (1 + 1 / √u) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    rw [mul_add, Real.mul_self_sqrt hu.le]; ring
  have hlog := div_one_add_le_log (s := 1 / √u) (by positivity)
  have hs : (1 / √u) / (1 + 1 / √u) = 1 / (√u + 1) := by field_simp
  rw [hs] at hlog
  have hL : 0 < log (1 + 1 / √u) := lt_of_lt_of_le (by positivity) hlog
  rw [← sub_div, hdiff, one_div_div]
  rw [div_le_iff₀ hL]
  calc 2 * π * Δ = 2 * π * Δ * (√u + 1) * (1 / (√u + 1)) := by field_simp
    _ ≤ 2 * π * Δ * (√u + 1) * log (1 + 1 / √u) := by gcongr

end RhGaps
