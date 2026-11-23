import RhGaps.Basic

/-!
  Lemma (TV) from proof.org §1 and its use in section 3.5(a):
  for a cover of [t₀, tₙ] by adjacent intervals
    Σⱼ G(sⱼ) ≤ Σⱼ Bⱼ ∫_{Iⱼ} G + Var(Ĥ; [t₀, tₙ]),   G = (Ĥ)₊,  Bⱼ ≥ |Iⱼ|⁻¹.
  Fully proved, with no axioms.
-/

open Real MeasureTheory

namespace RhGaps

/-- A difference of values ≤ the variation on the set. -/
lemma sub_le_variation {G : ℝ → ℝ} {s : Set ℝ} (hfin : eVariationOn G s ≠ ⊤)
    {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) : G u - G v ≤ (eVariationOn G s).toReal := by
  have h := eVariationOn.edist_le G hu hv
  have hd : dist (G u) (G v) ≤ (eVariationOn G s).toReal := by
    rw [dist_edist]; exact ENNReal.toReal_mono hfin h
  rw [Real.dist_eq] at hd
  exact (le_abs_self _).trans hd

/-- Variation is additive over adjacent intervals. -/
lemma sum_variation_adjacent (G : ℝ → ℝ) (t : ℕ → ℝ) (ht : Monotone t) (n : ℕ) :
    ∑ j ∈ Finset.range n, eVariationOn G (Set.Icc (t j) (t (j + 1)))
      = eVariationOn G (Set.Icc (t 0) (t n)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Set.Icc_self]
    exact (eVariationOn.subsingleton G Set.subsingleton_singleton).symm
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have := eVariationOn.Icc_add_Icc G (s := Set.univ) (ht (Nat.zero_le n))
      (ht (Nat.le_succ n)) (Set.mem_univ _)
    simpa using this

/-- The positive part does not increase variation (s ↦ s₊ is 1-Lipschitz). -/
lemma variation_pos_part_le (H : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun t => max (H t) 0) s ≤ eVariationOn H s := by
  have hL : LipschitzWith 1 (fun x : ℝ => max x 0) := LipschitzWith.id.max_const 0
  have := (hL.lipschitzOnWith (s := Set.univ)).comp_eVariationOn_le (g := H) (s := s)
    (Set.mapsTo_univ _ _)
  simpa [Function.comp_def] using this

/-- **Lemma (TV)** in the form used in section 3.5(a). -/
theorem tv_covering (H : ℝ → ℝ) (hH : Continuous H) (t : ℕ → ℝ) (ht : StrictMono t) (n : ℕ)
    (hvar : eVariationOn H (Set.Icc (t 0) (t n)) ≠ ⊤)
    (B : ℕ → ℝ) (hB : ∀ j < n, 1 / (t (j + 1) - t j) ≤ B j)
    (s : ℕ → ℝ) (hs : ∀ j, s j ∈ Set.Icc (t j) (t (j + 1))) :
    ∑ j ∈ Finset.range n, max (H (s j)) 0
      ≤ (∑ j ∈ Finset.range n, B j * (∫ u in (t j)..(t (j + 1)), max (H u) 0))
        + (eVariationOn H (Set.Icc (t 0) (t n))).toReal := by
  set G : ℝ → ℝ := fun u => max (H u) 0 with hGdef
  have hGc : Continuous G := hH.max continuous_const
  have hGvar : eVariationOn G (Set.Icc (t 0) (t n)) ≤ eVariationOn H (Set.Icc (t 0) (t n)) :=
    variation_pos_part_le H _
  -- the variation of G on each Iⱼ (j < n) is finite
  have hsub : ∀ j ∈ Finset.range n,
      eVariationOn G (Set.Icc (t j) (t (j + 1))) ≤ eVariationOn G (Set.Icc (t 0) (t n)) := by
    intro j hj
    apply eVariationOn.mono
    apply Set.Icc_subset_Icc (ht.monotone (Nat.zero_le j))
    exact ht.monotone (Finset.mem_range.mp hj)
  have hfin : ∀ j ∈ Finset.range n, eVariationOn G (Set.Icc (t j) (t (j + 1))) ≠ ⊤ :=
    fun j hj => ne_top_of_le_ne_top hvar ((hsub j hj).trans hGvar)
  -- the step for one interval
  have step : ∀ j ∈ Finset.range n, G (s j) ≤
      B j * (∫ u in (t j)..(t (j + 1)), G u)
        + (eVariationOn G (Set.Icc (t j) (t (j + 1)))).toReal := by
    intro j hj
    have hlt : t j < t (j + 1) := ht (Nat.lt_succ_self j)
    have h1 := le_avg_add_osc hlt (hGc.intervalIntegrable _ _)
      (fun u hu v hv => sub_le_variation (hfin j hj) hu hv) (hs j)
    have hint : 0 ≤ ∫ u in (t j)..(t (j + 1)), G u :=
      intervalIntegral.integral_nonneg hlt.le (fun u _ => le_max_right _ _)
    have h2 : (∫ u in (t j)..(t (j + 1)), G u) / (t (j + 1) - t j)
        ≤ B j * ∫ u in (t j)..(t (j + 1)), G u := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB j (Finset.mem_range.mp hj)) hint
    linarith
  calc ∑ j ∈ Finset.range n, G (s j)
      ≤ ∑ j ∈ Finset.range n, (B j * (∫ u in (t j)..(t (j + 1)), G u)
          + (eVariationOn G (Set.Icc (t j) (t (j + 1)))).toReal) := Finset.sum_le_sum step
    _ = (∑ j ∈ Finset.range n, B j * (∫ u in (t j)..(t (j + 1)), G u))
          + (∑ j ∈ Finset.range n, eVariationOn G (Set.Icc (t j) (t (j + 1)))).toReal := by
        rw [Finset.sum_add_distrib, ENNReal.toReal_sum hfin]
    _ = (∑ j ∈ Finset.range n, B j * (∫ u in (t j)..(t (j + 1)), G u))
          + (eVariationOn G (Set.Icc (t 0) (t n))).toReal := by
        rw [sum_variation_adjacent G t ht.monotone n]
    _ ≤ _ := by
        have := ENNReal.toReal_mono hvar hGvar
        simp only [hGdef] at this ⊢
        linarith

end RhGaps
