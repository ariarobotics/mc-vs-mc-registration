import CliqueCertificate.External.FiniteConsistency

/-! Enclosing radii, pairwise distances, and the finite Helly theorem. -/

namespace TranslationGeometry

section Definitions

open scoped NNReal

variable {α X E : Type*}

noncomputable def minimaxError (error : X → α → ℝ≥0) (C : Finset α) : ℝ≥0 :=
  ⨅ x, C.sup (error x)

noncomputable def pairMax (distance : α → α → ℝ≥0) (C : Finset α) : ℝ≥0 :=
  C.sup fun i => C.sup fun j => distance i j

export FiniteConsistency (rhoK maxConsensus mcK)

variable [NormedAddCommGroup E]

noncomputable def translationError (μ : α → E) (C : Finset α) : ℝ≥0 :=
  minimaxError (fun t i => nndist t (μ i)) C

noncomputable def cloudDiameter (μ : α → E) (C : Finset α) : ℝ≥0 :=
  pairMax (fun i j => nndist (μ i) (μ j)) C

export FiniteConsistency (rhoK_le_iff rhoK_mono rhoK_le_rho rhoK_eq_rho
  maxConsensus_antitone mcK_antitone maxConsensus_le_mcK rho_hierarchy_bounds
  mc_hierarchy_bounds mcK_eq_maxConsensus)

end Definitions

section Radii

open scoped NNReal

variable {α P E : Type*}

theorem minimaxError_mono (error : P → α → ℝ≥0) : Monotone (minimaxError error) := by
  intro C D hCD
  apply ciInf_mono (OrderBot.bddBelow _)
  intro T
  exact Finset.sup_le fun i hi => Finset.le_sup (hCD hi)

theorem minimaxError_le (error : P → α → ℝ≥0) (C : Finset α) (T : P) :
    minimaxError error C ≤ C.sup (error T) :=
  ciInf_le (OrderBot.bddBelow _) T

theorem minimaxError_empty [Nonempty P] (error : P → α → ℝ≥0) :
    minimaxError error ∅ = 0 := by
  simp [minimaxError]

theorem pairMax_le_iff (d : α → α → ℝ≥0) (C : Finset α) (ε : ℝ≥0) :
    pairMax d C ≤ ε ↔ ∀ i ∈ C, ∀ j ∈ C, d i j ≤ ε := by
  simp only [pairMax, Finset.sup_le_iff]

theorem le_pairMax (d : α → α → ℝ≥0) (C : Finset α)
    {i j : α} (hi : i ∈ C) (hj : j ∈ C) : d i j ≤ pairMax d C := by
  exact (Finset.le_sup (f := d i) hj).trans
    (Finset.le_sup (f := fun i => C.sup (d i)) hi)

variable [NormedAddCommGroup E]

theorem translationError_mono (μ : α → E) : Monotone (translationError μ) :=
  minimaxError_mono _

theorem translationError_empty (μ : α → E) : translationError μ ∅ = 0 :=
  minimaxError_empty _

theorem translationError_le (μ : α → E) (C : Finset α) (t : E) :
    translationError μ C ≤ C.sup (fun i => nndist t (μ i)) :=
  minimaxError_le _ C t

theorem translationError_singleton (μ : α → E) (i : α) :
    translationError μ {i} = 0 := by
  apply le_antisymm _ zero_le
  simpa using translationError_le μ {i} (μ i)

theorem translationError_attained [ProperSpace E] (μ : α → E) (C : Finset α) :
    ∃ t, C.sup (fun i => nndist t (μ i)) = translationError μ C := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · exact ⟨0, by simp [translationError_empty]⟩
  let f : E → ℝ≥0 := fun t => C.sup (fun j => nndist t (μ j))
  have hf : Continuous f := Continuous.finset_sup_apply
    (fun j _ => continuous_id.nndist continuous_const)
  obtain ⟨t, ht⟩ := hf.exists_forall_le' (μ i) (by
    filter_upwards [(tendsto_dist_right_cocompact_atTop (μ i)).eventually
      (Filter.eventually_ge_atTop (f (μ i) : ℝ))] with x hx
    exact NNReal.coe_le_coe.mp (hx.trans (NNReal.coe_le_coe.mpr
      (Finset.le_sup (f := fun j => nndist x (μ j)) hi))))
  exact ⟨t, le_antisymm (le_ciInf ht) (translationError_le μ C t)⟩

theorem translationError_le_iff [ProperSpace E] (μ : α → E) (C : Finset α) (τ : ℝ≥0) :
    translationError μ C ≤ τ ↔ ∃ t, ∀ i ∈ C, nndist t (μ i) ≤ τ := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := translationError_attained μ C
    exact ⟨t, fun i hi => (Finset.le_sup hi).trans (ht ▸ h)⟩
  · rintro ⟨t, ht⟩
    exact (translationError_le μ C t).trans (Finset.sup_le ht)

theorem translation_diameter_le_twice_residual (μ : α → E) (C : Finset α) (t : E) :
    cloudDiameter μ C ≤ 2 * C.sup (fun i => nndist t (μ i)) := by
  apply (pairMax_le_iff _ _ _).2
  intro i hi j hj
  calc
    nndist (μ i) (μ j) ≤ nndist t (μ i) + nndist t (μ j) := nndist_triangle_left _ _ _
    _ ≤ C.sup (fun i => nndist t (μ i)) + C.sup (fun i => nndist t (μ i)) :=
      add_le_add (Finset.le_sup (f := fun i => nndist t (μ i)) hi)
        (Finset.le_sup (f := fun i => nndist t (μ i)) hj)
    _ = _ := (two_mul _).symm

theorem half_diameter_le_translationError (μ : α → E) (C : Finset α) :
    cloudDiameter μ C / 2 ≤ translationError μ C := by
  apply le_ciInf
  intro t
  apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2
  simpa [mul_comm] using translation_diameter_le_twice_residual μ C t

theorem translationError_pair [NormedSpace ℝ E] [DecidableEq α] (μ : α → E) (i j : α) :
    translationError μ {i, j} = nndist (μ i) (μ j) / 2 := by
  classical
  apply le_antisymm
  · calc
      translationError μ {i, j} ≤
          ({i, j} : Finset α).sup (fun k => nndist (midpoint ℝ (μ i) (μ j)) (μ k)) :=
        translationError_le μ {i, j} _
      _ = _ := by
        simp [nndist_midpoint_left, nndist_midpoint_right, div_eq_mul_inv, mul_comm]
  · have h := half_diameter_le_translationError μ {i, j}
    simpa [cloudDiameter, pairMax, nndist_comm] using h

end Radii

section Pairs

open scoped NNReal

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem translation_rho_two (μ : α → E) (C : Finset α) :
    rhoK (translationError μ) 2 C = cloudDiameter μ C / 2 := by
  classical
  apply le_antisymm
  · apply (rhoK_le_iff _ _ _ _).2
    intro I hIC hcard
    by_cases htwo : I.card = 2
    · obtain ⟨i, j, _, rfl⟩ := Finset.card_eq_two.mp htwo
      rw [translationError_pair]
      exact div_le_div_of_nonneg_right
        (le_pairMax (fun a b => nndist (μ a) (μ b)) C
          (hIC (Finset.mem_insert_self i {j}))
          (hIC (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))) zero_le
    · have hone : I.card ≤ 1 := by omega
      obtain rfl | ⟨i, hi⟩ := I.eq_empty_or_nonempty
      · rw [translationError_empty]
        exact zero_le
      · have hsub : I ⊆ {i} := by
          intro j hj
          exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hone) j hj i hi)
        calc
          translationError μ I ≤ translationError μ {i} := translationError_mono μ hsub
          _ = 0 := translationError_singleton μ i
          _ ≤ _ := zero_le
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2
    apply (pairMax_le_iff _ _ _).2
    intro i hi j hj
    have hpair : translationError μ {i, j} ≤ rhoK (translationError μ) 2 C := by
      apply Finset.le_sup (f := translationError μ)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr
        (Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩),
        Finset.card_le_two⟩
    rw [translationError_pair] at hpair
    exact (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).1 hpair

end Pairs

section Helly

open scoped NNReal

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem translationError_le_iff_small_groups (μ : α → E) (C : Finset α) (τ : ℝ≥0) :
    translationError μ C ≤ τ ↔
      ∀ I ⊆ C, I.card ≤ Module.finrank ℝ E + 1 → translationError μ I ≤ τ := by
  constructor
  · intro h I hIC _
    exact (translationError_mono μ hIC).trans h
  · intro h
    have hinter : (⋂ i ∈ C, Metric.closedBall (μ i) (τ : ℝ)).Nonempty := by
      apply Convex.helly_theorem' (𝕜 := ℝ)
      · intro i _
        exact convex_closedBall (μ i) (τ : ℝ)
      · intro I hIC hcard
        obtain ⟨t, ht⟩ := (translationError_le_iff μ I τ).1 (h I hIC hcard)
        refine ⟨t, ?_⟩
        simp only [Set.mem_iInter, Metric.mem_closedBall]
        intro i hi
        exact NNReal.coe_le_coe.mpr (ht i hi)
    obtain ⟨t, ht⟩ := hinter
    apply (translationError_le_iff μ C τ).2
    refine ⟨t, ?_⟩
    simp only [Set.mem_iInter, Metric.mem_closedBall] at ht
    intro i hi
    exact NNReal.coe_le_coe.mp (ht i hi)

theorem translation_rho_dimension (μ : α → E) (C : Finset α) :
    rhoK (translationError μ) (Module.finrank ℝ E + 1) C = translationError μ C := by
  apply le_antisymm (rhoK_le_rho _ (translationError_mono μ) _ C)
  apply (translationError_le_iff_small_groups μ C _).2
  exact (rhoK_le_iff _ _ _ _).1 le_rfl

theorem translation_mc_dimension (μ : α → E) (U : Finset α) (τ : ℝ≥0) :
    mcK U (translationError μ) (Module.finrank ℝ E + 1) τ =
      maxConsensus U (translationError μ) τ := by
  unfold mcK
  congr 1
  funext C
  exact translation_rho_dimension μ C

theorem translation_rho_ge_dimension (μ : α → E) (C : Finset α) {k : ℕ}
    (hk : Module.finrank ℝ E + 1 ≤ k) :
    rhoK (translationError μ) k C = translationError μ C := by
  apply le_antisymm (rhoK_le_rho _ (translationError_mono μ) _ C)
  rw [← translation_rho_dimension μ C]
  exact rhoK_mono _ C hk

theorem translationError_real_eq_half_diameter (μ : α → ℝ) (C : Finset α) :
    translationError μ C = cloudDiameter μ C / 2 := by
  have h := translation_rho_dimension μ C
  simpa [translation_rho_two] using h.symm

end Helly

end TranslationGeometry
