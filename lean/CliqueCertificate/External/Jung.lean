import CliqueCertificate.External.Variance

/-! Jung bounds from radius deletion and the enclosing-radius hierarchy. -/

namespace TranslationGeometry

section Deletion

open scoped BigOperators NNReal

variable {α ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem translationError_subtype (p : α → E) (C : Finset α) :
    translationError (fun i : C => p i) Finset.univ = translationError p C := by
  unfold translationError minimaxError
  congr 1
  funext t
  apply le_antisymm
  · exact Finset.sup_le fun i _ => Finset.le_sup (f := fun i => nndist t (p i)) i.property
  · apply Finset.sup_le
    intro i hi
    exact Finset.le_sup (f := fun j : C => nndist t (p j)) (Finset.mem_univ ⟨i, hi⟩)

theorem weightedVariance_delete_bound [Fintype ι]
    (p : ι → E) (w : ι → ℝ) (hw : w ∈ probabilityWeights ι)
    (i : ι) (z : E) (R r : ℝ)
    (hvar : weightedVariance p w = R ^ 2)
    (hp : ‖p i - weightedCenter p w‖ ^ 2 ≤ R ^ 2)
    (ha : w i < 1) (hrest : ∀ j, j ≠ i → ‖p j - z‖ ≤ r) :
    (1 - 2 * w i) * R ^ 2 ≤ (1 - w i) ^ 2 * r ^ 2 := by
  classical
  have hsum : ∑ j, w j * ‖p j - z‖ ^ 2 ≤
      (1 - w i) * r ^ 2 + w i * ‖p i - z‖ ^ 2 := by
    calc
      _ ≤ ∑ j, (w j * r ^ 2 + if j = i then w i * (‖p i - z‖ ^ 2 - r ^ 2) else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = i
        · subst j
          simp only [ite_true]
          ring_nf
          exact le_rfl
        · simp only [hj, ite_false, add_zero]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hrest j hj) 2) (hw.1 j)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw.2]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring
  rw [weightedVariance_identity p w hw.2 z, hvar] at hsum
  let u := p i - weightedCenter p w
  let v := weightedCenter p w - z
  have hpz : p i - z = u + v := by dsimp [u, v]; abel
  rw [hpz, norm_add_sq_real] at hsum
  have hn := sq_nonneg ‖(1 - w i) • v - w i • u‖
  simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right] at hn
  rw [real_inner_comm u v] at hn
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ha.le)
  have hpi := mul_le_mul_of_nonneg_left hp (hw.1 i)
  change ‖u‖ ^ 2 ≤ R ^ 2 at hp
  change w i * ‖u‖ ^ 2 ≤ w i * R ^ 2 at hpi
  change (1 - w i) * (R ^ 2 + ‖v‖ ^ 2) ≤ _ at hmul
  nlinarith only [hn, hmul, hpi]

theorem deletion_coefficient {n a R r : ℝ} (hn : 3 ≤ n) (ha : 0 ≤ a)
    (hna : n * a ≤ 1)
    (h : (1 - 2 * a) * R ^ 2 ≤ (1 - a) ^ 2 * r ^ 2) :
    n * (n - 2) * R ^ 2 ≤ (n - 1) ^ 2 * r ^ 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hn2 : 0 ≤ n - 2 := by linarith
  have ha3 : 3 * a ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) ha]
  have hpos : 0 < 1 - 2 * a := by linarith
  have hc : n * (n - 2) * (1 - a) ^ 2 ≤ (n - 1) ^ 2 * (1 - 2 * a) := by
    have hh := mul_nonneg (sub_nonneg.mpr hna)
      (show 0 ≤ 1 + (n - 2) * a by positivity)
    nlinarith only [hh]
  have h1 := mul_le_mul_of_nonneg_left h (show 0 ≤ n * (n - 2) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
  apply (mul_le_mul_iff_right₀ hpos).mp
  nlinarith only [h1, h2]

theorem translation_radius_delete [ProperSpace E] [DecidableEq α] (p : α → E) (C : Finset α)
    (hcard : 3 ≤ C.card) :
    ∃ i ∈ C, (C.card : ℝ) * ((C.card : ℝ) - 2) * (translationError p C : ℝ) ^ 2 ≤
      ((C.card : ℝ) - 1) ^ 2 * (translationError p (C.erase i) : ℝ) ^ 2 := by
  classical
  have hC : C.Nonempty := Finset.card_pos.mp (by omega)
  have : Nonempty C := hC.to_subtype
  obtain ⟨w, hw, hv, hp⟩ := weightedVariance_radius_witness (fun i : C => p i)
  rw [translationError_subtype] at hv hp
  have hn : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hs : ∑ i : C, w i ≤ ∑ _i : C, (1 / (C.card : ℝ)) := by
    rw [hw.2]
    simp [div_eq_mul_inv, ne_of_gt hn]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  have hna : (C.card : ℝ) * w i ≤ 1 := by
    have hh := (le_div_iff₀ hn).1 hi
    nlinarith only [hh]
  have hn3 : (3 : ℝ) ≤ C.card := by exact_mod_cast hcard
  have ha : w i < 1 := by nlinarith [hw.1 i]
  obtain ⟨z, hz⟩ := translationError_attained p (C.erase i)
  refine ⟨i, i.property, deletion_coefficient hn3 (hw.1 i) hna ?_⟩
  apply weightedVariance_delete_bound (fun j : C => p j) w hw i z
    (translationError p C : ℝ) (translationError p (C.erase i) : ℝ)
    hv (hp i) ha
  intro j hji
  have hj : (j : α) ∈ C.erase i := Finset.mem_erase.mpr
    ⟨fun h => hji (Subtype.ext h), j.property⟩
  have hb := Finset.le_sup (f := fun j => nndist z (p j)) hj
  rw [hz] at hb
  simpa [dist_eq_norm, norm_sub_rev] using NNReal.coe_le_coe.mpr hb

end Deletion

section Hierarchy

open scoped NNReal

variable {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem translation_hierarchy_step (p : α → E) (C : Finset α) (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) * ((n : ℝ) - 2) * (rhoK (translationError p) n C : ℝ) ^ 2 ≤
      ((n : ℝ) - 1) ^ 2 * (rhoK (translationError p) (n - 1) C : ℝ) ^ 2 := by
  classical
  obtain ⟨I, hI, hmax⟩ := Finset.exists_mem_eq_sup
    (C.powerset.filter fun I => I.card ≤ n) ⟨∅, by simp⟩ (translationError p)
  change rhoK (translationError p) n C = translationError p I at hmax
  rw [hmax]
  obtain ⟨hIC, hcard⟩ := Finset.mem_filter.mp hI
  have hIC' := Finset.mem_powerset.mp hIC
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hsmall : I.card ≤ n - 1
  · have hb : translationError p I ≤ rhoK (translationError p) (n - 1) C :=
      Finset.le_sup (f := translationError p) (Finset.mem_filter.mpr ⟨hIC, hsmall⟩)
    have hsq := pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hb) 2
    calc
      _ ≤ (n : ℝ) * ((n : ℝ) - 2) *
          (rhoK (translationError p) (n - 1) C : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hn0 hn2)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith)
        (sq_nonneg (rhoK (translationError p) (n - 1) C : ℝ))
  · have hsize : I.card = n := by omega
    obtain ⟨i, hi, hdel⟩ := translation_radius_delete p I (by omega)
    have hb : translationError p (I.erase i) ≤ rhoK (translationError p) (n - 1) C := by
      apply Finset.le_sup (f := translationError p)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr ((Finset.erase_subset i I).trans hIC'),
        by simp [Finset.card_erase_of_mem hi, hsize]⟩
    rw [hsize] at hdel
    exact hdel.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hb) 2) (sq_nonneg _))

theorem translation_hierarchy_sq_bound (p : α → E) (C : Finset α)
    (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (n : ℝ) * ((k : ℝ) - 1) * (rhoK (translationError p) n C : ℝ) ^ 2 ≤
      ((n : ℝ) - 1) * (k : ℝ) * (rhoK (translationError p) k C : ℝ) ^ 2 := by
  induction n, hkn using Nat.le_induction with
  | base => ring_nf; exact le_rfl
  | succ n hn ih =>
    have hstep := translation_hierarchy_step p C (n + 1) (by omega)
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (hk.trans hn)
    have h1 := mul_le_mul_of_nonneg_left hstep (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith)
    have h2 := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ n by positivity)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h1 ⊢
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < (n : ℝ) - 1 by linarith)).mp
    nlinarith only [h1, h2]

end Hierarchy

section Jung

open scoped NNReal

noncomputable def jungFactor (d k : ℕ) : ℝ≥0 :=
  NNReal.sqrt (((d : ℝ≥0) * k) / (((d : ℝ≥0) + 1) * (k - 1 : ℕ)))

noncomputable def jungConstant (d : ℕ) : ℝ≥0 :=
  NNReal.sqrt ((d : ℝ≥0) / (2 * ((d : ℝ≥0) + 1)))

theorem jungFactor_pos {d k : ℕ} (hd : 1 ≤ d) (hk : 2 ≤ k) : 0 < jungFactor d k := by
  unfold jungFactor
  apply NNReal.sqrt_pos.mpr
  have hd0 : (0 : ℝ≥0) < d := by exact_mod_cast (show 0 < d by omega)
  have hk0 : (0 : ℝ≥0) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (0 : ℝ≥0) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  positivity

theorem jungConstant_pos {d : ℕ} (hd : 1 ≤ d) : 0 < jungConstant d := by
  unfold jungConstant
  apply NNReal.sqrt_pos.mpr
  have hd0 : (0 : ℝ≥0) < d := by exact_mod_cast (show 0 < d by omega)
  positivity

theorem jungFactor_two (d : ℕ) : jungFactor d 2 = 2 * jungConstant d := by
  apply (sq_eq_sq₀ zero_le zero_le).mp
  simp only [jungFactor, jungConstant, mul_pow, NNReal.sq_sqrt]
  norm_num
  field_simp
  ring

theorem jungFactor_dimension {d : ℕ} (hd : 1 ≤ d) : jungFactor d (d + 1) = 1 := by
  unfold jungFactor
  have hd0 : (d : ℝ≥0) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp [Nat.cast_add, mul_comm, hd0]

variable {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem translation_jung_higher (p : α → E) (C : Finset α) (k : ℕ)
    (hk : 2 ≤ k) (hkd : k ≤ Module.finrank ℝ E + 1) :
    translationError p C ≤ jungFactor (Module.finrank ℝ E) k * rhoK (translationError p) k C := by
  have hs := translation_hierarchy_sq_bound p C k (Module.finrank ℝ E + 1) hk hkd
  rw [translation_rho_dimension] at hs
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hs
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hden : (0 : ℝ) < ((Module.finrank ℝ E : ℝ) + 1) * ((k : ℝ) - 1) := by positivity
  apply (sq_le_sq₀ zero_le zero_le).mp
  rw [mul_pow, jungFactor, NNReal.sq_sqrt]
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_add, NNReal.coe_one, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith only [hs]

theorem translation_jung_upper (p : α → E) (C : Finset α)
    (hd : 1 ≤ Module.finrank ℝ E) :
    translationError p C ≤ jungConstant (Module.finrank ℝ E) * cloudDiameter p C := by
  have h := translation_jung_higher p C 2 (by omega) (by omega)
  rw [jungFactor_two, translation_rho_two] at h
  convert h using 1
  ring

theorem translation_jung_bounds (p : α → E) (C : Finset α)
    (hd : 1 ≤ Module.finrank ℝ E) :
    cloudDiameter p C / 2 ≤ translationError p C ∧
      translationError p C ≤ jungConstant (Module.finrank ℝ E) * cloudDiameter p C :=
  ⟨half_diameter_le_translationError p C, translation_jung_upper p C hd⟩

end Jung

end TranslationGeometry
