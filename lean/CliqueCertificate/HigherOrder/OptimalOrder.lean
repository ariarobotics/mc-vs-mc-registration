import CliqueCertificate.HigherOrder.Bounds

/-! Proposition 2 and the critical order d + 2. The proof uses an axis construction. -/

namespace HigherOrder.Obstruction

section Obstruction

open scoped NNReal Finset
open EuclideanGeometry

private theorem affine_relation_univ {n d : ℕ} (P Q : Fin n → ℝ^[d]) (α : Fin n → ℝ)
    (hα : ∑ i, α i = 0) :
    |‖∑ i, α i • P i‖ - ‖∑ i, α i • Q i‖| ≤
      (rho P Q Finset.univ : ℝ) * ∑ i, |α i| := by
  simpa [Finset.sum_coe_sort] using
    affine_relation_bound P Q Finset.univ α (by simpa [Finset.sum_coe_sort] using hα)

private theorem rho_le_of_fit {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))
    (T : E(d)) (τ : ℝ≥0) (h : ∀ i ∈ C, ‖T (P i) - Q i‖₊ ≤ τ) :
    rho P Q C ≤ τ := by
  apply Fits.rho_le (T := T)
  intro i hi
  exact NNReal.coe_le_coe.mpr (h i hi)

noncomputable section

variable {d : ℕ} [NeZero d]

abbrev axis (j : Fin d) : ℝ^[d] := EuclideanSpace.single j 1

def middle (ℓ : ℝ) : ℝ^[d] := WithLp.toLp 2 (fun j : Fin d => if j = 0 then 0 else ℓ)

def source (ℓ : ℝ) : Fin (d + 2) → ℝ^[d] :=
  Fin.addCases (fun j => if j = 0 then axis 0 else (((d : ℝ) - 1) * ℓ) • axis j)
    ![-axis 0, middle ℓ + (2 : ℝ) • axis 0]

def target (ℓ : ℝ) : Fin (d + 2) → ℝ^[d] :=
  Fin.addCases (fun j => if j = 0 then axis 0 else (((d : ℝ) - 1) * ℓ) • axis j)
    ![-axis 0, middle ℓ - (2 : ℝ) • axis 0]

def witness : Fin (d + 2) → ℝ :=
  Fin.addCases (fun j => if j = 0 then -1 else -1 / ((d : ℝ) - 1)) ![1, 1]

private theorem sum_except_zero (a b : ℝ) :
    (∑ j : Fin d, if j = 0 then a else b) = a + ((d : ℝ) - 1) * b := by
  have h (j : Fin d) : (if j = 0 then a else b) = b + if j = 0 then a - b else 0 := by
    split_ifs <;> ring
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem middle_apply (ℓ : ℝ) (j : Fin d) : middle ℓ j = if j = 0 then 0 else ℓ := rfl

@[simp] theorem middle_zero (ℓ : ℝ) : middle (d := d) ℓ 0 = 0 := by simp [middle_apply]

omit [NeZero d] in
@[simp] theorem axis_norm (j : Fin d) : ‖axis j‖ = 1 := by simp [axis]

theorem middle_norm_sq (ℓ : ℝ) : ‖middle (d := d) ℓ‖ ^ 2 = ((d : ℝ) - 1) * ℓ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [middle_apply, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [sum_except_zero]
  ring

theorem witness_sum (hd : 2 ≤ d) : ∑ i : Fin (d + 2), witness i = 0 := by
  have hr : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Fin.sum_univ_add]
  simp [witness, Fin.sum_univ_two, sum_except_zero]
  field_simp
  ring

omit [NeZero d] in
private theorem sum_smul_axis (f : Fin d → ℝ) :
    (∑ j : Fin d, f j • axis j) = WithLp.toLp 2 f := by
  ext k
  simp [axis, Pi.single_apply]

theorem witness_source_sum (ℓ : ℝ) (hd : 2 ≤ d) :
    ∑ i : Fin (d + 2), witness i • source ℓ i = 0 := by
  have hr : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hleft (j : Fin d) : witness (Fin.castAdd 2 j) • source ℓ (Fin.castAdd 2 j) =
      (if j = 0 then -1 else -ℓ) • axis j := by
    by_cases hj : j = 0
    · simp [source, witness, hj]
    · simp only [source, witness, Fin.addCases_left, ite_eq_right hj]
      rw [smul_smul]
      congr 1
      field_simp
  rw [Fin.sum_univ_add]
  simp_rw [hleft]
  rw [sum_smul_axis]
  simp only [source, witness, Fin.sum_univ_two]
  ext k
  by_cases hk : k = 0 <;> norm_num [hk, middle_apply, axis]

theorem witness_target_sum (ℓ : ℝ) (hd : 2 ≤ d) :
    ∑ i : Fin (d + 2), witness i • target ℓ i = (-4 : ℝ) • axis 0 := by
  have hp := witness_source_sum (d := d) ℓ hd
  rw [Fin.sum_univ_add] at hp ⊢
  simp only [source, target, witness, Fin.addCases_left, Fin.addCases_right,
    Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul] at hp ⊢
  rw [eq_neg_of_add_eq_zero_left hp]
  module

theorem witness_abs_sum (hd : 2 ≤ d) : ∑ i : Fin (d + 2), |witness i| = 4 := by
  have hr : 0 < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Fin.sum_univ_add]
  simp only [witness, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h (j : Fin d) : |if j = 0 then -1 else -1 / ((d : ℝ) - 1)| =
      if j = 0 then 1 else 1 / ((d : ℝ) - 1) := by
    split_ifs <;> simp [abs_div, abs_of_pos hr]
  simp_rw [h]
  rw [sum_except_zero]
  norm_num
  field_simp
  ring

theorem rho_lower (ℓ : ℝ) (hd : 2 ≤ d) :
    1 ≤ (rho (source (d := d) ℓ) (target ℓ) Finset.univ : ℝ) := by
  have h := affine_relation_univ (source (d := d) ℓ) (target ℓ) witness (witness_sum hd)
  rw [witness_source_sum ℓ hd, witness_target_sum ℓ hd, witness_abs_sum hd,
    norm_zero, norm_smul, Real.norm_eq_abs, axis_norm] at h
  norm_num at h
  exact_mod_cast h

omit [NeZero d] in
@[simp] theorem axis_inner_left (j : Fin d) (v : ℝ^[d]) : inner ℝ (axis j) v = v j := by
  simp [axis, EuclideanSpace.inner_single_left]

omit [NeZero d] in
@[simp] theorem axis_inner_right (v : ℝ^[d]) (j : Fin d) : inner ℝ v (axis j) = v j := by
  simp [axis, EuclideanSpace.inner_single_right]

def normal (ℓ : ℝ) (j : Fin d) : ℝ^[d] := (2 : ℝ) • axis 0 + ℓ • axis j

noncomputable def axis_rotation (ℓ : ℝ) (j : Fin d) : O(d) :=
  (linear_reflection (normal ℓ j)).trans (linear_reflection (axis j))

theorem normal_norm_sq (ℓ : ℝ) (j : Fin d) (hj : j ≠ 0) :
    ‖normal ℓ j‖ ^ 2 = 4 + ℓ ^ 2 := by
  norm_num [normal, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_smul_right, axis, EuclideanSpace.inner_single_left, hj]

theorem axis_rotation_fixed (ℓ : ℝ) (j k : Fin d) (hk : k ≠ 0) (hkj : k ≠ j) :
    axis_rotation ℓ j (axis k) = axis k := by
  have h₁ : inner ℝ (normal ℓ j) (axis k) = 0 := by
    simp [axis_inner_right, normal, axis, hk, hkj]
  have h₂ : inner ℝ (axis j) (axis k) = 0 := by simp [axis, hkj]
  change linear_reflection (axis j) (linear_reflection (normal ℓ j) (axis k)) = _
  rw [linear_reflection_fixed _ _ h₁, linear_reflection_fixed _ _ h₂]

theorem axis_rotation_special (ℓ : ℝ) (j : Fin d) (hj : j ≠ 0) :
    axis_rotation ℓ j (middle ℓ + (2 : ℝ) • axis 0) = middle ℓ - (2 : ℝ) • axis 0 := by
  have hn : ‖normal ℓ j‖ ^ 2 ≠ 0 := by rw [normal_norm_sq ℓ j hj]; positivity
  have hi : inner ℝ (normal ℓ j) (middle ℓ + (2 : ℝ) • axis 0) = ‖normal ℓ j‖ ^ 2 := by
    rw [normal_norm_sq ℓ j hj]
    simp [normal, inner_add_left, real_inner_smul_left, inner_add_right,
      real_inner_smul_right, middle_apply, axis, hj, norm_smul]
    ring
  change linear_reflection (axis j)
    (linear_reflection (normal ℓ j) (middle ℓ + (2 : ℝ) • axis 0)) = _
  rw [linear_reflection_apply (normal ℓ j) (middle ℓ + (2 : ℝ) • axis 0),
    hi, mul_div_cancel_right₀ _ hn, linear_reflection_apply]
  simp [axis_inner_left, middle_apply, normal, axis, hj]
  module

theorem axis_rotation_short_bound (ℓ : ℝ) (hℓ : 0 < ℓ) (j : Fin d) (hj : j ≠ 0) :
    ‖axis_rotation ℓ j (axis 0) - axis 0‖ ≤ 4 / ℓ := by
  have hfix : linear_reflection (axis j) (axis 0) = axis 0 :=
    linear_reflection_fixed _ _ (by simp [axis, Ne.symm hj])
  have hn : normal ℓ j ≠ 0 := by
    intro hn
    have := normal_norm_sq ℓ j hj
    rw [hn, norm_zero] at this
    nlinarith
  have hnorm : ℓ ≤ ‖normal ℓ j‖ := by
    have hs := normal_norm_sq ℓ j hj
    nlinarith [norm_nonneg (normal ℓ j)]
  change ‖linear_reflection (axis j) (linear_reflection (normal ℓ j) (axis 0)) - axis 0‖ ≤ _
  calc
    _ = ‖linear_reflection (normal ℓ j) (axis 0) - axis 0‖ := by
      conv_lhs => rw [← hfix]
      rw [← map_sub, LinearIsometryEquiv.norm_map, hfix]
    _ = 4 / ‖normal ℓ j‖ := by
      rw [linear_reflection_displacement _ _ hn]
      norm_num [normal, axis, hj, Ne.symm hj]
    _ ≤ 4 / ℓ := div_le_div_of_nonneg_left (by norm_num) hℓ hnorm

def short_normal (ℓ σ : ℝ) : ℝ^[d] :=
  σ • axis 0 + (1 / (((d : ℝ) - 1) * ℓ ^ 2)) • middle ℓ

private theorem middle_scaled_norm (ℓ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d) :
    ‖(1 / (((d : ℝ) - 1) * ℓ ^ 2)) • middle (d := d) ℓ‖ ≤ 1 / ℓ := by
  have hr : 1 ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hr0 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hs : ‖(1 / (((d : ℝ) - 1) * ℓ ^ 2)) • middle (d := d) ℓ‖ ^ 2 =
      1 / (((d : ℝ) - 1) * ℓ ^ 2) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, middle_norm_sq]
    field_simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 1 / ℓ)).mp
  rw [hs, div_pow, one_pow]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hℓ)
    (by nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg ℓ)])

private theorem short_normal_middle (ℓ σ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d) :
    inner ℝ (short_normal (d := d) ℓ σ) (middle ℓ) = 1 := by
  have hr : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  simp only [short_normal, inner_add_left, real_inner_smul_left, axis_inner_left,
    middle_zero, mul_zero, zero_add, real_inner_self_eq_norm_sq, middle_norm_sq]
  field_simp

private theorem short_reflection_fixed_long (ℓ σ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d)
    (j : Fin d) (hj : j ≠ 0) :
    hyperplane_reflection (short_normal ℓ σ) 1 ((((d : ℝ) - 1) * ℓ) • axis j) =
      (((d : ℝ) - 1) * ℓ) • axis j := by
  apply hyperplane_reflection_fixed
  have hr : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  simp [short_normal, real_inner_smul_right, axis_inner_right, middle_apply, axis, hj]
  field_simp

private theorem short_reflection_fixed_short (ℓ σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    hyperplane_reflection (short_normal (d := d) ℓ σ) 1 (σ • axis 0) = σ • axis 0 := by
  apply hyperplane_reflection_fixed
  rcases hσ with rfl | rfl <;>
    norm_num [short_normal, real_inner_smul_right, axis_inner_right, axis, middle_apply]

private theorem short_reflection_special_bound (ℓ σ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d)
    (hσ : σ = 1 ∨ σ = -1) :
    ‖hyperplane_reflection (short_normal (d := d) ℓ σ) 1 (middle ℓ + (2 : ℝ) • axis 0) -
      (middle ℓ - (2 : ℝ) • axis 0)‖ ≤ 4 / ℓ := by
  have hs : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have habs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hi : inner ℝ (short_normal (d := d) ℓ σ) (axis 0) = σ := by
    simp [short_normal, axis_inner_right, axis, middle_apply]
  have hsum : inner ℝ (short_normal (d := d) ℓ σ) (middle ℓ + (2 : ℝ) • axis 0) = 1 + 2 * σ := by
    rw [inner_add_right, real_inner_smul_right, short_normal_middle ℓ σ hℓ hd, hi]
  have heq : hyperplane_reflection (short_normal (d := d) ℓ σ) 1 (middle ℓ + (2 : ℝ) • axis 0) -
      (middle ℓ - (2 : ℝ) • axis 0) =
      (4 : ℝ) • (axis 0 -
        (inner ℝ (short_normal (d := d) ℓ σ) (axis 0) /
          ‖short_normal (d := d) ℓ σ‖ ^ 2) • short_normal ℓ σ) := by
    rw [hyperplane_reflection_apply, hsum, hi]
    module
  have hproj := norm_sub_projection_le (short_normal (d := d) ℓ σ) (axis 0) σ
  have hdiff : axis 0 - σ • short_normal (d := d) ℓ σ =
      -σ • ((1 / (((d : ℝ) - 1) * ℓ ^ 2)) • middle (d := d) ℓ) := by
    unfold short_normal
    rw [smul_add, smul_smul, ← pow_two, hs, one_smul]
    module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, habs, one_mul] at hproj
  rw [heq, norm_smul]
  norm_num only [Real.norm_eq_abs]
  calc
    _ ≤ 4 * ‖(1 / (((d : ℝ) - 1) * ℓ ^ 2)) • middle (d := d) ℓ‖ :=
      mul_le_mul_of_nonneg_left hproj (by norm_num)
    _ ≤ 4 * (1 / ℓ) := mul_le_mul_of_nonneg_left (middle_scaled_norm ℓ hℓ hd) (by norm_num)
    _ = 4 / ℓ := by ring

private theorem short_fit_at (ℓ σ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d)
    (hσ : σ = 1 ∨ σ = -1) (i : Fin (d + 2))
    (hpos : i = Fin.castAdd 2 (0 : Fin d) → σ = 1)
    (hneg : i = Fin.natAdd d (0 : Fin 2) → σ = -1) :
    ‖hyperplane_reflection (short_normal ℓ σ) 1 (source ℓ i) - target ℓ i‖ ≤ 4 / ℓ := by
  revert hpos hneg
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · intro hpos hneg
    by_cases hj : j = 0
    · subst j
      have hs := hpos rfl
      subst σ
      have hf : hyperplane_reflection (short_normal (d := d) ℓ 1) 1 (axis 0) = axis 0 := by
        simpa using short_reflection_fixed_short (d := d) ℓ 1 (Or.inl rfl)
      simp [source, target, hf, le_of_lt (by positivity : (0 : ℝ) < 4 / ℓ)]
    · simp only [source, target, Fin.addCases_left, ite_eq_right hj]
      rw [short_reflection_fixed_long ℓ σ hℓ hd j hj, sub_self, norm_zero]
      positivity
  · intro hpos hneg
    fin_cases k
    · have hs := hneg rfl
      subst σ
      have hf := short_reflection_fixed_short (d := d) ℓ (-1) (Or.inr rfl)
      simp only [neg_one_smul] at hf
      simp [source, target, hf, le_of_lt (by positivity : (0 : ℝ) < 4 / ℓ)]
    · simpa [source, target] using short_reflection_special_bound ℓ σ hℓ hd hσ

private theorem long_fit_at (ℓ : ℝ) (hℓ : 0 < ℓ) (j : Fin d) (hj : j ≠ 0)
    (i : Fin (d + 2)) (hi : i ≠ Fin.castAdd 2 j) :
    ‖axis_rotation ℓ j (source ℓ i) - target ℓ i‖ ≤ 4 / ℓ := by
  revert hi
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · intro hi
    by_cases hk : k = 0
    · simpa [source, target, hk] using axis_rotation_short_bound ℓ hℓ j hj
    · have hkj : k ≠ j := by intro h; subst k; exact hi rfl
      simp only [source, target, Fin.addCases_left, ite_eq_right hk]
      rw [map_smul, axis_rotation_fixed ℓ j k hk hkj, sub_self, norm_zero]
      positivity
  · intro hi
    fin_cases k
    · simp only [source, target, Fin.addCases_right, Fin.reduceFinMk, Matrix.cons_val_zero]
      rw [map_neg, neg_sub_neg, norm_sub_rev]
      exact axis_rotation_short_bound ℓ hℓ j hj
    · simp [source, target, axis_rotation_special ℓ j hj,
        le_of_lt (by positivity : (0 : ℝ) < 4 / ℓ)]

theorem omitted_fit (ℓ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d) (i : Fin (d + 2)) :
    ∃ T : E(d), ∀ j : Fin (d + 2), j ≠ i →
      ‖T (source ℓ j) - target ℓ j‖ ≤ 4 / ℓ := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · by_cases hk : k = 0
    · subst k
      refine ⟨hyperplane_reflection (short_normal ℓ (-1)) 1, fun j hj => ?_⟩
      apply short_fit_at ℓ (-1) hℓ hd (Or.inr rfl) j
      · intro h; exact False.elim (hj h)
      · intro _; rfl
    · exact ⟨(axis_rotation ℓ k).toAffineIsometryEquiv,
        fun j hj => long_fit_at ℓ hℓ k hk j hj⟩
  · fin_cases k
    · refine ⟨hyperplane_reflection (short_normal ℓ 1) 1, fun j hj => ?_⟩
      apply short_fit_at ℓ 1 hℓ hd (Or.inl rfl) j
      · intro _; rfl
      · intro h; exact False.elim (hj h)
    · refine ⟨AffineIsometryEquiv.refl ℝ (ℝ^[d]), fun j hj => ?_⟩
      revert hj
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · intro _; simp [source, target, le_of_lt (by positivity : (0 : ℝ) < 4 / ℓ)]
      · intro hj
        fin_cases k
        · simp [source, target, le_of_lt (by positivity : (0 : ℝ) < 4 / ℓ)]
        · exact False.elim (hj rfl)

theorem local_bound (ℓ : ℝ) (hℓ : 0 < ℓ) (hd : 2 ≤ d) :
    (rho_k (source (d := d) ℓ) (target ℓ) Finset.univ (d + 1) : ℝ) ≤ 4 / ℓ := by
  have hbound : rho_k (source (d := d) ℓ) (target ℓ) Finset.univ (d + 1) ≤
      ⟨4 / ℓ, by positivity⟩ := by
    apply (rho_k_le_iff _ _ _ _ _).2
    intro I _ hI
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show #I < #(Finset.univ : Finset (Fin (d + 2))) by
        simp only [Finset.card_univ, Fintype.card_fin]; omega)
    obtain ⟨T, hT⟩ := omitted_fit ℓ hℓ hd i
    apply rho_le_of_fit _ _ _ T
    intro j hj
    apply NNReal.coe_le_coe.mp
    exact hT j (fun heq => hi (heq ▸ hj))
  exact_mod_cast hbound

theorem local_error_tends_to_zero (hd : 2 ≤ d) :
    Filter.Tendsto
      (fun ℓ : ℝ => (rho_k (source (d := d) ℓ) (target ℓ) Finset.univ (d + 1) : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun ℓ => NNReal.coe_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with ℓ hℓ
    exact local_bound ℓ hℓ hd
  · change Filter.Tendsto (fun ℓ : ℝ => 4 * ℓ⁻¹) Filter.atTop (nhds 0)
    simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (4 : ℝ)

theorem lower_errors_tend_to_zero (hd : 2 ≤ d) (k : ℕ) (hk : k ≤ d + 1) :
    Filter.Tendsto
      (fun ℓ : ℝ => (rho_k (source (d := d) ℓ) (target ℓ) Finset.univ k : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun ℓ => NNReal.coe_nonneg _)
    (Filter.Eventually.of_forall fun ℓ => ?_) (local_error_tends_to_zero hd)
  exact_mod_cast rho_k_mono (source ℓ) (target ℓ) Finset.univ hk

omit [NeZero d] in

theorem lower_order_obstruction (hd : 2 ≤ d) :
    ∃ P Q : ℝ → Fin (d + 2) → ℝ^[d],
      Filter.Tendsto (fun ℓ => (rho_k (P ℓ) (Q ℓ) Finset.univ (d + 1) : ℝ))
        Filter.atTop (nhds 0) ∧
      ∀ ℓ : ℝ, 1 ≤ (rho (P ℓ) (Q ℓ) Finset.univ : ℝ) := by
  let : NeZero d := ⟨by omega⟩
  exact ⟨source, target, local_error_tends_to_zero hd, fun ℓ => rho_lower ℓ hd⟩

end

end Obstruction

end HigherOrder.Obstruction

namespace HigherOrder

section CriticalOrder

open scoped NNReal Finset

def admits_uniform_bound (d k : ℕ) : Prop :=
  ∃ K : ℝ≥0, ∀ (n : ℕ) (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n)),
    rho P Q C ≤ K * rho_k P Q C k

theorem lower_order_has_no_uniform_bound {d k : ℕ} (hd : 2 ≤ d) (hk : k ≤ d + 1)
    (K : ℝ≥0) :
    ∃ P Q : Fin (d + 2) → ℝ^[d],
      K * rho_k P Q Finset.univ k < rho P Q Finset.univ := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨ℓ, hℓ⟩ := UniformBounds.exists_violation
    (fun ℓ => rho_k (Obstruction.source ℓ) (Obstruction.target ℓ) Finset.univ k)
    (fun ℓ => rho (Obstruction.source ℓ) (Obstruction.target ℓ) Finset.univ)
    (Obstruction.lower_errors_tend_to_zero hd k hk)
    (fun ℓ => Obstruction.rho_lower ℓ hd) K
  exact ⟨Obstruction.source ℓ, Obstruction.target ℓ, hℓ⟩

theorem admits_uniform_bound_iff {d k : ℕ} (hd : 2 ≤ d) :
    admits_uniform_bound d k ↔ d + 2 ≤ k := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hk
    obtain ⟨P, Q, hbad⟩ := lower_order_has_no_uniform_bound (k := k) hd (by omega) K
    exact (not_lt_of_ge (hK _ P Q Finset.univ)) hbad
  · intro hk
    refine ⟨higher_order_factor d, fun n P Q C => ?_⟩
    exact (rho_le_higher_order_nnreal P Q C).trans
      (mul_le_mul' le_rfl (rho_k_mono P Q C hk))

end CriticalOrder

end HigherOrder
