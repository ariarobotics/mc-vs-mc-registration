import CliqueCertificate.HigherOrder.WeightedFit

/-! The orthonormal length-difference decomposition (Lemma 3). -/

open EuclideanGeometry

namespace HigherOrder

open scoped BigOperators

section Compatible

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem compatible_positive_factor (A G : V →ₗ[ℝ] E)
    (hpositive : (A.comp G.adjoint).IsPositive) :
    ∃ H : A.kerᗮ →ₗ[ℝ] A.kerᗮ, H.IsPositive ∧
      ∀ x : A.kerᗮ, G x = A (H x) := by
  classical
  let M := A.kerᗮ
  let B := A.comp M.subtype
  have hcomm : A.comp G.adjoint = G.comp A.adjoint := by
    have hh := hpositive.adjoint_eq
    simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] using hh.symm
  have hrange : B.range = A.range := by
    apply le_antisymm
    · exact LinearMap.range_comp_le_range _ _
    · rintro y ⟨x, rfl⟩
      have hker : x - M.starProjection x ∈ A.ker := by
        simpa only [M, Submodule.orthogonal_orthogonal] using
          M.sub_starProjection_mem_orthogonal x
      have heq : A (M.starProjection x) = A x := by
        have hh := hker
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hh
        exact hh.symm
      exact ⟨M.orthogonalProjectionOnto x, heq⟩
  have hinj : Function.Injective B := by
    intro x y hxy
    apply Subtype.ext
    have hk : (x : V) - y ∈ A.ker := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hxy
    have hm : (x : V) - y ∈ A.kerᗮ := M.sub_mem x.property y.property
    have hzero : (x : V) - y = 0 := by
      have hh := A.ker.orthogonal_disjoint.le_bot ⟨hk, hm⟩
      simpa using hh
    exact sub_eq_zero.mp hzero
  have hG (x : M) : G x ∈ B.range := by
    rw [hrange, ← A.range.orthogonal_orthogonal]
    apply (A.rangeᗮ.mem_orthogonal _).mpr
    intro y hy
    have hay : A.adjoint y = 0 := by
      simpa only [A.orthogonal_range, LinearMap.mem_ker] using hy
    have hgy : G.adjoint y ∈ A.ker := by
      rw [LinearMap.mem_ker]
      have hh := congrArg (fun L : E →ₗ[ℝ] E => L y) hcomm
      simpa [hay] using hh
    rw [← G.adjoint_inner_left]
    exact (A.ker.mem_orthogonal _).mp x.property _ hgy
  let e := LinearEquiv.ofInjective B hinj
  let H := e.symm.toLinearMap.comp ((G.comp M.subtype).codRestrict B.range hG)
  have hH (x : M) : A (H x) = G x := by
    have hh := e.apply_symm_apply (⟨G x, hG x⟩ : B.range)
    exact congrArg Subtype.val hh
  have hpre (x : M) : ∃ y : E, A.adjoint y = x := by
    have hx : (x : V) ∈ A.kerᗮ := x.property
    rw [A.orthogonal_ker] at hx
    exact hx
  have hsym : H.IsSymmetric := by
    intro x y
    obtain ⟨u, hu⟩ := hpre x
    obtain ⟨v, hv⟩ := hpre y
    change inner ℝ (H x : V) (y : V) = inner ℝ (x : V) (H y : V)
    rw [← hv, A.adjoint_inner_right, hH, ← hu, A.adjoint_inner_left, hH]
    have hh := hpositive.isSymmetric u v
    rw [hcomm] at hh
    simpa only [LinearMap.comp_apply, hu, hv] using hh
  refine ⟨H, ⟨hsym, ?_⟩, fun x => (hH x).symm⟩
  intro x
  obtain ⟨y, hy⟩ := hpre x
  change 0 ≤ inner ℝ (H x : V) (x : V)
  rw [← hy, A.adjoint_inner_right, hH]
  have hh := hpositive.inner_nonneg_left y
  rw [hcomm] at hh
  simpa only [LinearMap.comp_apply, hy] using hh

abbrev CompatibleIndex (A : V →ₗ[ℝ] E) :=
  Fin (Module.finrank ℝ A.kerᗮ) ⊕ Fin (Module.finrank ℝ A.ker)

theorem compatible_orthonormal_basis (A G : V →ₗ[ℝ] E)
    (hpositive : (A.comp G.adjoint).IsPositive) :
    ∃ b : OrthonormalBasis (CompatibleIndex A) ℝ V,
      (∀ i, A (b i) = 0 ∨ ∃ μ : ℝ, 0 ≤ μ ∧ G (b i) = μ • A (b i)) ∧
      (∀ i w, A w = 0 → G w = 0 →
        (A (b i) ≠ 0 ∨ G (b i) ≠ 0) → inner ℝ (b i) w = 0) := by
  classical
  let U := A.kerᗮ
  let W := A.ker
  obtain ⟨H, hH, hGH⟩ := compatible_positive_factor A G hpositive
  let bU := hH.isSymmetric.eigenvectorBasis rfl
  let G' := G.comp W.subtype
  let S := G'.adjoint.comp G'
  have hS : S.IsPositive := G'.isPositive_adjoint_comp_self
  let bW := hS.isSymmetric.eigenvectorBasis rfl
  let J := Fin (Module.finrank ℝ U) ⊕ Fin (Module.finrank ℝ W)
  let v : J → V := Sum.elim (fun i => (bU i : V)) (fun i => (bW i : V))
  let bW' := bW.map
    (LinearIsometryEquiv.ofEq W Wᗮᗮ (Submodule.orthogonal_orthogonal W).symm)
  let basis := (bU.prod bW').map Wᗮ.orthogonalDecomposition.symm
  have basis_apply (i : J) : basis i = v i := by
    cases i <;> simp [basis, v, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply,
      Submodule.orthogonalDecomposition_symm_apply, bW']
  have hparallel (i : J) : A (v i) = 0 ∨ ∃ μ : ℝ, 0 ≤ μ ∧ G (v i) = μ • A (v i) := by
    cases i with
    | inl i =>
      right
      refine ⟨hH.isSymmetric.eigenvalues rfl i, hH.nonneg_eigenvalues rfl i, ?_⟩
      have he := hH.isSymmetric.apply_eigenvectorBasis rfl i
      have hg := hGH (bU i)
      rw [show H (bU i) = hH.isSymmetric.eigenvalues rfl i • bU i from he] at hg
      simpa only [v, Sum.elim_inl, SetLike.val_smul, map_smul] using hg
    | inr i => exact Or.inl (bW i).property
  have hkernel (i : J) (w : V) (haw : A w = 0) (hgw : G w = 0)
      (hi : A (v i) ≠ 0 ∨ G (v i) ≠ 0) : inner ℝ (v i) w = 0 := by
    cases i with
    | inl i => exact (W.mem_orthogonal' _).mp (bU i).property w haw
    | inr i =>
      have hai : A (v (Sum.inr i)) = 0 := (bW i).property
      have hgi : G (v (Sum.inr i)) ≠ 0 := hi.resolve_left (not_not.mpr hai)
      let w' : W := ⟨w, haw⟩
      have hzero : S w' = 0 := by simp [S, G', w', hgw]
      have hei : S (bW i) = hS.isSymmetric.eigenvalues rfl i • bW i := by
        exact_mod_cast hS.isSymmetric.apply_eigenvectorBasis rfl i
      have hEig : hS.isSymmetric.eigenvalues rfl i ≠ 0 := by
        intro hz
        have hnorm : ‖G' (bW i)‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq, ← G'.adjoint_inner_right]
          change inner ℝ (bW i) (S (bW i)) = 0
          rw [hei, hz, zero_smul, inner_zero_right]
        have hh : G' (bW i) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
        exact hgi hh
      have hh := hS.isSymmetric (bW i) w'
      rw [hei, hzero, inner_zero_right, real_inner_smul_left] at hh
      exact (mul_eq_zero.mp hh).resolve_left hEig
  refine ⟨basis, ?_, ?_⟩
  · simpa only [basis_apply] using hparallel
  · simpa only [basis_apply] using hkernel

noncomputable def frobenius_sq (L : V →ₗ[ℝ] E) : ℝ :=
  (L.adjoint.comp L).trace ℝ V

theorem frobenius_sq_eq_sum {ι : Type*} [Fintype ι] (L : V →ₗ[ℝ] E)
    (b : OrthonormalBasis ι ℝ V) : frobenius_sq L = ∑ i, ‖L (b i)‖ ^ 2 := by
  rw [frobenius_sq, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.comp_apply, L.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem compatible_trace_decomposition (A G : V →ₗ[ℝ] E)
    (hpositive : (A.comp G.adjoint).IsPositive) :
    ∃ b : OrthonormalBasis (CompatibleIndex A) ℝ V,
    ∃ I : Finset (CompatibleIndex A), I.card ≤ 2 * Module.finrank ℝ E ∧
      frobenius_sq (A - G) = ∑ i ∈ I, (‖A (b i)‖ - ‖G (b i)‖) ^ 2 ∧
      ∀ i ∈ I, ∀ w, A w = 0 → G w = 0 → inner ℝ (b i) w = 0 := by
  classical
  obtain ⟨b, hparallel, hkernel⟩ := compatible_orthonormal_basis A G hpositive
  let I := Finset.univ.filter fun i => A (b i) ≠ 0 ∨ G (b i) ≠ 0
  let K := A.ker ⊓ G.ker
  have hmem (i : I) : b i ∈ Kᗮ := by
    apply (K.mem_orthogonal' _).mpr
    intro w hw
    exact hkernel i w hw.1 hw.2 (Finset.mem_filter.mp i.property).2
  let f : I → Kᗮ := fun i => ⟨b i, hmem i⟩
  have hf : Orthonormal ℝ f := by
    have hh := b.orthonormal.comp (fun i : I => i.val) Subtype.val_injective
    exact hh
  have hcard : I.card ≤ Module.finrank ℝ Kᗮ := by
    simpa only [Fintype.card_coe] using hf.linearIndependent.fintype_card_le_finrank
  have hrank : Module.finrank ℝ Kᗮ ≤ 2 * Module.finrank ℝ E := by
    let L := A.prod G
    have hker : L.ker = K := by ext x; simp [L, K]
    have hr := L.finrank_range_add_finrank_ker
    have hk := K.finrank_add_finrank_orthogonal
    have hdim := Submodule.finrank_le L.range
    rw [hker] at hr
    rw [Module.finrank_prod] at hdim
    omega
  have hnorm (i : CompatibleIndex A) :
      ‖A (b i) - G (b i)‖ ^ 2 = (‖A (b i)‖ - ‖G (b i)‖) ^ 2 := by
    rcases hparallel i with hz | ⟨μ, hμ, heq⟩
    · simp [hz]
    · rw [heq]
      have he : A (b i) - μ • A (b i) = (1 - μ) • A (b i) := by module
      rw [he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hμ, mul_pow, sq_abs]
      ring
  refine ⟨b, I, hcard.trans hrank, ?_, ?_⟩
  · rw [frobenius_sq_eq_sum _ b]
    simp only [LinearMap.sub_apply, hnorm]
    apply (Finset.sum_subset (Finset.subset_univ I) _).symm
    intro i _ hi
    have hzero : A (b i) = 0 ∧ G (b i) = 0 := by
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] using hi
    simp [hzero.1, hzero.2]
  · intro i hi w haw hgw
    exact hkernel i w haw hgw (Finset.mem_filter.mp hi).2

end Compatible

section Weighted

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

@[simp] theorem centered_map_single (w : C → ℝ) (i : C) :
    centered_map P C w (EuclideanSpace.single i 1) = centered_columns P C w i := by
  classical
  simp [centered_map]

theorem centered_map_adjoint (w : C → ℝ) (y : ℝ^[d]) (i : C) :
    (centered_map P C w).adjoint y i = inner ℝ (centered_columns P C w i) y := by
  have hh := (centered_map P C w).adjoint_inner_right (EuclideanSpace.single i 1) y
  simpa [EuclideanSpace.inner_single_left] using hh

theorem centered_cross_covariance (w : C → ℝ) :
    (centered_map P C w).comp (centered_map Q C w).adjoint =
      cross_covariance (centered_columns P C w) (centered_columns Q C w) := by
  apply LinearMap.ext
  intro y
  change (∑ i, (centered_map Q C w).adjoint y i • centered_columns P C w i) = _
  simp only [centered_map_adjoint]
  simp [cross_covariance, InnerProductSpace.rankOne_apply]

theorem centered_frobenius_sq (w : C → ℝ) (R : O(d)) :
    frobenius_sq (R.toLinearMap.comp (centered_map P C w) - centered_map Q C w) =
      centered_squared_error P Q C w R := by
  rw [frobenius_sq_eq_sum _ (EuclideanSpace.basisFun C ℝ)]
  simp only [EuclideanSpace.basisFun_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    centered_map_single, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  simp only [centered_columns, map_smul, ← smul_sub, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, centered_squared_error]

theorem centered_map_weight_zero (w : C → ℝ) (hw : w ∈ unit_weights C) :
    centered_map P C w (WithLp.toLp 2 w) = 0 := by
  have hsum : ∑ i, w i ^ 2 = 1 := hw
  change (∑ i : C, w i • (w i • (P i - weighted_mean P C w))) = 0
  simp only [smul_smul, ← pow_two, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hsum, one_smul]
  exact sub_self _

theorem centered_squared_error_eq_constant_sub_trace (w : C → ℝ) (R : O(d)) :
    centered_squared_error P Q C w R =
      (∑ i, (‖centered_columns P C w i‖ ^ 2 + ‖centered_columns Q C w i‖ ^ 2)) -
        2 * (R.toLinearMap.comp
          ((centered_map P C w).comp (centered_map Q C w).adjoint)).trace ℝ (ℝ^[d]) := by
  rw [centered_cross_covariance P Q C w, trace_cross_covariance,
    ← centered_frobenius_sq P Q C w R,
    frobenius_sq_eq_sum _ (EuclideanSpace.basisFun C ℝ)]
  simp only [EuclideanSpace.basisFun_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    centered_map_single, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    norm_sub_sq_real, R.norm_map, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

structure ProcrustesDecomposition (w : C → ℝ) where
  Index : Type
  [finite : Fintype Index]
  vector : Index → EuclideanSpace ℝ C
  orthonormal : Orthonormal ℝ vector
  card_bound : Fintype.card Index ≤ 2 * d
  annihilates_weights : ∀ j, inner ℝ (vector j) (WithLp.toLp 2 w) = 0
  energy_identity : weighted_error P Q C w = ∑ j,
    (‖centered_map P C w (vector j)‖ - ‖centered_map Q C w (vector j)‖) ^ 2

attribute [instance] ProcrustesDecomposition.finite

/-- Lemma 3: at most 2d orthonormal directions represent the weighted error. -/
theorem weighted_procrustes_decomposition (w : C → ℝ) (hw : w ∈ unit_weights C) :
    Nonempty (ProcrustesDecomposition P Q C w) := by
  classical
  let F := centered_map P C w
  let G := centered_map Q C w

  obtain ⟨R, positive_covariance, maximizes_trace⟩ :=
    orthogonal_positive_trace_maximizer (F.comp G.adjoint)
  have positive_covariance' : ((R.toLinearMap.comp F).comp G.adjoint).IsPositive := by
    simpa only [LinearMap.comp_assoc] using positive_covariance
  have minimizes_error (U : O(d)) :
      centered_squared_error P Q C w R ≤ centered_squared_error P Q C w U := by
    have trace_bound := maximizes_trace U.toLinearMap (by intro x; simp)
    rw [centered_squared_error_eq_constant_sub_trace,
      centered_squared_error_eq_constant_sub_trace]
    dsimp [F, G] at trace_bound
    linarith
  have optimal_energy := weighted_error_eq_of_centered_minimizer P Q C w hw R minimizes_error

  obtain ⟨basis, directions, card_bound, energy_identity, annihilates_kernel⟩ :=
    compatible_trace_decomposition (R.toLinearMap.comp F) G positive_covariance'
  refine ⟨{
    Index := directions
    vector := fun j => basis j
    orthonormal := basis.orthonormal.comp (fun j : directions => j.val) Subtype.val_injective
    card_bound := ?_
    annihilates_weights := ?_
    energy_identity := ?_
  }⟩
  · simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using card_bound
  · intro j
    apply annihilates_kernel j j.property
    · simp only [LinearMap.comp_apply, F, centered_map_weight_zero P C w hw, map_zero]
    · exact centered_map_weight_zero Q C w hw
  · rw [optimal_energy, ← centered_frobenius_sq P Q C w R]
    change frobenius_sq (R.toLinearMap.comp F - G) = _
    rw [energy_identity]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, R.norm_map, F, G] using
      (Finset.sum_coe_sort directions (fun i => (‖F (basis i)‖ - ‖G (basis i)‖) ^ 2)).symm

end Weighted

end HigherOrder
