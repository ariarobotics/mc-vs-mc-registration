import CliqueCertificate.Definitions

/-! Spectral operators, orthogonal rounding, trace identities, and reflections. -/

namespace EuclideanGeometry

section Spectral

open scoped BigOperators

section Diagonal

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E)

noncomputable def coordinate_diagonal (s : ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ]
    EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => s i * x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

noncomputable def spectral_diagonal (s : ι → ℝ) : E →ₗ[ℝ] E :=
  b.repr.symm.toLinearMap.comp ((coordinate_diagonal s).comp b.repr.toLinearMap)

@[simp] theorem spectral_diagonal_repr (s : ι → ℝ) (x : E) (i : ι) :
    b.repr (spectral_diagonal b s x) i = s i * b.repr x i := by
  simp [spectral_diagonal, coordinate_diagonal]

@[simp] theorem spectral_diagonal_basis (s : ι → ℝ) (i : ι) :
    spectral_diagonal b s (b i) = s i • b i := by
  classical
  apply b.repr.injective
  ext j
  simp [OrthonormalBasis.repr_self]
  split_ifs <;> simp_all

theorem spectral_diagonal_symmetric (s : ι → ℝ) :
    (spectral_diagonal b s).IsSymmetric := by
  intro x y
  rw [← b.repr.inner_map_map (spectral_diagonal b s x) y,
    ← b.repr.inner_map_map x (spectral_diagonal b s y)]
  simp only [PiLp.inner_apply, spectral_diagonal_repr]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem spectral_diagonal_norm_sq (s : ι → ℝ) (x : E) :
    ‖spectral_diagonal b s x‖ ^ 2 = ∑ i, s i ^ 2 * (b.repr x i) ^ 2 := by
  rw [← b.repr.norm_map (spectral_diagonal b s x), EuclideanSpace.real_norm_sq_eq]
  simp [mul_pow]

theorem spectral_diagonal_norm_le (s : ι → ℝ) (hs : ∀ i, |s i| ≤ 1) (x : E) :
    ‖spectral_diagonal b s x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [spectral_diagonal_norm_sq, ← b.repr.norm_map x, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have hsq : s i ^ 2 ≤ 1 := by nlinarith [abs_le.mp (hs i)]
  simpa using mul_le_mul_of_nonneg_right hsq (sq_nonneg (b.repr x i))

theorem spectral_diagonal_positive (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (spectral_diagonal b s).IsPositive := by
  refine ⟨spectral_diagonal_symmetric b s, fun x => ?_⟩
  change 0 ≤ inner ℝ (spectral_diagonal b s x) x
  rw [← b.repr.inner_map_map (spectral_diagonal b s x) x]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, spectral_diagonal_repr]
  apply Finset.sum_nonneg
  intro i _
  nlinarith [mul_nonneg (hs i) (sq_nonneg (b.repr x i))]

end Diagonal

section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonal_factor_of_norm_eq (S T : E →ₗ[ℝ] E)
    (hnorm : ∀ x, ‖S x‖ = ‖T x‖) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ x, R (S x) = T x := by
  have hbound : ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖S x‖ :=
    ⟨1, fun x => by rw [one_mul, hnorm]⟩
  let L := T.compLeftInverse S
  have hL (x : E) : L (S.rangeRestrict x) = T x :=
    T.compLeftInverse_apply_of_bdd S hbound x (S x) rfl
  let J : S.range →ₗᵢ[ℝ] E := { L.toLinearMap with
    norm_map' := by
      intro y
      obtain ⟨x, rfl⟩ := S.surjective_rangeRestrict y
      change ‖L (S.rangeRestrict x)‖ = ‖S x‖
      rw [hL]
      exact (hnorm x).symm }
  refine ⟨J.extend.toLinearIsometryEquiv rfl, fun x => ?_⟩
  exact (J.extend_apply (S.rangeRestrict x)).trans (hL x)

theorem orthogonal_polar_factor (T : E →ₗ[ℝ] E) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E,
    ∃ s : Fin (Module.finrank ℝ E) → ℝ, (∀ i, 0 ≤ s i) ∧
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ x, T x = R (spectral_diagonal b s x) := by
  classical
  let A := T.adjoint.comp T
  have hA : A.IsPositive := T.isPositive_adjoint_comp_self
  let b := hA.isSymmetric.eigenvectorBasis rfl
  let s : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    Real.sqrt (hA.isSymmetric.eigenvalues rfl i)
  let S := spectral_diagonal b s
  have hs (i : Fin (Module.finrank ℝ E)) : s i ^ 2 = hA.isSymmetric.eigenvalues rfl i :=
    Real.sq_sqrt (hA.nonneg_eigenvalues rfl i)
  have hnorm (x : E) : ‖S x‖ = ‖T x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖spectral_diagonal b s x‖ ^ 2 = _
    rw [spectral_diagonal_norm_sq, ← real_inner_self_eq_norm_sq (T x),
      ← T.adjoint_inner_right]
    change (∑ i, s i ^ 2 * (b.repr x i) ^ 2) = inner ℝ x (A x)
    rw [← b.repr.inner_map_map x (A x)]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [show b.repr (A x) i = hA.isSymmetric.eigenvalues rfl i * b.repr x i from
      hA.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i, hs]
    ring
  obtain ⟨R, hR⟩ := orthogonal_factor_of_norm_eq S T hnorm
  exact ⟨b, s, fun i => Real.sqrt_nonneg _, R, fun x => (hR x).symm⟩

theorem orthogonal_rounding (N : E →ₗ[ℝ] E) (hN : ∀ x, ‖N x‖ ≤ ‖x‖) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ x, ‖(2 : ℝ) • N x - R x‖ ≤ ‖x‖ := by
  obtain ⟨b, s, hs, R, hR⟩ := orthogonal_polar_factor N
  have hnorm (i : Fin (Module.finrank ℝ E)) : ‖N (b i)‖ = s i := by
    rw [hR, spectral_diagonal_basis, R.norm_map, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hs i), b.norm_eq_one, mul_one]
  have hsi (i : Fin (Module.finrank ℝ E)) : s i ≤ 1 := by
    have hu := hN (b i)
    rw [hnorm, b.norm_eq_one] at hu
    exact hu
  refine ⟨R, fun x => ?_⟩
  have heq : (2 : ℝ) • N x - R x =
      R (spectral_diagonal b (fun i => 2 * s i - 1) x) := by
    rw [hR]
    have hh : spectral_diagonal b (fun i => 2 * s i - 1) x =
        (2 : ℝ) • spectral_diagonal b s x - x := by
      apply b.repr.injective
      ext i
      simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul, spectral_diagonal_repr]
      ring
    rw [hh, map_sub, map_smul]
  rw [heq, R.norm_map]
  apply spectral_diagonal_norm_le
  intro i
  apply abs_le.mpr
  constructor <;> linarith [hs i, hsi i]

theorem orthogonal_rounding_quadratic (N : E →ₗ[ℝ] E) (hN : ∀ x, ‖N x‖ ≤ ‖x‖) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ x y,
      ‖R x - y‖ ^ 2 ≤
        2 * (‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * inner ℝ (N x) y) := by
  obtain ⟨R, hR⟩ := orthogonal_rounding N hN
  refine ⟨R, fun x y => ?_⟩
  have hinner : inner ℝ ((2 : ℝ) • N x - R x) y ≤ ‖x‖ * ‖y‖ :=
    (real_inner_le_norm _ y).trans (mul_le_mul_of_nonneg_right (hR x) (norm_nonneg y))
  rw [inner_sub_left, real_inner_smul_left] at hinner
  rw [norm_sub_sq_real, R.norm_map]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem orthogonal_positive_trace_maximizer (A : E →ₗ[ℝ] E) :
    ∃ R : E ≃ₗᵢ[ℝ] E, (R.toLinearMap.comp A).IsPositive ∧
      ∀ N : E →ₗ[ℝ] E, (∀ x, ‖N x‖ ≤ ‖x‖) →
      (N.comp A).trace ℝ E ≤ (R.toLinearMap.comp A).trace ℝ E := by
  obtain ⟨b, s, hs, U, hU⟩ := orthogonal_polar_factor A
  have ha (i : Fin (Module.finrank ℝ E)) : A (b i) = s i • U (b i) := by
    rw [hU, spectral_diagonal_basis, map_smul]
  have hcancel (i : Fin (Module.finrank ℝ E)) :
      U.symm.toLinearMap (U (b i)) = b i := U.symm_apply_apply _
  have hpositive : (U.symm.toLinearMap.comp A).IsPositive := by
    have heq : U.symm.toLinearMap.comp A = spectral_diagonal b s := by
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, hU, LinearIsometryEquiv.symm_apply_apply]
    rw [heq]
    exact spectral_diagonal_positive b s hs
  refine ⟨U.symm, hpositive, fun N hN => ?_⟩
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_le_sum
  intro i _
  simp only [LinearMap.comp_apply, ha, map_smul, hcancel, real_inner_smul_right,
    real_inner_self_eq_norm_sq,
    b.norm_eq_one, one_pow, mul_one]
  have hi : inner ℝ (b i) (N (U (b i))) ≤ 1 := by
    calc
      _ ≤ ‖b i‖ * ‖N (U (b i))‖ := real_inner_le_norm _ _
      _ ≤ 1 := by simpa using hN (U (b i))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (hs i)

theorem orthogonal_trace_maximizer (A : E →ₗ[ℝ] E) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ N : E →ₗ[ℝ] E, (∀ x, ‖N x‖ ≤ ‖x‖) →
      (N.comp A).trace ℝ E ≤ (R.toLinearMap.comp A).trace ℝ E := by
  obtain ⟨R, _, hR⟩ := orthogonal_positive_trace_maximizer A
  exact ⟨R, hR⟩

end Polar

end Spectral

section QuadraticAndTrace

open scoped BigOperators

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def quadratic_error (N : E →ₗ[ℝ] E) (x y : E) : ℝ :=
  ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * inner ℝ (N x) y

theorem quadratic_error_nonneg (N : E →ₗ[ℝ] E) (hN : ∀ x, ‖N x‖ ≤ ‖x‖)
    (x y : E) : 0 ≤ quadratic_error N x y := by
  have h := (real_inner_le_norm (N x) y).trans
    (mul_le_mul_of_nonneg_right (hN x) (norm_nonneg y))
  dsimp [quadratic_error]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem quadratic_error_orthogonal (R : E ≃ₗᵢ[ℝ] E) (x y : E) :
    quadratic_error R.toLinearMap x y = ‖R x - y‖ ^ 2 := by
  rw [norm_sub_sq_real, R.norm_map]
  simp only [quadratic_error, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  ring

theorem quadratic_error_homogeneous (N : E →ₗ[ℝ] E) (c : ℝ) (x y : E) :
    quadratic_error N (c • x) (c • y) = c ^ 2 * quadratic_error N x y := by
  simp only [quadratic_error, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem quadratic_error_add (N : E →ₗ[ℝ] E) (x y u v : E) :
    quadratic_error N (x + u) (y + v) = quadratic_error N x y + quadratic_error N u v +
      2 * (inner ℝ x u + inner ℝ y v - inner ℝ (N x) v - inner ℝ (N u) y) := by
  simp only [quadratic_error, norm_add_sq_real, map_add, inner_add_left, inner_add_right]
  ring

theorem quadratic_error_mix (N : E →ₗ[ℝ] E) (x y u v : E) (a b : ℝ)
    (hab : a + b = 1) :
    quadratic_error N (a • x + b • u) (a • y + b • v) =
      a * quadratic_error N x y + b * quadratic_error N u v -
        a * b * quadratic_error N (x - u) (y - v) := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  simp only [quadratic_error, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right, map_add, map_smul,
    inner_add_left, inner_add_right, norm_sub_sq_real, map_sub, inner_sub_left, inner_sub_right]
  ring

end Quadratic

section Trace

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def cross_covariance (x y : ι → E) : E →ₗ[ℝ] E :=
  ∑ i, (InnerProductSpace.rankOne ℝ (x i) (y i)).toLinearMap

theorem trace_cross_covariance (x y : ι → E) (N : E →ₗ[ℝ] E) :
    (N.comp (cross_covariance x y)).trace ℝ E = ∑ i, inner ℝ (N (x i)) (y i) := by
  have hcomp (u v : E) : N.comp (InnerProductSpace.rankOne ℝ u v).toLinearMap =
      (InnerProductSpace.rankOne ℝ (N u) v).toLinearMap := by
    ext z
    simp [InnerProductSpace.rankOne_apply]
  have hsum : N.comp (cross_covariance x y) =
      ∑ i, N.comp (InnerProductSpace.rankOne ℝ (x i) (y i)).toLinearMap := by
    ext z
    simp [cross_covariance]
  rw [hsum, map_sum]
  simp only [hcomp, InnerProductSpace.trace_rankOne, real_inner_comm]

theorem orthogonal_pairing_maximizer (x y : ι → E) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ N : E →ₗ[ℝ] E, (∀ u, ‖N u‖ ≤ ‖u‖) →
      (∑ i, inner ℝ (N (x i)) (y i)) ≤ ∑ i, inner ℝ (R (x i)) (y i) := by
  obtain ⟨R, hR⟩ := orthogonal_trace_maximizer (cross_covariance x y)
  refine ⟨R, fun N hN => ?_⟩
  simpa only [trace_cross_covariance, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    using hR N hN

theorem orthogonal_quadratic_minimizer (x y : ι → E) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ N : E →ₗ[ℝ] E, (∀ u, ‖N u‖ ≤ ‖u‖) →
      (∑ i, ‖R (x i) - y i‖ ^ 2) ≤ ∑ i, quadratic_error N (x i) (y i) := by
  obtain ⟨R, hR⟩ := orthogonal_pairing_maximizer x y
  refine ⟨R, fun N hN => ?_⟩
  have h := hR N hN
  simp only [norm_sub_sq_real, R.norm_map, quadratic_error, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end Trace

end QuadraticAndTrace

section FunctionalCalculus

open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem spectral_function_commutes (b : OrthonormalBasis ι ℝ E) (t : ι → ℝ)
    (f : ℝ → ℝ) (X : E →ₗ[ℝ] E)
    (hcomm : X.comp (EuclideanGeometry.spectral_diagonal b t) =
      (EuclideanGeometry.spectral_diagonal b t).comp X) :
    X.comp (EuclideanGeometry.spectral_diagonal b (fun i => f (t i))) =
      (EuclideanGeometry.spectral_diagonal b (fun i => f (t i))).comp X := by
  apply b.toBasis.ext
  intro j
  apply b.repr.injective
  ext i
  change b.repr (X (EuclideanGeometry.spectral_diagonal b (fun i => f (t i)) (b j))) i =
    b.repr (EuclideanGeometry.spectral_diagonal b (fun i => f (t i)) (X (b j))) i
  have hh := congrArg (fun x => b.repr x i) (LinearMap.congr_fun hcomm (b j))
  simp only [LinearMap.comp_apply, EuclideanGeometry.spectral_diagonal_basis, map_smul,
    EuclideanGeometry.spectral_diagonal_repr, PiLp.smul_apply, smul_eq_mul] at hh ⊢
  by_cases hij : t i = t j
  · rw [hij]
  · have hz : b.repr (X (b j)) i = 0 := by
      apply (mul_eq_zero.mp (show (t j - t i) * b.repr (X (b j)) i = 0 by nlinarith)).resolve_left
      exact sub_ne_zero.mpr (Ne.symm hij)
    rw [hz, mul_zero, mul_zero]

theorem norm_sq_of_diagonal_gram (b : OrthonormalBasis ι ℝ E) (t : ι → ℝ)
    (X : E →ₗ[ℝ] E) (hGram : X.adjoint.comp X = EuclideanGeometry.spectral_diagonal b t)
    (x : E) : ‖X x‖ ^ 2 = ∑ i, t i * (b.repr x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← X.adjoint_inner_right]
  change inner ℝ x (X.adjoint.comp X x) = _
  rw [hGram, ← b.repr.inner_map_map x (EuclideanGeometry.spectral_diagonal b t x)]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    EuclideanGeometry.spectral_diagonal_repr]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [FiniteDimensional ℝ E] in

theorem spectral_diagonal_comp (b : OrthonormalBasis ι ℝ E) (s t : ι → ℝ) :
    (EuclideanGeometry.spectral_diagonal b s).comp (EuclideanGeometry.spectral_diagonal b t) =
      EuclideanGeometry.spectral_diagonal b (fun i => s i * t i) := by
  ext x
  apply b.repr.injective
  ext i
  simp only [LinearMap.comp_apply, EuclideanGeometry.spectral_diagonal_repr]
  ring

end FunctionalCalculus

section Reflections

open scoped NNReal

variable {d : ℕ}

noncomputable def linear_reflection (v : ℝ^[d]) : O(d) :=
  Submodule.reflection (ℝ ∙ v)ᗮ

theorem linear_reflection_apply (v x : ℝ^[d]) :
    linear_reflection v x = x - (2 * inner ℝ v x / ‖v‖ ^ 2) • v := by
  rw [linear_reflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  module

theorem linear_reflection_fixed (v x : ℝ^[d]) (h : inner ℝ v x = 0) :
    linear_reflection v x = x := by
  simp [linear_reflection_apply, h]

noncomputable def hyperplane_reflection (v : ℝ^[d]) (b : ℝ) : E(d) :=
  (linear_reflection v).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ ((2 * b / ‖v‖ ^ 2) • v))

theorem hyperplane_reflection_apply (v x : ℝ^[d]) (b : ℝ) :
    hyperplane_reflection v b x = x - (2 * (inner ℝ v x - b) / ‖v‖ ^ 2) • v := by
  change linear_reflection v x + (2 * b / ‖v‖ ^ 2) • v = _
  rw [linear_reflection_apply]
  module

theorem hyperplane_reflection_fixed (v x : ℝ^[d]) (b : ℝ) (h : inner ℝ v x = b) :
    hyperplane_reflection v b x = x := by
  simp [hyperplane_reflection_apply, h]

theorem hyperplane_reflection_displacement (v x : ℝ^[d]) (b : ℝ) (hv : v ≠ 0) :
    ‖hyperplane_reflection v b x - x‖ = 2 * |inner ℝ v x - b| / ‖v‖ := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [hyperplane_reflection_apply, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg ‖v‖)]
  field_simp

theorem linear_reflection_displacement (v x : ℝ^[d]) (hv : v ≠ 0) :
    ‖linear_reflection v x - x‖ = 2 * |inner ℝ v x| / ‖v‖ := by
  simpa [hyperplane_reflection] using hyperplane_reflection_displacement v x 0 hv

theorem norm_sub_projection_le (v x : ℝ^[d]) (c : ℝ) :
    ‖x - (inner ℝ v x / ‖v‖ ^ 2) • v‖ ≤ ‖x - c • v‖ := by
  have hp : (ℝ ∙ v).starProjection x = (inner ℝ v x / ‖v‖ ^ 2) • v := by
    simpa using Submodule.starProjection_singleton ℝ (v := v) x
  rw [← hp, Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    (⟨c • v, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩ : ℝ ∙ v)

end Reflections

end EuclideanGeometry
