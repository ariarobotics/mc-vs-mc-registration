import CliqueCertificate.ProperMotion.Basic
import CliqueCertificate.External.LinearAlgebra

/-! Orthogonal differences factor through a skew-symmetric operator. -/

open EuclideanGeometry

namespace Proper

section Reduction

open scoped BigOperators
open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem det_adjoint (A : E →ₗ[ℝ] E) : LinearMap.det A.adjoint = LinearMap.det A := by
  classical
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose, LinearMap.det_toMatrix]

theorem orthogonal_det_one_of_add_injective (R : E ≃ₗᵢ[ℝ] E)
    (hinj : Function.Injective (fun x => x + R x)) : LinearMap.det R.toLinearMap = 1 := by
  let A := LinearMap.id + R.toLinearMap
  have ha : Function.Injective A := hinj
  have hdet : LinearMap.det A ≠ 0 := by
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr ha)
  have hid : R.toLinearMap.comp A.adjoint = A := by
    ext x
    simp only [A, map_add, LinearMap.adjoint_id,
      R.adjoint_toLinearMap_eq_symm, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply, map_add, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, R.apply_symm_apply]
    abel
  have hh := congrArg LinearMap.det hid
  rw [LinearMap.det_comp, det_adjoint] at hh
  exact (mul_eq_right₀ hdet).mp hh

theorem even_neg_one_eigenspace (R : E ≃ₗᵢ[ℝ] E)
    (hR : LinearMap.det R.toLinearMap = 1) :
    Even (Module.finrank ℝ (LinearMap.id + R.toLinearMap).ker) := by
  classical
  let K := (LinearMap.id + R.toLinearMap).ker
  have hneg (x : K) : R x = -(x : E) := by
    have hh := x.property
    change (x : E) + R x = 0 at hh
    exact eq_neg_of_add_eq_zero_right hh
  have hRmem (x : Kᗮ) : R x ∈ Kᗮ := by
    apply (K.mem_orthogonal' _).mpr
    intro y hy
    have hsymm : R.symm y = -y := by
      have hh := hneg ⟨y, hy⟩
      apply R.injective
      simp only [R.apply_symm_apply, map_neg, hh, neg_neg]
    have hh := R.inner_map_map x (R.symm y)
    rw [R.apply_symm_apply, hsymm, inner_neg_right] at hh
    rw [hh, (K.mem_orthogonal' _).mp x.property y hy, neg_zero]
  let L : Kᗮ →ₗᵢ[ℝ] Kᗮ :=
    { toLinearMap := (R.toLinearMap.comp Kᗮ.subtype).codRestrict Kᗮ hRmem
      norm_map' := fun x => R.norm_map x }
  let U := L.toLinearIsometryEquiv rfl
  have hinj : Function.Injective (fun x : Kᗮ => x + U x) := by
    change Function.Injective ((LinearMap.id + U.toLinearMap : Kᗮ →ₗ[ℝ] Kᗮ) : Kᗮ → Kᗮ)
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro x hx
    change x + U x = 0 at hx
    have hxK : (x : E) ∈ K := by
      change (x : E) + R x = 0
      exact congrArg Subtype.val hx
    have hz := (Submodule.mem_left_iff_eq_zero_of_disjoint K.orthogonal_disjoint).mp hxK
    exact hz
  have hUdet := orthogonal_det_one_of_add_injective U hinj
  let e := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  have heq : e.symm.toLinearMap.comp (R.toLinearMap.comp e.toLinearMap) =
      LinearMap.prodMap (-LinearMap.id) U.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change R ((x.1 : E) + (x.2 : E)) = -(x.1 : E) + R x.2
    rw [map_add, hneg]
  have hh := congrArg LinearMap.det heq
  have hconj := LinearMap.det_conj R.toLinearMap e.symm
  simp only [LinearEquiv.symm_symm] at hconj
  have hnegdet : LinearMap.det (-LinearMap.id : K →ₗ[ℝ] K) =
      (-1 : ℝ) ^ Module.finrank ℝ K := by
    rw [show (-LinearMap.id : K →ₗ[ℝ] K) = (-1 : ℝ) • LinearMap.id by ext; simp,
      LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [hconj, LinearMap.det_prodMap, hnegdet,
    hR, hUdet, mul_one] at hh
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hh.symm

theorem exists_orthogonal_skew_structure (heven : Even (Module.finrank ℝ E)) :
    ∃ J : E ≃ₗᵢ[ℝ] E, ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y) := by
  classical
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
  have hcard : Fintype.card (Fin k × Fin 2) = Module.finrank ℝ E := by simp [hk, mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  let b := (stdOrthonormalBasis ℝ E).reindex e.symm
  let D : EuclideanSpace ℝ (Fin k × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin k × Fin 2) :=
    { toFun := fun x => WithLp.toLp 2 (fun i => if i.2 = 0 then -x (i.1, 1) else x (i.1, 0))
      map_add' := by intro x y; ext i; dsimp; split_ifs <;> ring
      map_smul' := by intro c x; ext i; dsimp; split_ifs <;> ring }
  have hnorm (x : EuclideanSpace ℝ (Fin k × Fin 2)) : ‖D x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp [D, Fin.sum_univ_two]
    ring
  let J : E →ₗᵢ[ℝ] E :=
    { toLinearMap := b.repr.symm.toLinearMap.comp (D.comp b.repr.toLinearMap)
      norm_map' := by intro x; simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, b.repr.symm.norm_map, hnorm, b.repr.norm_map] }
  refine ⟨J.toLinearIsometryEquiv rfl, fun x y => ?_⟩
  change inner ℝ (J x) y = -inner ℝ x (J y)
  rw [← b.repr.inner_map_map (J x) y, ← b.repr.inner_map_map x (J y)]
  have hrepr (x : E) : b.repr (J x) = D (b.repr x) := by
    simp [J]
  rw [hrepr, hrepr]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [D, Fin.sum_univ_two]

end Reduction

section Factorization

open scoped BigOperators
open Module EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonal_difference_skew_factor (R : E ≃ₗᵢ[ℝ] E)
    (hR : LinearMap.det R.toLinearMap = 1) :
    ∃ V : E ≃ₗᵢ[ℝ] E, ∃ H : E →ₗ[ℝ] E,
      (∀ x y, inner ℝ (H x) y = -inner ℝ x (H y)) ∧
      ∀ x, V (x - R x) = H x := by
  classical
  let A := LinearMap.id + R.toLinearMap
  let G := A.adjoint.comp A
  have hG : G.IsPositive := A.isPositive_adjoint_comp_self
  let b := hG.isSymmetric.eigenvectorBasis rfl
  let t := hG.isSymmetric.eigenvalues rfl
  have ht (i : Fin (Module.finrank ℝ E)) : 0 ≤ t i := hG.nonneg_eigenvalues rfl i
  have hdiag : G = spectral_diagonal b t := by
    ext x
    apply b.repr.injective
    ext i
    rw [spectral_diagonal_repr]
    exact_mod_cast hG.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i
  have hGapply (x : E) : G x = (2 : ℝ) • x + R x + R.symm x := by
    simp only [G, A, LinearMap.comp_apply, map_add, LinearMap.adjoint_id,
      R.adjoint_toLinearMap_eq_symm, LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      R.symm_apply_apply]
    module
  have hcomm : R.toLinearMap.comp G = G.comp R.toLinearMap := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, hGapply, map_add, map_smul,
      R.apply_symm_apply, R.symm_apply_apply]
  let D := spectral_diagonal b (fun i => (Real.sqrt (t i))⁻¹)
  have hDsym := spectral_diagonal_symmetric b (fun i => (Real.sqrt (t i))⁻¹)
  have hDcomm : R.toLinearMap.comp D = D.comp R.toLinearMap := by
    apply spectral_function_commutes b t (fun z => (Real.sqrt z)⁻¹) R.toLinearMap
    simpa only [← hdiag] using hcomm
  have hDR (x : E) : D (R x) = R (D x) := (LinearMap.congr_fun hDcomm x).symm
  have hDRinv (x : E) : D (R.symm x) = R.symm (D x) := by
    apply R.injective
    rw [← hDR, R.apply_symm_apply, R.apply_symm_apply]
  let B := R.symm.toLinearMap - R.toLinearMap
  have hBskew (x y : E) : inner ℝ (B x) y = -inner ℝ x (B y) := by
    have h1 := R.toLinearMap.adjoint_inner_left y x
    have h2 := R.symm.toLinearMap.adjoint_inner_left y x
    simp only [R.adjoint_toLinearMap_eq_symm, R.symm.adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.symm_symm, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at h1 h2
    simp only [B, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, inner_sub_left, inner_sub_right]
    rw [h1, h2]
    ring
  have hDB (x : E) : D (B x) = B (D x) := by
    simp only [B, LinearMap.sub_apply, map_sub, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, hDR, hDRinv]
  let H₀ := D.comp B
  have hH₀skew (x y : E) : inner ℝ (H₀ x) y = -inner ℝ x (H₀ y) := by
    change inner ℝ (D (B x)) y = -inner ℝ x (D (B y))
    rw [hDsym, hBskew, ← hDB]
  have hAnorm (x : E) : ‖A x‖ ^ 2 = ∑ i, t i * (b.repr x i) ^ 2 :=
    norm_sq_of_diagonal_gram b t A hdiag x
  have hNnorm (x : E) : ‖x - R x‖ ^ 2 = ∑ i, (4 - t i) * (b.repr x i) ^ 2 := by
    have hh : ‖x - R x‖ ^ 2 = 4 * ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
      change ‖x - R x‖ ^ 2 = 4 * ‖x‖ ^ 2 - ‖x + R x‖ ^ 2
      rw [norm_sub_sq_real, norm_add_sq_real, R.norm_map]
      ring
    rw [hh, hAnorm, ← b.repr.norm_map x, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hBnorm (x : E) : ‖B x‖ ^ 2 = ∑ i, t i * (4 - t i) * (b.repr x i) ^ 2 := by
    have hh : ‖B x‖ ^ 2 = 4 * ‖x‖ ^ 2 - ‖R.symm x + R x‖ ^ 2 := by
      change ‖R.symm x - R x‖ ^ 2 = _
      rw [norm_sub_sq_real, norm_add_sq_real, R.norm_map, R.symm.norm_map]
      ring
    have heq : R.symm x + R x = spectral_diagonal b (fun i => t i - 2) x := by
      apply b.repr.injective
      have hsum : R.symm x + R x = G x - (2 : ℝ) • x := by rw [hGapply]; module
      rw [hsum, hdiag]
      ext i
      simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        spectral_diagonal_repr]
      ring
    rw [hh, heq, spectral_diagonal_norm_sq, ← b.repr.norm_map x,
      EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hH₀norm (x : E) : ‖H₀ x‖ ^ 2 =
      ∑ i, t i * (4 - t i) * (Real.sqrt (t i))⁻¹ ^ 2 * (b.repr x i) ^ 2 := by
    change ‖D (B x)‖ ^ 2 = _
    rw [hDB, hBnorm]
    simp only [D, spectral_diagonal_repr, mul_pow]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let K := A.ker
  let proj := spectral_diagonal b (fun i => if t i = 0 then 1 else 0)
  have hKcoef (y : E) (hy : y ∈ K) (i : Fin (Module.finrank ℝ E)) (hi : t i ≠ 0) :
      b.repr y i = 0 := by
    have hzero : G y = 0 := by
      change A.adjoint (A y) = 0
      rw [show A y = 0 from hy, map_zero]
    have hh := congrArg (fun x => b.repr x i) hzero
    rw [hdiag, spectral_diagonal_repr] at hh
    simp only [map_zero, PiLp.zero_apply] at hh
    exact (mul_eq_zero.mp hh).resolve_left hi
  have hprojmem (x : E) : proj x ∈ K := by
    change A (proj x) = 0
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [hAnorm]
    apply Finset.sum_eq_zero
    intro i _
    simp only [proj, spectral_diagonal_repr]
    split_ifs with hi <;> simp [hi]
  have hprojfix (y : E) (hy : y ∈ K) : proj y = y := by
    apply b.repr.injective
    ext i
    simp only [proj, spectral_diagonal_repr]
    by_cases hi : t i = 0
    · simp [hi]
    · simp [hi, hKcoef y hy i hi]
  have hDzero (y : E) (hy : y ∈ K) : D y = 0 := by
    apply b.repr.injective
    ext i
    simp only [D, spectral_diagonal_repr, map_zero, PiLp.zero_apply]
    by_cases hi : t i = 0
    · simp [hi]
    · simp [hKcoef y hy i hi]
  obtain ⟨J, hJ⟩ := exists_orthogonal_skew_structure (even_neg_one_eigenspace R hR)
  let projK : E →ₗ[ℝ] K := proj.codRestrict K hprojmem
  let Z := K.subtype.comp (J.toLinearMap.comp projK)
  have hZmem (x : E) : Z x ∈ K := (J (projK x)).property
  have hZnorm (x : E) : ‖Z x‖ = ‖proj x‖ := J.norm_map (projK x)
  have hprojsym := spectral_diagonal_symmetric b (fun i => if t i = 0 then 1 else 0)
  have hZskew (x y : E) : inner ℝ (Z x) y = -inner ℝ x (Z y) := by
    have hleft : inner ℝ (Z x) y = inner ℝ (Z x) (proj y) := by
      rw [← hprojsym, hprojfix _ (hZmem x)]
    have hright : inner ℝ x (Z y) = inner ℝ (proj x) (Z y) := by
      rw [hprojsym, hprojfix _ (hZmem y)]
    rw [hleft, hright]
    exact hJ (projK x) (projK y)
  have horth (x y : E) : inner ℝ (H₀ x) (Z y) = 0 := by
    change inner ℝ (D (B x)) (Z y) = 0
    rw [hDsym, hDzero _ (hZmem y), inner_zero_right]
  let H := H₀ + (2 : ℝ) • Z
  have hHskew (x y : E) : inner ℝ (H x) y = -inner ℝ x (H y) := by
    simp only [H, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hH₀skew, hZskew]
    ring
  have hHnorm (x : E) : ‖H x‖ = ‖x - R x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hh : ‖H x‖ ^ 2 = ‖H₀ x‖ ^ 2 + 4 * ‖proj x‖ ^ 2 := by
      change ‖H₀ x + (2 : ℝ) • Z x‖ ^ 2 = _
      rw [norm_add_sq_real, inner_smul_right, horth, norm_smul, Real.norm_eq_abs, hZnorm]
      norm_num
      ring
    rw [hh, hH₀norm, spectral_diagonal_norm_sq, Finset.mul_sum,
      ← Finset.sum_add_distrib, hNnorm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t i = 0
    · simp [hi]
    · have hs : (Real.sqrt (t i)) ^ 2 = t i := Real.sq_sqrt (ht i)
      have hs0 : Real.sqrt (t i) ≠ 0 := by
        intro hz
        rw [hz, zero_pow (by decide)] at hs
        exact hi hs.symm
      simp only [hi, ite_false, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, add_zero]
      field_simp
      rw [hs]
      ring
  let N := LinearMap.id - R.toLinearMap
  obtain ⟨V, hV⟩ := orthogonal_factor_of_norm_eq N H (fun x => (hHnorm x).symm)
  exact ⟨V, H, hHskew, hV⟩

end Factorization

end Proper
