import CliqueCertificate.Basic
import CliqueCertificate.External.Variance
import CliqueCertificate.External.LinearAlgebra

/-! Weighted fitting and the duality-gap bound (Lemma 2). -/

open EuclideanGeometry

namespace HigherOrder

section Definitions

open scoped NNReal Finset

variable {n d : ℕ}

def unit_weights (C : Finset (Fin n)) : Set (C → ℝ) := {w | ∑ i, w i ^ 2 = 1}

noncomputable def weighted_mean (P : Fin n → ℝ^[d]) (C : Finset (Fin n))
    (w : C → ℝ) : ℝ^[d] := ∑ i, w i ^ 2 • P i

noncomputable def weighted_squared_error (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (w : C → ℝ) (T : E(d)) : ℝ :=
  ∑ i, w i ^ 2 * ‖T (P i) - Q i‖ ^ 2

noncomputable def weighted_error (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))
    (w : C → ℝ) : ℝ := ⨅ T : E(d), weighted_squared_error P Q C w T

noncomputable def maximum_weighted_error (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) : ℝ := ⨆ (w : C → ℝ) (_ : w ∈ unit_weights C),
  weighted_error P Q C w

noncomputable def centered_squared_error (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (w : C → ℝ) (R : O(d)) : ℝ :=
  ∑ i, w i ^ 2 * ‖R (P i - weighted_mean P C w) - (Q i - weighted_mean Q C w)‖ ^ 2

noncomputable def centered_columns (P : Fin n → ℝ^[d]) (C : Finset (Fin n))
    (w : C → ℝ) (i : C) : ℝ^[d] := w i • (P i - weighted_mean P C w)

noncomputable def centered_map (P : Fin n → ℝ^[d]) (C : Finset (Fin n))
    (w : C → ℝ) : EuclideanSpace ℝ C →ₗ[ℝ] ℝ^[d] where
  toFun v := ∑ i, v i • centered_columns P C w i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, ← Finset.smul_sum]

variable (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

noncomputable def squared_distance_error : ℝ≥0 := ⨆ (i : C) (j : C),
  ⟨|‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2|, abs_nonneg _⟩

noncomputable def cloud_diameter : ℝ≥0 := ⨆ (i : C) (j : C), ‖P i - P j‖₊

noncomputable def combined_diameter : ℝ≥0 := cloud_diameter P C + cloud_diameter Q C

end Definitions

section WeightedError

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem weighted_squared_error_nonneg (w : C → ℝ) (T : E(d)) :
    0 ≤ weighted_squared_error P Q C w T :=
  Finset.sum_nonneg fun _i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weighted_error_nonneg (w : C → ℝ) : 0 ≤ weighted_error P Q C w :=
  le_ciInf fun T => weighted_squared_error_nonneg P Q C w T

theorem weighted_error_le (w : C → ℝ) (T : E(d)) :
    weighted_error P Q C w ≤ weighted_squared_error P Q C w T :=
  ciInf_le ⟨0, by rintro _ ⟨T, rfl⟩; exact weighted_squared_error_nonneg P Q C w T⟩ T

theorem centered_squared_error_nonneg (w : C → ℝ) (R : O(d)) :
    0 ≤ centered_squared_error P Q C w R :=
  Finset.sum_nonneg fun _i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weighted_centering_identity (w : C → ℝ) (hw : w ∈ unit_weights C)
    (R : O(d)) (t : ℝ^[d]) :
    (∑ i : C, w i ^ 2 * ‖R (P i) + t - Q i‖ ^ 2) =
      centered_squared_error P Q C w R +
        ‖t - (weighted_mean Q C w - R (weighted_mean P C w))‖ ^ 2 := by
  let μ : C → ℝ^[d] := fun i => Q i - R (P i)
  let weights : C → ℝ := fun i => w i ^ 2
  have hweights : ∑ i, weights i = 1 := hw
  have hc : TranslationGeometry.weightedCenter μ weights =
      weighted_mean Q C w - R (weighted_mean P C w) := by
    simp [TranslationGeometry.weightedCenter, μ, weights, weighted_mean,
      smul_sub, Finset.sum_sub_distrib, map_sum, map_smul]
  have hres (i : C) : ‖R (P i) + t - Q i‖ = ‖μ i - t‖ := by
    rw [show R (P i) + t - Q i = -(μ i - t) by dsimp [μ]; module, norm_neg]
  have hcent (i : C) :
      ‖R (P i - weighted_mean P C w) - (Q i - weighted_mean Q C w)‖ =
        ‖μ i - TranslationGeometry.weightedCenter μ weights‖ := by
    rw [show R (P i - weighted_mean P C w) - (Q i - weighted_mean Q C w) =
        -(μ i - TranslationGeometry.weightedCenter μ weights) by
      rw [map_sub, hc]; dsimp [μ]; module, norm_neg]
  have ht := TranslationGeometry.weightedVariance_identity μ weights hweights t
  have hmean := TranslationGeometry.weightedVariance_identity μ weights hweights
    (TranslationGeometry.weightedCenter μ weights)
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero] at hmean
  simp only [hres, centered_squared_error, hcent]
  rw [← hc, norm_sub_rev]
  rw [← hmean] at ht
  exact ht

theorem optimal_translation (w : C → ℝ) (hw : w ∈ unit_weights C) (R : O(d)) :
    weighted_squared_error P Q C w
      (R.toAffineIsometryEquiv.trans
        (AffineIsometryEquiv.vaddConst ℝ (weighted_mean Q C w - R (weighted_mean P C w)))) =
      centered_squared_error P Q C w R := by
  change (∑ i : C, w i ^ 2 *
    ‖R (P i) + (weighted_mean Q C w - R (weighted_mean P C w)) - Q i‖ ^ 2) = _
  rw [weighted_centering_identity P Q C w hw]
  simp

theorem weighted_error_eq_procrustes (w : C → ℝ) (hw : w ∈ unit_weights C) :
    weighted_error P Q C w = ⨅ R : O(d), centered_squared_error P Q C w R := by
  apply le_antisymm
  · apply le_ciInf
    intro R
    rw [← optimal_translation P Q C w hw R]
    exact weighted_error_le P Q C w _
  · apply le_ciInf
    intro T
    have hpoint (i : C) : T (P i) = T.linearIsometryEquiv (P i) + T 0 := by
      have hh : T.linearIsometryEquiv (P i) = T (P i) - T 0 := by
        simpa using T.map_vsub (P i) 0
      exact (eq_sub_iff_add_eq.mp hh).symm
    have heq : weighted_squared_error P Q C w T =
        centered_squared_error P Q C w T.linearIsometryEquiv +
          ‖T 0 - (weighted_mean Q C w - T.linearIsometryEquiv (weighted_mean P C w))‖ ^ 2 := by
      simp only [weighted_squared_error, hpoint]
      exact weighted_centering_identity P Q C w hw _ _
    rw [heq]
    exact (ciInf_le ⟨0, by
      rintro _ ⟨R, rfl⟩; exact centered_squared_error_nonneg P Q C w R⟩
      T.linearIsometryEquiv).trans (le_add_of_nonneg_right (sq_nonneg _))

theorem weighted_error_eq_of_centered_minimizer (w : C → ℝ) (hw : w ∈ unit_weights C)
    (R : O(d))
    (hmin : ∀ U, centered_squared_error P Q C w R ≤ centered_squared_error P Q C w U) :
    weighted_error P Q C w = centered_squared_error P Q C w R := by
  rw [weighted_error_eq_procrustes P Q C w hw]
  exact le_antisymm
    (ciInf_le ⟨0, by rintro _ ⟨U, rfl⟩; exact centered_squared_error_nonneg P Q C w U⟩ R)
    (le_ciInf hmin)

theorem weighted_error_lower_bound (w : C → ℝ) (hw : w ∈ unit_weights C) {b : ℝ}
    (h : ∀ R, b ≤ centered_squared_error P Q C w R) : b ≤ weighted_error P Q C w := by
  rw [weighted_error_eq_procrustes P Q C w hw]
  exact le_ciInf h

theorem weighted_error_le_rho_sq (w : C → ℝ) (hw : w ∈ unit_weights C) :
    weighted_error P Q C w ≤ (rho P Q C : ℝ) ^ 2 := by
  obtain ⟨T, best_fit⟩ := exists_best_fit P Q C
  apply (weighted_error_le P Q C w T).trans
  calc
    _ ≤ ∑ i : C, w i ^ 2 * (rho P Q C : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      exact best_fit i i.property
    _ = _ := by rw [← Finset.sum_mul, (show ∑ i, w i ^ 2 = 1 from hw), one_mul]

theorem maximum_weighted_error_le {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ w, w ∈ unit_weights C → weighted_error P Q C w ≤ b) :
    maximum_weighted_error P Q C ≤ b := by
  apply ciSup_le
  intro w
  by_cases hw : w ∈ unit_weights C
  · rw [ciSup_pos hw]
    exact h w hw
  · simpa only [hw, iSup_of_empty', Real.sSup_empty] using hb

theorem maximum_weighted_error_le_rho_sq :
    maximum_weighted_error P Q C ≤ (rho P Q C : ℝ) ^ 2 :=
  maximum_weighted_error_le P Q C (sq_nonneg _) (weighted_error_le_rho_sq P Q C)

private theorem weighted_errors_bddAbove :
    BddAbove (Set.range fun w : C → ℝ =>
      ⨆ (_ : w ∈ unit_weights C), weighted_error P Q C w) := by
  refine ⟨(rho P Q C : ℝ) ^ 2, ?_⟩
  rintro _ ⟨w, rfl⟩
  by_cases normalized : w ∈ unit_weights C
  · simpa only [ciSup_pos normalized] using weighted_error_le_rho_sq P Q C w normalized
  · simp [normalized]

theorem weighted_error_le_maximum (w : C → ℝ) (hw : w ∈ unit_weights C) :
    weighted_error P Q C w ≤ maximum_weighted_error P Q C := by
  simpa only [maximum_weighted_error, ciSup_pos hw] using
    le_ciSup (weighted_errors_bddAbove P Q C) w

theorem maximum_weighted_error_nonneg : 0 ≤ maximum_weighted_error P Q C := by
  simpa [maximum_weighted_error, unit_weights] using
    le_ciSup (weighted_errors_bddAbove P Q C) (0 : C → ℝ)

end WeightedError

section Relaxation

open scoped BigOperators
open EuclideanGeometry

section Variance

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def relaxed_variance (P Q : ι → E) (N : E →ₗ[ℝ] E) (a : ι → ℝ) : ℝ :=
  (∑ i, a i * quadratic_error N (P i) (Q i)) -
    quadratic_error N (TranslationGeometry.weightedCenter P a)
      (TranslationGeometry.weightedCenter Q a)

theorem relaxed_variance_centered (P Q : ι → E) (N : E →ₗ[ℝ] E) (a : ι → ℝ)
    (ha : ∑ i, a i = 1) :
    relaxed_variance P Q N a = ∑ i, a i * quadratic_error N
      (P i - TranslationGeometry.weightedCenter P a)
      (Q i - TranslationGeometry.weightedCenter Q a) := by
  have hcross : ∑ i, a i * inner ℝ (N (P i)) (Q i) -
      inner ℝ (N (TranslationGeometry.weightedCenter P a))
        (TranslationGeometry.weightedCenter Q a) =
      ∑ i, a i * inner ℝ (N (P i - TranslationGeometry.weightedCenter P a))
        (Q i - TranslationGeometry.weightedCenter Q a) := by
    simp only [map_sub, inner_sub_left, inner_sub_right, mul_sub,
      Finset.sum_sub_distrib]
    have h₁ : ∑ i, a i * inner ℝ (N (P i)) (TranslationGeometry.weightedCenter Q a) =
        inner ℝ (N (TranslationGeometry.weightedCenter P a))
          (TranslationGeometry.weightedCenter Q a) := by
      simp [TranslationGeometry.weightedCenter, map_sum, map_smul,
        sum_inner, real_inner_smul_left]
    have h₂ : ∑ i, a i * inner ℝ (N (TranslationGeometry.weightedCenter P a)) (Q i) =
        inner ℝ (N (TranslationGeometry.weightedCenter P a))
          (TranslationGeometry.weightedCenter Q a) := by
      simp [TranslationGeometry.weightedCenter, inner_sum, real_inner_smul_right]
    rw [h₁, h₂, ← Finset.sum_mul, ha]
    ring
  have hP := TranslationGeometry.weightedVariance_identity P a ha
    (TranslationGeometry.weightedCenter P a)
  have hQ := TranslationGeometry.weightedVariance_identity Q a ha
    (TranslationGeometry.weightedCenter Q a)
  simp only [TranslationGeometry.weightedVariance, sub_self, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hP hQ
  simp only [relaxed_variance, quadratic_error, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hfactor : ∀ f : ι → ℝ, (∑ i, a i * (2 * f i)) = 2 * ∑ i, a i * f i := by
    intro f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfactor, hfactor, hP, hQ]
  linarith

theorem relaxed_variance_nonneg (P Q : ι → E) (N : E →ₗ[ℝ] E)
    (hN : ∀ x, ‖N x‖ ≤ ‖x‖) (a : ι → ℝ)
    (ha : a ∈ TranslationGeometry.probabilityWeights ι) :
    0 ≤ relaxed_variance P Q N a := by
  rw [relaxed_variance_centered P Q N a ha.2]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (ha.1 i) (quadratic_error_nonneg N hN _ _)

theorem weighted_center_mix (P : ι → E) (f g : ι → ℝ) (a b : ℝ) :
    TranslationGeometry.weightedCenter P (fun i => a * f i + b * g i) =
      a • TranslationGeometry.weightedCenter P f + b • TranslationGeometry.weightedCenter P g := by
  simp [TranslationGeometry.weightedCenter, add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum]

theorem relaxed_variance_mix (P Q : ι → E) (N : E →ₗ[ℝ] E)
    (f g : ι → ℝ) (a b : ℝ) (hab : a + b = 1) :
    relaxed_variance P Q N (fun i => a * f i + b * g i) =
      a * relaxed_variance P Q N f + b * relaxed_variance P Q N g +
      a * b * quadratic_error N
        (TranslationGeometry.weightedCenter P f - TranslationGeometry.weightedCenter P g)
        (TranslationGeometry.weightedCenter Q f - TranslationGeometry.weightedCenter Q g) := by
  simp only [relaxed_variance, add_mul, mul_assoc, Finset.sum_add_distrib,
    ← Finset.mul_sum, weighted_center_mix, quadratic_error_mix N _ _ _ _ a b hab]
  ring

theorem relaxed_variance_concave (P Q : ι → E) (N : E →ₗ[ℝ] E)
    (hN : ∀ x, ‖N x‖ ≤ ‖x‖) :
    ConcaveOn ℝ (TranslationGeometry.probabilityWeights ι) (relaxed_variance P Q N) := by
  refine ⟨?_, ?_⟩
  · intro f hf g hg a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hf.1 i)) (mul_nonneg hb (hg.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]
  · intro f hf g hg a b ha hb hab
    change a * relaxed_variance P Q N f + b * relaxed_variance P Q N g ≤
      relaxed_variance P Q N (fun i => a * f i + b * g i)
    rw [relaxed_variance_mix P Q N f g a b hab]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg ha hb)
      (quadratic_error_nonneg N hN _ _))

theorem relaxed_variance_maximizer_pointwise
    (P Q : ι → E) (N : E →ₗ[ℝ] E) (hN : ∀ x, ‖N x‖ ≤ ‖x‖)
    (a : ι → ℝ) (ha : a ∈ TranslationGeometry.probabilityWeights ι)
    (hmax : IsMaxOn (relaxed_variance P Q N) (TranslationGeometry.probabilityWeights ι) a) :
    ∀ i, quadratic_error N (P i - TranslationGeometry.weightedCenter P a)
      (Q i - TranslationGeometry.weightedCenter Q a) ≤ relaxed_variance P Q N a := by
  classical
  intro i
  let e : ι → ℝ := fun j => if j = i then 1 else 0
  have he : e ∈ TranslationGeometry.probabilityWeights ι := by
    constructor
    · intro j; dsimp [e]; split_ifs <;> norm_num
    · simp [e]
  have hcP : TranslationGeometry.weightedCenter P e = P i := by
    simp [TranslationGeometry.weightedCenter, e, ite_smul]
  have hcQ : TranslationGeometry.weightedCenter Q e = Q i := by
    simp [TranslationGeometry.weightedCenter, e, ite_smul]
  have hv : relaxed_variance P Q N e = 0 := by
    simp [relaxed_variance, e, ite_mul, hcP, hcQ]
  let D := quadratic_error N (P i - TranslationGeometry.weightedCenter P a)
    (Q i - TranslationGeometry.weightedCenter Q a)
  have hD : 0 ≤ D := quadratic_error_nonneg N hN _ _
  have hcoeff : D - relaxed_variance P Q N a ≤ 0 := by
    apply TranslationGeometry.quadratic_linear_coefficient_nonpos hD
    intro t ht ht1
    have hmix : (fun j => t * e j + (1 - t) * a j) ∈
        TranslationGeometry.probabilityWeights ι := by
      refine ⟨fun j => add_nonneg (mul_nonneg ht (he.1 j))
        (mul_nonneg (sub_nonneg.mpr ht1) (ha.1 j)), ?_⟩
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, he.2, ha.2]
      ring
    have hh : relaxed_variance P Q N (fun j => t * e j + (1 - t) * a j) ≤
        relaxed_variance P Q N a := hmax hmix
    rw [relaxed_variance_mix P Q N e a t (1 - t) (by ring), hv, hcP, hcQ] at hh
    change t * 0 + (1 - t) * relaxed_variance P Q N a + t * (1 - t) * D ≤
      relaxed_variance P Q N a at hh
    nlinarith
  exact sub_nonpos.mp hcoeff

end Variance

end Relaxation

section Minimax

open scoped NNReal Finset

section Saddle

variable {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ} (P Q : ι → ℝ^[d])

omit [Nonempty ι] in
private theorem operator_mix (N M : ℝ^[d] →L[ℝ] ℝ^[d]) (w : ι → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    relaxed_variance P Q (a • N + b • M).toLinearMap w =
      a * relaxed_variance P Q N.toLinearMap w + b * relaxed_variance P Q M.toLinearMap w := by
  have hq (x y : ℝ^[d]) : quadratic_error (a • N + b • M).toLinearMap x y =
      a * quadratic_error N.toLinearMap x y + b * quadratic_error M.toLinearMap x y := by
    have hb : b = 1 - a := by linarith
    rw [hb]
    simp only [quadratic_error, ContinuousLinearMap.coe_coe, add_apply,
      smul_apply, inner_add_left, real_inner_smul_left]
    ring
  simp only [relaxed_variance, hq, mul_add, mul_left_comm (w _),
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

omit [Nonempty ι] in
private theorem operator_convex (w : ι → ℝ) :
    ConvexOn ℝ (Metric.closedBall (0 : ℝ^[d] →L[ℝ] ℝ^[d]) 1)
      (fun N => relaxed_variance P Q N.toLinearMap w) := by
  refine ⟨convex_closedBall _ _, ?_⟩
  intro N hN M hM a b ha hb hab
  change relaxed_variance P Q (a • N + b • M).toLinearMap w ≤
    a * relaxed_variance P Q N.toLinearMap w + b * relaxed_variance P Q M.toLinearMap w
  rw [operator_mix P Q N M w a b hab]

theorem relaxed_variance_saddle :
    ∃ N ∈ Metric.closedBall (0 : ℝ^[d] →L[ℝ] ℝ^[d]) 1,
    ∃ a ∈ TranslationGeometry.probabilityWeights ι,
      IsSaddlePointOn (Metric.closedBall 0 1) (TranslationGeometry.probabilityWeights ι)
        (fun N a => relaxed_variance P Q N.toLinearMap a) N a := by
  apply Sion.exists_isSaddlePointOn
  · exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  · exact convex_closedBall _ _
  · exact isCompact_closedBall _ _
  · intro a ha
    have hc : Continuous (fun N : ℝ^[d] →L[ℝ] ℝ^[d] =>
        relaxed_variance P Q N.toLinearMap a) := by
      unfold relaxed_variance quadratic_error
      change Continuous (fun N : ℝ^[d] →L[ℝ] ℝ^[d] =>
        (∑ i, a i * (‖P i‖ ^ 2 + ‖Q i‖ ^ 2 - 2 * inner ℝ (N (P i)) (Q i))) -
          (‖TranslationGeometry.weightedCenter P a‖ ^ 2 +
            ‖TranslationGeometry.weightedCenter Q a‖ ^ 2 -
              2 * inner ℝ (N (TranslationGeometry.weightedCenter P a))
                (TranslationGeometry.weightedCenter Q a)))
      fun_prop
    exact hc.continuousOn.lowerSemicontinuousOn
  · intro a ha
    exact (operator_convex P Q a).quasiconvexOn
  · exact TranslationGeometry.probabilityWeights_convex
  · exact TranslationGeometry.probabilityWeights_nonempty
  · exact TranslationGeometry.probabilityWeights_compact
  · intro N hN
    have hc : Continuous (relaxed_variance P Q N.toLinearMap) := by
      unfold relaxed_variance quadratic_error TranslationGeometry.weightedCenter
      fun_prop
    exact hc.continuousOn.upperSemicontinuousOn
  · intro N hN
    apply (relaxed_variance_concave P Q N.toLinearMap _).quasiconcaveOn
    intro x
    have hn : ‖N‖ ≤ 1 := by simpa using hN
    exact (N.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg x))

end Saddle

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

structure RelaxedFitCertificate where
  contraction : ℝ^[d] →L[ℝ] ℝ^[d]
  contractive : ∀ x, ‖contraction x‖ ≤ ‖x‖
  sourceCenter : ℝ^[d]
  targetCenter : ℝ^[d]
  residual_bound : ∀ i : C,
    quadratic_error contraction.toLinearMap (P i - sourceCenter) (Q i - targetCenter) ≤
      maximum_weighted_error P Q C

theorem weighted_fitting_certificate (hC : C.Nonempty) :
    Nonempty (RelaxedFitCertificate P Q C) := by
  classical
  let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
  obtain ⟨N, hN, a, ha, hsaddle⟩ := relaxed_variance_saddle (fun i : C => P i) (fun i : C => Q i)
  have hn : ‖N‖ ≤ 1 := by simpa using hN
  have hnorm (x : ℝ^[d]) : ‖N x‖ ≤ ‖x‖ :=
    (N.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg x))
  have hmax : IsMaxOn
      (relaxed_variance (fun i : C => P i) (fun i : C => Q i) N.toLinearMap)
      (TranslationGeometry.probabilityWeights C) a := fun b hb => hsaddle N hN b hb
  have hb : relaxed_variance (fun i : C => P i) (fun i : C => Q i) N.toLinearMap a ≤
      maximum_weighted_error P Q C := by
    let w : C → ℝ := fun i => Real.sqrt (a i)
    have hw2 (i : C) : w i ^ 2 = a i := Real.sq_sqrt (ha.1 i)
    have hw : w ∈ unit_weights C := by simpa only [unit_weights, Set.mem_ofPred_eq, hw2] using ha.2
    apply LE.le.trans _ (weighted_error_le_maximum P Q C w hw)
    apply weighted_error_lower_bound P Q C w hw
    intro R
    have hRmem : R.toLinearIsometry.toContinuousLinearMap ∈
        Metric.closedBall (0 : ℝ^[d] →L[ℝ] ℝ^[d]) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp)
    have hh := hsaddle R.toLinearIsometry.toContinuousLinearMap hRmem a ha
    change relaxed_variance (fun i : C => P i) (fun i : C => Q i) N.toLinearMap a ≤
      relaxed_variance (fun i : C => P i) (fun i : C => Q i) R.toLinearMap a at hh
    rw [relaxed_variance_centered _ _ R.toLinearMap _ ha.2] at hh
    simpa only [centered_squared_error, weighted_mean, hw2, TranslationGeometry.weightedCenter,
      quadratic_error_orthogonal] using hh
  have pointwise := relaxed_variance_maximizer_pointwise _ _ _ hnorm a ha hmax
  exact ⟨{
    contraction := N
    contractive := hnorm
    sourceCenter := TranslationGeometry.weightedCenter (fun i : C => P i) a
    targetCenter := TranslationGeometry.weightedCenter (fun i : C => Q i) a
    residual_bound := fun i => (pointwise i).trans hb
  }⟩

/-- Lemma 2: the squared minimax error is at most twice the weighted dual bound. -/
theorem weighted_fitting_bound :
    (rho P Q C : ℝ) ^ 2 ≤ 2 * maximum_weighted_error P Q C := by
  rcases C.eq_empty_or_nonempty with rfl | nonempty
  · simp [maximum_weighted_error, unit_weights]
  obtain ⟨certificate⟩ := weighted_fitting_certificate P Q C nonempty
  obtain ⟨rotation, rounding_bound⟩ :=
    orthogonal_rounding_quadratic certificate.contraction.toLinearMap certificate.contractive
  let alignment := alignment_from_centers rotation certificate.sourceCenter certificate.targetCenter
  apply rho_sq_le_of_squared_fit P Q C alignment
    (mul_nonneg (by norm_num) (maximum_weighted_error_nonneg P Q C))
  intro i hi
  rw [alignment_from_centers_residual]
  calc
    _ ≤ 2 * quadratic_error certificate.contraction.toLinearMap
        (P i - certificate.sourceCenter) (Q i - certificate.targetCenter) := rounding_bound _ _
    _ ≤ 2 * maximum_weighted_error P Q C :=
      mul_le_mul_of_nonneg_left (certificate.residual_bound ⟨i, hi⟩) (by norm_num)

end Minimax

end HigherOrder
