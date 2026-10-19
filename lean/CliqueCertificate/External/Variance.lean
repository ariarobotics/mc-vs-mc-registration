import CliqueCertificate.External.EnclosingBalls

/-! Probability weights and the variance characterization of an enclosing radius. -/

namespace TranslationGeometry

open scoped BigOperators NNReal

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def probabilityWeights (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

theorem probabilityWeights_nonempty [Nonempty ι] : (probabilityWeights ι).Nonempty := by
  let w := Convexity.StdSimplex.single (R := ℝ) (Classical.arbitrary ι)
  exact ⟨w.weights, w.weights_nonneg, w.total_of_fintype⟩

theorem probabilityWeights_convex : Convex ℝ (probabilityWeights ι) := by
  have h := (convex_singleton (1 : ℝ)).linear_preimage
    (∑ i : ι, LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)
  convert (convex_Ici (0 : ι → ℝ)).inter h using 1
  ext w
  simp [probabilityWeights, Pi.le_def]

noncomputable def weightedCenter (p : ι → E) (w : ι → ℝ) : E := ∑ i, w i • p i

noncomputable def weightedVariance (p : ι → E) (w : ι → ℝ) : ℝ :=
  ∑ i, w i * ‖p i‖ ^ 2 - ‖weightedCenter p w‖ ^ 2

theorem weightedVariance_identity (p : ι → E) (w : ι → ℝ)
    (hw : ∑ i, w i = 1) (z : E) :
    ∑ i, w i * ‖p i - z‖ ^ 2 = weightedVariance p w + ‖weightedCenter p w - z‖ ^ 2 := by
  have hi : ∑ i, w i * inner ℝ (p i) z = inner ℝ (weightedCenter p w) z := by
    simp [weightedCenter, sum_inner, real_inner_smul_left]
  simp only [norm_sub_sq_real, mul_sub, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hmul : (∑ i, w i * (2 * inner ℝ (p i) z)) =
      2 * ∑ i, w i * inner ℝ (p i) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmul, hi, ← Finset.sum_mul, hw]
  unfold weightedVariance
  ring

theorem weightedVariance_le_radius_sq [ProperSpace E] (p : ι → E)
    (w : ι → ℝ) (hw : w ∈ probabilityWeights ι) :
    weightedVariance p w ≤ (translationError p Finset.univ : ℝ) ^ 2 := by
  obtain ⟨z, hz⟩ := translationError_attained p Finset.univ
  have hbound : ∀ i, ‖p i - z‖ ≤ (translationError p Finset.univ : ℝ) := by
    intro i
    have hi := Finset.le_sup (f := fun j => nndist z (p j)) (Finset.mem_univ i)
    rw [hz] at hi
    simpa [dist_eq_norm, norm_sub_rev] using NNReal.coe_le_coe.mpr hi
  have hsum : ∑ i, w i * ‖p i - z‖ ^ 2 ≤
      (translationError p Finset.univ : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ i, w i * (translationError p Finset.univ : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2) (hw.1 i)
      _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]
  rw [weightedVariance_identity p w hw.2 z] at hsum
  nlinarith [sq_nonneg ‖weightedCenter p w - z‖]

theorem probabilityWeights_compact : IsCompact (probabilityWeights ι) := by
  have h := isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous
  rw [Convexity.StdSimplex.range_toFun_comp_weights] at h
  convert h using 1
  ext w
  simp [probabilityWeights]

theorem quadratic_linear_coefficient_nonpos {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ t, 0 ≤ t → t ≤ 1 → t * a ≤ t ^ 2 * b) : a ≤ 0 := by
  by_contra! ha
  let t := min 1 (a / (2 * (b + 1)))
  have hden : 0 < 2 * (b + 1) := by positivity
  have ht : 0 < t := lt_min zero_lt_one (div_pos ha hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hta : t * (2 * (b + 1)) ≤ a :=
    (le_div_iff₀ hden).1 (min_le_right _ _)
  have hh := h t ht.le ht1
  have htb : t * b < a := by nlinarith
  nlinarith

theorem weightedVariance_mix [DecidableEq ι] (p : ι → E) (w : ι → ℝ) (i : ι) (t : ℝ) :
    weightedVariance p (fun j => (1 - t) * w j + if j = i then t else 0) =
      weightedVariance p w + t * (‖p i - weightedCenter p w‖ ^ 2 - weightedVariance p w) -
        t ^ 2 * ‖p i - weightedCenter p w‖ ^ 2 := by
  have hc : weightedCenter p (fun j => (1 - t) * w j + if j = i then t else 0) =
      weightedCenter p w + t • (p i - weightedCenter p w) := by
    simp only [weightedCenter, add_smul, Finset.sum_add_distrib, mul_smul]
    rw [← Finset.smul_sum]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    module
  have hs : ∑ j, ((1 - t) * w j + if j = i then t else 0) * ‖p j‖ ^ 2 =
      (1 - t) * ∑ j, w j * ‖p j‖ ^ 2 + t * ‖p i‖ ^ 2 := by
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold weightedVariance
  rw [hs, hc, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, norm_sub_sq_real, inner_sub_right, real_inner_comm]
  rw [real_inner_self_eq_norm_sq]
  ring

theorem weightedVariance_maximizer [Nonempty ι] (p : ι → E) :
    ∃ w ∈ probabilityWeights ι,
      ∀ i, ‖p i - weightedCenter p w‖ ^ 2 ≤ weightedVariance p w := by
  classical
  have hcont : Continuous (weightedVariance p) := by
    unfold weightedVariance weightedCenter
    fun_prop
  obtain ⟨w, hw, hmax⟩ := probabilityWeights_compact.exists_isMaxOn
    probabilityWeights_nonempty hcont.continuousOn
  refine ⟨w, hw, fun i => ?_⟩
  have hcoeff : ‖p i - weightedCenter p w‖ ^ 2 - weightedVariance p w ≤ 0 := by
    apply quadratic_linear_coefficient_nonpos (sq_nonneg ‖p i - weightedCenter p w‖)
    intro t ht ht1
    have hmix : (fun j => (1 - t) * w j + if j = i then t else 0) ∈
        probabilityWeights ι := by
      constructor
      · intro j
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hw.1 j)) (by split_ifs <;> positivity)
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring
    have hh := hmax hmix
    change weightedVariance p (fun j => (1 - t) * w j + if j = i then t else 0) ≤
      weightedVariance p w at hh
    rw [weightedVariance_mix] at hh
    linarith
  linarith

theorem weightedVariance_radius_witness [ProperSpace E] [Nonempty ι] (p : ι → E) :
    ∃ w ∈ probabilityWeights ι,
      weightedVariance p w = (translationError p Finset.univ : ℝ) ^ 2 ∧
      ∀ i, ‖p i - weightedCenter p w‖ ^ 2 ≤ (translationError p Finset.univ : ℝ) ^ 2 := by
  obtain ⟨w, hw, hbound⟩ := weightedVariance_maximizer p
  have hrad := translationError_le p Finset.univ (weightedCenter p w)
  have hsup : ((Finset.univ.sup fun i => nndist (weightedCenter p w) (p i) : ℝ≥0) : ℝ) ^ 2 ≤
      weightedVariance p w := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => nndist (weightedCenter p w) (p i))
    rw [hi]
    simpa [dist_eq_norm, norm_sub_rev] using hbound i
  have heq : weightedVariance p w = (translationError p Finset.univ : ℝ) ^ 2 := by
    apply le_antisymm (weightedVariance_le_radius_sq p w hw)
    exact (pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hrad) 2).trans hsup
  exact ⟨w, hw, heq, fun i => heq ▸ hbound i⟩

end TranslationGeometry
