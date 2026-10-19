import CliqueCertificate.Definitions
import CliqueCertificate.External.FiniteConsistency

/-! Shared fitting, attainment, pairwise consistency, and consensus results. -/

section Fitting

open scoped NNReal

noncomputable def alignment_from_centers {d : ℕ} (R : O(d)) (p q : ℝ^[d]) : E(d) :=
  R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ (q - R p))

theorem alignment_from_centers_residual {d : ℕ} (R : O(d)) (p q x y : ℝ^[d]) :
    alignment_from_centers R p q x - y = R (x - p) - (y - q) := by
  change R x + (q - R p) - y = _
  rw [map_sub]
  module

variable {n d : ℕ} {P Q : Fin n → ℝ^[d]} {C D : Finset (Fin n)}
  {ε η : ℝ≥0} {T U : ℝ^[d] → ℝ^[d]}

def Fits (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n)) (ε : ℝ≥0)
    (T : ℝ^[d] → ℝ^[d]) : Prop :=
  ∀ i ∈ C, ‖T (P i) - Q i‖ ≤ (ε : ℝ)

theorem Fits.restrict (hfit : Fits P Q C ε T) (hDC : D ⊆ C) : Fits P Q D ε T :=
  fun i hi => hfit i (hDC hi)

theorem Fits.mono (hfit : Fits P Q C ε T) (hεη : ε ≤ η) : Fits P Q C η T :=
  fun i hi => (hfit i hi).trans (NNReal.coe_le_coe.mpr hεη)

theorem Fits.nnnorm_le (hfit : Fits P Q C ε T) {i : Fin n} (hi : i ∈ C) :
    ‖T (P i) - Q i‖₊ ≤ ε :=
  NNReal.coe_le_coe.mp (hfit i hi)

theorem Fits.disagreement_le (hT : Fits P Q C ε T) (hU : Fits P Q D η U)
    {i : Fin n} (hiC : i ∈ C) (hiD : i ∈ D) :
    ‖T (P i) - U (P i)‖ ≤ (ε : ℝ) + η := by
  calc
    _ ≤ ‖T (P i) - Q i‖ + ‖Q i - U (P i)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖T (P i) - Q i‖ + ‖U (P i) - Q i‖ := by rw [norm_sub_rev (Q i)]
    _ ≤ (ε : ℝ) + η := add_le_add (hT i hiC) (hU i hiD)

variable (P Q C)

theorem alignment_error_le_iff_fits (T : E(d)) (ε : ℝ≥0) :
    alignment_error P Q C T ≤ ε ↔ Fits P Q C ε T := by
  constructor
  · intro h i hi
    exact NNReal.coe_le_coe.mpr ((le_ciSup (f := fun j : C => ‖T (P j) - Q j‖₊)
      (Set.finite_range _).bddAbove ⟨i, hi⟩).trans h)
  · intro h
    exact ciSup_le' fun i => h.nnnorm_le i.property

theorem alignment_error_fits (T : E(d)) : Fits P Q C (alignment_error P Q C T) T :=
  (alignment_error_le_iff_fits P Q C T _).mp le_rfl

end Fitting

section Attainment

open scoped NNReal

private theorem isCompact_norm_preserving (d : ℕ) :
    IsCompact {A : ℝ^[d] →L[ℝ] ℝ^[d] | ∀ x, ‖A x‖ = ‖x‖} := by
  have hclosed : IsClosed {A : ℝ^[d] →L[ℝ] ℝ^[d] | ∀ x, ‖A x‖ = ‖x‖} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq (continuous_id.clm_apply continuous_const).norm continuous_const
  apply (isCompact_closedBall (0 : ℝ^[d] →L[ℝ] ℝ^[d]) 1).of_isClosed_subset hclosed
  intro A hA
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact A.opNorm_le_bound zero_le_one (fun x => by rw [hA x, one_mul])

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem alignment_error_min_on_rotations
    (R : (ℝ^[d] →L[ℝ] ℝ^[d]) → Prop) (hR : IsClosed {A | R A})
    (hR1 : R (ContinuousLinearMap.id ℝ (ℝ^[d]))) :
    ∃ T : E(d), R T.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ∧
      ∀ U : E(d), R U.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap →
        alignment_error P Q C T ≤ alignment_error P Q C U := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hC
  · exact ⟨1, hR1, fun _ _ => by simp [alignment_error]⟩
  obtain ⟨i₀, hi₀⟩ := hC

  let F := fun z : (ℝ^[d] →L[ℝ] ℝ^[d]) × ℝ^[d] =>
    ⨆ i : C, ‖z.1 (P i - P i₀) + z.2 - Q i‖₊
  have hF : Continuous F := by
    dsimp [F]
    simp_rw [← Finset.sup_univ_eq_ciSup]
    exact Continuous.finset_sup_apply fun i _ =>
      (((continuous_fst.clm_apply continuous_const).add continuous_snd).sub continuous_const).nnnorm

  let encode := fun T : E(d) =>
    (T.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap, T (P i₀))
  have hencode (T : E(d)) : F (encode T) = alignment_error P Q C T := by
    have hpoint (x : ℝ^[d]) :
        T.linearIsometryEquiv (x - P i₀) + T (P i₀) = T x := by
      simpa using congrArg (fun y => y + T (P i₀)) (T.map_vsub x (P i₀))
    change (⨆ i : C, ‖T.linearIsometryEquiv (P i - P i₀) + T (P i₀) - Q i‖₊) = _
    simp_rw [hpoint]
    rfl

  let K := ({A : ℝ^[d] →L[ℝ] ℝ^[d] | ∀ x, ‖A x‖ = ‖x‖} ∩ {A | R A}) ×ˢ
    Metric.closedBall (Q i₀) (alignment_error P Q C 1 : ℝ)
  have hK : IsCompact K :=
    ((isCompact_norm_preserving d).inter_right hR).prod (isCompact_closedBall _ _)
  have hmem (T : E(d)) (hRT : R T.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)
      (hT : alignment_error P Q C T ≤ alignment_error P Q C 1) :
      encode T ∈ K := by
    refine ⟨⟨fun x => T.linearIsometryEquiv.norm_map x, hRT⟩, ?_⟩
    have hpoint : ‖T (P i₀) - Q i₀‖₊ ≤ alignment_error P Q C T :=
      le_ciSup (f := fun i : C => ‖T (P i) - Q i‖₊)
        (Set.finite_range _).bddAbove (⟨i₀, hi₀⟩ : C)
    change dist (T (P i₀)) (Q i₀) ≤ (alignment_error P Q C 1 : ℝ)
    rw [dist_eq_norm]
    exact_mod_cast hpoint.trans hT
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨encode 1, hmem 1 hR1 le_rfl⟩ hF.continuousOn

  let L : ℝ^[d] →ₗᵢ[ℝ] ℝ^[d] :=
    { z.1.toLinearMap with norm_map' := hz.1.1 }
  let T : E(d) :=
    ((AffineIsometryEquiv.vaddConst ℝ (-P i₀) : E(d)).trans
      (L.toLinearIsometryEquiv rfl).toAffineIsometryEquiv).trans
      (AffineIsometryEquiv.vaddConst ℝ z.2)
  have hT : alignment_error P Q C T = F z := by
    change (⨆ i : C, ‖z.1 (P i + -P i₀) + z.2 - Q i‖₊) = _
    simp only [F, sub_eq_add_neg]

  refine ⟨T, hz.1.2, fun U hRU => ?_⟩
  rw [hT]
  by_cases hU : alignment_error P Q C U ≤ alignment_error P Q C 1
  · rw [← hencode U]
    exact hmin (hmem U hRU hU)
  · have hbase : F z ≤ alignment_error P Q C 1 := by
      rw [← hencode 1]
      exact hmin (hmem 1 hR1 le_rfl)
    exact hbase.trans (le_of_not_ge hU)

theorem rho_attained : ∃ T : E(d), alignment_error P Q C T = rho P Q C := by
  obtain ⟨T, -, hT⟩ := alignment_error_min_on_rotations P Q C (fun _ => True)
    isClosed_univ trivial
  exact ⟨T, le_antisymm (le_ciInf fun U => hT U trivial) (ciInf_le (OrderBot.bddBelow _) T)⟩

theorem rho_le_iff_exists_alignment (τ : ℝ≥0) :
    rho P Q C ≤ τ ↔ ∃ T : E(d), alignment_error P Q C T ≤ τ := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := rho_attained P Q C
    exact ⟨T, hT.le.trans h⟩
  · rintro ⟨T, hT⟩
    exact (ciInf_le (OrderBot.bddBelow _) T).trans hT

theorem exists_best_fit : ∃ T : E(d), Fits P Q C (rho P Q C) T := by
  obtain ⟨T, hT⟩ := rho_attained P Q C
  exact ⟨T, (alignment_error_le_iff_fits P Q C T _).mp hT.le⟩

theorem rho_le_iff_exists_fit (ε : ℝ≥0) :
    rho P Q C ≤ ε ↔ ∃ T : E(d), Fits P Q C ε T := by
  simp only [rho_le_iff_exists_alignment, alignment_error_le_iff_fits]

theorem Fits.rho_le {P Q : Fin n → ℝ^[d]} {C : Finset (Fin n)}
    {ε : ℝ≥0} {T : E(d)} (hfit : Fits P Q C ε T) :
    rho P Q C ≤ ε :=
  (rho_le_iff_exists_fit P Q C ε).mpr ⟨T, hfit⟩

theorem rho_sq_le_of_squared_fit (T : E(d)) {b : ℝ} (hb : 0 ≤ b)
    (hfit : ∀ i ∈ C, ‖T (P i) - Q i‖ ^ 2 ≤ b) :
    (rho P Q C : ℝ) ^ 2 ≤ b := by
  have hbound : Fits P Q C ⟨Real.sqrt b, Real.sqrt_nonneg b⟩ T := by
    intro i hi
    exact (Real.le_sqrt (norm_nonneg _) hb).mpr (hfit i hi)
  have hrho := NNReal.coe_le_coe.mpr hbound.rho_le
  exact (pow_le_pow_left₀ (rho P Q C).coe_nonneg hrho 2).trans_eq (Real.sq_sqrt hb)

end Attainment

section Hierarchy

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

theorem alignment_error_mono (T : E(d)) : Monotone (fun C => alignment_error P Q C T) := by
  intro C D hCD
  apply ciSup_le'
  intro i
  exact le_ciSup (f := fun j : D => ‖T (P j) - Q j‖₊)
    (Set.finite_range _).bddAbove (⟨i, hCD i.property⟩ : D)

theorem rho_mono : Monotone (rho P Q) := by
  intro C D hCD
  apply ciInf_mono (OrderBot.bddBelow _)
  intro T
  exact alignment_error_mono P Q T hCD

@[simp] theorem rho_empty : rho P Q ∅ = 0 := by
  simp [rho, alignment_error]

theorem alignment_error_symm (C : Finset (Fin n)) (T : E(d)) :
    alignment_error Q P C T.symm = alignment_error P Q C T := by
  have h (i : C) : ‖T.symm (Q i) - P i‖₊ = ‖T (P i) - Q i‖₊ := by
    change nndist (T.symm (Q i)) (P i) = nndist (T (P i)) (Q i)
    simpa only [T.symm_apply_apply, nndist_comm] using
      T.symm.isometry.nndist_eq (Q i) (T (P i))
  simp only [alignment_error, h]

private theorem rho_swap_le (C : Finset (Fin n)) : rho Q P C ≤ rho P Q C := by
  apply le_ciInf
  intro T
  rw [← alignment_error_symm P Q C T]
  exact ciInf_le (OrderBot.bddBelow _) T.symm

theorem rho_symm (C : Finset (Fin n)) : rho Q P C = rho P Q C :=
  le_antisymm (rho_swap_le P Q C) (rho_swap_le Q P C)

theorem le_rho_k (C I : Finset (Fin n)) (k : ℕ) (hIC : I ⊆ C) (hcard : #I ≤ k) :
    rho P Q I ≤ rho_k P Q C k := by
  rw [rho_k, ← FiniteConsistency.rhoK_eq_iSup]
  exact (FiniteConsistency.rhoK_le_iff _ k C _).1 le_rfl I hIC hcard

theorem rho_k_le_iff (C : Finset (Fin n)) (k : ℕ) (τ : ℝ≥0) :
    rho_k P Q C k ≤ τ ↔ ∀ I ⊆ C, #I ≤ k → rho P Q I ≤ τ := by
  rw [rho_k, ← FiniteConsistency.rhoK_eq_iSup]
  exact FiniteConsistency.rhoK_le_iff _ k C τ

theorem rho_k_mono (C : Finset (Fin n)) {k l : ℕ} (hkl : k ≤ l) :
    rho_k P Q C k ≤ rho_k P Q C l := by
  simp only [rho_k, ← FiniteConsistency.rhoK_eq_iSup]
  exact FiniteConsistency.rhoK_mono _ C hkl

theorem rho_k_le_rho (C : Finset (Fin n)) (k : ℕ) :
    rho_k P Q C k ≤ rho P Q C := by
  rw [rho_k, ← FiniteConsistency.rhoK_eq_iSup]
  exact FiniteConsistency.rhoK_le_rho _ (rho_mono P Q) k C

theorem rho_k_eq_rho (C : Finset (Fin n)) {k : ℕ} (hcard : #C ≤ k) :
    rho_k P Q C k = rho P Q C := by
  rw [rho_k, ← FiniteConsistency.rhoK_eq_iSup]
  exact FiniteConsistency.rhoK_eq_rho _ (rho_mono P Q) C hcard

theorem rho_k_symm (C : Finset (Fin n)) (k : ℕ) : rho_k Q P C k = rho_k P Q C k := by
  simp only [rho_k, rho_symm]

theorem maximum_consensus_k_antitone (τ : ℝ≥0) {k l : ℕ} (hkl : k ≤ l) :
    maximum_consensus_k P Q τ l ≤ maximum_consensus_k P Q τ k := by
  exact FiniteConsistency.consensus_mono fun I hI => (rho_k_mono P Q I hkl).trans hI

theorem maximum_consensus_le_k (τ : ℝ≥0) (k : ℕ) :
    maximum_consensus P Q τ ≤ maximum_consensus_k P Q τ k := by
  exact FiniteConsistency.consensus_mono fun I hI => (rho_k_le_rho P Q I k).trans hI

theorem maximum_consensus_k_eq (τ : ℝ≥0) {k : ℕ} (hk : n ≤ k) :
    maximum_consensus_k P Q τ k = maximum_consensus P Q τ := by
  unfold maximum_consensus_k maximum_consensus feasible
  have hcard (I : Finset (Fin n)) : #I ≤ k := (Finset.card_le_univ I).trans (by simpa using hk)
  simp_rw [rho_k_eq_rho P Q _ (hcard _)]

end Hierarchy

section AffineRelations

open scoped NNReal

/-- Lemma 1: zero-sum combinations are controlled by the optimal fitting error. -/
theorem affine_relation_bound (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))
    (α : Fin n → ℝ) (hα : ∑ i : C, α i = 0) :
    |‖∑ i : C, α i • P i‖ - ‖∑ i : C, α i • Q i‖| ≤
      (rho P Q C : ℝ) * ∑ i : C, |α i| := by
  obtain ⟨T, hfit⟩ := exists_best_fit P Q C
  let τ := rho P Q C

  let pSum := ∑ i : C, α i • P i
  let qSum := ∑ i : C, α i • Q i
  let R := T.linearIsometryEquiv

  have hlinear (i : C) : R (P i) = T (P i) - T 0 := by
    simpa using T.map_vsub (P i) 0

  have hsum : R pSum = ∑ i : C, α i • T (P i) := by
    simp_rw [pSum, map_sum, map_smul, hlinear, smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hα, zero_smul, sub_zero]

  calc
    |‖pSum‖ - ‖qSum‖| = |‖R pSum‖ - ‖qSum‖| := by rw [R.norm_map]
    _ ≤ ‖R pSum - qSum‖ := abs_norm_sub_norm_le _ _
    _ = ‖∑ i : C, α i • (T (P i) - Q i)‖ := by
      rw [hsum]
      simp only [qSum, smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i : C, ‖α i • (T (P i) - Q i)‖ := norm_sum_le _ _
    _ = ∑ i : C, |α i| * ‖T (P i) - Q i‖ := by simp_rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : C, |α i| * (τ : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfit i i.property) (abs_nonneg _))
    _ = (τ : ℝ) * ∑ i : C, |α i| := by rw [← Finset.sum_mul, mul_comm]

end AffineRelations

section Pairwise

open scoped NNReal Finset

theorem edge_change_bound {n d : ℕ}
    (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))
    {i j : Fin n} (hi : i ∈ C) (hj : j ∈ C) :
    |‖P i - P j‖ - ‖Q i - Q j‖| ≤ 2 * (rho P Q C : ℝ) := by
  obtain ⟨T, hfit⟩ := exists_best_fit P Q C
  rw [← dist_eq_norm, ← dist_eq_norm, ← T.isometry.dist_eq, ← Real.dist_eq]
  exact (dist_dist_dist_le _ _ _ _).trans (by
    simpa [dist_eq_norm, two_mul] using add_le_add (hfit i hi) (hfit j hj))

private theorem exists_aligned_difference (u v : ℝ^[d]) :
    ∃ R : O(d), ‖R u - v‖ = |‖u‖ - ‖v‖| := by
  by_cases hv : v = 0
  · exact ⟨1, by simp [hv]⟩
  let w := (‖u‖ / ‖v‖) • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hw : ‖w‖ = ‖u‖ := by
    simp [w, norm_smul, div_mul_cancel₀ _ hvnorm]
  let R : O(d) := Submodule.reflection (ℝ ∙ (u - w))ᗮ
  refine ⟨R, ?_⟩
  rw [show R u = w from Submodule.reflection_sub hw.symm]
  calc
    ‖w - v‖ = |‖u‖ / ‖v‖ - 1| * ‖v‖ := by
      rw [show w - v = (‖u‖ / ‖v‖ - 1) • v by simp [w, sub_smul],
        norm_smul, Real.norm_eq_abs]
    _ = |(‖u‖ / ‖v‖ - 1) * ‖v‖| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
    _ = |‖u‖ - ‖v‖| := by
      congr 1
      rw [sub_mul, div_mul_cancel₀ _ hvnorm, one_mul]

private theorem exists_pair_alignment (P Q : Fin n → ℝ^[d]) (i j : Fin n) :
    ∃ T : E(d), Fits P Q {i, j} (nndist ‖P i - P j‖₊ ‖Q i - Q j‖₊ / 2) T := by
  classical
  let u := P i - P j
  let v := Q i - Q j
  obtain ⟨R, hR⟩ := exists_aligned_difference u v
  let t := Q j + (1 / 2 : ℝ) • (v - R u)
  let T : E(d) := ((AffineIsometryEquiv.vaddConst ℝ (-P j) : E(d)).trans
    R.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ t)
  have hj : T (P j) - Q j = (1 / 2 : ℝ) • (v - R u) := by
    simp [T, t]
  have hi : T (P i) - Q i = -((1 / 2 : ℝ) • (v - R u)) := by
    change R (P i + -P j) + t - Q i = _
    dsimp [t, u, v]
    simp only [← sub_eq_add_neg]
    module
  have hnorm : ‖(1 / 2 : ℝ) • (v - R u)‖ = |‖u‖ - ‖v‖| / 2 := by
    rw [norm_smul, norm_sub_rev, hR]
    norm_num
    ring
  refine ⟨T, fun k hk => ?_⟩
  change ‖T (P k) - Q k‖ ≤ dist ‖P i - P j‖₊ ‖Q i - Q j‖₊ / 2
  change ‖T (P k) - Q k‖ ≤ |‖u‖ - ‖v‖| / 2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with hk | hk
  · simpa only [hk, hi, norm_neg] using hnorm.le
  · simpa only [hk, hj] using hnorm.le

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

theorem delta_le_iff (C : Finset (Fin n)) (ε : ℝ≥0) :
    delta P Q C ≤ ε ↔ ∀ i ∈ C, ∀ j ∈ C,
      nndist ‖P i - P j‖₊ ‖Q i - Q j‖₊ ≤ ε := by
  unfold delta
  rw [ciSup_le_iff' (Set.finite_range _).bddAbove]
  simp_rw [ciSup_le_iff' (Set.finite_range _).bddAbove]
  constructor
  · intro h i hi j hj
    exact h ⟨i, hi⟩ ⟨j, hj⟩
  · intro h i j
    exact h i i.property j j.property

theorem delta_le_twice_rho (C : Finset (Fin n)) :
    delta P Q C ≤ 2 * rho P Q C := by
  apply (delta_le_iff P Q C _).2
  intro i hi j hj
  apply NNReal.coe_le_coe.mp
  change |‖P i - P j‖ - ‖Q i - Q j‖| ≤ 2 * (rho P Q C : ℝ)
  exact edge_change_bound P Q C hi hj

theorem feasible_implies_pairwise_consistent (C : Finset (Fin n)) (τ : ℝ≥0)
    (h : feasible P Q C τ) : pairwise_consistent P Q C (2 * τ) :=
  (delta_le_twice_rho P Q C).trans (mul_le_mul_of_nonneg_left h zero_le)

theorem rho_pair (i j : Fin n) :
    rho P Q {i, j} = nndist ‖P i - P j‖₊ ‖Q i - Q j‖₊ / 2 := by
  classical
  apply le_antisymm
  · obtain ⟨T, hT⟩ := exists_pair_alignment P Q i j
    exact hT.rho_le
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2
    apply NNReal.coe_le_coe.mp
    change |‖P i - P j‖ - ‖Q i - Q j‖| ≤ (rho P Q {i, j} : ℝ) * 2
    simpa [mul_comm] using edge_change_bound P Q {i, j}
      (Finset.mem_insert_self i {j}) (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))

theorem rho_two (C : Finset (Fin n)) : rho_k P Q C 2 = delta P Q C / 2 := by
  classical
  apply le_antisymm
  · apply (rho_k_le_iff P Q C 2 _).2
    intro I hIC hcard
    by_cases htwo : #I = 2
    · obtain ⟨i, j, _, rfl⟩ := Finset.card_eq_two.mp htwo
      rw [rho_pair]
      exact div_le_div_of_nonneg_right
        ((delta_le_iff P Q C _).1 le_rfl i (hIC (Finset.mem_insert_self i {j}))
          j (hIC (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))) zero_le
    · have hone : #I ≤ 1 := by omega
      obtain rfl | ⟨i, hi⟩ := I.eq_empty_or_nonempty
      · rw [rho_empty]
        exact zero_le
      · have hsub : I ⊆ {i, i} := by
          intro j hj
          have hji := (Finset.card_le_one.mp hone) j hj i hi
          simp [hji]
        calc
          rho P Q I ≤ rho P Q {i, i} := rho_mono P Q hsub
          _ = 0 := by rw [rho_pair]; simp
          _ ≤ _ := zero_le
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2
    apply (delta_le_iff P Q C _).2
    intro i hi j hj
    have hpair := le_rho_k P Q C {i, j} 2
      (Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩) Finset.card_le_two
    rw [rho_pair] at hpair
    exact (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).1 hpair

theorem pairwise_consistent_iff_rho_two (C : Finset (Fin n)) (τ : ℝ≥0) :
    pairwise_consistent P Q C (2 * τ) ↔ rho_k P Q C 2 ≤ τ := by
  rw [pairwise_consistent, rho_two, div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
  rw [mul_comm τ 2]

theorem pairwise_consistent_iff_pair_feasible (C : Finset (Fin n)) (τ : ℝ≥0) :
    pairwise_consistent P Q C (2 * τ) ↔ ∀ I ⊆ C, #I ≤ 2 → feasible P Q I τ := by
  rw [pairwise_consistent_iff_rho_two, rho_k_le_iff]
  rfl

theorem pairwise_consistent_iff_feasible_of_card_le_two
    (C : Finset (Fin n)) (τ : ℝ≥0) (hcard : #C ≤ 2) :
    pairwise_consistent P Q C (2 * τ) ↔ feasible P Q C τ := by
  rw [pairwise_consistent_iff_rho_two, rho_k_eq_rho P Q C hcard]
  rfl

theorem max_clique_eq_maximum_consensus_two (τ : ℝ≥0) :
    max_clique P Q (2 * τ) = maximum_consensus_k P Q τ 2 := by
  unfold max_clique maximum_consensus_k
  simp_rw [pairwise_consistent_iff_rho_two]

theorem maximum_consensus_le_max_clique (τ : ℝ≥0) :
    maximum_consensus P Q τ ≤ max_clique P Q (2 * τ) := by
  rw [max_clique_eq_maximum_consensus_two]
  exact maximum_consensus_le_k P Q τ 2

end Pairwise

section Consensus

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

noncomputable def inlier_set (τ : ℝ≥0) (T : E(d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ‖T (P i) - Q i‖₊ ≤ τ

@[simp] theorem mem_inlier_set (τ : ℝ≥0) (T : E(d)) (i : Fin n) :
    i ∈ inlier_set P Q τ T ↔ ‖T (P i) - Q i‖₊ ≤ τ := by
  classical
  simp [inlier_set]

theorem feasible_iff_exists_inlier_superset (C : Finset (Fin n)) (τ : ℝ≥0) :
    feasible P Q C τ ↔ ∃ T : E(d), C ⊆ inlier_set P Q τ T := by
  rw [feasible, rho_le_iff_exists_fit]
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, fun i hi => (mem_inlier_set P Q τ T i).mpr ?_⟩
    exact hT.nnnorm_le hi
  · rintro ⟨T, hT⟩
    exact ⟨T, fun i hi => NNReal.coe_le_coe.mpr ((mem_inlier_set P Q τ T i).mp (hT hi))⟩

theorem inlier_set_feasible (τ : ℝ≥0) (T : E(d)) :
    feasible P Q (inlier_set P Q τ T) τ :=
  (feasible_iff_exists_inlier_superset P Q _ τ).mpr ⟨T, le_rfl⟩

theorem maximum_consensus_eq_iSup_inliers (τ : ℝ≥0) :
    maximum_consensus P Q τ = ⨆ T : E(d), #(inlier_set P Q τ T) := by
  classical
  have hb : BddAbove (Set.range fun T : E(d) => #(inlier_set P Q τ T)) := by
    refine ⟨n, ?_⟩
    rintro _ ⟨T, rfl⟩
    simpa using Finset.card_le_univ (inlier_set P Q τ T)
  apply le_antisymm
  · apply ciSup_le'
    intro C
    apply ciSup_le'
    intro hC
    obtain ⟨T, hT⟩ := (feasible_iff_exists_inlier_superset P Q C τ).mp hC
    exact (Finset.card_le_card hT).trans (le_ciSup hb T)
  · apply ciSup_le'
    intro T
    have hh := le_ciSup (f := fun C => ⨆ (_ : feasible P Q C τ), #C)
      (Set.finite_range _).bddAbove (inlier_set P Q τ T)
    simpa only [ciSup_pos (inlier_set_feasible P Q τ T), maximum_consensus] using hh

theorem maximum_consensus_attained (τ : ℝ≥0) :
    ∃ T : E(d), #(inlier_set P Q τ T) = maximum_consensus P Q τ := by
  rw [maximum_consensus_eq_iSup_inliers]
  apply exists_eq_ciSup_of_not_isSuccLimit
  · refine ⟨n, ?_⟩
    rintro _ ⟨T, rfl⟩
    simpa using Finset.card_le_univ (inlier_set P Q τ T)
  · exact Order.not_isSuccLimit_of_isSuccArchimedean

end Consensus

section Graphs

namespace ConsistencyGraph

open scoped NNReal Finset

def threshold {α : Type*} (error : α → α → ℝ≥0)
    (hsymm : ∀ i j, error i j = error j i) (ε : ℝ≥0) : SimpleGraph α where
  Adj i j := i ≠ j ∧ error i j ≤ ε
  symm := ⟨fun i j h => ⟨h.1.symm, (hsymm i j).symm.trans_le h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem isClique_threshold_iff {α : Type*} (error : α → α → ℝ≥0)
    (hsymm : ∀ i j, error i j = error j i) (hzero : ∀ i, error i i = 0)
    (ε : ℝ≥0) (C : Finset α) :
    (threshold error hsymm ε).IsClique C ↔ ∀ i ∈ C, ∀ j ∈ C, error i j ≤ ε := by
  constructor
  · intro h i hi j hj
    by_cases hij : i = j
    · subst j; rw [hzero]; exact zero_le
    · exact (h hi hj hij).2
  · intro h i hi j hj hij
    exact ⟨hij, h i hi j hj⟩

theorem cliqueNum_eq_iSup {α : Type*} [Finite α] (G : SimpleGraph α) :
    G.cliqueNum = ⨆ (C : Finset α) (_ : G.IsClique C), #C := by
  classical
  apply le_antisymm
  · obtain ⟨C, hC⟩ := G.exists_isNClique_cliqueNum
    rw [← hC.card_eq]
    have hh := le_ciSup (f := fun C : Finset α => ⨆ (_ : G.IsClique C), #C)
      (Set.finite_range _).bddAbove C
    simpa only [ciSup_pos hC.isClique] using hh
  · exact ciSup_le' fun C => ciSup_le' fun hC => hC.card_le_cliqueNum

end ConsistencyGraph

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

noncomputable def consistency_graph (ε : ℝ≥0) : SimpleGraph (Fin n) :=
  ConsistencyGraph.threshold (fun i j => nndist ‖P i - P j‖₊ ‖Q i - Q j‖₊)
    (by
      intro i j
      have hp : ‖P i - P j‖₊ = ‖P j - P i‖₊ := NNReal.eq (norm_sub_rev _ _)
      have hq : ‖Q i - Q j‖₊ = ‖Q j - Q i‖₊ := NNReal.eq (norm_sub_rev _ _)
      rw [hp, hq]) ε

theorem isClique_consistency_graph_iff (ε : ℝ≥0) (C : Finset (Fin n)) :
    (consistency_graph P Q ε).IsClique C ↔ pairwise_consistent P Q C ε := by
  rw [consistency_graph, ConsistencyGraph.isClique_threshold_iff _ _ (by simp),
    pairwise_consistent, delta_le_iff]

theorem cliqueNum_consistency_graph (ε : ℝ≥0) :
    (consistency_graph P Q ε).cliqueNum = max_clique P Q ε := by
  rw [ConsistencyGraph.cliqueNum_eq_iSup]
  simp_rw [isClique_consistency_graph_iff]
  rfl

theorem cliqueNum_le_maximum_consensus (G : SimpleGraph (Fin n)) (τ : ℝ≥0)
    (hfit : ∀ C : Finset (Fin n), G.IsClique C → feasible P Q C τ) :
    G.cliqueNum ≤ maximum_consensus P Q τ := by
  rw [ConsistencyGraph.cliqueNum_eq_iSup]
  exact FiniteConsistency.consensus_mono hfit

end Graphs
