import CliqueCertificate.HigherOrder.Procrustes

/-! Local affine relations (Lemma 4) and the unrestricted group-k bound (Theorem 1). -/

open EuclideanGeometry

namespace HigherOrder

section Sparsification

open scoped NNReal Finset

theorem sparse_nonnegative_weights {ι E : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (v : ι → E) (g : ι → ℝ) (C : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ C, 0 ≤ a i) :
    ∃ I ⊆ C, #I ≤ Module.finrank ℝ E + 1 ∧ ∃ b : ι → ℝ,
      (∀ i ∈ I, 0 ≤ b i) ∧
      (∑ i ∈ I, b i) = ∑ i ∈ C, a i ∧
      (∑ i ∈ I, b i • v i) = ∑ i ∈ C, a i • v i ∧
      (∑ i ∈ C, a i * g i) ≤ ∑ i ∈ I, b i * g i := by
  classical
  induction C using Finset.strongInductionOn generalizing a with
  | _ C ih =>
    by_cases hcard : #C ≤ Module.finrank ℝ E + 1
    · exact ⟨C, le_rfl, hcard, a, ha, rfl, rfl, le_rfl⟩
    by_cases hz : ∃ i ∈ C, a i = 0
    · obtain ⟨i, hi, hai⟩ := hz
      obtain ⟨I, hIC, hI, b, hb, hm, hv, hg⟩ :=
        ih (C.erase i) (Finset.erase_ssubset hi) a
          (fun j hj => ha j (Finset.mem_of_mem_erase hj))
      refine ⟨I, hIC.trans (Finset.erase_subset _ _), hI, b, hb, ?_, ?_, ?_⟩
      · simpa [Finset.sum_erase, hai] using hm
      · simpa [Finset.sum_erase, hai] using hv
      · simpa [Finset.sum_erase, hai] using hg
    have hpos (i : ι) (hi : i ∈ C) : 0 < a i :=
      lt_of_le_of_ne (ha i hi) (Ne.symm (fun h => hz ⟨i, hi, h⟩))
    let u : ι → ℝ × E := fun i => (1, v i)
    have hdep : ¬ LinearIndepOn ℝ u (C : Set ι) := by
      intro h
      have hc := h.linearIndependent.fintype_card_le_finrank
      have hdim : Module.finrank ℝ (ℝ × E) = 1 + Module.finrank ℝ E := by
        rw [Module.finrank_prod, Module.finrank_self]
      apply hcard
      simpa only [Finset.coe_sort_coe, Fintype.card_coe, Module.finrank_prod,
        Module.finrank_self, add_comm] using hc
    obtain ⟨h₀, hu, i₀, hi₀, hne₀⟩ := (not_linearIndepOn_finset_iff).1 hdep
    have hm₀ : ∑ i ∈ C, h₀ i = 0 := by
      have hh := congrArg Prod.fst hu
      simpa [u, Prod.fst_sum, Prod.snd_sum] using hh
    have hv₀ : ∑ i ∈ C, h₀ i • v i = 0 := by
      have hh := congrArg Prod.snd hu
      simpa [u, Prod.fst_sum, Prod.snd_sum] using hh
    let h : ι → ℝ := if 0 ≤ ∑ i ∈ C, h₀ i * g i then fun i => -h₀ i else h₀
    have hm : ∑ i ∈ C, h i = 0 := by
      dsimp [h]; split_ifs <;> simp [hm₀]
    have hv : ∑ i ∈ C, h i • v i = 0 := by
      dsimp [h]; split_ifs <;> simp [hv₀, Finset.sum_neg_distrib]
    have hg : ∑ i ∈ C, h i * g i ≤ 0 := by
      dsimp [h]; split_ifs with hh
      · simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonpos] using hh
      · exact (lt_of_not_ge hh).le
    have hnz : ∃ i ∈ C, h i ≠ 0 := by
      refine ⟨i₀, hi₀, ?_⟩
      dsimp [h]; split_ifs <;> simpa using hne₀
    obtain ⟨j, hj, hjpos⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero h hm hnz
    let S := C.filter fun i => 0 < h i
    have hS : S.Nonempty := ⟨j, by simp [S, hj, hjpos]⟩
    obtain ⟨j, hjS, hmin⟩ := S.exists_min_image (fun i => a i / h i) hS
    have hjC : j ∈ C := (Finset.mem_filter.mp hjS).1
    have hjh : 0 < h j := (Finset.mem_filter.mp hjS).2
    let t := a j / h j
    have ht : 0 ≤ t := div_nonneg (ha j hjC) hjh.le
    let b : ι → ℝ := fun i => a i - t * h i
    have hb (i : ι) (hi : i ∈ C) : 0 ≤ b i := by
      dsimp [b]
      by_cases hhi : 0 < h i
      · have hratio := hmin i (by simp [S, hi, hhi])
        have := (le_div_iff₀ hhi).1 hratio
        linarith
      · have hh := mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hhi)
        linarith [ha i hi]
    have hbj : b j = 0 := by simp [b, t, ne_of_gt hjh]
    have hmass : ∑ i ∈ C, b i = ∑ i ∈ C, a i := by
      simp [b, Finset.sum_sub_distrib, ← Finset.mul_sum, hm]
    have hvec : ∑ i ∈ C, b i • v i = ∑ i ∈ C, a i • v i := by
      simp [b, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hv]
    have hobj : ∑ i ∈ C, a i * g i ≤ ∑ i ∈ C, b i * g i := by
      simp only [b, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hg]
    obtain ⟨I, hIC, hI, c, hc, hcm, hcv, hcg⟩ :=
      ih (C.erase j) (Finset.erase_ssubset hjC) b
        (fun i hi => hb i (Finset.mem_of_mem_erase hi))
    refine ⟨I, hIC.trans (Finset.erase_subset _ _), hI, c, hc, ?_, ?_, ?_⟩
    · calc
        _ = ∑ i ∈ C, b i := by simpa [Finset.sum_erase, hbj] using hcm
        _ = _ := hmass
    · calc
        _ = ∑ i ∈ C, b i • v i := by simpa [Finset.sum_erase, hbj] using hcv
        _ = _ := hvec
    · apply hobj.trans
      simpa [Finset.sum_erase, hbj] using hcg

theorem sparse_affine_relation {n d : ℕ} (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (α : Fin n → ℝ) :
    ∃ I ⊆ C, #I ≤ d + 2 ∧ ∃ β : Fin n → ℝ,
      (∑ i ∈ I, β i) = ∑ i ∈ C, α i ∧
      (∑ i ∈ I, |β i|) = ∑ i ∈ C, |α i| ∧
      (∑ i ∈ I, β i • P i) = ∑ i ∈ C, α i • P i ∧
      ‖∑ i ∈ C, α i • Q i‖ ≤ ‖∑ i ∈ I, β i • Q i‖ := by
  classical
  let σ : Fin n → ℝ := fun i => if 0 ≤ α i then 1 else -1
  have hσ (i : Fin n) : |σ i| = 1 := by dsimp [σ]; split_ifs <;> norm_num
  have hα (i : Fin n) : |α i| * σ i = α i := by
    dsimp [σ]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  let z := ∑ i ∈ C, α i • Q i
  let v : Fin n → ℝ × ℝ^[d] := fun i => (σ i, σ i • P i)
  let g : Fin n → ℝ := fun i => inner ℝ z (σ i • Q i)
  obtain ⟨I, hIC, hI, b, hb, hm, hv, hg⟩ :=
    sparse_nonnegative_weights v g C (fun i => |α i|) (fun i _ => abs_nonneg _)
  let β : Fin n → ℝ := fun i => b i * σ i
  have hβ (i : Fin n) (hi : i ∈ I) : |β i| = b i := by
    simp [β, abs_mul, hσ, abs_of_nonneg (hb i hi)]
  have hsum : (∑ i ∈ I, β i) = ∑ i ∈ C, α i := by
    have hh := congrArg Prod.fst hv
    simpa [v, β, Prod.fst_sum, hα] using hh
  have hsource : (∑ i ∈ I, β i • P i) = ∑ i ∈ C, α i • P i := by
    have hh := congrArg Prod.snd hv
    simpa [v, β, Prod.snd_sum, ← mul_smul, hα] using hh
  have htarget : ‖z‖ ≤ ‖∑ i ∈ I, β i • Q i‖ := by
    have hh : ‖z‖ ^ 2 ≤ inner ℝ z (∑ i ∈ I, β i • Q i) := by
      calc
        _ = ∑ i ∈ C, |α i| * g i := by
          simp only [g, real_inner_smul_right, ← mul_assoc, hα]
          simp only [← real_inner_smul_right, ← inner_sum, z, real_inner_self_eq_norm_sq]
        _ ≤ _ := hg
        _ = _ := by simp [β, g, inner_sum, real_inner_smul_right, mul_assoc]
    have hCS := real_inner_le_norm z (∑ i ∈ I, β i • Q i)
    by_cases hz : ‖z‖ = 0
    · rw [hz]; exact norm_nonneg _
    · have hzpos := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
      nlinarith
  refine ⟨I, hIC, ?_, β, hsum, ?_, hsource, htarget⟩
  · simpa [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace,
      add_comm, add_left_comm, add_assoc] using hI
  · calc
      _ = ∑ i ∈ I, b i := Finset.sum_congr rfl hβ
      _ = _ := hm

private theorem affine_relation_finset {n d : ℕ} (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (α : Fin n → ℝ) (hα : ∑ i ∈ C, α i = 0) :
    |‖∑ i ∈ C, α i • P i‖ - ‖∑ i ∈ C, α i • Q i‖| ≤
      (rho P Q C : ℝ) * ∑ i ∈ C, |α i| := by
  have h := affine_relation_bound P Q C α
    (by simpa only [Finset.sum_coe_sort] using hα)
  rw [Finset.sum_coe_sort C (fun i => α i • P i),
    Finset.sum_coe_sort C (fun i => α i • Q i),
    Finset.sum_coe_sort C (fun i => |α i|)] at h
  exact h

private theorem affine_relation_one_sided {n d : ℕ} (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (α : Fin n → ℝ) (hα : ∑ i ∈ C, α i = 0) :
    ‖∑ i ∈ C, α i • Q i‖ - ‖∑ i ∈ C, α i • P i‖ ≤
      (rho_k P Q C (d + 2) : ℝ) * ∑ i ∈ C, |α i| := by
  obtain ⟨I, hIC, hI, β, hsum, habs, hsource, htarget⟩ := sparse_affine_relation P Q C α
  have h := affine_relation_finset P Q I β (hsum.trans hα)
  have hle : (rho P Q I : ℝ) ≤ rho_k P Q C (d + 2) := by
    exact_mod_cast le_rho_k P Q C I (d + 2) hIC hI
  have hmass : 0 ≤ ∑ i ∈ C, |α i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [hsource, habs] at h
  have hh := neg_le_abs (‖∑ i ∈ C, α i • P i‖ - ‖∑ i ∈ I, β i • Q i‖)
  have hmul := mul_le_mul_of_nonneg_right hle hmass
  linarith

/-- Lemma 4: zero-sum combinations are controlled by order d + 2. -/
theorem stronger_affine_relation_bound {n d : ℕ} (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (α : Fin n → ℝ) (hα : ∑ i : C, α i = 0) :
    |‖∑ i : C, α i • P i‖ - ‖∑ i : C, α i • Q i‖| ≤
      (rho_k P Q C (d + 2) : ℝ) * ∑ i : C, |α i| := by
  have hsum : ∑ i ∈ C, α i = 0 := by simpa only [Finset.sum_coe_sort] using hα
  have h₁ := affine_relation_one_sided P Q C α hsum
  have h₂ := affine_relation_one_sided Q P C α hsum
  rw [rho_k_symm] at h₂
  rw [Finset.sum_coe_sort C (fun i => α i • P i),
    Finset.sum_coe_sort C (fun i => α i • Q i),
    Finset.sum_coe_sort C (fun i => |α i|)]
  exact abs_le.mpr ⟨by linarith, h₂⟩

theorem stronger_affine_relation_bound_subtype {n d : ℕ} (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (α : C → ℝ) (hα : ∑ i, α i = 0) :
    |‖∑ i, α i • P i‖ - ‖∑ i, α i • Q i‖| ≤
      (rho_k P Q C (d + 2) : ℝ) * ∑ i, |α i| := by
  classical
  let β : Fin n → ℝ := fun i => if hi : i ∈ C then α ⟨i, hi⟩ else 0
  have hβ (i : C) : β i = α i := by simp [β, i.property]
  simpa only [hβ] using stronger_affine_relation_bound P Q C β (by simpa only [hβ] using hα)

end Sparsification

section Bounds

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem centered_map_affine (w : C → ℝ) (v : EuclideanSpace ℝ C)
    (hv : inner ℝ v (WithLp.toLp 2 w) = 0) :
    (∑ i, w i * v i = 0) ∧
      centered_map P C w v = ∑ i, (w i * v i) • P i := by
  classical
  have hz : ∑ i, w i * v i = 0 := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using hv
  refine ⟨hz, ?_⟩
  change (∑ i, v i • (w i • (P i - weighted_mean P C w))) = _
  simp only [smul_smul, smul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_comm (v _) (w _)]
  rw [← Finset.sum_smul, hz, zero_smul, sub_zero]

private theorem coefficient_mass_le_one (w : C → ℝ) (hw : w ∈ unit_weights C)
    (v : EuclideanSpace ℝ C) (hv : ‖v‖ = 1) : ∑ i, |w i * v i| ≤ 1 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |w i|) (fun i => |v i|)
  have hw' : ∑ i, w i ^ 2 = 1 := hw
  have hv' : ∑ i, v i ^ 2 = 1 := by
    simpa only [hv, one_pow] using (EuclideanSpace.real_norm_sq_eq v).symm
  simp only [← abs_mul, sq_abs, hw', hv', mul_one] at hcs
  have hnonneg : 0 ≤ ∑ i, |w i * v i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

theorem centered_norm_difference_le_higher_order (w : C → ℝ) (hw : w ∈ unit_weights C)
    (v : EuclideanSpace ℝ C) (unit_length : ‖v‖ = 1)
    (annihilates_weights : inner ℝ v (WithLp.toLp 2 w) = 0) :
    |‖centered_map P C w v‖ - ‖centered_map Q C w v‖| ≤ rho_k P Q C (d + 2) := by
  obtain ⟨zero_sum, source_relation⟩ := centered_map_affine P C w v annihilates_weights
  have target_relation := (centered_map_affine Q C w v annihilates_weights).2
  have relation_bound :=
    stronger_affine_relation_bound_subtype P Q C (fun i => w i * v i) zero_sum
  rw [← source_relation, ← target_relation] at relation_bound
  have mass_bound := coefficient_mass_le_one C w hw v unit_length
  exact relation_bound.trans (by
    simpa using mul_le_mul_of_nonneg_left mass_bound (NNReal.coe_nonneg _))

theorem weighted_error_le_higher_order (w : C → ℝ) (hw : w ∈ unit_weights C) :
    weighted_error P Q C w ≤ 2 * d * (rho_k P Q C (d + 2) : ℝ) ^ 2 := by
  classical
  obtain ⟨decomposition⟩ := weighted_procrustes_decomposition P Q C w hw
  have direction_bound (j : decomposition.Index) :
      (‖centered_map P C w (decomposition.vector j)‖ -
        ‖centered_map Q C w (decomposition.vector j)‖) ^ 2 ≤
        (rho_k P Q C (d + 2) : ℝ) ^ 2 := by
    have length_bound := centered_norm_difference_le_higher_order P Q C w hw
      (decomposition.vector j) (decomposition.orthonormal.norm_eq_one j)
      (decomposition.annihilates_weights j)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (NNReal.coe_nonneg _)).2 length_bound
  rw [decomposition.energy_identity]
  calc
    _ ≤ ∑ _j : decomposition.Index, (rho_k P Q C (d + 2) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun j _ => direction_bound j
    _ = Fintype.card decomposition.Index * (rho_k P Q C (d + 2) : ℝ) ^ 2 := by simp
    _ ≤ 2 * d * (rho_k P Q C (d + 2) : ℝ) ^ 2 := by
      gcongr
      exact_mod_cast decomposition.card_bound

theorem rho_sq_le_higher_order :
    (rho P Q C : ℝ) ^ 2 ≤ 4 * d * (rho_k P Q C (d + 2) : ℝ) ^ 2 := by
  have weighted_bound : maximum_weighted_error P Q C ≤
      2 * d * (rho_k P Q C (d + 2) : ℝ) ^ 2 :=
    maximum_weighted_error_le P Q C (by positivity)
      (weighted_error_le_higher_order P Q C)
  calc
    _ ≤ 2 * maximum_weighted_error P Q C := weighted_fitting_bound P Q C
    _ ≤ 4 * d * (rho_k P Q C (d + 2) : ℝ) ^ 2 := by linarith

theorem rho_le_higher_order :
    (rho P Q C : ℝ) ≤ 2 * Real.sqrt d * (rho_k P Q C (d + 2) : ℝ) := by
  have square_root_identity := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  apply (sq_le_sq₀ (NNReal.coe_nonneg _) (by positivity)).mp
  calc
    _ ≤ 4 * d * (rho_k P Q C (d + 2) : ℝ) ^ 2 := rho_sq_le_higher_order P Q C
    _ = (2 * Real.sqrt d * (rho_k P Q C (d + 2) : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, square_root_identity]
      ring

noncomputable def higher_order_factor (d : ℕ) : ℝ≥0 := 2 * NNReal.sqrt d

theorem rho_le_higher_order_nnreal :
    rho P Q C ≤ higher_order_factor d * rho_k P Q C (d + 2) := by
  apply NNReal.coe_le_coe.mp
  simpa [higher_order_factor] using rho_le_higher_order P Q C

theorem maximum_consensus_higher_order_lower (τ : ℝ≥0) (hd : 0 < d) :
    maximum_consensus_k P Q (τ / higher_order_factor d) (d + 2) ≤
      maximum_consensus P Q τ := by
  have hf : 0 < higher_order_factor d := by
    unfold higher_order_factor
    positivity
  unfold maximum_consensus_k maximum_consensus feasible
  apply FiniteConsistency.consensus_mono
  intro I hI
  exact (rho_le_higher_order_nnreal P Q I).trans (by
    simpa only [mul_comm] using (le_div_iff₀ hf).mp hI)

theorem maximum_consensus_higher_order_bounds (τ : ℝ≥0) (hd : 0 < d) :
    maximum_consensus_k P Q (τ / higher_order_factor d) (d + 2) ≤
      maximum_consensus P Q τ ∧
    maximum_consensus P Q τ ≤ maximum_consensus_k P Q τ (d + 2) :=
  ⟨maximum_consensus_higher_order_lower P Q τ hd, maximum_consensus_le_k P Q τ (d + 2)⟩

end Bounds

end HigherOrder
