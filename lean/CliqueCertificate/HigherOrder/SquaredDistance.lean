import CliqueCertificate.HigherOrder.Bounds

/-! The squared-distance bound (Proposition 1), clique certificate, and diameter constants. -/

open EuclideanGeometry

namespace HigherOrder

section ErrorBound

open scoped NNReal Finset

section Frobenius

variable {V E ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]

theorem orthonormal_energy_le_frobenius (L : V →ₗ[ℝ] E) (v : ι → V)
    (hv : Orthonormal ℝ v) : ∑ i, ‖L (v i)‖ ^ 2 ≤ frobenius_sq L := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hexp (i : ι) : ‖L (v i)‖ ^ 2 =
      ∑ j, (inner ℝ (v i) (L.adjoint (b j))) ^ 2 := by
    rw [← b.repr.norm_map (L (v i)), EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    rw [OrthonormalBasis.repr_apply_apply, L.adjoint_inner_right, real_inner_comm]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j, ‖L.adjoint (b j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.norm_eq_abs, sq_abs] using
        (hv.sum_inner_products_le (s := Finset.univ) (L.adjoint (b j)))
    _ = frobenius_sq L.adjoint := (frobenius_sq_eq_sum _ b).symm
    _ = frobenius_sq L := by
      simp only [frobenius_sq, LinearMap.adjoint_adjoint]
      exact LinearMap.trace_comp_comm' _ _

theorem orthonormal_quadratic_energy_le (L : V →ₗ[ℝ] V) (v : ι → V)
    (hv : Orthonormal ℝ v) :
    ∑ i, (inner ℝ (v i) (L (v i))) ^ 2 ≤ frobenius_sq L := by
  apply LE.le.trans _ (orthonormal_energy_le_frobenius L v hv)
  apply Finset.sum_le_sum
  intro i _
  have hh := abs_real_inner_le_norm (v i) (L (v i))
  rw [hv.1 i, one_mul] at hh
  nlinarith [sq_abs (inner ℝ (v i) (L (v i))), abs_nonneg (inner ℝ (v i) (L (v i))),
    norm_nonneg (L (v i))]

end Frobenius

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem squared_distance_error_le (i j : C) :
    |‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2| ≤ (squared_distance_error P Q C : ℝ) := by
  change ((⟨|‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2|, abs_nonneg _⟩ : ℝ≥0) : ℝ) ≤ _
  apply NNReal.coe_le_coe.mpr
  unfold squared_distance_error
  let f (i j : C) : ℝ≥0 := ⟨|‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2|, abs_nonneg _⟩
  exact (le_ciSup (f := fun j : C => f i j) (Set.finite_range _).bddAbove j).trans
    (le_ciSup (f := fun i : C => ⨆ j : C, f i j) (Set.finite_range _).bddAbove i)

theorem squared_distance_error_le_iff (ε : ℝ≥0) :
    squared_distance_error P Q C ≤ ε ↔
      ∀ i j : C, |‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2| ≤ (ε : ℝ) := by
  constructor
  · intro bound i j
    exact (squared_distance_error_le P Q C i j).trans (NNReal.coe_le_coe.mpr bound)
  · intro pair_bound
    exact ciSup_le' fun i => ciSup_le' fun j => NNReal.coe_le_coe.mp (pair_bound i j)

noncomputable def distance_difference_map (w : C → ℝ) :
    EuclideanSpace ℝ C →ₗ[ℝ] EuclideanSpace ℝ C where
  toFun v := WithLp.toLp 2 (fun i => ∑ j,
    (w i * w j * (‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2)) * v j)
  map_add' x y := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext i; simp [mul_left_comm, Finset.mul_sum]

private theorem affine_squared_distances {ι : Type*} [Fintype ι]
    (X : ι → ℝ^[d]) (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    (∑ i, ∑ j, a i * a j * ‖X i - X j‖ ^ 2) = -2 * ‖∑ i, a i • X i‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, a i * a j * ‖X i‖ ^ 2) = 0 := by
    simp_rw [mul_right_comm (a _) (a _) _, ← Finset.mul_sum, ha, mul_zero]
    simp
  have h2 : (∑ i, ∑ j, a i * a j * ‖X j‖ ^ 2) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.sum_mul, ha, zero_mul]
    simp
  have h3 : (∑ i, ∑ j, a i * a j * inner ℝ (X i) (X j)) =
      ‖∑ i, a i • X i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (X j) (X i)]
    ring
  have hexpand (i j : ι) : a i * a j * ‖X i - X j‖ ^ 2 =
      a i * a j * ‖X i‖ ^ 2 + a i * a j * ‖X j‖ ^ 2 -
        2 * (a i * a j * inner ℝ (X i) (X j)) := by
    rw [norm_sub_sq_real]
    ring
  simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]
  ring

theorem distance_difference_quadratic (w : C → ℝ) (v : EuclideanSpace ℝ C)
    (hv : inner ℝ v (WithLp.toLp 2 w) = 0) :
    inner ℝ v (distance_difference_map P Q C w v) =
      -2 * (‖centered_map P C w v‖ ^ 2 - ‖centered_map Q C w v‖ ^ 2) := by
  classical
  obtain ⟨hz, hP⟩ := centered_map_affine P C w v hv
  have hQ := (centered_map_affine Q C w v hv).2
  have heq : inner ℝ v (distance_difference_map P Q C w v) =
      (∑ i, ∑ j, (w i * v i) * (w j * v j) * ‖P i - P j‖ ^ 2) -
        (∑ i, ∑ j, (w i * v i) * (w j * v j) * ‖Q i - Q j‖ ^ 2) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      distance_difference_map, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, w i * w j * (‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2) * v j) * v i = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, affine_squared_distances _ _ hz, affine_squared_distances _ _ hz, hP, hQ]
  ring

theorem distance_difference_frobenius_le (w : C → ℝ) (hw : w ∈ unit_weights C) :
    frobenius_sq (distance_difference_map P Q C w) ≤
      (squared_distance_error P Q C : ℝ) ^ 2 := by
  classical
  rw [frobenius_sq_eq_sum _ (EuclideanSpace.basisFun C ℝ)]
  have heq (j : C) : ‖distance_difference_map P Q C w (EuclideanSpace.basisFun C ℝ j)‖ ^ 2 =
      ∑ i, (w i * w j) ^ 2 * (‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [distance_difference_map, EuclideanSpace.basisFun_apply, mul_pow]
  simp_rw [heq]
  calc
    _ ≤ ∑ j : C, ∑ i : C, (w i * w j) ^ 2 * (squared_distance_error P Q C : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hh := squared_distance_error_le P Q C i j
      have hn := NNReal.coe_nonneg (squared_distance_error P Q C)
      nlinarith [sq_abs (‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2),
        abs_nonneg (‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2)]
    _ = (squared_distance_error P Q C : ℝ) ^ 2 := by
      have hw' : ∑ i, w i ^ 2 = 1 := hw
      simp_rw [mul_pow, mul_assoc, ← Finset.sum_mul, hw', one_mul, ← Finset.sum_mul]
      rw [hw', one_mul]

private theorem norm_difference_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (by nlinarith : a ^ 2 - b ^ 2 ≤ 0)]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]
  · rw [abs_of_nonneg (by nlinarith : 0 ≤ a ^ 2 - b ^ 2)]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hab)]

theorem weighted_error_le_squared_distance (w : C → ℝ) (hw : w ∈ unit_weights C) :
    weighted_error P Q C w ≤ Real.sqrt (2 * d) / 2 * squared_distance_error P Q C := by
  classical
  obtain ⟨decomposition⟩ := weighted_procrustes_decomposition P Q C w hw
  let distance_difference := distance_difference_map P Q C w
  let quadratic_form (j : decomposition.Index) :=
    inner ℝ (decomposition.vector j) (distance_difference (decomposition.vector j))
  have direction_bound (j : decomposition.Index) :
      (‖centered_map P C w (decomposition.vector j)‖ -
        ‖centered_map Q C w (decomposition.vector j)‖) ^ 2 ≤ |quadratic_form j| / 2 := by
    have length_bound := norm_difference_sq_le _ _
      (norm_nonneg (centered_map P C w (decomposition.vector j)))
      (norm_nonneg (centered_map Q C w (decomposition.vector j)))
    have quadratic_identity := distance_difference_quadratic P Q C w
      (decomposition.vector j) (decomposition.annihilates_weights j)
    change quadratic_form j = _ at quadratic_identity
    rw [quadratic_identity, abs_mul]
    norm_num
    exact length_bound
  have energy_bound : (∑ j, quadratic_form j ^ 2) ≤ (squared_distance_error P Q C : ℝ) ^ 2 :=
    (orthonormal_quadratic_energy_le distance_difference decomposition.vector
      decomposition.orthonormal).trans (distance_difference_frobenius_le P Q C w hw)

  have sum_bound :
      ∑ j, |quadratic_form j| ≤ Real.sqrt (2 * d) * squared_distance_error P Q C := by
    calc
      _ ≤ Real.sqrt (Fintype.card decomposition.Index) *
          Real.sqrt (∑ j, quadratic_form j ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun _j : decomposition.Index => (1 : ℝ)) (fun j => |quadratic_form j|)
      _ ≤ Real.sqrt (2 * d) * Real.sqrt ((squared_distance_error P Q C : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast decomposition.card_bound
      _ = Real.sqrt (2 * d) * squared_distance_error P Q C := by
        rw [Real.sqrt_sq (NNReal.coe_nonneg _)]
  rw [decomposition.energy_identity]
  calc
    _ ≤ ∑ j, |quadratic_form j| / 2 := Finset.sum_le_sum fun j _ => direction_bound j
    _ = (∑ j, |quadratic_form j|) / 2 := by rw [Finset.sum_div]
    _ ≤ Real.sqrt (2 * d) / 2 * squared_distance_error P Q C := by linarith

/-- Proposition 1: squared-distance discrepancies control the squared fitting error. -/
theorem rho_sq_le_squared_distance :
    (rho P Q C : ℝ) ^ 2 ≤ Real.sqrt (2 * d) * squared_distance_error P Q C := by
  have weighted_bound : maximum_weighted_error P Q C ≤
      Real.sqrt (2 * d) / 2 * squared_distance_error P Q C :=
    maximum_weighted_error_le P Q C (by positivity)
      (weighted_error_le_squared_distance P Q C)
  calc
    _ ≤ 2 * maximum_weighted_error P Q C := weighted_fitting_bound P Q C
    _ ≤ Real.sqrt (2 * d) * squared_distance_error P Q C := by linarith

theorem cloud_pair_distance_le (i j : C) : ‖P i - P j‖₊ ≤ cloud_diameter P C :=
  (le_ciSup (f := fun j : C => ‖P i - P j‖₊) (Set.finite_range _).bddAbove j).trans
    (le_ciSup (f := fun i : C => ⨆ j : C, ‖P i - P j‖₊)
      (Set.finite_range _).bddAbove i)

theorem cloud_diameter_le_iff (D : ℝ≥0) :
    cloud_diameter P C ≤ D ↔ ∀ i j : C, ‖P i - P j‖₊ ≤ D := by
  constructor
  · intro bound i j
    exact (cloud_pair_distance_le P C i j).trans bound
  · intro pair_bound
    exact ciSup_le' fun i => ciSup_le' fun j => pair_bound i j

theorem squared_distance_error_le_diameter_delta :
    squared_distance_error P Q C ≤ combined_diameter P Q C * delta P Q C := by
  apply (squared_distance_error_le_iff P Q C _).2
  intro i j
  change |‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2| ≤
    (combined_diameter P Q C : ℝ) * (delta P Q C : ℝ)
  have hsum : ‖P i - P j‖ + ‖Q i - Q j‖ ≤ (combined_diameter P Q C : ℝ) := by
    exact_mod_cast add_le_add (cloud_pair_distance_le P C i j) (cloud_pair_distance_le Q C i j)
  have hdiff : |‖P i - P j‖ - ‖Q i - Q j‖| ≤ (delta P Q C : ℝ) := by
    have hh := NNReal.coe_le_coe.mpr
      ((delta_le_iff P Q C _).1 le_rfl i i.property j j.property)
    simpa only [coe_nndist, NNReal.dist_eq, coe_nnnorm] using hh
  have heq : |‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2| =
      (‖P i - P j‖ + ‖Q i - Q j‖) * |‖P i - P j‖ - ‖Q i - Q j‖| := by
    rw [show ‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2 =
      (‖P i - P j‖ + ‖Q i - Q j‖) * (‖P i - P j‖ - ‖Q i - Q j‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq]
  exact mul_le_mul hsum hdiff (abs_nonneg _) (NNReal.coe_nonneg _)

theorem rho_sq_le_diameter_delta :
    (rho P Q C : ℝ) ^ 2 ≤ Real.sqrt (2 * d) * combined_diameter P Q C * delta P Q C := by
  have hh := NNReal.coe_le_coe.mpr (squared_distance_error_le_diameter_delta P Q C)
  exact (rho_sq_le_squared_distance P Q C).trans (by
    simpa only [NNReal.coe_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _))

theorem target_diameter_le_source_add_delta :
    cloud_diameter Q C ≤ cloud_diameter P C + delta P Q C := by
  apply (cloud_diameter_le_iff Q C _).2
  intro i j
  apply (NNReal.le_add_nndist ‖Q i - Q j‖₊ ‖P i - P j‖₊).trans
  refine add_le_add (cloud_pair_distance_le P C i j) ?_
  simpa only [nndist_comm] using (delta_le_iff P Q C _).1 le_rfl i i.property j j.property

theorem squared_distance_error_le_source_diameter_delta :
    squared_distance_error P Q C ≤ (2 * cloud_diameter P C + delta P Q C) * delta P Q C := by
  apply (squared_distance_error_le_diameter_delta P Q C).trans
  apply mul_le_mul_of_nonneg_right _ (show 0 ≤ delta P Q C from zero_le)
  simpa only [combined_diameter, two_mul, add_assoc] using
    add_le_add (le_refl (cloud_diameter P C)) (target_diameter_le_source_add_delta P Q C)

theorem rho_sq_le_source_diameter_delta :
    (rho P Q C : ℝ) ^ 2 ≤
      Real.sqrt (2 * d) * (2 * cloud_diameter P C + delta P Q C) * delta P Q C := by
  have hh := NNReal.coe_le_coe.mpr (squared_distance_error_le_source_diameter_delta P Q C)
  exact (rho_sq_le_squared_distance P Q C).trans (by
    simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _))

theorem rho_le_source_diameter_of_small_delta (ε : ℝ≥0) (c : ℝ)
    (hδ : delta P Q C ≤ ε) (hε : ε ≤ cloud_diameter P C / 100)
    (hc : 0 ≤ c) (hfactor : Real.sqrt (2 * d) * (201 / 100) ≤ c ^ 2) :
    (rho P Q C : ℝ) ≤ c * Real.sqrt ((cloud_diameter P C : ℝ) * ε) := by
  apply (sq_le_sq₀ (NNReal.coe_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hδ' : (delta P Q C : ℝ) ≤ ε := NNReal.coe_le_coe.mpr hδ
  have hε' : (ε : ℝ) ≤ (cloud_diameter P C : ℝ) / 100 := by exact_mod_cast hε
  calc
    _ ≤ Real.sqrt (2 * d) * (2 * cloud_diameter P C + delta P Q C) * delta P Q C :=
      rho_sq_le_source_diameter_delta P Q C
    _ ≤ Real.sqrt (2 * d) * (2 * cloud_diameter P C + ε) * ε := by gcongr
    _ ≤ Real.sqrt (2 * d) * ((201 / 100) * cloud_diameter P C) * ε := by
      gcongr
      linarith
    _ = (Real.sqrt (2 * d) * (201 / 100)) * ((cloud_diameter P C : ℝ) * ε) := by ring
    _ ≤ c ^ 2 * ((cloud_diameter P C : ℝ) * ε) := by gcongr

theorem rho_le_source_diameter_2d {n : ℕ} (P Q : Fin n → ℝ^[2]) (C : Finset (Fin n))
    (ε : ℝ≥0) (hδ : delta P Q C ≤ ε) (hε : ε ≤ cloud_diameter P C / 100) :
    (rho P Q C : ℝ) ≤ (201 / 100) * Real.sqrt ((cloud_diameter P C : ℝ) * ε) := by
  apply rho_le_source_diameter_of_small_delta P Q C ε (201 / 100) hδ hε (by norm_num)
  norm_num

theorem rho_le_source_diameter_3d {n : ℕ} (P Q : Fin n → ℝ^[3]) (C : Finset (Fin n))
    (ε : ℝ≥0) (hδ : delta P Q C ≤ ε) (hε : ε ≤ cloud_diameter P C / 100) :
    (rho P Q C : ℝ) ≤ (222 / 100) * Real.sqrt ((cloud_diameter P C : ℝ) * ε) := by
  apply rho_le_source_diameter_of_small_delta P Q C ε (222 / 100) hδ hε (by norm_num)
  have hs : Real.sqrt 6 ≤ 49 / 20 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  norm_num only [Nat.cast_ofNat] at *
  linarith

theorem feasible_of_squared_distance (τ : ℝ≥0)
    (h : Real.sqrt (2 * d) * squared_distance_error P Q C ≤ (τ : ℝ) ^ 2) :
    feasible P Q C τ := by
  apply NNReal.coe_le_coe.mp
  exact (sq_le_sq₀ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).mp
    ((rho_sq_le_squared_distance P Q C).trans h)

end ErrorBound

section Certificate

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

noncomputable def squared_pair_error (i j : Fin n) : ℝ≥0 :=
  ⟨|‖P i - P j‖ ^ 2 - ‖Q i - Q j‖ ^ 2|, abs_nonneg _⟩

noncomputable def squared_consistency_graph (η : ℝ≥0) : SimpleGraph (Fin n) :=
  ConsistencyGraph.threshold
    (squared_pair_error P Q)
    (by
      intro i j
      apply NNReal.eq
      simp only [squared_pair_error, norm_sub_rev (P i), norm_sub_rev (Q i)]) η

theorem isClique_squared_consistency_graph_iff (η : ℝ≥0) (C : Finset (Fin n)) :
    (squared_consistency_graph P Q η).IsClique C ↔ squared_distance_error P Q C ≤ η := by
  rw [squared_consistency_graph, ConsistencyGraph.isClique_threshold_iff _ _ (by
    intro i
    apply NNReal.eq
    change |‖P i - P i‖ ^ 2 - ‖Q i - Q i‖ ^ 2| = 0
    simp)]
  constructor
  · intro h
    exact ciSup_le' fun i => ciSup_le' fun j => h i i.property j j.property
  · intro h i hi j hj
    exact (squared_distance_error_le P Q C ⟨i, hi⟩ ⟨j, hj⟩).trans h

theorem cliqueNum_squared_graph_le_consensus (η τ : ℝ≥0)
    (hη : Real.sqrt (2 * d) * (η : ℝ) ≤ (τ : ℝ) ^ 2) :
    (squared_consistency_graph P Q η).cliqueNum ≤ maximum_consensus P Q τ := by
  apply cliqueNum_le_maximum_consensus
  intro C hC
  apply feasible_of_squared_distance P Q C τ
  exact (mul_le_mul_of_nonneg_left
    (NNReal.coe_le_coe.mpr ((isClique_squared_consistency_graph_iff P Q η C).mp hC))
    (Real.sqrt_nonneg _)).trans hη

theorem squared_distance_clique_bound (τ : ℝ≥0) (hd : 0 < d) :
    (squared_consistency_graph P Q (τ ^ 2 / NNReal.sqrt (2 * d))).cliqueNum ≤
      maximum_consensus P Q τ := by
  apply cliqueNum_squared_graph_le_consensus
  have hs : 0 < Real.sqrt (2 * (d : ℝ)) := by positivity
  simp only [NNReal.coe_div, NNReal.coe_pow, Real.coe_sqrt, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_natCast]
  exact (mul_div_cancel₀ _ hs.ne').le

end Certificate

end HigherOrder
