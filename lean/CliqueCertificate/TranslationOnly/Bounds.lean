import CliqueCertificate.Basic
import CliqueCertificate.External.Jung

/-! Translation-only Jung bounds, exactness at order d + 1, and consistency graphs. -/

namespace Translation

section Definitions

open scoped NNReal Finset

variable {n d : ℕ}

def displacement (P Q : Fin n → ℝ^[d]) (R : O(d)) (i : Fin n) : ℝ^[d] := Q i - R (P i)

variable (μ : Fin n → ℝ^[d])

noncomputable def alignment_error (C : Finset (Fin n)) (t : ℝ^[d]) : ℝ≥0 :=
  C.sup fun i => nndist t (μ i)

noncomputable def rho (C : Finset (Fin n)) : ℝ≥0 :=
  ⨅ t, alignment_error μ C t

noncomputable def feasible (C : Finset (Fin n)) (τ : ℝ≥0) : Prop :=
  rho μ C ≤ τ

noncomputable def delta (C : Finset (Fin n)) : ℝ≥0 :=
  C.sup fun i => C.sup fun j => nndist (μ i) (μ j)

noncomputable def pairwise_consistent (C : Finset (Fin n)) (ε : ℝ≥0) : Prop :=
  delta μ C ≤ ε

noncomputable def rho_k (C : Finset (Fin n)) (k : ℕ) : ℝ≥0 :=
  TranslationGeometry.rhoK (rho μ) k C

noncomputable def maximum_consensus (τ : ℝ≥0) : ℕ :=
  TranslationGeometry.maxConsensus Finset.univ (rho μ) τ

noncomputable def maximum_consensus_k (τ : ℝ≥0) (k : ℕ) : ℕ :=
  TranslationGeometry.mcK Finset.univ (rho μ) k τ

noncomputable def max_clique (ε : ℝ≥0) : ℕ :=
  TranslationGeometry.maxConsensus Finset.univ (delta μ) ε

noncomputable def jung_constant (d : ℕ) : ℝ≥0 :=
  NNReal.sqrt ((d : ℝ≥0) / (2 * ((d : ℝ≥0) + 1)))

noncomputable def jung_factor (d k : ℕ) : ℝ≥0 :=
  NNReal.sqrt (((d : ℝ≥0) * k) / (((d : ℝ≥0) + 1) * (k - 1 : ℕ)))

end Definitions

end Translation

section Bounds

namespace TranslationGeometry

export FiniteConsistency (maxConsensus_le_of_feasible maxConsensus_scaled_lower)

end TranslationGeometry

namespace Translation

open scoped NNReal Finset

variable {n d : ℕ} (μ : Fin n → ℝ^[d])

theorem residual_eq (P Q : Fin n → ℝ^[d]) (R : O(d)) (t : ℝ^[d]) (i : Fin n) :
    ‖R (P i) + t - Q i‖₊ = nndist t (displacement P Q R i) := by
  rw [nndist_eq_nnnorm]
  congr 1
  dsimp [displacement]
  abel

theorem alignment_error_eq_residual (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (R : O(d)) (t : ℝ^[d]) :
    alignment_error (displacement P Q R) C t = C.sup (fun i => ‖R (P i) + t - Q i‖₊) := by
  simp only [alignment_error, residual_eq]

theorem rho_attained (C : Finset (Fin n)) :
    ∃ t, alignment_error μ C t = rho μ C :=
  TranslationGeometry.translationError_attained μ C

theorem rho_le_iff_exists_translation (C : Finset (Fin n)) (τ : ℝ≥0) :
    rho μ C ≤ τ ↔ ∃ t, ∀ i ∈ C, nndist t (μ i) ≤ τ :=
  TranslationGeometry.translationError_le_iff μ C τ

theorem fixed_rotation_feasible_iff_exists_translation (P Q : Fin n → ℝ^[d])
    (C : Finset (Fin n)) (R : O(d)) (τ : ℝ≥0) :
    feasible (displacement P Q R) C τ ↔ ∃ t, ∀ i ∈ C, ‖R (P i) + t - Q i‖₊ ≤ τ := by
  simp_rw [residual_eq]
  exact rho_le_iff_exists_translation (displacement P Q R) C τ

theorem rho_mono : Monotone (rho μ) :=
  TranslationGeometry.translationError_mono μ

theorem delta_le_iff (C : Finset (Fin n)) (ε : ℝ≥0) :
    delta μ C ≤ ε ↔ ∀ i ∈ C, ∀ j ∈ C,
      nndist (μ i) (μ j) ≤ ε :=
  TranslationGeometry.pairMax_le_iff _ C ε

theorem half_delta_le_rho (C : Finset (Fin n)) :
    delta μ C / 2 ≤ rho μ C :=
  TranslationGeometry.half_diameter_le_translationError μ C

theorem rho_le_jung_delta (C : Finset (Fin n)) (hd : 1 ≤ d) :
    rho μ C ≤ jung_constant d * delta μ C := by
  change TranslationGeometry.translationError μ C ≤
    jung_constant d * TranslationGeometry.cloudDiameter μ C
  simpa [jung_constant, TranslationGeometry.jungConstant] using
    TranslationGeometry.translation_jung_upper μ C (by simpa using hd)

theorem jung_bounds (C : Finset (Fin n)) (hd : 1 ≤ d) :
    delta μ C / 2 ≤ rho μ C ∧
      rho μ C ≤ jung_constant d * delta μ C :=
  ⟨half_delta_le_rho μ C, rho_le_jung_delta μ C hd⟩

theorem feasible_implies_pairwise_consistent (C : Finset (Fin n)) (τ : ℝ≥0)
    (h : feasible μ C τ) : pairwise_consistent μ C (2 * τ) := by
  have hbound := (half_delta_le_rho μ C).trans h
  simpa [pairwise_consistent, mul_comm] using
    (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).1 hbound

theorem pairwise_consistent_implies_feasible (C : Finset (Fin n)) (τ : ℝ≥0)
    (hd : 1 ≤ d) (h : pairwise_consistent μ C (τ / jung_constant d)) :
    feasible μ C τ := by
  have hJ : 0 < jung_constant d := TranslationGeometry.jungConstant_pos hd
  exact (rho_le_jung_delta μ C hd).trans (by
    calc
      jung_constant d * delta μ C ≤ jung_constant d * (τ / jung_constant d) :=
        mul_le_mul_of_nonneg_left h zero_le
      _ = τ := by field_simp)

theorem rho_pair (i j : Fin n) :
    rho μ {i, j} = nndist (μ i) (μ j) / 2 :=
  TranslationGeometry.translationError_pair μ i j

theorem rho_two (C : Finset (Fin n)) :
    rho_k μ C 2 = delta μ C / 2 :=
  TranslationGeometry.translation_rho_two μ C

theorem pairwise_consistent_iff_rho_two (C : Finset (Fin n)) (τ : ℝ≥0) :
    pairwise_consistent μ C (2 * τ) ↔ rho_k μ C 2 ≤ τ := by
  rw [pairwise_consistent, rho_two, div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
  rw [mul_comm τ 2]

theorem max_clique_eq_maximum_consensus_two (τ : ℝ≥0) :
    max_clique μ (2 * τ) = maximum_consensus_k μ τ 2 := by
  unfold max_clique maximum_consensus_k TranslationGeometry.mcK TranslationGeometry.maxConsensus
  congr 1
  apply Finset.filter_congr
  intro C _
  exact pairwise_consistent_iff_rho_two μ C τ

theorem clique_sandwich (τ : ℝ≥0) (hd : 1 ≤ d) :
    max_clique μ (τ / jung_constant d) ≤ maximum_consensus μ τ ∧
      maximum_consensus μ τ ≤ max_clique μ (2 * τ) := by
  constructor
  · apply TranslationGeometry.maxConsensus_scaled_lower
    · exact TranslationGeometry.jungConstant_pos hd
    · intro C _
      exact rho_le_jung_delta μ C hd
  · apply TranslationGeometry.maxConsensus_le_of_feasible
    intro C _ hC
    exact feasible_implies_pairwise_consistent μ C τ hC

theorem rho_le_jung_factor_rho_k (C : Finset (Fin n)) (k : ℕ)
    (hk : 2 ≤ k) (hkd : k ≤ d + 1) :
    rho μ C ≤ jung_factor d k * rho_k μ C k := by
  change TranslationGeometry.translationError μ C ≤
    jung_factor d k * TranslationGeometry.rhoK
      (TranslationGeometry.translationError μ) k C
  simpa [jung_factor, TranslationGeometry.jungFactor] using
    TranslationGeometry.translation_jung_higher μ C k hk (by simpa using hkd)

theorem higher_order_sandwich (τ : ℝ≥0) (k : ℕ)
    (hk : 2 ≤ k) (hkd : k ≤ d + 1) :
    maximum_consensus_k μ (τ / jung_factor d k) k ≤ maximum_consensus μ τ ∧
      maximum_consensus μ τ ≤ maximum_consensus_k μ τ k := by
  unfold maximum_consensus_k maximum_consensus TranslationGeometry.mcK
  constructor
  · apply TranslationGeometry.maxConsensus_scaled_lower
    · exact TranslationGeometry.jungFactor_pos (by omega) hk
    · intro C _
      exact rho_le_jung_factor_rho_k μ C k hk hkd
  · exact TranslationGeometry.maxConsensus_le_mcK Finset.univ _ (rho_mono μ) k τ

theorem feasible_iff_small_subsets (C : Finset (Fin n)) (τ : ℝ≥0) :
    feasible μ C τ ↔ ∀ I ⊆ C, #I ≤ d + 1 → feasible μ I τ := by
  simpa [feasible, rho, alignment_error, TranslationGeometry.translationError,
    TranslationGeometry.minimaxError] using
    TranslationGeometry.translationError_le_iff_small_groups μ C τ

theorem rho_k_eq_rho_of_dimension (C : Finset (Fin n)) :
    rho_k μ C (d + 1) = rho μ C := by
  change TranslationGeometry.rhoK (TranslationGeometry.translationError μ) (d + 1) C =
    TranslationGeometry.translationError μ C
  simpa using TranslationGeometry.translation_rho_dimension μ C

theorem maximum_consensus_k_eq_of_dimension (τ : ℝ≥0) :
    maximum_consensus_k μ τ (d + 1) = maximum_consensus μ τ := by
  change TranslationGeometry.mcK Finset.univ (TranslationGeometry.translationError μ) (d + 1) τ =
    TranslationGeometry.maxConsensus Finset.univ (TranslationGeometry.translationError μ) τ
  simpa using TranslationGeometry.translation_mc_dimension μ Finset.univ τ

theorem rho_k_le_iff (C : Finset (Fin n)) (k : ℕ) (τ : ℝ≥0) :
    rho_k μ C k ≤ τ ↔ ∀ I ⊆ C, #I ≤ k → feasible μ I τ :=
  TranslationGeometry.rhoK_le_iff (rho μ) k C τ

theorem rho_k_mono (C : Finset (Fin n)) {k l : ℕ} (hkl : k ≤ l) :
    rho_k μ C k ≤ rho_k μ C l :=
  TranslationGeometry.rhoK_mono _ C hkl

theorem rho_k_le_rho (C : Finset (Fin n)) (k : ℕ) :
    rho_k μ C k ≤ rho μ C :=
  TranslationGeometry.rhoK_le_rho _ (rho_mono μ) k C

theorem maximum_consensus_k_antitone (τ : ℝ≥0) {k l : ℕ} (hkl : k ≤ l) :
    maximum_consensus_k μ τ l ≤ maximum_consensus_k μ τ k :=
  TranslationGeometry.mcK_antitone Finset.univ _ τ hkl

theorem rho_k_eq_rho_of_ge_dimension (C : Finset (Fin n)) {k : ℕ}
    (hk : d + 1 ≤ k) : rho_k μ C k = rho μ C := by
  apply le_antisymm (rho_k_le_rho μ C k)
  rw [← rho_k_eq_rho_of_dimension μ C]
  exact rho_k_mono μ C hk

theorem maximum_consensus_k_eq_of_ge_dimension (τ : ℝ≥0) {k : ℕ}
    (hk : d + 1 ≤ k) : maximum_consensus_k μ τ k = maximum_consensus μ τ := by
  unfold maximum_consensus_k maximum_consensus TranslationGeometry.mcK
  have heq : TranslationGeometry.rhoK (rho μ) k = rho μ :=
    funext fun C => rho_k_eq_rho_of_ge_dimension μ C hk
  rw [heq]

theorem small_subsets_imply_fit (C : Finset (Fin n)) (τ : ℝ≥0) (k : ℕ)
    (hk : 2 ≤ k) (hkd : k ≤ d + 1)
    (h : ∀ I ⊆ C, #I ≤ k → feasible μ I τ) :
    ∃ t, ∀ i ∈ C, nndist t (μ i) ≤ τ * jung_factor d k := by
  apply (rho_le_iff_exists_translation μ C _).1
  calc
    rho μ C ≤ jung_factor d k * rho_k μ C k :=
      rho_le_jung_factor_rho_k μ C k hk hkd
    _ ≤ jung_factor d k * τ :=
      mul_le_mul_of_nonneg_left ((rho_k_le_iff μ C k τ).2 h) zero_le
    _ = τ * jung_factor d k := mul_comm _ _

theorem rho_eq_half_delta_one_dimension
    (μ : Fin n → ℝ^[1]) (C : Finset (Fin n)) :
    rho μ C = delta μ C / 2 := by
  rw [← rho_k_eq_rho_of_dimension μ C]
  exact rho_two μ C

theorem maximum_consensus_eq_max_clique_one_dimension
    (μ : Fin n → ℝ^[1]) (τ : ℝ≥0) :
    maximum_consensus μ τ = max_clique μ (2 * τ) := by
  rw [max_clique_eq_maximum_consensus_two]
  exact (maximum_consensus_k_eq_of_dimension μ τ).symm

theorem jung_factor_two (d : ℕ) : jung_factor d 2 = 2 * jung_constant d :=
  TranslationGeometry.jungFactor_two d

theorem jung_factor_dimension {d : ℕ} (hd : 1 ≤ d) : jung_factor d (d + 1) = 1 :=
  TranslationGeometry.jungFactor_dimension hd

end Translation

end Bounds

namespace Translation

section Graphs

open scoped NNReal Finset

variable {n d : ℕ} (μ : Fin n → ℝ^[d])

noncomputable def consistency_graph (ε : ℝ≥0) : SimpleGraph (Fin n) :=
  ConsistencyGraph.threshold (fun i j => nndist (μ i) (μ j))
    (fun i j => nndist_comm (μ i) (μ j)) ε

theorem isClique_consistency_graph_iff (ε : ℝ≥0) (C : Finset (Fin n)) :
    (consistency_graph μ ε).IsClique C ↔ pairwise_consistent μ C ε := by
  rw [consistency_graph, ConsistencyGraph.isClique_threshold_iff _ _ (by simp),
    pairwise_consistent, delta_le_iff]

theorem cliqueNum_consistency_graph (ε : ℝ≥0) :
    (consistency_graph μ ε).cliqueNum = max_clique μ ε := by
  classical
  rw [ConsistencyGraph.cliqueNum_eq_iSup]
  simp_rw [isClique_consistency_graph_iff]
  simp only [max_clique, TranslationGeometry.maxConsensus, Finset.sup_eq_ciSup,
    Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  rfl

theorem graph_clique_sandwich (τ : ℝ≥0) (hd : 1 ≤ d) :
    (consistency_graph μ (τ / jung_constant d)).cliqueNum ≤ maximum_consensus μ τ ∧
      maximum_consensus μ τ ≤ (consistency_graph μ (2 * τ)).cliqueNum := by
  simp_rw [cliqueNum_consistency_graph]
  exact clique_sandwich μ τ hd

end Graphs

end Translation
