import CliqueCertificate.ProperMotion.Anchors
import CliqueCertificate.HigherOrder.OptimalOrder

/-! The proper group-k bound (Proposition 3) and the critical order d + 1. -/

namespace Proper

section Bounds

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem point_error_le_alignment (T : SE(d)) {i : Fin n} (hi : i ∈ C) :
    ‖T (P i) - Q i‖₊ ≤ alignment_error P Q C T :=
  (alignment_error_fits P Q C T).nnnorm_le hi

theorem rho_le_higher_order :
    rho P Q C ≤ (2 * d + 1 : ℝ≥0) * rho_k P Q C (d + 1) := by
  classical
  let ε := rho_k P Q C (d + 1)

  obtain ⟨anchors, anchors_subset, anchors_card, anchor_control⟩ := anchor_control_pointwise P C
  have anchors_feasible : rho P Q anchors ≤ ε :=
    le_rho_k P Q C anchors (d + 1) anchors_subset (anchors_card.trans (Nat.le_succ d))
  obtain ⟨base_motion, base_fit⟩ := (rho_le_iff_exists_fit P Q anchors ε).mp anchors_feasible

  have global_fit : Fits P Q C ((2 * d + 1 : ℝ≥0) * ε) base_motion := by
    intro i hi
    have local_feasible : rho P Q (insert i anchors) ≤ ε :=
      le_rho_k P Q C _ (d + 1) (Finset.insert_subset hi anchors_subset)
        ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right anchors_card 1))
    obtain ⟨local_motion, local_fit⟩ :=
      (rho_le_iff_exists_fit P Q (insert i anchors) ε).mp local_feasible

    have anchor_agreement (j : Fin n) (hj : j ∈ anchors) :
        ‖base_motion (P j) - local_motion (P j)‖ ≤ 2 * (ε : ℝ) := by
      simpa only [two_mul] using
        base_fit.disagreement_le local_fit hj (Finset.mem_insert_of_mem hj)
    have point_agreement :=
      anchor_control base_motion local_motion (2 * ε) (by positivity) anchor_agreement i hi

    calc
      _ ≤ ‖base_motion (P i) - local_motion (P i)‖ + ‖local_motion (P i) - Q i‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ d * (2 * (ε : ℝ)) + ε :=
        add_le_add point_agreement (local_fit i (Finset.mem_insert_self _ _))
      _ = (((2 * d + 1 : ℝ≥0) * ε) : ℝ) := by
        push_cast
        ring
  exact global_fit.proper_rho_le

theorem maximum_consensus_k_le_scaled (τ : ℝ≥0) :
    maximum_consensus_k P Q (τ / (2 * d + 1)) (d + 1) ≤ maximum_consensus P Q τ := by
  unfold maximum_consensus_k maximum_consensus
  apply FiniteConsistency.consensus_mono
  intro I hI
  have hc : (2 * d + 1 : ℝ≥0) ≠ 0 := by positivity
  exact (rho_le_higher_order P Q I).trans
    ((mul_le_mul' le_rfl hI).trans_eq (mul_div_cancel₀ τ hc))

theorem maximum_consensus_sandwich (τ : ℝ≥0) :
    maximum_consensus_k P Q (τ / (2 * d + 1)) (d + 1) ≤ maximum_consensus P Q τ ∧
      maximum_consensus P Q τ ≤ maximum_consensus_k P Q τ (d + 1) :=
  ⟨maximum_consensus_k_le_scaled P Q τ, maximum_consensus_le_k P Q τ (d + 1)⟩

end Bounds

section Obstruction

open scoped NNReal Finset

theorem lower_order_obstruction {d : ℕ} (hd : 2 ≤ d) :
    ∃ P Q : ℝ → Fin (d + 2) → ℝ^[d],
      Filter.Tendsto (fun ℓ => (Proper.rho_k (P ℓ) (Q ℓ) Finset.univ d : ℝ))
        Filter.atTop (nhds 0) ∧
      ∀ ℓ : ℝ, 1 ≤ (Proper.rho (P ℓ) (Q ℓ) Finset.univ : ℝ) := by
  let : NeZero d := ⟨by omega⟩
  refine ⟨HigherOrder.Obstruction.source, HigherOrder.Obstruction.target, ?_, fun ℓ => ?_⟩
  · simp_rw [Proper.rho_k_eq_unrestricted_of_le _ _ _ le_rfl]
    exact HigherOrder.Obstruction.lower_errors_tend_to_zero hd d (by omega)
  · exact (HigherOrder.Obstruction.rho_lower ℓ hd).trans
      (NNReal.coe_le_coe.mpr (Proper.unrestricted_rho_le _ _ _))

end Obstruction

section CriticalOrder

open scoped NNReal Finset

def admits_uniform_bound (d k : ℕ) : Prop :=
  ∃ K : ℝ≥0, ∀ (n : ℕ) (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n)),
    rho P Q C ≤ K * rho_k P Q C k

theorem lower_order_has_no_uniform_bound {d k : ℕ} (hd : 2 ≤ d) (hk : k ≤ d)
    (K : ℝ≥0) :
    ∃ P Q : Fin (d + 2) → ℝ^[d],
      K * rho_k P Q Finset.univ k < rho P Q Finset.univ := by
  let : NeZero d := ⟨by omega⟩
  have hlocal : Filter.Tendsto (fun ℓ =>
      (rho_k (HigherOrder.Obstruction.source (d := d) ℓ)
        (HigherOrder.Obstruction.target (d := d) ℓ) Finset.univ k : ℝ))
      Filter.atTop (nhds 0) := by
    simp_rw [rho_k_eq_unrestricted_of_le _ _ _ hk]
    exact HigherOrder.Obstruction.lower_errors_tend_to_zero hd k (by omega)
  obtain ⟨ℓ, hℓ⟩ := UniformBounds.exists_violation _ _ hlocal
    (fun ℓ => (HigherOrder.Obstruction.rho_lower ℓ hd).trans
      (NNReal.coe_le_coe.mpr (unrestricted_rho_le _ _ _))) K
  exact ⟨HigherOrder.Obstruction.source (d := d) ℓ, HigherOrder.Obstruction.target (d := d) ℓ, hℓ⟩

theorem admits_uniform_bound_iff {d k : ℕ} (hd : 2 ≤ d) :
    admits_uniform_bound d k ↔ d + 1 ≤ k := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hk
    obtain ⟨P, Q, hbad⟩ := lower_order_has_no_uniform_bound (k := k) hd (by omega) K
    exact (not_lt_of_ge (hK _ P Q Finset.univ)) hbad
  · intro hk
    refine ⟨2 * d + 1, fun n P Q C => ?_⟩
    exact (rho_le_higher_order P Q C).trans
      (mul_le_mul' le_rfl (rho_k_mono P Q C hk))

end CriticalOrder

end Proper
