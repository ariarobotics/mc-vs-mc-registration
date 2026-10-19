import Mathlib

/-! Finite-set consistency hierarchies and uniform-bound obstructions. -/

namespace FiniteConsistency

section Hierarchy

open scoped NNReal

variable {α : Type*}

noncomputable def rhoK (ρ : Finset α → ℝ≥0) (k : ℕ) (C : Finset α) : ℝ≥0 :=
  (C.powerset.filter fun I => I.card ≤ k).sup ρ

noncomputable def maxConsensus (U : Finset α) (ρ : Finset α → ℝ≥0)
    (τ : ℝ≥0) : ℕ := by
  classical
  exact (U.powerset.filter fun C => ρ C ≤ τ).sup Finset.card

noncomputable def mcK (U : Finset α) (ρ : Finset α → ℝ≥0)
    (k : ℕ) (τ : ℝ≥0) : ℕ :=
  maxConsensus U (rhoK ρ k) τ

theorem rhoK_le_iff (ρ : Finset α → ℝ≥0) (k : ℕ) (C : Finset α) (τ : ℝ≥0) :
    rhoK ρ k C ≤ τ ↔ ∀ I ⊆ C, I.card ≤ k → ρ I ≤ τ := by
  simp only [rhoK, Finset.sup_le_iff, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h I hIC hcard => h I ⟨hIC, hcard⟩, fun h I hI => h I hI.1 hI.2⟩

theorem rhoK_eq_iSup (ρ : Finset α → ℝ≥0) (k : ℕ) (C : Finset α) :
    rhoK ρ k C = ⨆ (I : Finset α) (_ : I ⊆ C) (_ : I.card ≤ k), ρ I := by
  simp only [rhoK, Finset.sup_eq_ciSup, Finset.mem_filter, Finset.mem_powerset,
    ciSup_and]

theorem rhoK_mono (ρ : Finset α → ℝ≥0) (C : Finset α)
    {k l : ℕ} (hkl : k ≤ l) : rhoK ρ k C ≤ rhoK ρ l C := by
  apply (rhoK_le_iff ρ k C _).2
  intro I hIC hcard
  exact (rhoK_le_iff ρ l C _).1 le_rfl I hIC (hcard.trans hkl)

theorem rhoK_le_rho (ρ : Finset α → ℝ≥0) (hρ : Monotone ρ)
    (k : ℕ) (C : Finset α) : rhoK ρ k C ≤ ρ C :=
  (rhoK_le_iff ρ k C _).2 fun _ hIC _ => hρ hIC

theorem rhoK_eq_rho (ρ : Finset α → ℝ≥0) (hρ : Monotone ρ)
    (C : Finset α) {k : ℕ} (hcard : C.card ≤ k) : rhoK ρ k C = ρ C :=
  le_antisymm (rhoK_le_rho ρ hρ k C)
    ((rhoK_le_iff ρ k C _).1 le_rfl C le_rfl hcard)

theorem maxConsensus_le_of_feasible (U : Finset α) (ρ σ : Finset α → ℝ≥0)
    (τ υ : ℝ≥0) (h : ∀ C ⊆ U, ρ C ≤ τ → σ C ≤ υ) :
    maxConsensus U ρ τ ≤ maxConsensus U σ υ := by
  classical
  apply Finset.sup_le
  intro C hC
  obtain ⟨hCU, hρ⟩ := Finset.mem_filter.mp hC
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨hCU, h C (Finset.mem_powerset.mp hCU) hρ⟩)

theorem maxConsensus_scaled_lower (U : Finset α) (ρ σ : Finset α → ℝ≥0)
    (J τ : ℝ≥0) (hJ : 0 < J) (h : ∀ C ⊆ U, ρ C ≤ J * σ C) :
    maxConsensus U σ (τ / J) ≤ maxConsensus U ρ τ := by
  apply maxConsensus_le_of_feasible
  intro C hCU hC
  calc
    ρ C ≤ J * σ C := h C hCU
    _ ≤ J * (τ / J) := mul_le_mul_of_nonneg_left hC zero_le
    _ = τ := by field_simp

theorem maxConsensus_antitone (U : Finset α) (ρ σ : Finset α → ℝ≥0)
    (τ : ℝ≥0) (h : ∀ C ⊆ U, ρ C ≤ σ C) :
    maxConsensus U σ τ ≤ maxConsensus U ρ τ :=
  maxConsensus_le_of_feasible U σ ρ τ τ fun C hCU hC => (h C hCU).trans hC

theorem consensus_mono [Finite α] {F G : Finset α → Prop} (hFG : ∀ I, F I → G I) :
    (⨆ (I : Finset α) (_ : F I), I.card) ≤ ⨆ (I : Finset α) (_ : G I), I.card := by
  classical
  apply ciSup_le'
  intro I
  apply ciSup_le'
  intro hI
  simpa only [ciSup_pos (hFG I hI)] using
    (le_ciSup (f := fun I => ⨆ (_ : G I), I.card) (Set.finite_range _).bddAbove I)

theorem mcK_antitone (U : Finset α) (ρ : Finset α → ℝ≥0)
    (τ : ℝ≥0) {k l : ℕ} (hkl : k ≤ l) : mcK U ρ l τ ≤ mcK U ρ k τ :=
  maxConsensus_antitone U _ _ τ fun C _ => rhoK_mono ρ C hkl

theorem maxConsensus_le_mcK (U : Finset α) (ρ : Finset α → ℝ≥0)
    (hρ : Monotone ρ) (k : ℕ) (τ : ℝ≥0) :
    maxConsensus U ρ τ ≤ mcK U ρ k τ :=
  maxConsensus_antitone U _ _ τ fun C _ => rhoK_le_rho ρ hρ k C

theorem rho_hierarchy_bounds (ρ : Finset α → ℝ≥0) (hρ : Monotone ρ)
    (C : Finset α) (k : ℕ) :
    rhoK ρ k C ≤ rhoK ρ (k + 1) C ∧ rhoK ρ (k + 1) C ≤ ρ C :=
  ⟨rhoK_mono ρ C (Nat.le_succ k), rhoK_le_rho ρ hρ (k + 1) C⟩

theorem mc_hierarchy_bounds (U : Finset α) (ρ : Finset α → ℝ≥0)
    (hρ : Monotone ρ) (k : ℕ) (τ : ℝ≥0) :
    maxConsensus U ρ τ ≤ mcK U ρ (k + 1) τ ∧ mcK U ρ (k + 1) τ ≤ mcK U ρ k τ :=
  ⟨maxConsensus_le_mcK U ρ hρ (k + 1) τ, mcK_antitone U ρ τ (Nat.le_succ k)⟩

theorem mcK_eq_maxConsensus (U : Finset α) (ρ : Finset α → ℝ≥0)
    (hρ : Monotone ρ) (τ : ℝ≥0) {k : ℕ} (hk : U.card ≤ k) :
    mcK U ρ k τ = maxConsensus U ρ τ := by
  apply le_antisymm
  · apply maxConsensus_antitone
    intro C hCU
    exact le_of_eq (rhoK_eq_rho ρ hρ C ((Finset.card_le_card hCU).trans hk)).symm
  · exact maxConsensus_le_mcK U ρ hρ k τ

end Hierarchy

end FiniteConsistency

namespace UniformBounds

section UniformBounds

open scoped NNReal

theorem exists_violation (localError globalError : ℝ → ℝ≥0)
    (hlocal : Filter.Tendsto (fun ℓ => (localError ℓ : ℝ)) Filter.atTop (nhds 0))
    (hglobal : ∀ ℓ, 1 ≤ (globalError ℓ : ℝ)) (K : ℝ≥0) :
    ∃ ℓ, K * localError ℓ < globalError ℓ := by
  have hden : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨ℓ, hℓ⟩ := (hlocal.eventually (gt_mem_nhds (div_pos zero_lt_one hden))).exists
  have hh := (lt_div_iff₀ hden).mp hℓ
  refine ⟨ℓ, NNReal.coe_lt_coe.mp ?_⟩
  simp only [NNReal.coe_mul]
  nlinarith [hglobal ℓ, NNReal.coe_nonneg (localError ℓ)]

end UniformBounds

end UniformBounds
