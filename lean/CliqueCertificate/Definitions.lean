import Mathlib

/-! Euclidean motions, fitting error, consensus, and local consistency. -/

notation "ℝ^[" d "]" => EuclideanSpace ℝ (Fin d)

abbrev OrthogonalGroup (d : ℕ) := ℝ^[d] ≃ₗᵢ[ℝ] ℝ^[d]
abbrev EuclideanGroup (d : ℕ) := ℝ^[d] ≃ᵃⁱ[ℝ] ℝ^[d]

def SpecialEuclideanGroup (d : ℕ) :=
  {T : EuclideanGroup d // LinearEquiv.det T.linearIsometryEquiv.toLinearEquiv = 1}

instance {d : ℕ} : CoeFun (SpecialEuclideanGroup d) (fun _ => ℝ^[d] → ℝ^[d]) :=
  ⟨fun T p => T.1 p⟩

notation "O(" d ")" => OrthogonalGroup d
notation "E(" d ")" => EuclideanGroup d
notation "SE(" d ")" => SpecialEuclideanGroup d

section Objectives

open scoped NNReal Finset

variable (P Q : Fin n → ℝ^[d])

noncomputable def alignment_error (C : Finset (Fin n)) (T : E(d)) : ℝ≥0 :=
  ⨆ i : C, ‖T (P i) - Q i‖₊

noncomputable def rho (C : Finset (Fin n)) : ℝ≥0 :=
  ⨅ T : E(d), alignment_error P Q C T

noncomputable def feasible (C : Finset (Fin n)) (τ : ℝ≥0) : Prop :=
  rho P Q C ≤ τ

noncomputable def maximum_consensus (τ : ℝ≥0) : ℕ :=
  ⨆ (I : Finset (Fin n)) (_ : feasible P Q I τ), #I

noncomputable def delta (C : Finset (Fin n)) : ℝ≥0 :=
  ⨆ (i : C) (j : C), nndist ‖P i - P j‖₊ ‖Q i - Q j‖₊

noncomputable def pairwise_consistent (C : Finset (Fin n)) (ε : ℝ≥0) : Prop :=
  delta P Q C ≤ ε

noncomputable def max_clique (ε : ℝ≥0) : ℕ :=
  ⨆ (I : Finset (Fin n)) (_ : pairwise_consistent P Q I ε), #I

noncomputable def rho_k (C : Finset (Fin n)) (k : ℕ) : ℝ≥0 :=
  ⨆ (I : Finset (Fin n)) (_ : I ⊆ C) (_ : #I ≤ k), rho P Q I

noncomputable def maximum_consensus_k (τ : ℝ≥0) (k : ℕ) : ℕ :=
  ⨆ (I : Finset (Fin n)) (_ : rho_k P Q I k ≤ τ), #I

end Objectives
