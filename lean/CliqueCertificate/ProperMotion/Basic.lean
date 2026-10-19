import CliqueCertificate.Basic

/-! Proper motions, attainment, and local orientation equivalence (Lemma 5). -/

namespace Proper

section Definitions

open scoped NNReal Finset

noncomputable def identity (d : ℕ) : SE(d) :=
  ⟨1, by change LinearEquiv.det (LinearEquiv.refl ℝ (ℝ^[d])) = 1; simp⟩

noncomputable instance (d : ℕ) : Inhabited SE(d) := ⟨identity d⟩

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

noncomputable def alignment_error (C : Finset (Fin n)) (T : SE(d)) : ℝ≥0 :=
  _root_.alignment_error P Q C T.val

noncomputable def rho (C : Finset (Fin n)) : ℝ≥0 := ⨅ T : SE(d), alignment_error P Q C T

noncomputable def feasible (C : Finset (Fin n)) (τ : ℝ≥0) : Prop := rho P Q C ≤ τ

noncomputable def rho_k (C : Finset (Fin n)) (k : ℕ) : ℝ≥0 :=
  ⨆ (I : Finset (Fin n)) (_ : I ⊆ C) (_ : #I ≤ k), rho P Q I

noncomputable def maximum_consensus (τ : ℝ≥0) : ℕ :=
  ⨆ (I : Finset (Fin n)) (_ : feasible P Q I τ), #I

noncomputable def maximum_consensus_k (τ : ℝ≥0) (k : ℕ) : ℕ :=
  ⨆ (I : Finset (Fin n)) (_ : rho_k P Q I k ≤ τ), #I

noncomputable def disagreement (C : Finset (Fin n)) (T U : SE(d)) : ℝ≥0 :=
  ⨆ i : C, ‖T (P i) - U (P i)‖₊

end Definitions

section Attainment

open scoped NNReal

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem alignment_error_le_iff_fits (T : SE(d)) (ε : ℝ≥0) :
    alignment_error P Q C T ≤ ε ↔ Fits P Q C ε T :=
  _root_.alignment_error_le_iff_fits P Q C T.val ε

theorem alignment_error_fits (T : SE(d)) : Fits P Q C (alignment_error P Q C T) T :=
  (alignment_error_le_iff_fits P Q C T _).mp le_rfl

theorem rho_attained : ∃ T : SE(d), alignment_error P Q C T = rho P Q C := by
  obtain ⟨T, hT, hmin⟩ := alignment_error_min_on_rotations P Q C (fun A => A.det = 1)
    (isClosed_eq ContinuousLinearMap.continuous_det continuous_const)
    (by exact LinearMap.det_id)
  have hdet : LinearEquiv.det T.linearIsometryEquiv.toLinearEquiv = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    exact hT
  refine ⟨⟨T, hdet⟩, le_antisymm (le_ciInf fun U => hmin U.val ?_) ?_⟩
  · have hU := congrArg (fun u : ℝˣ => (u : ℝ)) U.property
    rw [LinearEquiv.coe_det, Units.val_one] at hU
    exact hU
  · exact ciInf_le (OrderBot.bddBelow _) (⟨T, hdet⟩ : SE(d))

theorem rho_le_iff_exists_alignment (τ : ℝ≥0) :
    rho P Q C ≤ τ ↔ ∃ T : SE(d), alignment_error P Q C T ≤ τ := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := rho_attained P Q C
    exact ⟨T, hT.le.trans h⟩
  · rintro ⟨T, hT⟩
    exact (ciInf_le (OrderBot.bddBelow _) T).trans hT

theorem exists_best_fit : ∃ T : SE(d), Fits P Q C (rho P Q C) T := by
  obtain ⟨T, hT⟩ := rho_attained P Q C
  exact ⟨T, (alignment_error_le_iff_fits P Q C T _).mp hT.le⟩

theorem rho_le_iff_exists_fit (ε : ℝ≥0) :
    rho P Q C ≤ ε ↔ ∃ T : SE(d), Fits P Q C ε T := by
  simp only [rho_le_iff_exists_alignment, alignment_error_le_iff_fits]

theorem _root_.Fits.proper_rho_le {P Q : Fin n → ℝ^[d]} {C : Finset (Fin n)}
    {ε : ℝ≥0} {T : SE(d)} (hfit : Fits P Q C ε T) : rho P Q C ≤ ε :=
  (rho_le_iff_exists_fit P Q C ε).mpr ⟨T, hfit⟩

end Attainment

section Orientation

open scoped NNReal Finset
open Module

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonal_det_eq_one_or_neg_one (R : E ≃ₗᵢ[ℝ] E) :
    LinearEquiv.det R.toLinearEquiv = 1 ∨ LinearEquiv.det R.toLinearEquiv = -1 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hh := b.det_to_matrix_orthonormalBasis_real (b.map R)
  have heq : b.toBasis.det (b.map R) = LinearMap.det R.toLinearMap := by
    rw [Basis.det_apply, ← LinearMap.det_toMatrix b.toBasis]
    rw [LinearMap.toMatrix_eq_basisToMatrix]
    congr 1
  rw [heq] at hh
  rcases hh with hh | hh
  · left
    apply Units.ext
    simpa only [LinearEquiv.coe_det, Units.val_one] using hh
  · right
    apply Units.ext
    simpa only [LinearEquiv.coe_det, Units.val_neg, Units.val_one] using hh

theorem normal_reflection_det (v : E) (hv : v ≠ 0) :
    LinearEquiv.det (Submodule.reflection (ℝ ∙ v)ᗮ).toLinearEquiv = -1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hv]
  simp

end Linear

variable {n d : ℕ} (P Q : Fin n → ℝ^[d]) (C : Finset (Fin n))

theorem proper_extension_on_small_set (hcard : #C ≤ d) (T : E(d)) :
    ∃ U : SE(d), ∀ i ∈ C, U (P i) = T (P i) := by
  classical
  rcases orthogonal_det_eq_one_or_neg_one T.linearIsometryEquiv with hT | hT
  · exact ⟨⟨T, hT⟩, fun _ _ => rfl⟩
  rcases C.eq_empty_or_nonempty with rfl | hC
  · exact ⟨identity d, by simp⟩
  obtain ⟨i₀, hi₀⟩ := hC
  let K := Submodule.span ℝ ((C.erase i₀).image (fun i => P i - P i₀) : Set (ℝ^[d]))
  have hdim : Module.finrank ℝ K < d := by
    have hh := (finrank_span_finset_le_card (R := ℝ)
      ((C.erase i₀).image (fun i => P i - P i₀))).trans Finset.card_image_le
    have hc := Finset.card_erase_add_one hi₀
    change Module.finrank ℝ K ≤ (C.erase i₀).card at hh
    omega
  have horth : 0 < Module.finrank ℝ Kᗮ := by
    have hh := K.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
    omega
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := Kᗮ)).mp horth
  have hv0 : (v : ℝ^[d]) ≠ 0 := by
    intro hz
    apply hv
    exact Subtype.ext hz
  let R := Submodule.reflection (ℝ ∙ (v : ℝ^[d]))ᗮ
  let S : E(d) := ((AffineIsometryEquiv.vaddConst ℝ (-P i₀)).trans
    R.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ (P i₀))
  have hSdet : LinearEquiv.det S.linearIsometryEquiv.toLinearEquiv = -1 :=
    normal_reflection_det v.val hv0
  have hfix (i : Fin n) (hi : i ∈ C) : S (P i) = P i := by
    have hmem : P i - P i₀ ∈ K := by
      by_cases heq : i = i₀
      · simp [heq]
      · exact Submodule.subset_span (Finset.mem_image.mpr
          ⟨i, Finset.mem_erase.mpr ⟨heq, hi⟩, rfl⟩)
    have hinner : inner ℝ (v : ℝ^[d]) (P i - P i₀) = 0 :=
      (K.mem_orthogonal' v.val).mp v.property _ hmem
    have hf : R (P i - P i₀) = P i - P i₀ := by
      rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
      simp [hinner]
    change R (P i + -P i₀) + P i₀ = P i
    rw [← sub_eq_add_neg, hf]
    abel
  have hproper : LinearEquiv.det (S.trans T).linearIsometryEquiv.toLinearEquiv = 1 := by
    change LinearEquiv.det (S.linearIsometryEquiv.toLinearEquiv.trans
      T.linearIsometryEquiv.toLinearEquiv) = 1
    rw [LinearEquiv.det_trans, hT, hSdet]
    simp
  exact ⟨⟨S.trans T, hproper⟩, fun i hi => by change T (S (P i)) = T (P i); rw [hfix i hi]⟩

theorem unrestricted_rho_le : _root_.rho P Q C ≤ rho P Q C := by
  apply le_ciInf
  intro T
  exact ciInf_le (OrderBot.bddBelow _) T.val

theorem rho_eq_unrestricted_of_card_le (hcard : #C ≤ d) : rho P Q C = _root_.rho P Q C := by
  apply le_antisymm _ (unrestricted_rho_le P Q C)
  apply le_ciInf
  intro T
  obtain ⟨U, hU⟩ := proper_extension_on_small_set P C hcard T
  apply (ciInf_le (OrderBot.bddBelow _) U).trans_eq
  unfold alignment_error _root_.alignment_error
  congr 1
  funext i
  have hh : U.val (P i) = T (P i) := hU i i.property
  rw [hh]

theorem rho_k_eq_unrestricted_of_le {k : ℕ} (hk : k ≤ d) :
    rho_k P Q C k = _root_.rho_k P Q C k := by
  classical
  unfold rho_k _root_.rho_k
  congr 1
  funext I
  congr 1
  funext hIC
  congr 1
  funext hcard
  exact rho_eq_unrestricted_of_card_le P Q I (hcard.trans hk)

end Orientation

section Hierarchy

open scoped NNReal Finset

variable {n d : ℕ} (P Q : Fin n → ℝ^[d])

theorem alignment_error_mono (T : SE(d)) : Monotone (fun C => alignment_error P Q C T) :=
  _root_.alignment_error_mono P Q T.val

theorem rho_mono : Monotone (rho P Q) := by
  intro C D hCD
  apply ciInf_mono (OrderBot.bddBelow _)
  intro T
  exact alignment_error_mono P Q T hCD

@[simp] theorem rho_empty : rho P Q ∅ = 0 := by
  simp [rho, alignment_error, _root_.alignment_error]

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

end Proper
