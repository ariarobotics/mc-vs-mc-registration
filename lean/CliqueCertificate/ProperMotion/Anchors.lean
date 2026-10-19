import CliqueCertificate.ProperMotion.SkewGeometry

/-! Maximal facets and the anchor-control bound (Lemma 6). -/

open EuclideanGeometry

namespace Proper

section NormingBasis

open scoped BigOperators
open Module

theorem finite_norming_basis {ι V : Type*} [Finite ι] [Nonempty ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (v : ι → V) (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ a : Fin (Module.finrank ℝ V) → ι,
    ∃ b : Basis (Fin (Module.finrank ℝ V)) ℝ V,
      (∀ j, b j = v (a j)) ∧ ∀ i j, |b.repr (v i) j| ≤ 1 := by
  classical
  let := Fintype.ofFinite ι
  let m := Module.finrank ℝ V
  let b₀ := Module.finBasis ℝ V
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' ℝ v
  let : Finite κ := Finite.of_injective c hc
  let : Fintype κ := Fintype.ofFinite κ
  let bκ := Basis.mk hli (hsp.trans hspan).ge
  have hcard : Fintype.card κ = m := (Module.finrank_eq_card_basis bκ).symm
  let e := Fintype.equivFinOfCardEq hcard
  let c₀ : Fin m → ι := fun j => c (e.symm j)
  have hunit : IsUnit (b₀.det (fun j => v (c₀ j))) := by
    convert b₀.isUnit_det (bκ.reindex e) using 1
    simp only [Basis.coe_reindex, bκ, Basis.coe_mk, c₀]
    rfl
  have hne : b₀.det (fun j => v (c₀ j)) ≠ 0 := isUnit_iff_ne_zero.mp hunit
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin m → ι => |b₀.det (fun j => v (a j))|) Finset.univ_nonempty
  have hdet : b₀.det (fun j => v (a j)) ≠ 0 := by
    intro hz
    have hh := hmax c₀ (Finset.mem_univ _)
    rw [hz, abs_zero] at hh
    exact hne (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  obtain ⟨haLI, haSpan⟩ := (b₀.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hdet)
  let b := Basis.mk haLI haSpan.ge
  refine ⟨a, b, fun _ => by simp [b], fun i j => ?_⟩
  have hid := LinearMap.congr_fun (b₀.det_smul_mk_coord_eq_det_update haLI haSpan.ge j) (v i)
  change b₀.det (fun j => v (a j)) * b.repr (v i) j =
    b₀.det (Function.update (fun j => v (a j)) j (v i)) at hid
  have hupdate : Function.update (fun j => v (a j)) j (v i) =
      fun k => v (Function.update a j i k) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [hupdate] at hid
  have hh := hmax (Function.update a j i) (Finset.mem_univ _)
  rw [← hid, abs_mul] at hh
  exact (mul_le_mul_iff_right₀ (abs_pos.mpr hdet)).mp (by simpa only [mul_comm, one_mul] using hh)

theorem linear_norming_bound {ι V F : Type*}
    [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : ι → V) {m : ℕ} (a : Fin m → ι) (b : Basis (Fin m) ℝ V)
    (hb : ∀ j, b j = v (a j)) (hcoord : ∀ i j, |b.repr (v i) j| ≤ 1)
    (L : V →ₗ[ℝ] F) (ε : ℝ) (_hε : 0 ≤ ε) (hbound : ∀ j, ‖L (v (a j))‖ ≤ ε) (i : ι) :
    ‖L (v i)‖ ≤ m * ε := by
  classical
  rw [← b.sum_repr (v i), map_sum]
  calc
    _ ≤ ∑ j, ‖L (b.repr (v i) j • b j)‖ := norm_sum_le _ _
    _ = ∑ j, |b.repr (v i) j| * ‖L (v (a j))‖ := by
      simp only [map_smul, norm_smul, Real.norm_eq_abs, hb]
    _ ≤ ∑ _j : Fin m, ε := by
      apply Finset.sum_le_sum
      intro j _
      exact (mul_le_mul (hcoord i j) (hbound j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul ε)
    _ = m * ε := by simp

end NormingBasis

section Determinants

open Module
open scoped BigOperators

theorem basis_det_update {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] (b : Basis ι ℝ V) (k : ι) (z : V) :
    b.det (Function.update b k z) = b.repr z k := by
  have hb : Basis.mk b.linearIndependent b.span_eq.ge = b := by ext i; simp
  simpa [hb, Basis.det_self] using (LinearMap.congr_fun
    (b.det_smul_mk_coord_eq_det_update b.linearIndependent b.span_eq.ge k) z).symm

theorem basis_det_two_updates {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] (b : Basis ι ℝ V) (i j : ι) (hij : i ≠ j)
    (x y : V) :
    b.det (Function.update (Function.update b i x) j y) =
      b.repr x i * b.repr y j - b.repr x j * b.repr y i := by
  classical
  have hsingle := basis_det_update b
  have hswap : b.det (Function.update (Function.update b i (b j)) j (b i)) = -1 := by
    have heq : Function.update (Function.update b i (b j)) j (b i) =
        b ∘ Equiv.swap i j := by
      funext k
      by_cases hki : k = i
      · subst k; simp [hij]
      · by_cases hkj : k = j
        · subst k; simp
        · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [heq, b.det.map_perm]
    simp [hij, Basis.det_self]
  conv_lhs => rw [← b.sum_repr y, b.det.map_update_sum]
  simp only [b.det.map_update_smul, smul_eq_mul]
  have hterm (k : ι) :
      b.det (Function.update (Function.update b i x) j (b k)) =
        if k = j then b.repr x i else if k = i then -b.repr x j else 0 := by
    by_cases hkj : k = j
    · subst k
      rw [Function.update_comm hij]
      simp only [Function.update_eq_self, hsingle, ite_true]
    · by_cases hki : k = i
      · subst k
        rw [← b.sum_repr x]
        have heq : Function.update (Function.update b i (∑ k, b.repr x k • b k)) j (b i) =
            Function.update (Function.update b j (b i)) i (∑ k, b.repr x k • b k) :=
          Function.update_comm hij _ _ _
        rw [heq, b.det.map_update_sum]
        simp only [b.det.map_update_smul, smul_eq_mul]
        have hz (k : ι) (hk : k ≠ j) :
            b.det (Function.update (Function.update b j (b i)) i (b k)) = 0 := by
          by_cases hki : k = i
          · subst k
            exact b.det.map_eq_zero_of_eq _ (by simp [Ne.symm hij]) hij
          · exact b.det.map_eq_zero_of_eq _ (i := i) (j := k)
              (by simp [hki, hk]) (Ne.symm hki)
        rw [Finset.sum_eq_single j]
        · rw [← Function.update_comm hij, hswap]
          simp [hkj]
        · intro k _ hk; rw [hz k hk, mul_zero]
        · simp
      · rw [b.det.map_eq_zero_of_eq _ (i := j) (j := k) (by simp [hki, hkj]) (Ne.symm hkj)]
        simp [hkj, hki]
  simp_rw [hterm]
  have hsplit (k : ι) :
      b.repr y k * (if k = j then b.repr x i else if k = i then -b.repr x j else 0) =
        (if k = j then b.repr y k * b.repr x i else 0) -
        (if k = i then b.repr y k * b.repr x j else 0) := by
    by_cases hk : k = j
    · subst k; simp [Ne.symm hij]
    · by_cases hk' : k = i <;> simp [hk, hk', hij]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end Determinants

section FacetSelection

open Module
open scoped BigOperators

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def facet_form (b : Basis (Fin (d + 1)) ℝ (ℝ × E)) (p : Fin d → E) :
    (ℝ × E) →ₗ[ℝ] ℝ :=
  b.det.toMultilinearMap.toLinearMap (Fin.snoc (fun j => (1, p j)) 0) (Fin.last d)

omit [FiniteDimensional ℝ E] in
@[simp] theorem facet_form_apply (b : Basis (Fin (d + 1)) ℝ (ℝ × E))
    (p : Fin d → E) (z : ℝ × E) :
    facet_form b p z = b.det (Fin.snoc (fun j => (1, p j)) z) := by
  simp only [facet_form, MultilinearMap.toLinearMap_apply, Fin.update_snoc_last]
  rfl

noncomputable def facet_normal (b : Basis (Fin (d + 1)) ℝ (ℝ × E)) (p : Fin d → E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    ((facet_form b p).comp (LinearMap.inr ℝ ℝ E)).toContinuousLinearMap

@[simp] theorem inner_facet_normal (b : Basis (Fin (d + 1)) ℝ (ℝ × E))
    (p : Fin d → E) (x : E) :
    inner ℝ (facet_normal b p) x = facet_form b p (0, x) := by
  exact InnerProductSpace.toDual_symm_apply

omit [FiniteDimensional ℝ E] in
@[simp] theorem facet_form_vertex (b : Basis (Fin (d + 1)) ℝ (ℝ × E))
    (p : Fin d → E) (j : Fin d) : facet_form b p (1, p j) = 0 := by
  rw [facet_form_apply]
  exact b.det.map_eq_zero_of_eq _ (i := j.castSucc) (j := Fin.last d)
    (by simp) (Fin.castSucc_ne_last j)

theorem exists_nonzero_facet {ι : Type*} [Finite ι] [Nonempty ι]
    (hd : 0 < d) (hdim : Module.finrank ℝ E = d) (p : ι → E)
    (b : Basis (Fin (d + 1)) ℝ (ℝ × E))
    (hspan : Submodule.span ℝ (Set.range (fun i => ((1 : ℝ), p i))) = ⊤) :
    ∃ a : Fin d → ι, facet_normal b (p ∘ a) ≠ 0 := by
  classical
  have hdimF : Module.finrank ℝ (ℝ × E) = d + 1 := by
    rw [Module.finrank_prod, Module.finrank_self, hdim]; omega
  obtain ⟨a', b', hb', _⟩ := finite_norming_basis (fun i => ((1 : ℝ), p i)) hspan
  let e := finCongr hdimF
  let a : Fin (d + 1) → ι := a' ∘ e.symm
  let B := b'.reindex e
  have hB (j : Fin (d + 1)) : B j = (1, p (a j)) := by
    simpa only [B, Basis.reindex_apply, a, Function.comp_apply] using hb' (e.symm j)
  have hdet : b.det (fun j => (1, p (a j))) ≠ 0 := by
    have hh := isUnit_iff_ne_zero.mp (b.isUnit_det B)
    simpa only [← hB] using hh
  let q : Fin d → E := fun j => p (a j.castSucc)
  let j₀ : Fin d := ⟨0, hd⟩
  refine ⟨fun j => a j.castSucc, ?_⟩
  intro hz
  have hf := inner_facet_normal b q (p (a (Fin.last d)) - q j₀)
  have heq : ((0 : ℝ), p (a (Fin.last d)) - q j₀) =
      (1, p (a (Fin.last d))) - (1, q j₀) := by ext <;> simp
  rw [show facet_normal b q = 0 from hz, inner_zero_left, heq, map_sub,
    facet_form_vertex, sub_zero, facet_form_apply] at hf
  apply hdet
  calc
    _ = b.det (Fin.snoc (fun j => (1, q j)) (1, p (a (Fin.last d)))) := by
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [q]
    _ = 0 := hf.symm

theorem maximal_facet {ι : Type*} [Finite ι] [Nonempty ι]
    (hd : 0 < d) (hdim : Module.finrank ℝ E = d) (p : ι → E)
    (b : Basis (Fin (d + 1)) ℝ (ℝ × E))
    (hspan : Submodule.span ℝ (Set.range (fun i => ((1 : ℝ), p i))) = ⊤) :
    ∃ a : Fin d → ι, facet_normal b (p ∘ a) ≠ 0 ∧
      ∀ c : Fin d → ι, ‖facet_normal b (p ∘ c)‖ ≤ ‖facet_normal b (p ∘ a)‖ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin d → ι => ‖facet_normal b (p ∘ a)‖) Finset.univ_nonempty
  refine ⟨a, ?_, fun c => ha c (Finset.mem_univ _)⟩
  obtain ⟨c, hc⟩ := exists_nonzero_facet hd hdim p b hspan
  intro hz
  have hh := ha c (Finset.mem_univ _)
  rw [hz, norm_zero] at hh
  exact hc (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

end FacetSelection

section FacetCoordinates

open Module
open scoped BigOperators

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem maximal_facet_coordinates {ι : Type*} [Finite ι] [Nonempty ι]
    (hd : 0 < d) (hdim : Module.finrank ℝ E = d) (p : ι → E)
    (b : Basis (Fin (d + 1)) ℝ (ℝ × E))
    (hspan : Submodule.span ℝ (Set.range (fun i => ((1 : ℝ), p i))) = ⊤) :
    ∃ (a : Fin d → ι) (n : E) (B : Basis (Fin (d + 1)) ℝ (ℝ × E)) (g : Fin d → E),
      ‖n‖ = 1 ∧ (∀ j, B j.castSucc = (1, p (a j))) ∧ B (Fin.last d) = (0, n) ∧
      (∀ j y, B.repr (0, y) j.castSucc = inner ℝ (g j) y) ∧
      (∀ y, B.repr (0, y) (Fin.last d) = inner ℝ n y) ∧
      ∀ i j, ‖B.repr (1, p i) j.castSucc • n - B.repr (1, p i) (Fin.last d) • g j‖ ≤ 1 := by
  classical
  obtain ⟨a, ha, hmax⟩ := maximal_facet hd hdim p b hspan
  let q := p ∘ a
  let ν := facet_normal b q
  let κ := ‖ν‖
  have hκ : 0 < κ := norm_pos_iff.mpr ha
  let n := κ⁻¹ • ν
  have hn : ‖n‖ = 1 := by
    simp only [n, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hκ]
    exact inv_mul_cancel₀ hκ.ne'
  have hν : ν = κ • n := by simp [n, smul_smul, mul_inv_cancel₀ hκ.ne']
  let v : Fin (d + 1) → ℝ × E := Fin.snoc (fun j => ((1 : ℝ), q j)) ((0 : ℝ), n)
  have hvdet : b.det v = κ := by
    rw [← facet_form_apply, ← inner_facet_normal]
    change inner ℝ ν n = κ
    rw [hν, real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
    ring
  obtain ⟨hli, hsp⟩ := b.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr (hvdet.trans_ne hκ.ne'))
  let B := Basis.mk hli hsp.ge
  have hB (j : Fin (d + 1)) : B j = v j := by simp [B]
  have hb : b.det = κ • B.det := by
    have hh := b.det.eq_smul_basis_det B
    have hdB : b.det B = κ := by
      rw [show (B : Fin (d + 1) → ℝ × E) = v from funext hB]
      exact hvdet
    simpa only [hdB] using hh
  have hbapply (z : Fin (d + 1) → ℝ × E) : b.det z = κ * B.det z := by
    rw [hb]; rfl
  have hlast (y : E) : B.repr (0, y) (Fin.last d) = inner ℝ n y := by
    have hh := inner_facet_normal b q y
    rw [facet_form_apply, hbapply] at hh
    have heq : Fin.snoc (fun j => ((1 : ℝ), q j)) ((0 : ℝ), y) =
        Function.update B (Fin.last d) (0, y) := by
      rw [show (B : Fin (d + 1) → ℝ × E) = v from funext hB]
      simp only [v, Fin.update_snoc_last]
    rw [heq, basis_det_update] at hh
    change inner ℝ ν y = κ * B.repr (0, y) (Fin.last d) at hh
    rw [hν, real_inner_smul_left] at hh
    exact (mul_left_cancel₀ hκ.ne' hh).symm
  let g : Fin d → E := fun j => (InnerProductSpace.toDual ℝ E).symm
    ((B.coord j.castSucc).comp (LinearMap.inr ℝ ℝ E)).toContinuousLinearMap
  have hg (j : Fin d) (y : E) : B.repr (0, y) j.castSucc = inner ℝ (g j) y :=
    by
      change ((B.coord j.castSucc).comp (LinearMap.inr ℝ ℝ E)).toContinuousLinearMap y = _
      exact InnerProductSpace.toDual_symm_apply.symm
  refine ⟨a, n, B, g, hn, fun j => ?_, ?_, hg, hlast, fun i j => ?_⟩
  · simp [hB, v, q]
  · simp [hB, v]
  · have hreplace : facet_normal b (p ∘ Function.update a j i) =
        κ • (B.repr (1, p i) j.castSucc • n - B.repr (1, p i) (Fin.last d) • g j) := by
      apply ext_inner_right ℝ
      intro y
      rw [inner_facet_normal]
      have heq : Fin.snoc (fun k => ((1 : ℝ), p (Function.update a j i k))) ((0 : ℝ), y) =
          Function.update (Function.update B j.castSucc (1, p i)) (Fin.last d) (0, y) := by
        funext k
        refine Fin.lastCases ?_ (fun l => ?_) k
        · simp
        · by_cases hl : l = j
          · subst l; simp
          · simp [hl, hB, v, q]
      rw [facet_form_apply]
      simp only [Function.comp_apply]
      rw [heq, hbapply,
        basis_det_two_updates B j.castSucc (Fin.last d) (Fin.castSucc_ne_last j), hg, hlast]
      simp only [real_inner_smul_left, inner_sub_left]
    have hh := hmax (Function.update a j i)
    rw [hreplace, norm_smul, Real.norm_eq_abs, abs_of_pos hκ] at hh
    change κ * _ ≤ κ at hh
    exact (mul_le_mul_iff_right₀ hκ).mp (by simpa only [mul_comm, one_mul] using hh)

end FacetCoordinates

section Interpolation

open scoped BigOperators
open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem facet_coefficient_norm_le (n g z : E) (hn : ‖n‖ = 1)
    (hng : inner ℝ n g = 0) (β ζ : ℝ)
    (hcoeff : ‖β • n - ζ • g‖ ≤ 1) :
    ‖β • z + ζ • (inner ℝ g z • n - inner ℝ n z • g)‖ ≤ ‖z‖ := by
  have hn2 : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hgn : inner ℝ g n = 0 := by rw [real_inner_comm, hng]
  have hgproj : inner ℝ g (z - inner ℝ n z • n) = inner ℝ g z := by
    simp [inner_sub_right, real_inner_smul_right, hgn]
  have hproj : ‖z - inner ℝ n z • n‖ ^ 2 = ‖z‖ ^ 2 - inner ℝ n z ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, real_inner_comm z n, hn]
    ring
  have hcs := real_inner_mul_inner_self_le g (z - inner ℝ n z • n)
  rw [hgproj, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hproj] at hcs
  have hk : ‖inner ℝ g z • n - inner ℝ n z • g‖ ^ 2 ≤ ‖g‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow,
      sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, hng, hn]
    nlinarith [hcs]
  have horth : inner ℝ z (inner ℝ g z • n - inner ℝ n z • g) = 0 := by
    simp only [inner_sub_right, real_inner_smul_right, real_inner_comm z n,
      real_inner_comm z g]
    ring
  have hc : β ^ 2 + ζ ^ 2 * ‖g‖ ^ 2 ≤ 1 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
      hng, hn] at hh
    norm_num at hh
    exact hh
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, horth]
  calc
    _ = β ^ 2 * ‖z‖ ^ 2 + ζ ^ 2 *
        ‖inner ℝ g z • n - inner ℝ n z • g‖ ^ 2 := by ring
    _ ≤ β ^ 2 * ‖z‖ ^ 2 + ζ ^ 2 * (‖g‖ ^ 2 * ‖z‖ ^ 2) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hk (sq_nonneg _)) _
    _ = (β ^ 2 + ζ ^ 2 * ‖g‖ ^ 2) * ‖z‖ ^ 2 := by ring
    _ ≤ 1 * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = ‖z‖ ^ 2 := one_mul _

theorem skew_trace_eq_zero (H : E →ₗ[ℝ] E)
    (hH : ∀ x y, inner ℝ (H x) y = -inner ℝ x (H y)) :
    H.trace ℝ E = 0 := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  apply Finset.sum_eq_zero
  intro i _
  have h := hH (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)
  rw [real_inner_comm (H _)] at h
  rw [real_inner_comm]
  linarith

theorem facet_skew_affine_bound {d : ℕ} (q : Fin d → E) (n : E)
    (B : Module.Basis (Fin (d + 1)) ℝ (ℝ × E)) (g : Fin d → E)
    (hn : ‖n‖ = 1) (hB : ∀ j, B j.castSucc = (1, q j))
    (hBn : B (Fin.last d) = (0, n))
    (hg : ∀ j y, B.repr (0, y) j.castSucc = inner ℝ (g j) y)
    (hlast : ∀ y, B.repr (0, y) (Fin.last d) = inner ℝ n y)
    (x : E) (hcoeff : ∀ j,
      ‖B.repr (1, x) j.castSucc • n - B.repr (1, x) (Fin.last d) • g j‖ ≤ 1)
    (H : E →ₗ[ℝ] E) (hH : ∀ x y, inner ℝ (H x) y = -inner ℝ x (H y))
    (s : E) (ε : ℝ) (hbound : ∀ j, ‖H (q j) + s‖ ≤ ε) :
    ‖H x + s‖ ≤ d * ε := by
  classical
  have hHself (y : E) : inner ℝ (H y) y = 0 := by
    have hh := hH y y
    have hc := real_inner_comm (H y) y
    linarith
  have hgn (j : Fin d) : inner ℝ n (g j) = 0 := by
    have hh := hg j n
    rw [← hBn] at hh
    simp only [Basis.repr_self, Finsupp.single_apply,
      (Fin.castSucc_ne_last j).symm, ite_false] at hh
    rw [real_inner_comm]
    exact hh.symm
  have hrepr (t : ℝ) (y : E) :
      (∑ j : Fin d, B.repr (t, y) j.castSucc • (1, q j)) +
        B.repr (t, y) (Fin.last d) • (0, n) = (t, y) := by
    have hh := B.sum_repr (t, y)
    rw [Fin.sum_univ_castSucc] at hh
    simpa only [hB, hBn] using hh
  have hfirst (t : ℝ) (y : E) : ∑ j : Fin d, B.repr (t, y) j.castSucc = t := by
    have hh := congrArg Prod.fst (hrepr t y)
    simpa [Prod.fst_sum] using hh
  have hsecond (t : ℝ) (y : E) :
      ∑ j : Fin d, B.repr (t, y) j.castSucc • q j =
        y - B.repr (t, y) (Fin.last d) • n := by
    have hh := congrArg Prod.snd (hrepr t y)
    simp only [Prod.snd_add, Prod.snd_sum] at hh
    exact eq_sub_of_add_eq hh
  have hsumg : ∑ j, g j = 0 := by
    apply ext_inner_right ℝ
    intro y
    rw [sum_inner, inner_zero_left]
    simpa only [← hg] using hfirst 0 y
  have hproj (y : E) : ∑ j, inner ℝ (g j) y • q j = y - inner ℝ n y • n := by
    simpa only [hg, hlast] using hsecond 0 y
  have hcov : EuclideanGeometry.cross_covariance q g =
      LinearMap.id - (InnerProductSpace.rankOne ℝ n n).toLinearMap := by
    apply LinearMap.ext
    intro y
    simpa [EuclideanGeometry.cross_covariance, InnerProductSpace.rankOne_apply] using hproj y
  have hnH : inner ℝ n (H n) = 0 := by rw [real_inner_comm]; exact hHself n
  have htrace : ∑ j, inner ℝ (g j) (H (q j)) = 0 := by
    have hcomp : H.comp (EuclideanGeometry.cross_covariance q g) =
        H - (InnerProductSpace.rankOne ℝ (H n) n).toLinearMap := by
      apply LinearMap.ext
      intro y
      rw [hcov]
      simp [InnerProductSpace.rankOne_apply]
    have hh := EuclideanGeometry.trace_cross_covariance q g H
    rw [hcomp, map_sub, skew_trace_eq_zero H hH,
      InnerProductSpace.trace_rankOne, hnH, sub_zero] at hh
    simpa only [real_inner_comm] using hh.symm
  have htracef : ∑ j, inner ℝ (g j) (H (q j) + s) = 0 := by
    simp only [inner_add_right, Finset.sum_add_distrib]
    rw [htrace, ← sum_inner, hsumg, inner_zero_left, add_zero]
  have hnormal : ∑ j, inner ℝ n (H (q j) + s) • g j = -H n := by
    apply ext_inner_right ℝ
    intro y
    rw [sum_inner, inner_neg_left]
    simp only [real_inner_smul_left, inner_add_right, add_mul, Finset.sum_add_distrib]
    have hh : ∑ j, inner ℝ n (H (q j)) * inner ℝ (g j) y =
        inner ℝ n (H (∑ j, inner ℝ (g j) y • q j)) := by
      simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hh, ← Finset.mul_sum, ← sum_inner, hsumg, inner_zero_left, mul_zero,
      add_zero, hproj, map_sub, map_smul, inner_sub_right, real_inner_smul_right,
      hnH, mul_zero, sub_zero]
    linarith [hH n y]
  let β : Fin d → ℝ := fun j => B.repr (1, x) j.castSucc
  let ζ := B.repr (1, x) (Fin.last d)
  let f : Fin d → E := fun j => H (q j) + s
  have hlinear : ∑ j, β j • f j = H x + s - ζ • H n := by
    simp only [f, smul_add, Finset.sum_add_distrib, ← map_smul, ← map_sum, ← Finset.sum_smul]
    rw [show (∑ j, β j • q j) = x - ζ • n from hsecond 1 x,
      show (∑ j, β j) = 1 from hfirst 1 x, one_smul, map_sub, map_smul]
    module
  have hinterp : ∑ j, (β j • f j + ζ •
      (inner ℝ (g j) (f j) • n - inner ℝ n (f j) • g j)) = H x + s := by
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib,
      ← Finset.sum_smul, show (∑ j, inner ℝ (g j) (f j)) = 0 from htracef,
      zero_smul, show (∑ j, inner ℝ n (f j) • g j) = -H n from hnormal, hlinear]
    module
  rw [← hinterp]
  calc
    _ ≤ ∑ j, ‖β j • f j + ζ •
        (inner ℝ (g j) (f j) • n - inner ℝ n (f j) • g j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ε := by
      apply Finset.sum_le_sum
      intro j _
      exact (facet_coefficient_norm_le n (g j) (f j) hn (hgn j) (β j) ζ (hcoeff j)).trans
        (hbound j)
    _ = d * ε := by simp

end Interpolation

section SkewAnchors

open Module
open scoped BigOperators

theorem skew_affine_norming_set {ι E : Type*} [Finite ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (hd : 0 < d) (hdim : Module.finrank ℝ E = d) (p : ι → E) :
    ∃ A : Finset ι, A.card ≤ d ∧
      ∀ (H : E →ₗ[ℝ] E), (∀ x y, inner ℝ (H x) y = -inner ℝ x (H y)) →
      ∀ (s : E) (ε : ℝ), 0 ≤ ε → (∀ i ∈ A, ‖H (p i) + s‖ ≤ ε) →
      ∀ i, ‖H (p i) + s‖ ≤ d * ε := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let W := Submodule.span ℝ (Set.range (fun i => ((1 : ℝ), p i)))
  have hdimF : Module.finrank ℝ (ℝ × E) = d + 1 := by
    rw [Module.finrank_prod, Module.finrank_self, hdim]; omega
  by_cases hW : W = ⊤
  · let b := (Module.finBasis ℝ (ℝ × E)).reindex (finCongr hdimF)
    obtain ⟨a, n, B, g, hn, hB, hBn, hg, hlast, hcoeff⟩ :=
      maximal_facet_coordinates hd hdim p b hW
    let A := Finset.univ.image a
    refine ⟨A, (Finset.card_image_le).trans (by simp), fun H hH s ε _ hbound i => ?_⟩
    exact facet_skew_affine_bound (p ∘ a) n B g hn hB hBn hg hlast (p i)
      (hcoeff i) H hH s ε (fun j => hbound (a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  · have hrank : Module.finrank ℝ W ≤ d := by
      have hh := Submodule.finrank_lt hW
      rw [hdimF] at hh
      omega
    have hmem (i : ι) : ((1 : ℝ), p i) ∈ W := Submodule.subset_span ⟨i, rfl⟩
    let v : ι → W := fun i => ⟨(1, p i), hmem i⟩
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
      (Submodule.span_range_subtype_eq_top_iff W hmem).mpr rfl
    obtain ⟨a, b, hb, hcoord⟩ := finite_norming_basis v hspan
    let A := Finset.univ.image a
    refine ⟨A, (Finset.card_image_le).trans (by simpa using hrank), fun H _ s ε hε hbound i => ?_⟩
    let L : (ℝ × E) →ₗ[ℝ] E :=
      H.comp (LinearMap.snd ℝ ℝ E) + (LinearMap.fst ℝ ℝ E).smulRight s
    have hh := linear_norming_bound v a b hb hcoord (L.comp W.subtype) ε hε
      (fun j => by
        simpa [L, v] using hbound (a j)
          (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)) i
    change ‖H (p i) + (1 : ℝ) • s‖ ≤ _ at hh
    rw [one_smul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hrank) hε)

end SkewAnchors

section AnchorControl

open scoped BigOperators NNReal Finset

theorem proper_difference_skew_factor {d : ℕ} (T U : SE(d)) :
    ∃ (H : ℝ^[d] →ₗ[ℝ] ℝ^[d]) (s : ℝ^[d]),
      (∀ x y, inner ℝ (H x) y = -inner ℝ x (H y)) ∧
      ∀ x, ‖H x + s‖ = ‖T x - U x‖ := by
  let L := T.val.linearIsometryEquiv
  let M := U.val.linearIsometryEquiv
  let R := M.trans L.symm
  have hRunit : LinearEquiv.det R.toLinearEquiv = 1 := by
    change LinearEquiv.det (M.toLinearEquiv.trans L.toLinearEquiv.symm) = 1
    rw [LinearEquiv.det_trans, LinearEquiv.det_symm, map_inv]
    change (LinearEquiv.det T.val.linearIsometryEquiv.toLinearEquiv)⁻¹ *
      LinearEquiv.det U.val.linearIsometryEquiv.toLinearEquiv = 1
    rw [T.property, U.property, inv_one, mul_one]
  have hR : LinearMap.det R.toLinearMap = 1 := by
    have hh := congrArg (fun u : ℝˣ => (u : ℝ)) hRunit
    rw [LinearEquiv.coe_det, Units.val_one] at hh
    exact hh
  obtain ⟨V, H, hH, hfactor⟩ := orthogonal_difference_skew_factor R hR
  let W := L.symm.trans V
  have hT (x : ℝ^[d]) : T x = L x + T 0 := by
    have hh := T.val.map_vsub x 0
    change L (x - 0) = T x - T 0 at hh
    rw [sub_zero] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm
  have hU (x : ℝ^[d]) : U x = M x + U 0 := by
    have hh := U.val.map_vsub x 0
    change M (x - 0) = U x - U 0 at hh
    rw [sub_zero] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm
  refine ⟨H, W (T 0 - U 0), hH, fun x => ?_⟩
  have hh : W (T x - U x) = H x + W (T 0 - U 0) := by
    rw [hT, hU]
    have heq : L x + T 0 - (M x + U 0) = (L x - M x) + (T 0 - U 0) := by abel
    rw [heq, map_add]
    change V (L.symm (L x - M x)) + _ = _
    rw [map_sub, L.symm_apply_apply]
    exact congrArg (fun y => y + W (T 0 - U 0)) (hfactor x)
  rw [← hh, W.norm_map]

theorem anchor_control_pointwise {n d : ℕ} (P : Fin n → ℝ^[d]) (C : Finset (Fin n)) :
    ∃ A : Finset (Fin n), A ⊆ C ∧ #A ≤ d ∧
      ∀ (T U : SE(d)) (ε : ℝ), 0 ≤ ε →
        (∀ i ∈ A, ‖T (P i) - U (P i)‖ ≤ ε) →
        ∀ i ∈ C, ‖T (P i) - U (P i)‖ ≤ d * ε := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨∅, Finset.empty_subset _, by simp, fun T U ε _ _ i _ => ?_⟩
    simp [Subsingleton.elim (T (P i)) (U (P i))]
  by_cases hC : C.Nonempty
  · let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
    obtain ⟨A, hcard, hA⟩ := skew_affine_norming_set (Nat.pos_of_ne_zero hd)
      (by simp : Module.finrank ℝ (ℝ^[d]) = d) (fun i : C => P i)
    refine ⟨A.image Subtype.val, ?_, Finset.card_image_le.trans hcard,
      fun T U ε hε hbound i hi => ?_⟩
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.property
    · obtain ⟨H, s, hH, hnorm⟩ := proper_difference_skew_factor T U
      rw [← hnorm]
      exact hA H hH s ε hε
        (fun j hj => (hnorm _).trans_le (hbound j (Finset.mem_image.mpr ⟨j, hj, rfl⟩))) ⟨i, hi⟩
  · refine ⟨∅, Finset.empty_subset _, by simp, fun _ _ _ _ _ i hi => ?_⟩
    exact False.elim (hC ⟨i, hi⟩)

/-- Lemma 6: at most d anchors control disagreement between proper motions. -/
theorem anchor_control {n d : ℕ} (P : Fin n → ℝ^[d]) (C : Finset (Fin n)) :
    ∃ A : Finset (Fin n), A ⊆ C ∧ #A ≤ d ∧
      ∀ T U : SE(d), disagreement P C T U ≤ d * disagreement P A T U := by
  obtain ⟨A, hAC, hcard, hA⟩ := anchor_control_pointwise P C
  refine ⟨A, hAC, hcard, fun T U => ?_⟩
  apply ciSup_le'
  intro i
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast] using
    hA T U (disagreement P A T U) (NNReal.coe_nonneg _)
      (fun j hj => NNReal.coe_le_coe.mpr
        (le_ciSup (f := fun j : A => ‖T (P j) - U (P j)‖₊)
          (Set.finite_range _).bddAbove ⟨j, hj⟩)) i i.property

end AnchorControl

end Proper
