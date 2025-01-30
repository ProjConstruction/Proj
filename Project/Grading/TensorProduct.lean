import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

import Project.Grading.HomogeneousSubmonoid

import Project.ForMathlib.TensorProduct

variable {ιA ιB R A B : Type*}
variable [DecidableEq ιA] [AddCommGroup ιA]
variable [DecidableEq ιB] [AddCommGroup ιB]
variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
variable (𝒜 : ιA → Submodule R A) (ℬ : ιB → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

namespace TensorProduct

open scoped DirectSum

noncomputable def gradingByProduct : ιA × ιB → Submodule R (A ⊗[R] B) := fun p ↦
  LinearMap.range (TensorProduct.map (𝒜 p.1).subtype (ℬ p.2).subtype)

scoped infix:min "⊗" => gradingByProduct

instance : SetLike.GradedMonoid (𝒜 ⊗ ℬ) where
  one_mem := ⟨1 ⊗ₜ 1, rfl⟩
  mul_mem := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    simp only [Prod.mk_add_mk]
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul, Submodule.zero_mem]
    | tmul a b =>
      -- simp only [map_tmul, Submodule.coe_subtype]
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, mul_zero, Submodule.zero_mem]
      | tmul a' b' =>
        simp only [map_tmul, Submodule.coe_subtype, Algebra.TensorProduct.tmul_mul_tmul]
        exact ⟨⟨a.1 * a'.1, SetLike.GradedMul.mul_mem a.2 a'.2⟩ ⊗ₜ
          ⟨b.1 * b'.1, SetLike.GradedMul.mul_mem b.2 b'.2⟩, rfl⟩
      | add y y' hy hy' =>
        simp only [map_tmul, Submodule.coe_subtype, map_add, mul_add]
        exact Submodule.add_mem _ hy hy'
    | add x x' hx hx' =>
      simp only [map_add, add_mul]
      exact Submodule.add_mem _ hx hx'

-- noncomputable def decompositionByProductAux : (A ⊗[R] B) →ₗ[R] (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) :=
-- map (DirectSum.decomposeLinearEquiv _ |>.toLinearMap)
--   (DirectSum.decomposeLinearEquiv _ |>.toLinearMap)

noncomputable def decompositionByProduct : (A ⊗[R] B) →ₗ[R] (⨁ (p : ιA × ιB), (𝒜 ⊗ ℬ) p) :=
TensorProduct.lift
  (DirectSum.toModule _ _ _ fun i ↦
    { toFun a := DirectSum.toModule _ _ _ fun j ↦
      { toFun b := DirectSum.lof R (ιA × ιB) (fun p => (𝒜 ⊗ ℬ) p) (i, j) ⟨a.1 ⊗ₜ b.1, ⟨a ⊗ₜ b, rfl⟩⟩
        map_add' := by
          intros
          simp only [Submodule.coe_add, ← map_add]
          congr 1
          ext
          simp only [tmul_add, Submodule.coe_add]
        map_smul' := by
          intros
          simp only [← map_smul]
          congr 1
          ext
          simp }
      map_add' := by
        rintro ⟨a, ha⟩ ⟨a', ha'⟩
        ext j ⟨b, hb⟩ ⟨i', j'⟩
        simp only [AddMemClass.mk_add_mk, LinearMap.coe_comp, Function.comp_apply,
          DirectSum.toModule_lof, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          DirectSum.add_apply, Submodule.coe_add]
        by_cases h : i = i' ∧ j = j'
        · rcases h with ⟨h₁, h₂⟩
          subst h₁
          subst h₂
          simp [add_tmul]

        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne,
          DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
        simp only [ZeroMemClass.coe_zero, add_zero]
        · aesop
        · aesop
        · aesop
      map_smul' := by
        rintro r ⟨a, ha⟩
        ext j ⟨b, hb⟩ ⟨i', j'⟩
        simp only [SetLike.mk_smul_mk, LinearMap.coe_comp, Function.comp_apply,
          DirectSum.toModule_lof, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply, SetLike.coe_eq_coe]
        rw [← map_smul]
        congr 1  }) ∘ₗ
  map (DirectSum.decomposeLinearEquiv 𝒜 |>.toLinearMap) (DirectSum.decomposeLinearEquiv ℬ |>.toLinearMap)

@[simp]
lemma decompositionByProduct_apply_tmul_homogeneous
      (a : A) (b : B) (i : ιA) (j : ιB) (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ j) :
    decompositionByProduct 𝒜 ℬ (a ⊗ₜ b) =
    DirectSum.lof R (ιA × ιB) (fun p => (𝒜 ⊗ ℬ) p) (i, j) ⟨_, ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, rfl⟩⟩ := by
  lift a to 𝒜 i
  · exact ha
  lift b to ℬ j
  · exact hb
  simp only [decompositionByProduct, LinearMap.coe_comp, Function.comp_apply, map_tmul,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe, lift.tmul,
    Subtype.coe_eta, Submodule.coe_subtype]
  erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
  rfl

noncomputable instance : DirectSum.Decomposition (𝒜 ⊗ ℬ) where
  decompose' := decompositionByProduct ..
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      apply DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_ a
      · simp
      · intro i a
        apply DirectSum.Decomposition.inductionOn ℬ ?_ ?_ ?_ b
        · simp
        · intro j b
          rw [decompositionByProduct_apply_tmul_homogeneous (ha := a.2) (hb := b.2)]
          simp only [Subtype.coe_eta, map_tmul, Submodule.coe_subtype]
          erw [DirectSum.coeAddMonoidHom_of]
        · intro b b' hb hb'
          simp [tmul_add, hb, hb']
      · intro a a' ha ha'
        simp [ha, ha', add_tmul]
    | add x y hx hy =>
      simp [hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | H_zero => simp
    | H_basic p x =>
      obtain ⟨i, j⟩ := p
      obtain ⟨_, ⟨x, rfl⟩⟩ := x
      simp only [DirectSum.coeAddMonoidHom_of]
      rw [← DirectSum.lof_eq_of R (ιA × ιB) (fun p => (𝒜 ⊗ ℬ) p)]
      induction x using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        ext ⟨m, n⟩
        simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero, DirectSum.coe_of_apply,
          Prod.mk.injEq, DirectSum.lof_eq_of]
        aesop
      | tmul a b =>
        simp only [map_tmul, Submodule.coe_subtype]
        rw [decompositionByProduct_apply_tmul_homogeneous (ha := a.2) (hb := b.2)]
        simp only [Subtype.coe_eta, map_tmul, Submodule.coe_subtype]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
        rw [← map_add]
        rfl
    | H_plus x y hx hy =>
      simp [hx, hy]

noncomputable instance : GradedAlgebra (𝒜 ⊗ ℬ) where

omit [DecidableEq
  ιA] [AddCommGroup ιA] [DecidableEq ιB] [AddCommGroup ιB] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
lemma mem_degree_iff {iA : ιA} {iB : ιB} (x : A ⊗[R] B) :
    x ∈ (𝒜 ⊗ ℬ) (iA, iB) ↔
    ∃ (c : (𝒜 iA ⊗[R] ℬ iB) →₀ (𝒜 iA × ℬ iB)),
      x = ∑ i ∈ c.support, (c i).1.1 ⊗ₜ (c i).2.1 := by
  classical
  fconstructor
  · rintro (h : x ∈ LinearMap.range _)
    simp only [LinearMap.mem_range] at h
    obtain ⟨x, rfl⟩ := h
    have : x ∈ (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at this
    obtain ⟨c, hc, (rfl : ∑ i ∈ c.support, _ • _ = _)⟩ := this
    choose x' y' hxy' using hc
    let x : c.support → 𝒜 iA := fun i ↦ x' i.2
    let y : c.support → ℬ iB := fun i ↦ y' i.2
    have hxy : ∀ i, x i ⊗ₜ[R] y i = i := fun i ↦ hxy' i.2
    rw [← Finset.sum_attach (s := c.support)]
    simp_rw [← hxy]
    simp only [smul_tmul', map_sum, map_tmul, map_smul, Submodule.coe_subtype]

    let C : (𝒜 iA ⊗[R] ℬ iB) →₀ (𝒜 iA × ℬ iB) :=
      Finsupp.onFinset c.support
        (fun i ↦ if h : i ∈ c.support then (c i • x' h, y' h) else 0)
        (by simp only [ne_eq, dite_eq_right_iff, Prod.mk_eq_zero, not_forall, not_and,
            forall_exists_index]; aesop)
    use C
    rw [Finset.sum_subset (Finsupp.support_onFinset_subset : C.support ⊆ c.support) (by
      intro i hi hi'
      simp only [Finsupp.mem_support_iff, ne_eq, dite_not, Finsupp.onFinset_apply, dite_eq_left_iff,
        Prod.mk_eq_zero, not_forall, not_and, not_exists, Classical.not_imp, Decidable.not_not,
        C] at hi hi' ⊢
      rw [dif_neg hi]
      specialize hi' hi
      obtain ⟨h, h'⟩ := hi'
      simp only [h, ZeroMemClass.coe_zero, h', tmul_zero, C])]
    rw [← Finset.sum_attach (s := c.support)]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, hi⟩ -
    simp only [Finsupp.mem_support_iff, ne_eq, dite_not, Finsupp.onFinset_apply, C] at hi ⊢
    rw [dif_neg hi]
    simp only [SetLike.val_smul, x, y, C, hxy']
  · rintro ⟨c, rfl⟩
    exact sum_mem fun i hi ↦ ⟨(c i).1 ⊗ₜ (c i).2, rfl⟩

-- Proposition 2.5.1
open HomogeneousSubmonoid in
lemma elemIsRelevant_of_exists [AddGroup.FG ιA] [AddGroup.FG ιB]
    (x : A ⊗[R] B) (hom_x : SetLike.Homogeneous (𝒜 ⊗ ℬ) x)
    (rel_x : ElemIsRelevant x hom_x) :
    ∃ (n : ℕ) (sA : Fin n → A) (sB : Fin n → B)
      (hom_sA : ∀ i, SetLike.Homogeneous 𝒜 (sA i))
      (hom_sB : ∀ i, SetLike.Homogeneous ℬ (sB i))
      (rel_sA : ∀ i, ElemIsRelevant (sA i) (hom_sA i))
      (rel_sB : ∀ i, ElemIsRelevant (sB i) (hom_sB i))
      (k : ℕ),
      x ^ k = ∑ i : Fin n, sA i ⊗ₜ sB i:= by
  rw [elemIsRelevant_iff] at rel_x
  obtain ⟨N, y, d, mem_d, fin_index, ⟨k, hk⟩⟩ := rel_x
  let dA : Fin N → ιA := Prod.fst ∘ d
  let dB : Fin N → ιB := Prod.snd ∘ d
  have hdA : (AddSubgroup.closure (Set.range dA)).FiniteIndex := by
    have := AddSubgroup.index_map_dvd (f := AddMonoidHom.fst ιA ιB)
      (AddSubgroup.closure (Set.range d)) (fun i ↦ ⟨⟨i, 0⟩, rfl⟩)
    rw [show (AddSubgroup.map (AddMonoidHom.fst ιA ιB) (AddSubgroup.closure (Set.range d))) =
      AddSubgroup.closure (Set.range dA) by
      refine le_antisymm ?_ ?_
      · simp only [AddSubgroup.map_le_iff_le_comap, AddSubgroup.closure_le, AddSubgroup.coe_comap,
        AddMonoidHom.coe_fst]
        rintro _ ⟨i, rfl⟩
        simp only [Set.mem_preimage, SetLike.mem_coe]
        refine AddSubgroup.subset_closure ⟨i, rfl⟩
      · simp only [AddSubgroup.closure_le, AddSubgroup.coe_map, AddMonoidHom.coe_fst]
        rintro _ ⟨i, rfl⟩
        simp only [Set.mem_image, SetLike.mem_coe, Prod.exists, exists_and_right, exists_eq_right]
        refine ⟨dB i, AddSubgroup.subset_closure ⟨i, rfl⟩⟩] at this
    constructor
    intro h
    rw [h] at this
    simp only [zero_dvd_iff] at this
    have := fin_index.1
    contradiction
  have hdB : (AddSubgroup.closure (Set.range dB)).FiniteIndex := by
    have := AddSubgroup.index_map_dvd (f := AddMonoidHom.snd ιA ιB)
      (AddSubgroup.closure (Set.range d)) (fun i ↦ ⟨⟨0, i⟩, rfl⟩)
    rw [show (AddSubgroup.map (AddMonoidHom.snd ιA ιB) (AddSubgroup.closure (Set.range d))) =
      AddSubgroup.closure (Set.range dB) by
      refine le_antisymm ?_ ?_
      · simp only [AddSubgroup.map_le_iff_le_comap, AddSubgroup.closure_le, AddSubgroup.coe_comap,
        AddMonoidHom.coe_fst]
        rintro _ ⟨i, rfl⟩
        simp only [Set.mem_preimage, SetLike.mem_coe]
        refine AddSubgroup.subset_closure ⟨i, rfl⟩
      · simp only [AddSubgroup.closure_le, AddSubgroup.coe_map, AddMonoidHom.coe_fst]
        rintro _ ⟨i, rfl⟩
        simp only [AddMonoidHom.coe_snd, Set.mem_image, SetLike.mem_coe, Prod.exists,
          exists_eq_right]
        refine ⟨dA i, AddSubgroup.subset_closure ⟨i, rfl⟩⟩] at this
    constructor
    intro h
    rw [h] at this
    simp only [zero_dvd_iff] at this
    have := fin_index.1
    contradiction
  have hy (i : Fin N) : y i ∈ (𝒜 ⊗ ℬ) (dA i, dB i) := by apply mem_d
  simp_rw [mem_degree_iff] at hy
  choose c hc using hy
  simp_rw [hc] at hk
  rw [Finset.prod_sum] at hk
  simp only [Finset.prod_attach_univ, ← prod_tmul_prod] at hk

  let t := (Finset.univ.pi fun x ↦ (c x).support)

  let M := t.card
  let sA : Fin M → A :=
    (fun x ↦ ∏ i : Fin N, (c i (x.1 i (by simp))).1) ∘ t.equivFin.symm
  let sB : Fin M → B :=
    (fun x ↦ ∏ i : Fin N, (c i (x.1 i (by simp))).2) ∘
    (Finset.univ.pi fun x ↦ (c x).support).equivFin.symm
  have hom_sA : ∀ i, SetLike.Homogeneous 𝒜 (sA i) := by
    intro i
    simp only [Function.comp_apply, sA, M]
    apply SetLike.Homogeneous.prod'
    intro j
    simp only [SetLike.homogeneous_coe, sA, M]
  have hom_sB : ∀ i, SetLike.Homogeneous ℬ (sB i) := by
    intro i
    simp only [Function.comp_apply, sB, M]
    apply SetLike.Homogeneous.prod'
    intro j
    simp only [SetLike.homogeneous_coe, sB, M]
  have rel_sA : ∀ i, ElemIsRelevant (sA i) (hom_sA i) := by
    intro i
    rw [elemIsRelevant_iff]
    refine ⟨N, (fun j ↦ ((c j) (t.equivFin.symm i |>.1 j (by simp))).1.1), dA, ?_, hdA, 1, by
      simp [pow_one, sA]⟩
    simp only [SetLike.coe_mem, implies_true, sA, t, sB, M]
  have rel_sB : ∀ i, ElemIsRelevant (sB i) (hom_sB i) := by
    intro i
    rw [elemIsRelevant_iff]
    refine ⟨N, (fun j ↦ ((c j) (t.equivFin.symm i |>.1 j (by simp))).2.1), dB, ?_, hdB, 1, by
      simp [pow_one, sB]⟩
    simp only [SetLike.coe_mem, implies_true, sA, t, sB, M]
  use M, sA, sB, hom_sA, hom_sB, rel_sA, rel_sB, k
  rw [← hk, ← Finset.sum_attach]
  fapply Fintype.sum_bijective
  · exact t.equivFin.toFun
  · exact t.equivFin.bijective
  · rintro ⟨x, hx⟩
    simp only [Equiv.toFun_as_coe, Function.comp_apply, Equiv.symm_apply_apply, sA, t, sB, M]

end TensorProduct
