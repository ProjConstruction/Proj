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

variable {𝒜 ℬ}
omit [DecidableEq
  ιA] [AddCommGroup ιA] [DecidableEq ιB] [AddCommGroup ιB] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
lemma tmul_homogeneous {a : A} {b : B}
    (ha : SetLike.Homogeneous 𝒜 a) (hb : SetLike.Homogeneous ℬ b) :
    SetLike.Homogeneous (𝒜 ⊗ ℬ) (a ⊗ₜ b) := by
  rcases ha with ⟨i, ha⟩
  rcases hb with ⟨j, hb⟩
  use (i, j), ⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩
  simp

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

open HomogeneousSubmonoid in
lemma tmul_elemIsRelevant [AddGroup.FG ιA] [AddGroup.FG ιB]
    {x : A} {y : B} {hom_x : SetLike.Homogeneous 𝒜 x} {hom_y : SetLike.Homogeneous ℬ y}
    (rel_x : ElemIsRelevant x hom_x) (rel_y : ElemIsRelevant y hom_y) :
    ElemIsRelevant (x ⊗ₜ y) (tmul_homogeneous hom_x hom_y) := by
  sorry

-- Proposition 2.5.1
open HomogeneousSubmonoid in
lemma elemIsRelevant_of_exists [AddGroup.FG ιA] [AddGroup.FG ιB]
    (x : A ⊗[R] B) (hom_x : SetLike.Homogeneous (𝒜 ⊗ ℬ) x)
    (rel_x : ElemIsRelevant x hom_x) :
    ∃ (n : ℕ) (sA : Fin n → A) (sB : Fin n → B)
      (hom_sA : ∀ i, SetLike.Homogeneous 𝒜 (sA i))
      (hom_sB : ∀ i, SetLike.Homogeneous ℬ (sB i))
      (_ : ∀ i, ElemIsRelevant (sA i) (hom_sA i))
      (_ : ∀ i, ElemIsRelevant (sB i) (hom_sB i))
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
      simp [pow_one, sB, t]⟩
    simp only [SetLike.coe_mem, implies_true, t, sB, sA, M]
  use M, sA, sB, hom_sA, hom_sB, rel_sA, rel_sB, k
  rw [← hk, ← Finset.sum_attach]
  fapply Fintype.sum_bijective
  · exact t.equivFin.toFun
  · exact t.equivFin.bijective
  · rintro ⟨x, hx⟩
    simp only [Equiv.toFun_as_coe, Function.comp_apply, Equiv.symm_apply_apply, sA, t, sB, M]

variable (𝒜 ℬ) in
open HomogeneousSubmonoid in
protected noncomputable def dagger : Ideal (A ⊗[R] B) :=
{ __ := (LinearMap.range
  (map (Submodule.subtype 𝒜†.toIdeal) (Submodule.subtype ℬ†.toIdeal) :
    ((dagger 𝒜).toIdeal ⊗[R] (dagger ℬ).toIdeal) →ₗ[R] (A ⊗[R] B)))
  smul_mem' := by
    intro r x hx
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, LinearMap.mem_range, smul_eq_mul] at hx ⊢
    obtain ⟨x, rfl⟩ := hx
    induction x using TensorProduct.induction_on with
    | zero =>
      use 0
      simp only [map_zero, mul_zero]
    | tmul a b =>
      simp only [map_tmul, LinearMap.coe_restrictScalars, Submodule.coe_subtype]
      induction r using TensorProduct.induction_on with
      | zero =>
        use 0
        simp only [map_zero, zero_mul]
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul]
        use (a' • a) ⊗ₜ (b' • b)
        simp only [map_tmul, LinearMap.coe_restrictScalars, map_smul, Submodule.coe_subtype,
          smul_eq_mul]
      | add x y hx hy =>
        obtain ⟨y₁, eq1⟩ := hx
        obtain ⟨y₂, eq₂⟩ := hy
        use y₁ + y₂
        simp only [map_add, eq1, eq₂, add_mul]
    | add x y hx hy =>
      obtain ⟨y₁, eq₁⟩ := hx
      obtain ⟨y₂, eq₂⟩ := hy
      use y₁ + y₂
      simp only [map_add, eq₁, eq₂, mul_add] }

open HomogeneousSubmonoid in
lemma rad_dagger [AddGroup.FG ιA] [AddGroup.FG ιB] :
    (dagger (𝒜 ⊗ ℬ)).toIdeal.radical =
    Ideal.radical (TensorProduct.dagger 𝒜 ℬ)  := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.radical_le_radical_iff]
    change Ideal.span _ ≤ _
    rw [Ideal.span_le]
    rintro x ⟨hom, rel⟩
    simp only [Submodule.coe_set_mk, Submodule.coe_toAddSubmonoid, SetLike.mem_coe,
      LinearMap.mem_range]
    obtain ⟨n, a, b, hom_a, hom_b, rel_a, rel_b, ⟨k, eq⟩⟩ := elemIsRelevant_of_exists x hom rel
    rw [Ideal.mem_radical_iff]
    use k
    rw [eq]
    refine sum_mem fun i _ ↦ ?_
    simp only [TensorProduct.dagger, Submodule.mem_mk, Submodule.mem_toAddSubmonoid,
      LinearMap.mem_range]
    use ⟨a i, Ideal.subset_span ⟨hom_a i, rel_a i⟩⟩ ⊗ₜ ⟨b i, Ideal.subset_span ⟨hom_b i, rel_b i⟩⟩
    rfl
  · apply Ideal.radical_mono
    let M : Submodule R (A ⊗[R] B) :=
    { carrier := (𝒜⊗ℬ)†.toIdeal
      smul_mem' r x hx := by
        simp only [SetLike.mem_coe, HomogeneousIdeal.mem_iff] at hx ⊢
        rw [_root_.Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hx
      add_mem' := add_mem
      zero_mem' := zero_mem _ }
    change LinearMap.range _ ≤ M
    rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap]

    rintro x -
    simp only [Submodule.mem_comap]
    change _ ∈ Submodule.span _ _

    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp only [map_tmul, LinearMap.coe_restrictScalars, Submodule.coe_subtype,
        HomogeneousIdeal.mem_iff]
      change a ∈ Submodule.span _ _ at ha
      change b ∈ Submodule.span _ _ at hb
      change _ ∈ Ideal.span _
      rw [mem_span_set] at ha hb
      obtain ⟨c, hc, (rfl : ∑ i ∈ c.support, _ • _ = _)⟩ := ha
      obtain ⟨d, hd, (rfl : ∑ i ∈ d.support, _ • _ = _)⟩ := hb
      simp only [smul_eq_mul, tmul_sum, sum_tmul]
      refine sum_mem fun i hi ↦ sum_mem fun j hj ↦ ?_
      specialize hc hj
      specialize hd hi
      obtain ⟨hj, hj'⟩ := hc
      obtain ⟨hi, hi'⟩ := hd
      rw [show (c j * j) ⊗ₜ[R] (d i * i) = (c j ⊗ₜ d i) * (j ⊗ₜ i) by
        simp only [Algebra.TensorProduct.tmul_mul_tmul]]
      apply Ideal.mul_mem_left
      refine Ideal.subset_span ?_
      refine ⟨tmul_homogeneous hj hi, tmul_elemIsRelevant hj' hi'⟩
    | add x y hx hy =>
      simp only [map_add, LinearMap.map_add]
      exact Submodule.add_mem _ hx hy

end TensorProduct
