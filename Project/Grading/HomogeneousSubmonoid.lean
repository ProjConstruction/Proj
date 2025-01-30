import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Schreier

import Project.ForMathlib.SubgroupBasic
import Project.ForMathlib.SetLikeHomogeneous
import Project.GR.Basic

open DirectSum TensorProduct
open scoped NNReal

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A]  (𝒜 : ι → σ)
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]

structure HomogeneousSubmonoid extends Submonoid A where
  homogeneous : ∀ {x}, x ∈ toSubmonoid → SetLike.Homogeneous 𝒜 x

open scoped GR

namespace HomogeneousSubmonoid

variable {𝒜} (S : HomogeneousSubmonoid 𝒜)

def closure (s : Set A) (hs : ∀ x ∈ s, SetLike.Homogeneous 𝒜 x) : HomogeneousSubmonoid 𝒜 where
  __ := Submonoid.closure s
  homogeneous {x} (hx : x ∈ Submonoid.closure s) :=
    Submonoid.closure_induction hs
      (SetLike.homogeneous_one 𝒜)
      (fun _ _ _ _ hx hy => SetLike.homogeneous_mul hx hy) hx

lemma mem_closure_singleton (a : A) (ha : SetLike.Homogeneous 𝒜 a) (x) :
    x ∈ (closure {a} (by simpa)).toSubmonoid ↔
    ∃ (n : ℕ), x = a ^ n := by
  simp [closure, Submonoid.mem_closure_singleton, eq_comm]

def bar : HomogeneousSubmonoid 𝒜 where
  carrier := {x | SetLike.Homogeneous 𝒜 x ∧ ∃ y ∈ S.toSubmonoid, x ∣ y}
  mul_mem' := by
    rintro x y ⟨hom_x, ⟨ax, ⟨hax, hax'⟩⟩⟩ ⟨hom_y, ⟨ay, ⟨hay, hay'⟩⟩⟩
    exact ⟨SetLike.homogeneous_mul hom_x hom_y, ⟨ax * ay, ⟨mul_mem hax hay,
      mul_dvd_mul hax' hay'⟩⟩⟩
  one_mem' := ⟨SetLike.homogeneous_one 𝒜, ⟨1, ⟨one_mem _, by rfl⟩⟩⟩
  homogeneous := by rintro x ⟨hom_x, ⟨y, ⟨hy, hy'⟩⟩⟩; exact hom_x

def deg : AddSubmonoid ι where
  carrier := {i | ∃ x ∈ S.toSubmonoid, x ∈ 𝒜 i}
  add_mem' := by
    rintro i j ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    exact ⟨x * y, mul_mem hx hy, SetLike.GradedMul.mul_mem hx' hy'⟩
  zero_mem' := ⟨1, one_mem _, SetLike.GradedOne.one_mem⟩

lemma mem_deg_singleton (a : A) (ha : SetLike.Homogeneous 𝒜 a) (x) :
    x ∈ (closure {a} (by simpa)).deg ↔
    (∃ n : ℕ, a ^ n ∈ 𝒜 x) := by
  simp only [deg, ne_eq, Set.mem_setOf_eq, exists_and_right]
  fconstructor
  · rintro ⟨y, hy, h⟩
    rw [mem_closure_singleton (ha := ha)] at hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨n, ‹_›⟩
  · rintro ⟨n, hn⟩
    refine ⟨a^n, ?_, hn⟩
    rw [mem_closure_singleton (ha := ha)]
    aesop

lemma mem_deg {i} : i ∈ S.deg ↔ ∃ x ∈ S.toSubmonoid, x ∈ 𝒜 i := Iff.rfl

lemma zero_mem_deg [Nontrivial A] : 0 ∈ S.deg :=
  ⟨1, one_mem _, SetLike.GradedOne.one_mem⟩

def monDeg  : AddSubmonoid ι := AddSubmonoid.closure S.deg

scoped notation:max ι"["S"⟩" => monDeg (ι := ι) S

def agrDeg : AddSubgroup ι := AddSubgroup.closure S.deg

scoped notation:max ι"["S"]" => agrDeg (ι := ι) S

noncomputable def agrDegEquiv : ι[S⟩ᵃᵍʳ ≃+ ι[S] := (AddGR.equivAsAddSubgroup ..).trans
  { __ := AddSubgroup.inclusion (by
      rw [AddSubgroup.closure_le]
      change S.monDeg ≤ S.agrDeg.toAddSubmonoid
      erw [AddSubmonoid.closure_le]
      dsimp only [AddSubgroup.coe_toAddSubmonoid, agrDeg]
      exact AddSubgroup.subset_closure)
    invFun := AddSubgroup.inclusion (by
      erw [AddSubgroup.closure_le]
      refine AddSubgroup.subset_closure.trans ?_
      refine AddSubgroup.closure_mono ?_
      exact AddSubmonoid.subset_closure)
    left_inv x := rfl
    right_inv x := rfl }

noncomputable def convMonDegEmbedding : (ℝ≥0 ⊗[ℕ] ι[S⟩) →ₗ[ℝ≥0] (ℝ ⊗[ℤ] ι) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun r :=
        { toFun i := r.1 ⊗ₜ i.1
          map_add' x y := by simp [← tmul_add]
          map_smul' s x := by
            simp only [NNReal.val_eq_coe, AddSubmonoidClass.coe_nsmul, eq_natCast, Nat.cast_id]
            rw [smul_tmul']
            erw [show s • r.1 = (s : ℤ) • r.1 from rfl]
            rw [smul_tmul]
            congr 1
            simp }
      map_add' r s := by ext; simp [add_tmul]
      map_smul' r s := by
        ext
        simp only [smul_eq_mul, NNReal.val_eq_coe, NNReal.coe_mul, LinearMap.coe_mk,
          AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply, smul_tmul']
        rfl }

@[simp]
lemma convMonDegEmbedding_apply_tmul (r : ℝ≥0) (i : ι[S⟩) :
    convMonDegEmbedding S (r ⊗ₜ i) = r.1 ⊗ₜ i.1 := rfl

noncomputable def convMonDeg : Submodule ℝ≥0 (ℝ ⊗[ℤ] ι) := LinearMap.range (convMonDegEmbedding S)

noncomputable def convMonDeg' : Submodule ℝ≥0 (ℝ ⊗[ℤ] ι) :=
  Submodule.span ℝ≥0 {x | ∃ (a : ℝ≥0) (i : ι) (_ : i ∈ S.deg) , x = a.1 ⊗ₜ i }

scoped notation:max ι"["S"⟩ℝ≥0" => convMonDeg (ι := ι) S

lemma mem_convMonDeg [Nontrivial A] (x) :
    x ∈ ι[S⟩ℝ≥0 ↔
    ∃ (s : ι →₀ ℝ≥0), (∀ i ∈ s.support, i ∈ S.deg) ∧ x = ∑ i ∈ s.support, (s i).1 ⊗ₜ i := by
  classical
  fconstructor
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero =>
      refine ⟨0, ?_, by simp⟩
      intro i hi
      simp only [Finsupp.support_zero, Finset.not_mem_empty] at hi
    | tmul a i =>
      rcases i with ⟨i, hi⟩
      induction hi using AddSubmonoid.closure_induction with
      | mem i hi =>
        refine ⟨Finsupp.single i a, ?_, ?_⟩
        · intro i hi
          simp only [Finsupp.mem_support_iff, Finsupp.single_apply, ne_eq, ite_eq_right_iff,
            Classical.not_imp] at hi
          rwa [← hi.1]
        simp only [convMonDegEmbedding_apply_tmul, NNReal.val_eq_coe]
        rw [eq_comm, Finset.sum_eq_single i]
        · simp
        · intro j hj H
          simp [Finsupp.single_eq_of_ne H.symm]
        aesop
      | one => exact ⟨0, by aesop, by simp⟩
      | mul i j _ _ ih ih' =>
        obtain ⟨s, hs, eq⟩ := ih
        obtain ⟨t, ht, eq'⟩ := ih'
        simp only [convMonDegEmbedding_apply_tmul, NNReal.val_eq_coe, ne_eq, tmul_add] at eq eq' ⊢
        simp_rw [eq, eq']
        refine ⟨s + t, ?_, ?_⟩
        · intro j hj
          have := Finsupp.support_add hj
          simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq] at this hs ht
          tauto
        simp only [Finsupp.coe_add, Pi.add_apply, NNReal.coe_add, add_tmul, Finset.sum_add_distrib]
        nth_rewrite 1 [show (s + t).support = s.support ∪ ((s + t).support \ s.support) by
          ext; aesop]
        nth_rewrite 2 [show (s + t).support = t.support ∪ ((s + t).support \ t.support) by
          ext; aesop]
        rw [Finset.sum_union_eq_left, Finset.sum_union_eq_left]
        · aesop
        · aesop
    | add x y ihx ihy =>
      obtain ⟨s, hs, eq⟩ := ihx
      obtain ⟨t, ht, eq'⟩ := ihy
      simp only [NNReal.val_eq_coe, Finsupp.mem_support_iff, ne_eq, map_add] at eq eq' ⊢
      simp_rw [eq, eq']
      refine ⟨s + t, ⟨?_, ?_⟩⟩
      · intro j hj
        simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.coe_add, Pi.add_apply,
          AddLeftCancelMonoid.add_eq_zero, not_and] at hs ht hj
        tauto
      simp only [Finsupp.coe_add, Pi.add_apply, NNReal.coe_add, add_tmul, Finset.sum_add_distrib]
      nth_rewrite 1 [show (s + t).support = s.support ∪ ((s + t).support \ s.support) by
        ext; aesop]
      nth_rewrite 2 [show (s + t).support = t.support ∪ ((s + t).support \ t.support) by
        ext; aesop]
      rw [Finset.sum_union_eq_left, Finset.sum_union_eq_left]
      · aesop
      · intro a ha ha'
        simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at ha'
        simp only [ha', NNReal.coe_zero, zero_tmul]

  · rintro ⟨a, ha, hi, rfl⟩
    refine Submodule.sum_mem _ fun i hi => ?_
    exact ⟨a i ⊗ₜ[ℕ] ⟨i, AddSubmonoid.subset_closure (ha i hi)⟩, rfl⟩

def IsRelevant : Prop := ∀ (i : ι), ∃ (n : ℕ), 0 < n ∧ n • i ∈ ι[S.bar]

lemma isRelevant_iff_isTorsion_quotient : S.IsRelevant ↔ AddMonoid.IsTorsion (ι ⧸ ι[S.bar]) := by
  fconstructor
  · intro H x
    induction x using Quotient.inductionOn' with | h x =>
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn, hx⟩ := H x
    refine ⟨n, hn, ?_⟩
    change Quotient.mk'' (n • x) = _
    rwa [QuotientAddGroup.eq_zero_iff]
  · intro H i
    specialize H i
    rw [isOfFinAddOrder_iff_nsmul_eq_zero] at H
    obtain ⟨n, hn, hni⟩ := H
    refine ⟨n, hn, ?_⟩
    change Quotient.mk'' (n • i) = _ at hni
    rwa [QuotientAddGroup.eq_zero_iff] at hni

lemma isRelevant_iff_finite_quotient_of_FG [AddGroup.FG ι] :
    S.IsRelevant ↔ Finite (ι ⧸ ι[S.bar]) := by
  rw [isRelevant_iff_isTorsion_quotient]
  fconstructor
  · intro H
    exact AddCommGroup.finite_of_fg_torsion _ H
  · intro H
    apply is_add_torsion_of_finite

lemma isRelevant_iff_finiteIndex_of_FG [AddGroup.FG ι] :
    S.IsRelevant ↔ ι[S.bar].FiniteIndex := by
  rw [isRelevant_iff_finite_quotient_of_FG]
  fconstructor
  · intro H
    exact ι[S.bar].finiteIndex_of_finite_quotient
  · intro H
    exact ι[S.bar].finite_quotient_of_finiteIndex

abbrev SetIsRelevant (s : Set A) (hs : ∀ i ∈ s, SetLike.Homogeneous 𝒜 i) : Prop :=
  closure s hs |>.IsRelevant

abbrev ElemIsRelevant (a : A) (ha : SetLike.Homogeneous 𝒜 a) : Prop :=
  closure {a} (by simpa) |>.IsRelevant

attribute [to_additive] Subgroup.closure_mul_image_mul_eq_top
attribute [to_additive] Subgroup.closure_mul_image_eq
attribute [to_additive] Subgroup.closure_mul_image_eq_top
attribute [to_additive] Subgroup.closure_mul_image_eq_top'
attribute [to_additive] Subgroup.exists_finset_card_le_mul
attribute [to_additive] Subgroup.fg_of_index_ne_zero

lemma exists_factorisation_of_elemIsRelevant
    [AddGroup.FG ι] (a : A) (ha : SetLike.Homogeneous 𝒜 a) (a_rel : ElemIsRelevant a ha) :
    ∃ (n : ℕ) (x : Fin n → A) (d : Fin n → ι)
      (_ : ∀ (i : Fin n), x i ∈ 𝒜 (d i)),
      (AddSubgroup.closure (Set.range d)).FiniteIndex ∧
      (∃ (k : ℕ), ∏ i : Fin n, x i = a ^ k) := by
  classical
  rw [ElemIsRelevant, isRelevant_iff_finiteIndex_of_FG] at a_rel
  haveI fg : AddGroup.FG ι[(closure {a} (by simpa)).bar] := by
    exact AddSubgroup.fg_of_index_ne_zero _
  obtain ⟨s, hs1, hs2⟩ :=
    AddGroup.exists_finite_generating_set_of_FG' ι
    (closure (𝒜 := 𝒜) {a} (by simpa)).bar.deg fg
  have hs3 : ∀ i : s, ∃ (y : A), y ∈ 𝒜 i ∧ (∃ (n : ℕ), y ∣ a^n) := by
    rintro ⟨i, hi⟩
    specialize hs1 hi
    simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, ne_eq] at hs1
    obtain ⟨y, ⟨_, ⟨z, hz1, hz2⟩⟩, hy⟩ := hs1
    rw [mem_closure_singleton (ha := ha)] at hz1
    obtain ⟨n, rfl⟩ := hz1
    exact ⟨y, hy, n, hz2⟩

  choose y y_mem y_dvd using hs3
  choose n y_dvd using y_dvd
  let N : ℕ := s.card
  let d : Fin N → ι := Subtype.val ∘ (Finset.equivFin s).symm
  let x : Fin N → A := y ∘ (Finset.equivFin s).symm
  let k : Fin N → ℕ := n ∘ (Finset.equivFin s).symm
  let K : ℕ := ∑ i : Fin N, k i
  have dvd : (∏ i : Fin N, x i) ∣ a ^ K := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    rintro ⟨i, hi⟩ -
    apply y_dvd
  obtain ⟨b, hb, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 (by
    refine SetLike.Homogeneous.prod' 𝒜 x fun j ↦ ?_
    simpa [x] using ⟨_, y_mem _⟩) (by
    refine SetLike.Homogeneous.pow 𝒜 ?_ _
    assumption) dvd
  refine ⟨N + 1, Fin.cons b x, Fin.cons j d, ?_, ?_, ⟨K, ?_⟩⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa
    · intro m
      apply y_mem

  · have : AddSubgroup.closure s ≤ AddSubgroup.closure (Set.range (Fin.cons j d)) := by
      apply AddSubgroup.closure_mono
      intro i hi
      simp only [Fin.range_cons, Set.mem_insert_iff, Set.mem_range, Function.comp_apply, d, N]
      if h : i = j
      then left; exact h
      else
      right
      use s.equivFin ⟨i, hi⟩
      simp only [Equiv.symm_apply_apply, N, d]
    rw [hs2] at this
    convert AddSubgroup.finiteIndex_of_le this
    exact a_rel
  · simp [← hb, mul_comm]

lemma elemIsRelevant_of_homogeneous_of_factorisation
    [AddGroup.FG ι] (a : A) (ha : SetLike.Homogeneous 𝒜 a)
    (n : ℕ) (x : Fin n → A) (d : Fin n → ι)
    (mem : ∀ (i : Fin n), x i ∈ 𝒜 (d i))
    (finiteIndex : (AddSubgroup.closure (Set.range d)).FiniteIndex)
    (k : ℕ) (eq : ∏ i : Fin n, x i = a ^ k) :  ElemIsRelevant a ha := by
  rw [ElemIsRelevant, isRelevant_iff_finiteIndex_of_FG]
  set H := _; change AddSubgroup.FiniteIndex H
  suffices le : AddSubgroup.closure (Set.range d) ≤ H by
    exact AddSubgroup.finiteIndex_of_le le
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  refine AddSubgroup.subset_closure ?_
  simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, ne_eq]
  exact ⟨x i, ⟨⟨d i, mem i⟩, ⟨a ^ k, by rw [mem_closure_singleton (ha := ha)]; aesop, by
    rw [← eq]; apply Finset.dvd_prod_of_mem; aesop⟩⟩, mem i⟩

lemma elemIsRelevant_iff [AddGroup.FG ι]
    (a : A) (ha : SetLike.Homogeneous 𝒜 a) :
    ElemIsRelevant a ha ↔
    ∃ (n : ℕ) (x : Fin n → A) (d : Fin n → ι)
      (_ : ∀ (i : Fin n), x i ∈ 𝒜 (d i)),
      (AddSubgroup.closure (Set.range d)).FiniteIndex ∧
      (∃ (k : ℕ), ∏ i : Fin n, x i = a ^ k) := by
  fconstructor
  · intro h
    exact exists_factorisation_of_elemIsRelevant _ ha h
  · rintro ⟨n, x, d, mem, finiteIndex, k, eq⟩
    exact elemIsRelevant_of_homogeneous_of_factorisation _ ha n x d mem finiteIndex k eq

variable (𝒜) in
def dagger : HomogeneousIdeal 𝒜 where
  __ := Ideal.span { x | ∃ (h : SetLike.Homogeneous 𝒜 x), ElemIsRelevant x h }
  is_homogeneous' := Ideal.homogeneous_span _ _ (by rintro x ⟨h, _⟩; exact h)

scoped postfix:max "†" => dagger

end HomogeneousSubmonoid
