import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

import Project.ForMathlib.SubgroupBasic

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

def bar : HomogeneousSubmonoid 𝒜 where
  carrier := {x | SetLike.Homogeneous 𝒜 x ∧ ∃ y ∈ S.toSubmonoid, x ∣ y}
  mul_mem' := by
    rintro x y ⟨hom_x, ⟨ax, ⟨hax, hax'⟩⟩⟩ ⟨hom_y, ⟨ay, ⟨hay, hay'⟩⟩⟩
    exact ⟨SetLike.homogeneous_mul hom_x hom_y, ⟨ax * ay, ⟨mul_mem hax hay,
      mul_dvd_mul hax' hay'⟩⟩⟩
  one_mem' := ⟨SetLike.homogeneous_one 𝒜, ⟨1, ⟨one_mem _, by rfl⟩⟩⟩
  homogeneous := by rintro x ⟨hom_x, ⟨y, ⟨hy, hy'⟩⟩⟩; exact hom_x

def deg : Set ι := {i | ∃ x ∈ S.toSubmonoid, x ≠ 0 ∧ x ∈ 𝒜 i}

omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] in
lemma mem_deg {i} : i ∈ S.deg ↔ ∃ x ∈ S.toSubmonoid, x ≠ 0 ∧ x ∈ 𝒜 i := Iff.rfl

lemma zero_mem_deg [Nontrivial A] : 0 ∈ S.deg :=
  ⟨1, one_mem _, one_ne_zero, SetLike.GradedOne.one_mem⟩

def monDeg [AddCommGroup ι] : AddSubmonoid ι := AddSubmonoid.closure S.deg

scoped notation:max ι"["S"⟩" => monDeg (ι := ι) S

def agrDeg [AddCommGroup ι] : AddSubgroup ι := AddSubgroup.closure S.deg

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

omit [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp]
lemma convMonDegEmbedding_apply_tmul (r : ℝ≥0) (i : ι[S⟩) :
    convMonDegEmbedding S (r ⊗ₜ i) = r.1 ⊗ₜ i.1 := rfl

noncomputable def convMonDeg : Submodule ℝ≥0 (ℝ ⊗[ℤ] ι) := LinearMap.range (convMonDegEmbedding S)

noncomputable def convMonDeg' : Submodule ℝ≥0 (ℝ ⊗[ℤ] ι) :=
  Submodule.span ℝ≥0 {x | ∃ (a : ℝ≥0) (i : ι) (_ : i ∈ S.deg) , x = a.1 ⊗ₜ i }

scoped notation:max ι"["S"⟩ℝ≥0" => convMonDeg (ι := ι) S

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
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
      · aesop

  · rintro ⟨a, ha, hi, rfl⟩
    refine Submodule.sum_mem _ fun i hi => ?_
    exact ⟨a i ⊗ₜ[ℕ] ⟨i, AddSubmonoid.subset_closure (ha i hi)⟩, rfl⟩

def isRelevant : Prop := ∀ (i : ι), ∃ (n : ℕ), n • i ∈ ι[S.bar]

abbrev setIsRelevant (s : Set A) (hs : ∀ i ∈ s, SetLike.Homogeneous 𝒜 i) : Prop :=
  closure s hs |>.isRelevant

abbrev elemIsRelevant (a : A) (ha : SetLike.Homogeneous 𝒜 a) : Prop :=
  closure {a} (by simpa) |>.isRelevant

lemma zero_elemIsRelevant : elemIsRelevant (𝒜 := 𝒜) 0 ⟨0, zero_mem _⟩ := by
  intro i
  use 0
  simp only [zero_smul]
  exact zero_mem _

attribute [-simp] Finsupp.mem_support_iff in
example (x : A) (homogeneous : SetLike.Homogeneous 𝒜 x) (rel : elemIsRelevant x homogeneous) :
    ∃ (k : ℕ) (c : ι →₀ A), x^k = ∏ i ∈ c.support, (c i) := by
  rcases homogeneous with ⟨i, hi⟩
  obtain ⟨k, hk⟩ := rel i
  erw [AddSubgroup.mem_closure_iff_exists] at hk
  obtain ⟨c, hc1, hc2⟩ := hk
  generalize_proofs h at hc1
  have (k : ι)  :
      (k ∈ (closure {x} h).bar.deg) ↔ ∃ (a : A) (n : ℕ), a ∈ 𝒜 k ∧ a ≠ 0 ∧ a ∣ x ^ n := by
    simp only [deg, bar, closure, Submonoid.mem_closure_singleton, exists_exists_eq_and,
      Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, ne_eq, exists_and_left]

    constructor
    · rintro ⟨a, ⟨-, ⟨n, ha1⟩⟩, ⟨ha2, ha3⟩⟩
      exact ⟨a, ha3, ha2, n, ha1⟩
    · rintro ⟨a, ha1, ha2, ⟨n, ha3⟩⟩
      exact ⟨a, ⟨⟨k, ha1⟩, ⟨n, ha3⟩⟩, ha2, ha1⟩
  simp_rw [this] at hc1

  simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, ne_eq] at hc1
  choose y hy1 hy2 hy3 using hc1
  choose hy0 hy1 using hy1
  change ∀ _ _, ∃ _ ∈ Submonoid.closure _, _ at hy1
  simp_rw [Submonoid.mem_closure_singleton] at hy1




  sorry

variable (𝒜) in
def daggerIdeal : HomogeneousIdeal 𝒜 where
  __ := Ideal.span { x | ∃ (h : SetLike.Homogeneous 𝒜 x), elemIsRelevant x h }
  is_homogeneous' := Ideal.homogeneous_span _ _ (by rintro x ⟨h, _⟩; exact h)

scoped postfix:max "†" => daggerIdeal

end HomogeneousSubmonoid
