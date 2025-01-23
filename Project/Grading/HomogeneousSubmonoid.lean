import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

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

scoped notation:max ι"["S"⟩≥0" => convMonDeg (ι := ι) S

example [Nontrivial A] (x) :
    x ∈ convMonDeg' S ↔
    ∃ (a b : ℝ≥0) (i j : ι) (hi : i ∈ S.deg) (hj : j ∈ S.deg), x = a.1 ⊗ₜ i + b.1 ⊗ₜ j := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨a, i, hi, rfl⟩
      exact ⟨a, 0, i, 0, hi, S.zero_mem_deg, by simp⟩
    | zero =>
      refine ⟨0, 0, 0, 0, S.zero_mem_deg, S.zero_mem_deg, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a₁, a₂, i₁, i₂, hi₁, hi₂, eq⟩ := ihx
      obtain ⟨b₁, b₂, j₁, j₂, hj₁, hj₂, eq'⟩ := ihy
      rw [eq, eq']
      sorry
    | smul x hx => sorry
  · sorry

def isRelevant : Prop := ∀ (i : ι), ∃ (n : ℕ), n • i ∈ ι[S.bar]

abbrev setIsRelevant (s : Set A) (hs : ∀ i ∈ s, SetLike.Homogeneous 𝒜 i) : Prop :=
  closure s hs |>.isRelevant

abbrev elemIsRelevant (a : A) (ha : SetLike.Homogeneous 𝒜 a) : Prop :=
  closure {a} (by simpa) |>.isRelevant

variable (𝒜) in
def daggerIdeal : HomogeneousIdeal 𝒜 where
  __ := Ideal.span { x | ∃ (h : SetLike.Homogeneous 𝒜 x), elemIsRelevant x h }
  is_homogeneous' := Ideal.homogeneous_span _ _ (by rintro x ⟨h, _⟩; exact h)

scoped postfix:max "†" => daggerIdeal

end HomogeneousSubmonoid
