import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal

import Project.GR.Basic

open DirectSum TensorProduct

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

def monDeg [AddCommGroup ι] : AddSubmonoid ι := AddSubmonoid.closure S.deg

scoped notation:max ι"["S"⟩" => monDeg (ι := ι) S

def agrDeg [AddCommGroup ι] : AddSubgroup ι := AddSubgroup.closure ι[ S ⟩

scoped notation:max ι"["S"]" => agrDeg (ι := ι) S

noncomputable def genDegAGREquiv : ι[S⟩ᵃᵍʳ ≃+ ι[S] := AddGR.equivAsAddSubgroup ..

def convMonDeg := ι[S⟩ ⊗[ℕ] ℝ

scoped notation ι"["S"⟩≥0" => convMonDeg (ι := ι) S

def isRelevant : Prop := ∀ (i : ι), ∃ (n : ℕ), n • i ∈ ι[S.bar]

abbrev setIsRelevant (s : Set A) (hs : ∀ i ∈ s, SetLike.Homogeneous 𝒜 i) : Prop :=
  closure s hs |>.isRelevant

abbrev elemIsRelevant (a : A) (ha : SetLike.Homogeneous 𝒜 a) : Prop :=
  closure {a} (by simpa) |>.isRelevant

variable (𝒜) in
def daggerIdeal : Ideal A :=
  Ideal.span { x | ∃ (h : SetLike.Homogeneous 𝒜 x), elemIsRelevant x h }

scoped postfix:max "†" => daggerIdeal

end HomogeneousSubmonoid
