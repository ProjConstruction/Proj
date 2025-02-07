import Mathlib.RingTheory.GradedAlgebra.Basic

variable {ι A B σ τ : Type*}
variable [AddCommMonoid ι] [DecidableEq ι]
variable [CommSemiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable [CommSemiring B] [SetLike τ B] [AddSubmonoidClass τ B] (ℬ : ι → τ) [GradedRing ℬ]

structure GradedRingHom extends RingHom A B where
  map_mem' : ∀ {i : ι} {x : A}, x ∈ 𝒜 i → toFun x ∈ ℬ i

namespace GradedRingHom

scoped[Graded] infix:25 "→+*" => GradedRingHom

open scoped Graded

instance : FunLike (𝒜 →+* ℬ) A B where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hf⟩ eq
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, DFunLike.coe_fn_eq] at eq
    subst eq
    rfl

instance : RingHomClass (𝒜 →+* ℬ) A B where
  map_mul f := f.toRingHom.map_mul
  map_one f := f.toRingHom.map_one
  map_add f := f.toRingHom.map_add
  map_zero f := f.toRingHom.map_zero

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubmonoidClass σ A] [GradedRing 𝒜]
  [AddSubmonoidClass τ B] [GradedRing ℬ] in
variable {𝒜 ℬ} in
lemma map_mem (f : 𝒜 →+* ℬ) {i : ι} {x : A} (hx : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  f.map_mem' hx

variable {𝒜 ℬ} in
omit [AddCommMonoid ι] [DecidableEq ι] [AddSubmonoidClass σ A] [GradedRing 𝒜]
  [AddSubmonoidClass τ B] [GradedRing ℬ] in
lemma map_homogeneous (f : 𝒜 →+* ℬ) {a : A} (hom_a : SetLike.Homogeneous 𝒜 a)  :
    SetLike.Homogeneous ℬ (f a) := by
  obtain ⟨i, hi⟩ := hom_a
  exact ⟨_, f.map_mem hi⟩

end GradedRingHom

structure GradedRingEquiv extends RingEquiv A B where
  map_mem' : ∀ {i : ι} {x : A}, x ∈ 𝒜 i → toFun x ∈ ℬ i
  inv_mem' : ∀ {i : ι} {y : B}, y ∈ ℬ i → invFun y ∈ 𝒜 i

namespace GradedRingEquiv

scoped[Graded] infix:25 "≃+*" => GradedRingEquiv

open scoped Graded

instance : EquivLike (𝒜 ≃+* ℬ) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f a := by simp
  right_inv f a := by simp
  coe_injective' := by
    rintro ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩ eq
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      DFunLike.coe_fn_eq] at eq
    subst eq
    simp

variable {𝒜 ℬ} in
omit [AddCommMonoid ι] [DecidableEq ι] [AddSubmonoidClass σ A]
  [GradedRing 𝒜] [AddSubmonoidClass τ B] [GradedRing ℬ] in
lemma map_mem (f : 𝒜 ≃+* ℬ) {i : ι} {x : A} (hx : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  f.map_mem' hx

variable {𝒜 ℬ} in
omit [AddCommMonoid ι] [DecidableEq ι] [AddSubmonoidClass σ A]
  [GradedRing 𝒜] [AddSubmonoidClass τ B] [GradedRing ℬ] in
lemma inv_mem (f : 𝒜 ≃+* ℬ) {i : ι} {y : B} (hy : y ∈ ℬ i) : f.invFun y ∈ 𝒜 i :=
  f.inv_mem' hy

@[simps]
def toGradedRingHom (f : 𝒜 ≃+* ℬ) : 𝒜 →+* ℬ where
  toFun := f
  map_one' := f.map_one
  map_mul' := f.map_mul
  map_zero' := f.map_zero
  map_add' := f.map_add
  map_mem' := f.map_mem

def refl : 𝒜 ≃+* 𝒜 where
  toRingEquiv := RingEquiv.refl A
  map_mem' := id
  inv_mem' := id

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubmonoidClass σ A] [GradedRing 𝒜] in
lemma refl_toRingEquiv : (refl 𝒜).toRingEquiv = RingEquiv.refl A := rfl

end GradedRingEquiv
