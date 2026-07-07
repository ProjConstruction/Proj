import Mathlib.RingTheory.GradedAlgebra.Basic

open DirectSum

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
lemma map_homogeneous (f : 𝒜 →+* ℬ) {a : A} (hom_a : SetLike.IsHomogeneousElem 𝒜 a)  :
    SetLike.IsHomogeneousElem ℬ (f a) := by
  obtain ⟨i, hi⟩ := hom_a
  exact ⟨_, f.map_mem hi⟩

variable {𝒜 ℬ} in
def asDirectSum (f : 𝒜 →+* ℬ) : (⨁ i, 𝒜 i) →+* (⨁ i, ℬ i) :=
toSemiring (fun i ↦
  { toFun x := of _ i ⟨f x, f.map_mem x.2⟩
    map_zero' := by
      simp only [ZeroMemClass.coe_zero, map_zero]
      ext
      simp only [coe_of_apply, zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero,
        ite_eq_right_iff]
      aesop
    map_add' _ _ := by
      simp only [AddMemClass.coe_add, map_add]
      ext
      simp only [coe_of_apply, add_apply, AddMemClass.coe_add]
      aesop })
  (by
    ext i
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, SetLike.coe_gOne, map_one, coe_of_apply,
      one_def, SetLike.coe_eq_coe]
    rfl)
  (by
    intro i j a b
    ext k
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, SetLike.coe_gMul, map_mul, coe_of_apply,
      of_mul_of, SetLike.coe_eq_coe]
    rfl)

variable {𝒜 ℬ} in
@[simp]
lemma asDirectSum_apply_of (f : 𝒜 →+* ℬ) {i : ι} (x : 𝒜 i) :
    f.asDirectSum (of _ i x) = of _ i ⟨f x, f.map_mem x.2⟩ := by
  delta asDirectSum
  simp only [toSemiring_apply, toAddMonoid_of, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

variable {𝒜 ℬ} in
lemma commutes (f : 𝒜 →+* ℬ) :
    DirectSum.decompose ℬ ∘ f = f.asDirectSum ∘ (DirectSum.decompose 𝒜) := by
  ext x : 1
  induction x using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous j x  =>
    simp only [Function.comp_apply, decompose_coe]
    simp [decompose_of_mem _ (f.map_mem x.2)]
  | add a a' iha iha' =>
    simp only [Function.comp_apply] at iha iha'
    simp only [Function.comp_apply, map_add, decompose_add, iha, iha']

variable {𝒜 ℬ} in
lemma commutes_apply (f : 𝒜 →+* ℬ) (x) :
    DirectSum.decompose ℬ (f x) = f.asDirectSum (DirectSum.decompose 𝒜 x) :=
  congr_fun (commutes f) x

variable {𝒜 ℬ} in
@[simp]
lemma decompose_apply_decompose (f : 𝒜 →+* ℬ) (x) (i) :
    decompose ℬ (f (decompose 𝒜 x i)) =
    of _ i ⟨f (decompose 𝒜 x i), f.map_mem (SetLike.coe_mem _)⟩ := by
  rw [commutes_apply]
  simp only [decompose_coe, asDirectSum_apply_of]

variable {𝒜 ℬ} in
lemma homogeneous_of_apply_homogeneous
      (f : 𝒜 →+* ℬ) {i : ι} {a : A} (hom : f a ∈ ℬ i) :
    ∃ (a' : A), a' ∈ 𝒜 i ∧ f a' = f a := by
  classical
  have eq1 : f a = decompose ℬ (f a) i := by
    simp [decompose_of_mem _ hom, coe_of_apply]
  change f a = decomposeAddEquiv ℬ (f a) i at eq1
  conv_rhs at eq1 => rw [← sum_support_decompose 𝒜 a]
  simp only [map_sum, decomposeAddEquiv_apply, decompose_apply_decompose] at eq1
  rw [DFinsupp.finset_sum_apply] at eq1
  simp only [AddSubmonoidClass.coe_finset_sum, coe_of_apply, apply_ite, ZeroMemClass.coe_zero,
    Finset.sum_ite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not] at eq1

  split_ifs at eq1 with h
  · exact ⟨0, zero_mem _, eq1 ▸ map_zero _⟩
  · exact ⟨decompose 𝒜 a i, SetLike.coe_mem _, eq1.symm⟩


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
