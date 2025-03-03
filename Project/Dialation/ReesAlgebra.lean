import Project.Dialation.Multicenter

import Mathlib.RingTheory.GradedAlgebra.Basic

suppress_compilation

open DirectSum

namespace Multicenter

open Dilatation

section semiring

variable {A : Type*} [CommSemiring A] (F : Multicenter A) [DecidableEq F.index]
abbrev ReesAlgebra := ⨁ (v : F^ℕ), 𝐋^v

def reesAlgebraMul : F.ReesAlgebra →+ (F.ReesAlgebra →+ F.ReesAlgebra) :=
  DirectSum.toAddMonoid fun v ↦
    { toFun x := DirectSum.toAddMonoid fun w ↦
        { toFun y := .of _ (v + w) ⟨x * y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩
          map_zero' := by ext; simp [DirectSum.coe_of_apply]
          map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [mul_add] }
      map_zero' := by ext; simp [DirectSum.coe_of_apply]
      map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [add_mul] }


@[simp]
lemma reesAlgebraMul_of_of (v w : F^ℕ) (x y) :
    F.reesAlgebraMul (.of _ v x) (.of _ w y) =
    .of _ (v + w) ⟨x*y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩ := by
  simp [reesAlgebraMul]


namespace ReesAlgebra

instance : Mul F.ReesAlgebra where
  mul x y := F.reesAlgebraMul x y

lemma mul_def (x y : F.ReesAlgebra) :
  x * y = F.reesAlgebraMul x y := rfl

@[simp]
lemma mul_of_of (v w : F^ℕ) (x y) :
    (DirectSum.of _ v x : F.ReesAlgebra) * (.of _ w y) =
    .of _ (v + w) ⟨x * y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩ := by
  exact reesAlgebraMul_of_of _ _ _ _ _

instance : One F.ReesAlgebra where
  one := .of _ 0 ⟨1, by simp⟩

lemma one_def :
  (1 : F.ReesAlgebra) = .of _ 0 ⟨1, by simp⟩ := rfl

instance : LeftDistribClass F.ReesAlgebra where
  left_distrib := by intros; simp [mul_def]

instance : RightDistribClass F.ReesAlgebra where
  right_distrib := by intros; simp [mul_def]

instance : Semigroup F.ReesAlgebra where
  mul_assoc := by
   intro a b c
   induction  a using DirectSum.induction_on with
   |H_zero => simp [mul_def]
   |H_basic va ma =>
    induction b using DirectSum.induction_on with
     |H_zero => simp [mul_def]
     |H_basic vb mb =>
       induction c using DirectSum.induction_on with
       |H_zero => simp [mul_def]
       |H_basic vc mc =>
        simp only [mul_of_of]
        ext
        simp only [mul_assoc, coe_of_apply, add_assoc]
        split_ifs <;> rfl
       |H_plus x y hx hy =>
        simp only [mul_def, reesAlgebraMul_of_of, map_add] at hx hy ⊢
        rw[← hx,← hy]
     |H_plus x y hx hy =>
      simp only [mul_def, map_add, AddMonoidHom.add_apply] at hx hy ⊢
      rw[← hx,← hy]
   |H_plus x y hx hy =>
    simp only [mul_def, map_add, AddMonoidHom.add_apply] at hx hy ⊢
    rw[← hx,← hy]

instance : MulOneClass F.ReesAlgebra where
  one_mul := by
    intro a
    induction  a using DirectSum.induction_on with
    |H_zero =>
      simp [mul_def, one_def]
    | H_basic i x =>
      rw [one_def, mul_of_of]
      ext
      simp only [one_mul, coe_of_apply, zero_add]
      split_ifs <;> rfl
    | H_plus x y hx hy =>
      rw [mul_add, hx, hy]
  mul_one := by
    intro a
    induction  a using DirectSum.induction_on with
    |H_zero =>
      simp [mul_def, one_def]
    | H_basic i x =>
      rw [one_def, mul_of_of]
      ext
      simp only [mul_one, coe_of_apply, add_zero]
      split_ifs <;> rfl
    | H_plus x y hx hy =>
      rw [add_mul, hx, hy]

instance : Monoid F.ReesAlgebra where
  one_mul := one_mul
  mul_one := mul_one

instance : CommMonoid F.ReesAlgebra where
  mul_comm := by
   intro a b
   induction  a using DirectSum.induction_on with
   |H_zero =>
    simp [mul_def]
   |H_basic va ma =>
    induction b using DirectSum.induction_on with
    |H_zero =>
     simp [mul_def]
    |H_basic vb mb =>
     simp only [mul_of_of]
     ext
     simp only [mul_comm, coe_of_apply, add_comm]
     split_ifs <;> rfl
    |H_plus x y hx hy =>
     rw [mul_add, hx, hy, add_mul]
   |H_plus x y hx hy =>
    rw [mul_add, add_mul, hx, hy]

instance : MonoidWithZero F.ReesAlgebra where
  zero_mul := by
   intro a
   simp [mul_def]
  mul_zero := by
   intro a
   simp [mul_def]

instance : CommSemiring F.ReesAlgebra where
  __ := inferInstanceAs <| AddCommMonoid F.ReesAlgebra
  left_distrib := left_distrib
  right_distrib := right_distrib
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero

@[simps]
def _root_.Multicenter.toReesAlgebra : A →+* F.ReesAlgebra where
  toFun a := .of _ 0 ⟨a, by simp⟩
  map_one' := rfl
  map_mul' a b := by
    ext : 2
    rw [DirectSum.coe_of_apply, mul_of_of, DirectSum.coe_of_apply]
    simp
  map_zero' := by
    ext
    rw [DirectSum.coe_of_apply]
    simp
  map_add' := by
    intro a b
    ext
    simp only [Finsupp.prod_zero_index, add_apply, Submodule.coe_add]
    erw [DirectSum.coe_of_apply, DirectSum.coe_of_apply, DirectSum.coe_of_apply]
    simp only [Finsupp.prod_zero_index]
    split_ifs <;> simp

instance : Algebra A F.ReesAlgebra where
  smul a x := a • x
  algebraMap := F.toReesAlgebra
  commutes' a x := by
    simp only [toReesAlgebra_apply, Finsupp.prod_zero_index, mul_comm]
  smul_def' a x := by
    simp only [toReesAlgebra_apply, Finsupp.prod_zero_index]
    induction x using DirectSum.induction_on with
    |H_zero => simp
    |H_basic i x =>
      erw [mul_of_of]
      ext
      rw [DirectSum.smul_apply]
      simp only [SetLike.val_smul, coe_of_apply, smul_eq_mul, zero_add]
      split_ifs <;> simp
    |H_plus x y hx hy =>
      rw [smul_add, hx, hy, mul_add]

lemma algebraMap_eq : (algebraMap A F.ReesAlgebra) = toReesAlgebra F := rfl

@[simp]
lemma smul_of (a : A) (v : F^ℕ) (x) :
    (a • .of _ v x : F.ReesAlgebra) = .of _ v (a • x) := by
  simp only [Algebra.smul_def, algebraMap_eq, toReesAlgebra_apply, Finsupp.prod_zero_index]
  erw [mul_of_of]
  simp only
  ext
  simp only [coe_of_apply, zero_add]
  split_ifs <;> rfl



@[simps]
def single (v : F^ℕ) : 𝐋^v →ₗ[A] F.ReesAlgebra where
  toFun x := .of _ v x
  map_add' x y := by simp
  map_smul' x y := by
    classical
    simp only [RingHom.id_apply, smul_of]

end ReesAlgebra

end semiring

section ring

variable {A : Type*} [CommRing A] (F : Multicenter A) [DecidableEq F.index]

namespace ReesAlgebra

instance : CommRing F.ReesAlgebra where
  __ := inferInstanceAs <| CommSemiring F.ReesAlgebra
  __ := inferInstanceAs <| AddCommGroup F.ReesAlgebra

def grading (v : F^ℕ) : Submodule A F.ReesAlgebra := LinearMap.range (single F v)

instance : SetLike.GradedOne (grading F) where
  one_mem := by
    simp only [grading, Finsupp.prod_zero_index, LinearMap.mem_range, Subtype.exists,
      Ideal.one_eq_top, Submodule.mem_top, exists_true_left]
    use 1
    simp [one_def, single]

instance : SetLike.GradedMul (grading F) where
  mul_mem := by
    rintro v w _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    simp only [single, LinearMap.coe_mk, AddHom.coe_mk, mul_of_of]
    exact ⟨⟨x * y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩, rfl⟩

instance : SetLike.GradedMonoid (grading F) where

def decompose : F.ReesAlgebra →ₗ[A] ⨁ (v : F^ℕ), grading F v :=
  DirectSum.toModule _ _ _ fun v ↦
  { toFun x := .of _ v ⟨_, ⟨x, rfl⟩⟩
    map_add' x y := by
      simp only [single_apply, map_add]
      ext w w'
      simp only [coe_of_apply, add_apply, Submodule.coe_add]
      split_ifs <;> simp
    map_smul' a x := by
      dsimp
      ext w w'
      rw [coe_of_apply, smul_apply]
      simp only [SetLike.val_smul, SetLike.coe_eq_coe]
      rw [smul_apply, coe_of_apply]
      simp only
      split_ifs
      · dsimp
        ext
        rw [coe_of_apply]
        simp only [SetLike.val_smul, smul_eq_mul]
        rw [coe_of_apply]
        split_ifs <;> simp
      · simp}

@[simp]
lemma decompose_of (v : F^ℕ) (x) :
    decompose F (.of _ v x) = .of _ v ⟨_, ⟨x, rfl⟩⟩ := by
  simp only [decompose, single_apply]
  erw [toModule_lof]
  rfl

@[simp]
lemma decompose_single (v : F^ℕ) (x) :
    decompose F (single F v x) = .of _ v ⟨_, ⟨x, rfl⟩⟩ := decompose_of _ _ _


instance : GradedAlgebra (grading F) where
  decompose' := decompose F
  left_inv x := by
    induction x using DirectSum.induction_on with
    |H_zero =>
      rw [(decompose F).map_zero, (DirectSum.coeAddMonoidHom (grading F)).map_zero]
    |H_basic v x =>
      simp only [decompose_of, single_apply, coeAddMonoidHom_of]
    |H_plus x y hx hy =>
      rw [map_add, (DirectSum.coeAddMonoidHom (grading F)).map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    |H_zero =>
      rw [(DirectSum.coeAddMonoidHom (grading F)).map_zero, (decompose F).map_zero]
    |H_basic v x =>
      rcases x with ⟨_, ⟨x, rfl⟩⟩
      simp
    |H_plus x y hx hy =>
      rw [(DirectSum.coeAddMonoidHom (grading F)).map_add, map_add, hx, hy]

end ReesAlgebra

end ring


end Multicenter
