import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.DirectSum.Basic

open DirectSum

section defs

variable (A : Type*) [CommSemiring A]

structure Multicenter where
  (index : Type)
  (ideal : index → Ideal A)
  (elem : index → A)
  (mem : ∀ i : index, elem i ∈ ideal i)

end defs

namespace Multicenter

section semiring

variable {A : Type*} [CommSemiring A] (M : Multicenter A)

scoped notation:max M"^ℕ" => DirectSum (Multicenter.index M) (fun _ => ℕ)

abbrev powIndex : Type := ⨁ _ : M.index, ℕ

def shiftedIdeal (i : M.index) : Ideal A := M.ideal i + Ideal.span {M.elem i}

abbrev sumShiftedIdealPower (v : M^ℕ) : Ideal A :=
    ⨆ i : M.index, (M.shiftedIdeal i)^(v i)

local prefix:max "𝐋^" => sumShiftedIdealPower M

variable [DecidableEq M.index]
abbrev sumElemPower (v : M^ℕ) : A := ∏ i ∈ v.support, M.elem i ^ v i

local prefix:max "𝐚^" => sumElemPower M

structure PreDialation where
  pow : M^ℕ
  num : A
  num_mem : num ∈ 𝐋^pow

def r : M.PreDialation → M.PreDialation → Prop := fun x y =>
  ∃ β : M^ℕ, x.num * 𝐚^(β + y.pow) = y.num * 𝐚^(β + x.pow)

variable {M}

lemma r_refl (x : M.PreDialation) : M.r x x := by sorry

lemma r_symm (x y : M.PreDialation) : M.r x y → M.r y x := by sorry

lemma r_trans (x y z : M.PreDialation) : M.r x y → M.r y z → M.r x z := by sorry

def setoid : Setoid (M.PreDialation) where
  r := M.r
  iseqv :=
  { refl := r_refl
    symm {x y} := r_symm x y
    trans {x y z} := r_trans x y z }

variable (M) in
def Dialation := Quotient M.setoid

scoped notation:max A"["M"]" => Dialation (A := A) M

instance : Add A[M] where
  add := Quotient.map₂ sorry sorry

instance : Mul A[M] where
  mul := Quotient.map₂ sorry sorry

instance : Zero A[M] where
  zero := sorry

instance : One A[M] where
  one := sorry

instance : AddCommMonoid A[M] where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  nsmul := nsmulRec


instance instCommSemiring : CommSemiring A[M] where
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry

end semiring

section ring

variable {A : Type*} [CommRing A] (M : Multicenter A) [DecidableEq M.index]

instance : Neg A[M] where
  neg := Quotient.map sorry sorry

instance : CommRing A[M] where
  __ := instCommSemiring
  zsmul := zsmulRec
  neg_add_cancel := sorry

end ring

end Multicenter
