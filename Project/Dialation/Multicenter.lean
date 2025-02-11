import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.DirectSum.Basic

open DirectSum

variable (A : Type*) [CommSemiring A]

structure Multicenter where
  (index : Type)
  (ideal : index → Ideal A)
  (elem : index → A)
  (mem : ∀ i : index, elem i ∈ ideal i)

namespace Multicenter

variable {A}
variable (M : Multicenter A)

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

def dialation := Quotient M.setoid

end Multicenter
