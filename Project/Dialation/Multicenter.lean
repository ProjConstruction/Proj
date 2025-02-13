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

variable {A : Type*} [CommSemiring A] (F : Multicenter A)

scoped notation: max F"^ℕ"  => Multicenter.index F  →₀ ℕ

abbrev powIndex : Type := ⨁ _ : F.index, ℕ

def LargeIdeal (i : F.index) : Ideal A := F.ideal i + Ideal.span {F.elem i}

abbrev prodLargeIdealPower (v : F^ℕ) : Ideal A :=
    ∏ i ∈ v.support, (F.LargeIdeal i)^(v i)

local prefix:max "𝐋^" => prodLargeIdealPower F

variable [DecidableEq F.index]
abbrev prodElemPower (v : F^ℕ) : A := v.prod fun i k ↦ F.elem i ^ k

local prefix:max "𝐚^" => prodElemPower F

structure PreDil where
  pow : F^ℕ
  num : A
  num_mem : num ∈ 𝐋^pow

def r : F.PreDil → F.PreDil → Prop := fun x y =>
  ∃ β : F^ℕ, x.num * 𝐚^(β + y.pow) = y.num * 𝐚^(β + x.pow)

variable {F}

lemma prodElemPow_add (β γ : F^ℕ ) : 𝐚^(β + γ)= 𝐚^β* 𝐚^γ := by
 simp[prodElemPower]
 simp[pow_add, Finset.prod_mul_distrib,
  Finset.prod_subset_one_on_sdiff, Finsupp.prod_add_index]

omit [DecidableEq F.index] in
lemma r_refl (x : F.PreDil) : F.r x x := by simp[r]

omit [DecidableEq F.index] in
lemma r_symm (x y : F.PreDil) : F.r x y → F.r y x := by
  intro h
  rcases h with ⟨β , hβ⟩
  use β
  rw[hβ.symm]

lemma r_trans (x y z : F.PreDil) : F.r x y → F.r y z → F.r x z := by
  intro h g
  rcases h with ⟨β , hβ⟩
  rcases g with ⟨γ , gγ⟩
  have eq' := congr($hβ * 𝐚^(γ+z.pow))
  have eq'' := congr($gγ * 𝐚^(β+x.pow))
  use β+γ+y.pow
  simp only [← prodElemPow_add, ← mul_assoc] at eq' eq'' ⊢
  rw [show β + γ + y.pow + z.pow = (β + y.pow) + (γ + z.pow) by abel,
    prodElemPow_add, ← mul_assoc, hβ, mul_assoc, mul_comm (𝐚^ _), ← mul_assoc, gγ,
    mul_assoc, ← prodElemPow_add]
  congr 2
  abel

def setoid : Setoid (F.PreDil) where
  r := F.r
  iseqv :=
  { refl := r_refl
    symm {x y} := r_symm x y
    trans {x y z} := r_trans x y z }

variable (F) in
def Dilatation := Quotient F.setoid

scoped notation:max A"["F"]" => Dilatation (A := A) F

instance : Add A[F] where
  add := Quotient.map₂ sorry sorry

instance : Mul A[F] where
  mul := Quotient.map₂ sorry sorry

instance : Zero A[F] where
  zero := sorry

instance : One A[F] where
  one := sorry

instance : AddCommMonoid A[F] where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  nsmul := nsmulRec


instance instCommSemiring : CommSemiring A[F] where
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

variable {A : Type*} [CommRing A] (F : Multicenter A) [DecidableEq F.index]

instance : Neg A[F] where
  neg := Quotient.map sorry sorry

instance : CommRing A[F] where
  __ := instCommSemiring
  zsmul := zsmulRec
  neg_add_cancel := sorry

end ring

end Multicenter
