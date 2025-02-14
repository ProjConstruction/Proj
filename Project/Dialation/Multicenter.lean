import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.DirectSum.Basic

suppress_compilation

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

def LargeIdeal (i : F.index) : Ideal A := F.ideal i + Ideal.span {F.elem i}

abbrev prodLargeIdealPower (v : F^ℕ) : Ideal A :=
  v.prod fun i k ↦ F.LargeIdeal i ^ k

local prefix:max "𝐋^" => prodLargeIdealPower F

variable {F} in
lemma prod_mem_prodLargeIdealPower_add {v w : F^ℕ} {a b : A} (ha : a ∈ 𝐋^v) (hb : b ∈ 𝐋^w) :
    a * b ∈ 𝐋^(v + w) := by
  classical
  simp? [prodLargeIdealPower] at ha hb ⊢
  rw [Finsupp.prod_add_index]
  pick_goal 2
  · intro a ha
    simp
  pick_goal 2
  · intro a ha m n
    rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

variable [DecidableEq F.index]
abbrev prodElemPower (v : F^ℕ) : A := v.prod fun i k ↦ F.elem i ^ k

local prefix:max "𝐚^" => prodElemPower F

lemma prodElemPow_add (β γ : F^ℕ ) : 𝐚^(β + γ)= 𝐚^β* 𝐚^γ := by
 simp[prodElemPower]
 simp[pow_add, Finset.prod_mul_distrib,
  Finset.prod_subset_one_on_sdiff, Finsupp.prod_add_index]

structure PreDil where
  pow : F^ℕ
  num : A
  num_mem : num ∈ 𝐋^pow

def r : F.PreDil → F.PreDil → Prop := fun x y =>
  ∃ β : F^ℕ, x.num * 𝐚^(β + y.pow) = y.num * 𝐚^(β + x.pow)

variable {F}

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

namespace Dilatation

def mk (x : F.PreDil) : A[F] := Quotient.mk _ x

lemma mk_eq_mk (x y : F.PreDil) : mk x = mk y ↔ F.r x y := by
  erw [Quotient.eq]
  rfl

@[elab_as_elim]
lemma induction_on {C : A[F] → Prop} (x : A[F]) (h : ∀ x : F.PreDil, C (mk x)) : C x := by
  induction x using Quotient.inductionOn with | h a =>
  exact h a

def descFun {B : Type*} (f : F.PreDil → B) (hf : ∀ x y, F.r x y → f x = f y) : A[F] → B :=
  Quotient.lift f hf

def descFun₂ {B : Type*} (f : F.PreDil → F.PreDil → B)
    (hf : ∀ a b x y, F.r a b → F.r x y → f a x = f b y) :
    A[F] → A[F] → B :=
  Quotient.lift₂ f <| fun a x b y ↦ hf a b x y

@[simp]
lemma descFun_mk {B : Type*} (f : F.PreDil → B) (hf : ∀ x y, F.r x y → f x = f y) (x : F.PreDil) :
    descFun f hf (mk x) = f x := rfl

@[simp]
lemma descFun₂_mk_mk {B : Type*} (f : F.PreDil → F.PreDil → B)
    (hf : ∀ a b x y, F.r a b → F.r x y → f a x = f b y) (x y : F.PreDil) :
    descFun₂ f hf (mk x) (mk y) = f x y := rfl

instance : Add A[F] where
  add := Quotient.map₂ sorry sorry

@[simps]
def mul' (x y : F.PreDil) : F.PreDil where
  pow := x.pow + y.pow
  num := x.num * y.num
  num_mem := prod_mem_prodLargeIdealPower_add x.num_mem y.num_mem

instance : Mul A[F] where
  mul := descFun₂ (fun x y ↦ mk <| mul' x y) <| by
    rintro a b x y ⟨α, hα⟩ ⟨β, hβ⟩
    rw [mk_eq_mk]
    use α + β
    simp only [mul'_num, mul'_pow]
    rw [show α + β + (b.pow + y.pow) = (α + b.pow) + (β + y.pow) by abel, prodElemPow_add,
      show a.num * x.num * (𝐚^(α + b.pow) * 𝐚^(β + y.pow)) =
        (a.num * 𝐚^(α + b.pow)) * (x.num * 𝐚^(β + y.pow)) by ring, hα, hβ,
      show b.num * 𝐚^(α + a.pow) * (y.num * 𝐚^(β + x.pow)) =
        b.num * y.num * (𝐚^(α + a.pow) * 𝐚^(β + x.pow)) by ring, ← prodElemPow_add]
    congr 2
    abel

lemma mk_mul_mk (x y : F.PreDil) : mk x * mk y = mk (mul' x y) := rfl

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

end Dilatation

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
