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

lemma elem_mem_LargeIdeal (i: F.index) : F.elem i ∈ F.LargeIdeal i := by
  suffices inequality : Ideal.span {F.elem i} ≤ F.LargeIdeal i by
   apply inequality
   exact Ideal.mem_span_singleton_self (F.elem i)
  simp only [LargeIdeal, Submodule.add_eq_sup, le_sup_right]

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

 omit [DecidableEq F.index] in

lemma prodElemPow_mem (v :F^ℕ) : 𝐚^v ∈ 𝐋^v := by
  apply Ideal.prod_mem_prod
  intro i hi
  simp only
  apply Ideal.pow_mem_pow
  exact elem_mem_LargeIdeal F i


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

@[simps]
def add' (x y : F.PreDil) : F.PreDil where
 pow := x.pow + y.pow
 num := 𝐚^y.pow * x.num + 𝐚^x.pow * y.num
 num_mem := Ideal.add_mem _ (by
  rw[add_comm]
  exact prod_mem_prodLargeIdealPower_add (prodElemPow_mem F y.pow) x.num_mem) (prod_mem_prodLargeIdealPower_add (prodElemPow_mem F x.pow) y.num_mem)

instance : Add A[F] where
  add := descFun₂ (fun x y ↦ mk ( add' x y))  <| by
   rintro x y x' y' ⟨α, hα⟩ ⟨β, hβ⟩
   have eq := congr($hβ * 𝐚^(α+ β))
   have eq' := congr($hα * 𝐚^(α+β))
   --have eq'': LHS of eq + LHS of eq'= RHS of eq + RHS of eq':= by rw [eq, eq']
   simp only
   rw [mk_eq_mk]
   use α + β
   -- apply eq'' + distrib tricks
   ring
   abel
   sorry

lemma mk_add_mk (x y : F.PreDil) : mk x + mk y = mk (add' x y) := rfl

@[simps]
def mul' (x y : F.PreDil) : F.PreDil where
  pow := x.pow + y.pow
  num := x.num * y.num
  num_mem := prod_mem_prodLargeIdealPower_add x.num_mem y.num_mem

lemma dist' (x y z : F.PreDil) : F.r (mul' x (add' y z))
                                (add' (mul' x y) (mul' x z))  := by
  use 0
  simp [mul'_num, add'_num, add'_pow, mul'_pow, zero_add]
  rw [ prodElemPow_add,  mul_assoc, mul_comm (𝐚^ _), ← mul_assoc,
    mul_assoc, ← prodElemPow_add,  prodElemPow_add]
  ring
  -- MORE RING DISTRIB TRICKS REQUIRED
  sorry

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
  zero := mk {
    pow := 0
    num := 0
    num_mem := by exact Submodule.zero_mem (F.prodLargeIdealPower 0)
  }

lemma zero_def :  (0 :A[F]) =  (mk {
    pow := 0
    num := 0
    num_mem := by simp only [Finsupp.prod_zero_index, Ideal.one_eq_top, Submodule.zero_mem]
  } :A[F]):= rfl

instance : One A[F] where
  one := mk {
    pow := 0
    num := 1
    num_mem := by exact Submodule.one_le.mp fun ⦃x⦄ a ↦ a
  }

  lemma one_def :  (1 :A[F]) =  (mk {
    pow := 0
    num := 1
    num_mem := by simp only [Finsupp.prod_zero_index, Ideal.one_eq_top,
    Submodule.mem_top]
  } :A[F]):= rfl

instance : AddCommMonoid A[F] where
  add_assoc := by
   intro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    rw[mk_add_mk]
    rw[mk_add_mk]
    rw[mk_add_mk]
    rw[mk_add_mk]
    rw[mk_eq_mk]
    use 0
    simp[prodElemPow_add]
    ring



  zero_add := by
   intro a
   induction a using induction_on with |h x=>
    rw[zero_def]
    rw[mk_add_mk]
    rw[mk_eq_mk]
    use 0
    simp[prodElemPow_add]
  add_zero := by
   intro a
   induction a using induction_on with |h x=>
    rw[zero_def]
    rw[mk_add_mk]
    rw[mk_eq_mk]
    use 0
    simp[prodElemPow_add]
  add_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    rw[mk_add_mk]
    rw[mk_add_mk]
    rw[mk_eq_mk]
    use 0
    simp[prodElemPow_add]
    ring
  nsmul := nsmulRec


instance instCommSemiring : CommSemiring A[F] where
  left_distrib := by
   rintro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    rw[mk_add_mk]
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_add_mk]
    rw[mk_eq_mk]
    simp[dist']
  right_distrib := by
   rintro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    rw[mk_add_mk]
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_add_mk]
    rw[mk_eq_mk]
    -- SMALL COMMUTATIVITY TRICK REQUIRED
    simp[dist']
    sorry
  zero_mul := by
   rintro a
   induction a using induction_on with |h x =>
    rw[zero_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp only [mul'_num, zero_mul, add_zero, Finsupp.prod_zero_index, mul_one, mul'_pow, zero_add]

  mul_zero := by
   rintro a
   induction a using induction_on with |h x =>
    rw[zero_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp only [mul'_num, mul_zero, add_zero, Finsupp.prod_zero_index, mul_one, mul'_pow, zero_add,
      zero_mul]

  mul_assoc := by
   intro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp only [mul'_num, mul'_pow, zero_add]
    -- SMALL DISTRIB TRICK REQUIRED
    sorry
  one_mul := by
   intro a
   induction a using induction_on with |h x =>
    rw[one_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp only [mul'_num, one_mul, zero_add, mul'_pow]

  mul_one := by
   intro a
   induction a using induction_on with |h x =>
    rw[one_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp only [mul'_num, mul_one, zero_add, mul'_pow, add_zero]


  --HEART TRICK required
  set_option synthInstance.maxHeartbeats 500000 in
  set_option maxHeartbeats 2000000 in
  mul_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp?
    sorry
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
