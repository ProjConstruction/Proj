import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Project.Dialation.lemma
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Basic
suppress_compilation

open DirectSum

section defs

variable (A : Type*) [CommSemiring A]

structure Multicenter where
  (index : Type*)
  (ideal : index → Ideal A)
  (elem : index → A)
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

scoped prefix:max "𝐋^" => prodLargeIdealPower _

scoped notation:max "𝐋^["F"]" => prodLargeIdealPower F


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

abbrev prodElemPower (v : F^ℕ) : A := v.prod fun i k ↦ F.elem i ^ k

scoped prefix:max "𝐚^" => prodElemPower _

scoped notation:max "𝐚^["F"]" => prodElemPower F

lemma prodElemPow_add (β γ : F^ℕ ) : 𝐚^(β + γ)= 𝐚^β* 𝐚^γ := by
  classical
 simp[prodElemPower]
 simp[pow_add, Finset.prod_mul_distrib,
  Finset.prod_subset_one_on_sdiff, Finsupp.prod_add_index]

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

lemma r_refl (x : F.PreDil) : F.r x x := by simp[r]

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

scoped notation:max ring"["multicenter"]" => Dilatation (A := ring) multicenter
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
  add := descFun₂ (fun x y ↦ mk (add' x y))  <| by
   rintro x y x' y' ⟨α, hα⟩ ⟨β, hβ⟩
   have eq := congr($hβ * 𝐚^(x.pow + y.pow + α))
   have eq' := congr($hα * 𝐚^(x'.pow + y'.pow + β))
   have eq'' := congr($eq + $eq')
   simp only
   rw [mk_eq_mk]
   use α + β
   simp only [mul_assoc, ← prodElemPow_add] at eq''
   simp only [add'_num, add'_pow, add_mul]
   rw [mul_comm _ x.num, mul_comm _ x'.num, mul_assoc, ← prodElemPow_add,
    mul_assoc, ← prodElemPow_add]
   rw [mul_comm _ y.num, mul_comm _ y'.num, mul_assoc, ← prodElemPow_add,
    mul_assoc, ← prodElemPow_add]
   convert eq'' using 1 <;>
   · rw [add_comm]
     congr 3 <;> abel

lemma mk_add_mk (x y : F.PreDil) : mk x + mk y = mk (add' x y) := rfl

@[simps]
def mul' (x y : F.PreDil) : F.PreDil where
  pow := x.pow + y.pow
  num := x.num * y.num
  num_mem := prod_mem_prodLargeIdealPower_add x.num_mem y.num_mem

lemma dist' (x y z : F.PreDil) : F.r (mul' x (add' y z))
                                (add' (mul' x y) (mul' x z))  := by
  use 0
  simp [prodElemPow_add]
  ring

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

instance monoid : Monoid A[F] where
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
    simp [prodElemPow_add]
    ring
  one_mul := by
   intro a
   induction a using induction_on with |h x =>
    rw[one_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp [prodElemPow_add]
  mul_one := by
   intro a
   induction a using induction_on with |h x =>
    rw[one_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp [prodElemPow_add]

instance instCommSemiring : CommSemiring A[F] where
  __ := monoid
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
    use 0
    simp [prodElemPow_add]
    ring
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
    use 0
    simp [prodElemPow_add]
    ring
  zero_mul := by
   rintro a
   induction a using induction_on with |h x =>
    rw[zero_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp [prodElemPow_add]
  mul_zero := by
   rintro a
   induction a using induction_on with |h x =>
    rw[zero_def]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp [prodElemPow_add]
  mul_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    rw[mk_mul_mk]
    rw[mk_mul_mk]
    rw[mk_eq_mk]
    use 0
    simp [prodElemPow_add]
    ring

variable (F) in
@[simps]
def fromBaseRing : A →+* A[F] where
  toFun x := .mk
        { pow := 0
          num := x
          num_mem := by simp }
  map_one' := by simp [one_def]
  map_mul' _ _ := by simp only [mk_mul_mk, mk_eq_mk]; use 0; simp
  map_zero' := by simp [zero_def]
  map_add' _ _ := by simp [mk_add_mk, mk_eq_mk]; use 0; simp

instance : Algebra A A[F] := RingHom.toAlgebra (fromBaseRing F)

lemma algebraMap_eq : (algebraMap A A[F]) = fromBaseRing F := rfl

lemma algebraMap_apply (x : A) : algebraMap A A[F] x = mk {
  pow := 0
  num := x
  num_mem := by simp
} := rfl

lemma smul_mk (x : A) (y : F.PreDil) : x • mk y = mk {
    pow := y.pow
    num := x * y.num
    num_mem := Ideal.mul_mem_left _ _ y.num_mem } := by
  simp only [Algebra.smul_def, algebraMap_apply, mk_mul_mk, mk_eq_mk]
  use 0
  simp

abbrev frac (ν : F^ℕ)  (m: 𝐋^ν) : A[F]:=
  mk {
    pow := ν
    num := m
    num_mem := by simp
    }

scoped notation:max m"/.[" F"]"ν => frac (F := F) ν m

scoped notation:max m"/."ν => frac ν m

lemma frac_add_frac (v w : F^ℕ) (m : 𝐋^v) (n : 𝐋^w) :
    (m/.v) + (n/.w) =
    (⟨m * 𝐚^w + n * 𝐚^v, Ideal.add_mem _
      (prod_mem_prodLargeIdealPower_add m.2 (prodElemPow_mem F w))
      (add_comm v w ▸ prod_mem_prodLargeIdealPower_add n.2 (prodElemPow_mem F v))⟩)/.(v + w) := by
  simp only [frac, mk_add_mk, mk_eq_mk]
  use 0
  simp only [add'_num, zero_add, prodElemPow_add, add'_pow]
  ring

lemma frac_mul_frac (v w : F^ℕ) (m : 𝐋^v) (n : 𝐋^w) :
    (m/.v) * (n/.w) =
    (⟨m * n, prod_mem_prodLargeIdealPower_add m.2 n.2⟩)/.(v + w) := by
  simp only [frac, mk_mul_mk, mk_eq_mk]
  use 0
  simp

lemma smul_frac (a : A) (v : F^ℕ) (m : 𝐋^v) : a • (m/.v) = (a • m)/.v := by
  simp only [frac, smul_mk, mk_eq_mk]
  use 0
  simp


lemma nonzerodiv_image (v :F^ℕ) :
   algebraMap A A[F] 𝐚^v ∈ nonZeroDivisors A[F] := by
    intro x h
    induction x using induction_on with |h x =>
    rw[algebraMap_apply] at h
    rw[mk_mul_mk] at h
    rw[zero_def]  at h
    rw[mk_eq_mk] at h
    rcases h with ⟨ α, hα ⟩
    simp at hα
    rw[zero_def]
    rw[mk_eq_mk]
    use v +α
    simp [prodElemPow_add, ← mul_assoc, hα]




lemma image_elem_LargeIdeal_equal  (v : F^ℕ) :
 Ideal.span ({algebraMap A A[F] (𝐚^v)}) =
    Ideal.map (algebraMap A A[F]) (𝐋^v):= by
    refine le_antisymm ?_  ?_
    · rw [Ideal.span_le]
      simp
      apply  Ideal.mem_map_of_mem
      exact prodElemPow_mem F v
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have eq: algebraMap A A[F] x =
       algebraMap A A[F] 𝐚^v * ⟨ x , hx⟩  /.v := by
       simp  [algebraMap_apply, frac, mk_mul_mk, mk_eq_mk]
       use 0
       simp [mul_comm]
      simp only [Ideal.mem_comap]
      rw [eq]
      apply Ideal.mul_mem_right
      apply Ideal.subset_span
      simp only [Set.mem_singleton_iff]



end Dilatation

end semiring

section ring

namespace Dilatation

variable {A : Type*} [CommRing A] {F : Multicenter A}

@[simps]
def neg' (x : F.PreDil) : F.PreDil where
  pow := x.pow
  num := -x.num
  num_mem := neg_mem x.num_mem

instance : Neg A[F] where
  neg := descFun (mk ∘ neg') <| by
    rintro x y ⟨α, hα⟩
    simp only [Function.comp_apply, mk_eq_mk]
    use α
    simp [hα]

lemma mk_neg (x : F.PreDil) : -mk x = mk (neg' x) := rfl

instance : CommRing A[F] where
  __ := instCommSemiring
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    induction a using induction_on with |h x =>
    simp only [mk_neg, mk_add_mk, zero_def, mk_eq_mk]
    use 0
    simp

lemma neg_frac (v : F^ℕ) (m : 𝐋^v) : -(m/.v) = (-m)/.v := by
  simp only [frac, mk_neg, mk_eq_mk]
  use 0
  simp

end Dilatation

end ring

section universal_property

variable {A B : Type*} [CommRing A] [CommRing B] (F : Multicenter A)


lemma  cond_univ_implies_large_cond [Algebra A B]
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)):
    (∀ (ν : F^ℕ) , (Ideal.span {(algebraMap A B) (𝐚^ν)} = Ideal.map (algebraMap A B) (𝐋^ν))) :=by
     classical
     intro v
     simp[prodLargeIdealPower]
     simp [prodElemPower]
     simp only [Finsupp.prod, map_prod, map_pow]
     rw[Ideal.prod_span']
     simp[← Ideal.span_singleton_pow, gen]
     simp[Ideal.prod_map, Ideal.map_pow]


lemma equ_trivial_image_divisor_ring  [Algebra A B]  :
 ∀ i, Ideal.map (algebraMap A B) (Ideal.span {F.elem i})=
      Ideal.span {(algebraMap A B) (F.elem i)} := by
      intro i
      rw [Ideal.map_span, Set.image_singleton]



lemma equiv_small_big_cond [Algebra A B]  :
( ∀ i, Ideal.map (algebraMap A B) (Ideal.span {F.elem i}) = Ideal.map (algebraMap A B) (F.LargeIdeal i)) ↔
( ∀ i, Ideal.map (algebraMap A B) (Ideal.span {F.elem i}) ≥  Ideal.map (algebraMap A B) (F.ideal i)) := by
  constructor
  · intro h i
    have eq1 : (F.LargeIdeal i) ≥ (F.ideal i)  := by
      simp [LargeIdeal]
    have eq2 : Ideal.map (algebraMap A B) (F.LargeIdeal i) ≥
               Ideal.map (algebraMap A B) (F.ideal i) := by
                simp[Ideal.map_mono, eq1]
    simp[eq2, h]

  · intro h i
    have eq1: Ideal.map (algebraMap A B) (F.LargeIdeal i)=
               Ideal.map (algebraMap A B) (F.ideal i)+
               Ideal.map (algebraMap A B) (Ideal.span {F.elem i}):= by
               simp[LargeIdeal]
               rw [Ideal.map_sup]
    have eq2: Ideal.map (algebraMap A B) (Ideal.span {F.elem i})
             ≥  Ideal.map (algebraMap A B) (F.LargeIdeal i) := by
             simp[eq1, h]
    have eq3: Ideal.map (algebraMap A B) (Ideal.span {F.elem i})
             ≤   Ideal.map (algebraMap A B) (F.LargeIdeal i) := by
             simp[LargeIdeal, eq1, Ideal.map_sup]
    have eq4: Ideal.map (algebraMap A B) (Ideal.span {F.elem i})
             = Ideal.map (algebraMap A B) (F.LargeIdeal i) := by
             exact LE.le.antisymm' eq2 eq3
    exact eq4

lemma  lemma_exists_in_image [Algebra A B]
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)):
    (∀(ν : F^ℕ) (m : 𝐋^ν) ,  (∃! bm : B ,  (algebraMap A B) 𝐚^ν *bm=(algebraMap A B) (m) )):= by
      intro v m
      have mem : (algebraMap A B) m ∈  Ideal.map (algebraMap A B) (𝐋^v) := by
          apply Ideal.mem_map_of_mem
          exact m.2
      rw[← cond_univ_implies_large_cond] at mem
      rw[Ideal.mem_span_singleton'] at mem
      rcases mem with ⟨bm, eq_bm⟩
      use bm
      rw[mul_comm] at eq_bm
      use eq_bm
      intro bm' eq
      rw[← eq_bm] at eq
      rw[mul_cancel_left_mem_nonZeroDivisors] at eq
      · exact eq
      · simp[prodElemPower, Finsupp.prod]
        apply prod_mem
        intro i hi
        apply pow_mem
        apply non_zero_divisor
      · exact gen



def def_unique_elem [Algebra A B] (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)): B :=
     (lemma_exists_in_image  F  non_zero_divisor gen v m).choose

lemma def_unique_elem_spec [Algebra A B] (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)):
    (algebraMap A B) 𝐚^v * def_unique_elem F v m non_zero_divisor gen = (algebraMap A B) m := by
    apply (lemma_exists_in_image F non_zero_divisor gen v m).choose_spec.1

lemma def_unique_elem_unique  [Algebra A B] (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)):
    ∀ bm : B, (algebraMap A B) 𝐚^v * bm = (algebraMap A B) m →  def_unique_elem F v m non_zero_divisor gen =bm:= by
    intro bm hbm
    apply ((lemma_exists_in_image F  non_zero_divisor gen v m).choose_spec.2 bm hbm).symm



def desc [Algebra A B]
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)) :
     A[F] →ₐ[A] B where
  toFun := Dilatation.descFun (fun x ↦ def_unique_elem F  x.pow ⟨ x.num, x.num_mem⟩  non_zero_divisor gen )
                            ( by
                              intro x y h
                              rcases h with ⟨β, hβ⟩
                              simp only
                              apply def_unique_elem_unique
                              apply_fun (fun z => (algebraMap A B) (𝐚^ (β + y.pow)) * z)
                              · simp only [mul_assoc, hβ]
                                rw[← map_mul, mul_comm _ x.num]
                                rw [hβ]
                                simp only [map_mul]
                                rw[← def_unique_elem_spec F y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
                                simp only [prodElemPow_add, map_mul]
                                ring
                              · intro x y hx
                                simp only at hx
                                rwa [mul_cancel_left_mem_nonZeroDivisors] at hx
                                simp only [prodElemPower, Finsupp.prod, Finsupp.coe_add,
                                  Pi.add_apply, map_prod, map_pow]
                                apply prod_mem
                                intro i hi
                                apply pow_mem
                                apply non_zero_divisor)
  map_one' := by
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply def_unique_elem_unique
    simp
  map_mul' := by
    intro x y
    induction x using Dilatation.induction_on with |h x =>
    induction y using Dilatation.induction_on with |h y =>
    simp only [Dilatation.descFun₂_mk_mk, Dilatation.mk_mul_mk]
    apply def_unique_elem_unique
    · exact non_zero_divisor
    · exact gen
    · simp
      rw[← def_unique_elem_spec F  y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw[← def_unique_elem_spec F x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp [prodElemPow_add]
      ring
  map_zero' := by
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply def_unique_elem_unique
    simp
  map_add' :=  by
    intro x y
    induction x using Dilatation.induction_on with |h x =>
    induction y using Dilatation.induction_on with |h y =>
    simp only [Dilatation.descFun₂_mk_mk, Dilatation.mk_mul_mk]
    apply def_unique_elem_unique
    · exact non_zero_divisor
    · exact gen
    · simp
      rw[← def_unique_elem_spec F  y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw[← def_unique_elem_spec F x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp [prodElemPow_add]
      ring
  commutes' := by
    intro x
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply def_unique_elem_unique
    simp



open Multicenter
open Dilatation
lemma dsc_spec [Algebra A B] (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i)):
    (algebraMap A B) 𝐚^v * desc F non_zero_divisor gen (m/.v)  = (algebraMap A B) m := by
    apply (lemma_exists_in_image F non_zero_divisor gen v m).choose_spec.1


lemma  lemma_exists_unique_morphism [Algebra A B]
    (non_zero_divisor : ∀ i : F.index, (algebraMap A B) (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)} = Ideal.map (algebraMap A B) (F.LargeIdeal i))
    (χ':A[F]→ₐ[A] B)  : χ' = desc F non_zero_divisor gen := by
      ext x
      induction x using induction_on with |h x =>
      have eq1 : ((algebraMap A B) 𝐚^x.pow) *(χ' ⟨x.num, x.num_mem⟩/.x.pow) =
       (χ' (algebraMap A A[F] 𝐚^x.pow)) *(χ' ⟨x.num, x.num_mem⟩/.x.pow) := by rw[AlgHom.commutes]
      have eq2 : ((algebraMap A B) 𝐚^x.pow) *(χ' ⟨x.num, x.num_mem⟩/.x.pow) =
       ((algebraMap A B) x.num) := by
         rw[eq1, ← map_mul]
         simp only [algebraMap_apply, mk_mul_mk, mul']
         rw[← AlgHom.commutes (χ' : A[F] →ₐ[A] B)]
         congr 1
         simp[algebraMap_apply]
         simp[mk_eq_mk]
         use 0
         simp
         simp[mul_comm]
      have eq3:  def_unique_elem F  x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen =
         (χ' ⟨x.num, x.num_mem⟩/.x.pow) := by
          apply def_unique_elem_unique
          exact eq2
      rw[← eq3]
      rfl

open Dilatation
open Multicenter
lemma reciprocal_for_univ [Algebra A B] (F : Multicenter A)
   (χ':A[F] →ₐ[A] B) : ∀ i, Ideal.span {(algebraMap A B) (F.elem i)}
         = Ideal.map (algebraMap A B) (F.LargeIdeal i):= by
          intro i
          let v : F^ℕ := Finsupp.single i 1
          have eq1:  Ideal.span {(algebraMap A A[F]) (𝐚^v)}
             = Ideal.map (algebraMap A A[F]) (𝐋^v):= by
             rw [image_elem_LargeIdeal_equal v]
          have eq2: 𝐚^v = F.elem i := by
            rw [prodElemPower]
            rw [Finsupp.prod_single_index]
            ring
            ring
          have eq3 : 𝐋^v = F.LargeIdeal i := by
              rw[prodLargeIdealPower]
              rw [Finsupp.prod_single_index]
              ring
              ring
          have eq4: Ideal.span {(algebraMap A A[F]) (F.elem i)}
             = Ideal.map (algebraMap A A[F]) (F.LargeIdeal i):= by
                   have eq41: Ideal.span {(algebraMap A A[F]) (F.elem i)}=
                      Ideal.span {(algebraMap A A[F]) (𝐚^v)} := by
                      rw[eq2]
                   have eq42: Ideal.map (algebraMap A A[F]) (F.LargeIdeal i)=
                      Ideal.map (algebraMap A A[F]) (𝐋^v) := by
                      rw[eq3]
                   rw[eq41, eq42, eq1]
          have eqA:  Ideal.map (algebraMap A B) (Ideal.span {F.elem i})
           = Ideal.map (algebraMap A B) (F.LargeIdeal i) := by
               have eq6: Ideal.map (algebraMap A A[F]) (Ideal.span {(F.elem i)})
                       = Ideal.span {(algebraMap A A[F]) (F.elem i)} := by
                  rw [equ_trivial_image_divisor_ring  ]
               have eq7: Ideal.map (algebraMap A A[F]) (Ideal.span {(F.elem i)})
                        =Ideal.map (algebraMap A A[F]) (F.LargeIdeal i) := by
                        rw[ eq6, ← eq4]
               have eq8: Ideal.map (χ'.toRingHom)
                          (Ideal.map (algebraMap A A[F]) (Ideal.span {(F.elem i)}))
                        =Ideal.map (χ'.toRingHom )
                          (Ideal.map (algebraMap A A[F]) (F.LargeIdeal i)) := by
                          rw[eq7]
               have eqcomp: (algebraMap A B) = (RingHom.comp χ'.toRingHom (algebraMap A A[F])) := by
                  simp
               have eq9: Ideal.map (algebraMap A B) (Ideal.span {F.elem i})
                        =Ideal.map (algebraMap A B) (F.LargeIdeal i) := by
                        rw [Ideal.map_map (algebraMap A A[F]) χ'.toRingHom] at eq8
                        rw [Ideal.map_map (algebraMap A A[F]) χ'.toRingHom] at eq8
                        simp[Function.comp_apply, Function.comp_apply] at eq8
                        exact eq8
               exact eq9

          have eqB: Ideal.map (algebraMap A B) (Ideal.span {F.elem i})=
            Ideal.span {(algebraMap A B) (F.elem i)}:= by
                rw [equ_trivial_image_divisor_ring  ]

          rw[←eqB, eqA]






open Multicenter
open Dilatation

open Multicenter
open Dilatation



/--/
def cat_dil_test_reg (F: Multicenter A) fullsubcategory of Cat A-alg ,
 Objects := {f:A→+* B |  f (F.elem i) ∈ nonZeroDivisors B }  := by
 sorry


lemma dil_representable_functor (F: Multicenter A) :
    A[F] represents the functor cat_dil_test_reg A F → Set,
    f ↦ singleton if ∀ i, Ideal.span {f (F.elem i)} ⊇  f (F.LargeIdeal i)
             emptyset else := by
     sorry
-/


@[simps]
def image_mult [Algebra A B] :  Multicenter B :=
  {index  :=F.index
   ideal  :=(fun i ↦ Ideal.map (algebraMap A B) (F.ideal i))
   elem := (fun i ↦ (algebraMap A B) (F.elem i))}


/-
lemma image_mult_LargeIdeal [Algebra A B] (i : F.index):
  (image_mult (B:=B) F ).LargeIdeal i = Ideal.map (algebraMap A B) (F.LargeIdeal i) := by
   simp [LargeIdeal]
   rw[Ideal.map_sup]
   rw[Ideal.map_span]
   simp

instance [Algebra A B] (G : Multicenter B) : Algebra A B[G] :=
  RingHom.toAlgebra (RingHom.comp (algebraMap B B[G]) (algebraMap A B))


def functo_dila_alg [Algebra A B]: A[F] →ₐ[A]  B[image_mult (B := B) F]  :=
  desc F
    (by
     classical
     intro i
     have h := nonzerodiv_image (F := image_mult (B := B) F ) (Finsupp.single i 1)
     simp at h
     exact h
     )
    (by
     classical
     intro i
     let v : F^ℕ := Finsupp.single i 1
     have h := image_elem_LargeIdeal_equal (F := image_mult (B := B[image_mult (B := B) F]) (image_mult (B := B) F) ) v
     simp only at h
     have eq2: 𝐚^v = F.elem i := by
            rw [prodElemPower]
            rw [Finsupp.prod_single_index]
            ring
            ring
     have eq3 : 𝐋^v = F.LargeIdeal i := by
              rw[prodLargeIdealPower]
              rw [Finsupp.prod_single_index]
              ring
              ring


     sorry
      )

lemma unique_functorial_morphism_dilatation [Algebra A B]
 (other:A[F]→ₐ[A] B[image_mult (B := B) F]) :
   other= desc F (algebraMap A B[image_mult (B := B) F])  :=by

      sorry


open Multicenter
open Dilatation
scoped notation: max A"["F".loc]" =>
   Localization (Submonoid.closure (Set.range (fun j => (F.elem j : A))))

instance (F : Multicenter A) : Algebra A A[F.loc] :=
  (algebraMap A Localization (Submonoid.closure (Set.range (fun j => (F.elem j : A)))))

def dil_to_localise_mor_alg (F: Multicenter A) :
  A[F] →ₐ[A] A[F.loc]  :=
   desc F (algebraMap A A[F.loc])
       (by
        sorry)
       (by
        sorry)


lemma dil_to_localise_mor_alg_unique (F: Multicenter A):
  (other: A[F] →ₐ[A] Localization
  (Submonoid.closure (Set.range (fun j => (F.elem j : A))))) :
   other = desc_alg_small F (algebraMap A
           Localization (Submonoid.closure
           (Set.range (fun j => (F.elem j : A))))) := by
            sorry

--can we introduce a notation for
  --Localization  (Submonoid.closure (Set.range (fun j => (F.elem j : A))))
    -- for example A[F.elem^-1] would be very useful

lemma dil_to_localise_mor_is_injective (F: Multicenter A) :
  A[F] →ₐ[A] A[F.loc] is injective:= by
  sorry

lemma im_dil_is_subalgebra_in_loc (F: Multicenter A) :
 im( A[F] →ₐ[A] A[F.elem^-1])=
   subAalgebra of A[F.elem^-1] generated by {frac{F.ideal i}{F.elem i}: i ∈ F.index}
        :=
    by double inclusion
    sorry

lemma dil_isom_subalgebra_in_loc (F: Multicenter A) :
 iso A[F] →ₐ[A] subAalgebra of A[F.elem^-1] generated by {frac{F.ideal i}{F.elem i}: i ∈ F.index} :=
    by dil_to_localise_mor_is_injective and im_dil_is_subalgebra_in_loc
    sorry


lemma dil_eq_loc_if_maxLarge (F: Multicenter A) (F.LargeIdeal i = A):
   A[F] →ₐ[A] A[F.loc] is an isomorphism:= by
    it is enough to prove that it is surjective which is easy
    sorry

def  comprimed_center (F : Multicenter A) (F.index is finite) : Multicenter A :=
  { index := singleton
    ideal :=  ∑ (i : F.index) ,
               F.LargeIdeal i * ∏ (j : (Finset.univ.erase i)) (Ideal.span {F.elem j})
    elem := ∏ (i : F.index) F.elem i
    }

def monopoly (F : Multicenter A) (F.index is finite) :
  A[F] →ₐ[A] A[comprimed_center F] := desc F
    (by
     intro i
     simp
     apply Ideal.mul_mem_right
     apply Ideal.subset_span
     simp
     )
    (by
     intro i
     simp
     apply Ideal.mul_mem_right
     apply Ideal.subset_span
     simp
     )

end universal_property
-/

/-

open Dilatation
open Multicenter
variable {A : Type*} [CommRing A] (F : Multicenter A)
abbrev ReesAlgebra := ⨁ (v : F^ℕ), 𝐋^v




variable [DecidableEq F.index] in
def reesAlgebraMul : F.ReesAlgebra →+ (F.ReesAlgebra →+ F.ReesAlgebra) :=
  DirectSum.toAddMonoid fun v ↦
    { toFun x := DirectSum.toAddMonoid fun w ↦
        { toFun y := .of _ (v + w) ⟨x * y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩
          map_zero' := by ext; simp [DirectSum.coe_of_apply]
          map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [mul_add] }
      map_zero' := by ext; simp [DirectSum.coe_of_apply]
      map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [add_mul] }


variable [DecidableEq F.index] in
instance : Mul F.ReesAlgebra where
  mul x y := F.reesAlgebraMul x y


variable [DecidableEq F.index] in
@[simp]
lemma reesAlgebraMul_of_of (v w : F^ℕ) (x y) :
    F.reesAlgebraMul (.of _ v x) (.of _ w y) =
    .of _ (v + w) ⟨x*y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩ := by
  simp [reesAlgebraMul]

variable [DecidableEq F.index] in
@[simp]
lemma reesAlgebra_mul_of_of (v w : F^ℕ) (x y) :
    (DirectSum.of _ v x : F.ReesAlgebra) * (.of _ w y) =
    .of _ (v + w) ⟨x * y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩ := by
  exact reesAlgebraMul_of_of _ _ _ _ _


set_option maxHeartbeats 500000
variable [DecidableEq F.index] in
instance : CommSemiring F.ReesAlgebra where
  left_distrib := by
   intro a
   intro b
   intro c
   change  F.reesAlgebraMul _ _ =  F.reesAlgebraMul _ _ +  F.reesAlgebraMul _ _
   simp
  right_distrib := by
   intro a
   intro b
   intro c
   change  F.reesAlgebraMul _ _ =  F.reesAlgebraMul _ _ +  F.reesAlgebraMul _ _
   simp
  zero_mul := by
   intro a
   change  F.reesAlgebraMul _ _ =  0
   simp
  mul_zero := by
   intro a
   change  F.reesAlgebraMul _ _ =  0
   simp
  mul_assoc := by /-
   intro a b c
   induction  a using DirectSum.induction_on with
   |H_zero =>
    change  F.reesAlgebraMul (F.reesAlgebraMul _ _ ) _ =  0
    simp
   |H_basic va ma =>
    induction b using DirectSum.induction_on with
     |H_zero =>
      change F.reesAlgebraMul  (F.reesAlgebraMul _ _ ) _ =  (F.reesAlgebraMul _ (F.reesAlgebraMul _ _ ) )
      simp
     |H_basic vb mb =>
       induction c using DirectSum.induction_on with
       |H_zero =>
         change F.reesAlgebraMul  _ _ =  (F.reesAlgebraMul _ (F.reesAlgebraMul _ _ ) )
         simp
       |H_basic vc mc =>
         simp[reesAlgebraMul_of_of, reesAlgebra_mul_of_of ]
         ext
         simp [DirectSum.coe_of_apply, add_assoc , mul_assoc ]
         split_ifs <;> rfl
       |H_plus x y hx hy =>
         change F.reesAlgebraMul  (F.reesAlgebraMul _ _ ) _ =
           (F.reesAlgebraMul _ (F.reesAlgebraMul _ _ ) ) at hx hy ⊢
         simp
         rw[← hx,← hy]
         simp
     |H_plus x y hx hy =>
         change F.reesAlgebraMul  (F.reesAlgebraMul _ _ ) _ =
           (F.reesAlgebraMul _ (F.reesAlgebraMul _ _ ) ) at hx hy ⊢
         simp
         rw[← hx,← hy]
   |H_plus x y hx hy =>
         change F.reesAlgebraMul  (F.reesAlgebraMul _ _ ) _ =
           (F.reesAlgebraMul _ (F.reesAlgebraMul _ _ ) ) at hx hy ⊢
         simp
         rw[← hx,← hy]-/ sorry

  mul_comm := by
   intro a b
   induction  a using DirectSum.induction_on with
   |H_zero =>
    change  F.reesAlgebraMul _ _ =  F.reesAlgebraMul _ _
    simp
   |H_basic va ma =>
    induction b using DirectSum.induction_on with
    |H_zero =>
     change  F.reesAlgebraMul _ _ =  F.reesAlgebraMul _ _
     simp
    |H_basic vb mb =>
     simp[reesAlgebraMul_of_of, reesAlgebra_mul_of_of ]
     ext
     simp [DirectSum.coe_of_apply, mul_comm, add_comm]
     split_ifs <;> rfl

    |H_plus x y hx hy =>
     change  F.reesAlgebraMul _ _ =  F.reesAlgebraMul _ _ at hx hy ⊢
     simp
     rw[← hx,← hy]

   |H_plus x y hx hy =>
     change  F.reesAlgebraMul _ _ =  F.reesAlgebraMul _ _ at hx hy ⊢
     simp
     rw[← hx,← hy]

  one := .of _ 0 ⟨1, by simp⟩
  one_mul := by
         intro a
         induction  a using DirectSum.induction_on with
         |H_zero =>
            have eq : (.of _ 0 ⟨1, by simp⟩ )* (.of _ 0 ⟨0, by simp⟩) = (.of _ 0 ⟨0, by simp⟩ ) := by

            sorry
         | H_basic i x =>
            sorry
         | H_plus x y _ _ =>
            sorry

         sorry
  mul_one := _

variable [DecidableEq F.index] in
def toReesAlgebra : A →+* F.ReesAlgebra where
  toFun a := .of _ 0 ⟨a, by simp⟩
  map_one' := by
    simp [reesAlgebraMul_of_of]
    simp[reesAlgebraMul_of_of ]
    sorry
  map_mul' := by
    intro a b
    simp [DirectSum.coe_of_apply]
    ext
    simp [DirectSum.coe_of_apply, mul_assoc]

    sorry
  map_zero' := by
    simp only [Finsupp.prod_zero_index]
    ext
    simp [DirectSum.coe_of_apply, mul_comm, add_comm]

    sorry
  map_add' := _

variable [DecidableEq F.index] in
instance : Algebra A F.ReesAlgebra :=
  RingHom.toAlgebra (toReesAlgebra F)

#check F.ReesAlgebra
 sorry

def placed_in_degree (F : Multicenter A) (v : F^ℕ) (x : 𝐋^v) :
   F.ReesAlgebra  := .of _ v ⟨x, by simp⟩   sorry

lemma potion_Rees_dilatation_iso (F : Multicenter A) :
  Potion a_i  placed in degree i for all i F.ReesAlgebra  ≅ A[F] := by
   sorry

def union_center (F F': Multicenter A): Multicenter A :=
  { index := F.index ⊔ F'.index
    ideal := fun i => match i with
      | sum.inl i => F.LargeIdeal i
      | sum.inr i => F'.LargeIdeal i
    elem := fun i => match i with
      | sum.inl i => F.elem i
      | sum.inr i => F'.elem i
    }

lemma union_center_iso (F F': Multicenter A) (F.index=F'.index)
 (F.LargeIdeal i = F'.LargeIdeal i):
  A[union_center F F'] ≅ Potion {a_i deg i}⊔{a_i'deg i} ReesAlgebra F := by
  sorry




end Multicenter



/-lemma dilatation_ring_flat_base_change (χ : A →+* B):
 χ ∈ RingHom.Flat  → A[F]⊗[A] B ≅ B[image_mult χ] := by
   --universal property of tensor product, exists -->
   --χ flat and nonzerodiv_image implies that  𝐚^ν is a nonzerodivisor in A[F]⊗[A] B
   --cond on ideals is ok
   --apply univ property to get a morphism of <--
   --check that both compositions are identity
  sorry

lemma flat_module_localization_at_prime_iff (M: Module.A):
 (M =0) ↔ (∀ q : maxideal.A : localization M A\ q =0 ):=
  → is trivial
  intro M
  assume let x ∈ M let Nx = submodule of M generated by x
  let I=Submodule.annihilator Nx, this is an ideal of A
  ∀ q in maxideal.A, exists f ∈ A \ q such that f∈ I -- because x=0 in the localization
  ∀ q in maxideal.A, I is not included in q
  applying Ideal.exists_le_maximal we get I=A
  so 1.x=0
  so M=0
  sorry

lemma open_implies_flat_ring (χ : A →+* B):
 (B.Spec → A.Spec is open_immerison )→ (χ : A →+* B is flat_ring_map):=
   intro χ
   -- AlgebraicGeometry.isOpenImmersion_iff_stalk
     -- and AlgebraicGeometry.IsAffineOpen.isLocalization_stalk implies
       -- that for all q ⊆ B prime ideals,
           --- IsLocalization.AtPrime f^-1(q) A → IsLocalization.AtPrime b B
               ----- is an isomorphism
  sorry
-/
-/
