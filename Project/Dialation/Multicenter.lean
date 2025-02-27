import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Project.Dialation.lemma
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

--lemma eq below ?

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


lemma  cond_univ_implies_large_cond (χ : A →+* B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)):
    (∀ (ν : F^ℕ) , (Ideal.span {χ (𝐚^ν)} = Ideal.map χ (𝐋^ν))) :=by
     classical
     intro v
     simp[prodLargeIdealPower]
     simp [prodElemPower]
     simp only [Finsupp.prod, map_prod, map_pow]
     rw[Ideal.prod_span']
     simp[← Ideal.span_singleton_pow, gen]
     simp[Ideal.prod_map, Ideal.map_pow]



lemma  lemma_exists_in_image (χ : A →+* B)
    (non_zero_divisor : ∀ i : F.index, χ (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)):
    (∀(ν : F^ℕ) (m : 𝐋^ν) ,  (∃! bm : B ,  χ 𝐚^ν *bm=χ (m) )):= by
      intro v m
      have mem : χ m ∈  Ideal.map χ (𝐋^v) := by
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



def def_unique_elem (χ : A →+* B) (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, χ (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)): B :=
     (lemma_exists_in_image  F χ non_zero_divisor gen v m).choose

lemma def_unique_elem_spec (χ : A →+* B) (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, χ (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)):
    χ 𝐚^v * def_unique_elem F χ v m non_zero_divisor gen = χ m := by
    apply (lemma_exists_in_image F χ non_zero_divisor gen v m).choose_spec.1

lemma def_unique_elem_unique  (χ : A →+* B) (v : F^ℕ) (m : 𝐋^v)
    (non_zero_divisor : ∀ i : F.index, χ (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)):
    ∀ bm : B, χ 𝐚^v * bm = χ m →  def_unique_elem F χ v m non_zero_divisor gen =bm:= by
    intro bm hbm
    apply ((lemma_exists_in_image F χ non_zero_divisor gen v m).choose_spec.2 bm hbm).symm



def desc (χ : A →+* B)
    (non_zero_divisor : ∀ i : F.index, χ (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)) :
     A[F] →+* B where
  toFun := Dilatation.descFun (fun x ↦ def_unique_elem F χ x.pow ⟨ x.num, x.num_mem⟩  non_zero_divisor gen )
                            ( by
                              intro x y h
                              rcases h with ⟨β, hβ⟩
                              simp only
                              apply def_unique_elem_unique
                              apply_fun (fun z => χ (𝐚^ (β + y.pow)) * z)
                              · simp only [mul_assoc, hβ]
                                rw[← map_mul, mul_comm _ x.num]
                                rw [hβ]
                                simp only [map_mul]
                                rw[← def_unique_elem_spec F χ y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
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
      rw[← def_unique_elem_spec F χ y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw[← def_unique_elem_spec F χ x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
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
      rw[← def_unique_elem_spec F χ y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw[← def_unique_elem_spec F χ x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp [prodElemPow_add]
      ring



lemma  lemma_exists_unique_morphism (χ : A →+* B)
    (non_zero_divisor : ∀ i : F.index, χ (F.elem i) ∈ nonZeroDivisors B)
    (gen : ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i))
    (χ':A[F]→+*B) (χ'  fromBaseRing A F = χ ) :
     χ' = desc A B F χ non_zero_divisor gen := by
     intro v m
    sorry



def image_mult (χ : A →+* B) : image of F under χ :=
 B.Multicenter := index  =F.index
  (fun i ↦ Ideal.map χ (F.LargeIdeal i))
  (fun i ↦ χ (F.elem i))
  sorry

def functo_dila_ring (χ : A →+* B) : A[F] →+* B[image mult χ B] where
  toFun := sorry

lemma unique_functorial_morphism_dilatation (χ : A →+* B)
(χ':A[F]→+*[A] B[image_mult B χ F]) : χ' = functo_dila_ring χ B  :=by

  sorry



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
instance : Mul F.ReesAlgebra where
  mul x y := F.reesAlgebraMul x y

variable [DecidableEq F.index] in
@[simp]
lemma reesAlgebra_mul_of_of (v w : F^ℕ) (x y) :
    (DirectSum.of _ v x : F.ReesAlgebra) * (.of _ w y) =
    .of _ (v + w) ⟨x * y, prod_mem_prodLargeIdealPower_add x.2 y.2⟩ :=
  reesAlgebraMul_of_of ..

variable [DecidableEq F.index] in
instance : CommSemiring F.ReesAlgebra where
  left_distrib := by
   intro a
   intro b
   intro c
   sorry
  right_distrib := _
  zero_mul := by
   simp? sorry
  mul_zero := _
  mul_assoc := _
  mul_comm := _
  one := .of _ 0 ⟨1, by simp⟩
  one_mul := _
  mul_one := _

variable [DecidableEq F.index] in
def toReesAlgebra : A →+* F.ReesAlgebra where
  toFun a := .of _ 0 ⟨a, by simp⟩
  map_one' := _
  map_mul' := _
  map_zero' := _
  map_add' := _

variable [DecidableEq F.index] in
instance : Algebra A F.ReesAlgebra :=
  RingHom.toAlgebra (toReesAlgebra F)

#check F.ReesAlgebra
 sorry

def placed_in_degree (F : Multicenter A) (v : F^ℕ) (x : 𝐋^v) :
   ReesAlgebra F := .of _ v ⟨x, by simp⟩   sorry

lemma potion_Rees_dilatation_iso (F : Multicenter A) :
  Potion a_i  placed in degree i for all i ReesAlgebra F ≅ A[F] := by
   sorry

def union_center (F F': Multicenter A): Multicenter A :=
  { index := F.index ⊔ F'.index
    LargeIdeal := fun i => match i with
      | sum.inl i => F.LargeIdeal i
      | sum.inr i => F'.LargeIdeal i
    elem := fun i => match i with
      | sum.inl i => F.elem i
      | sum.inr i => F'.elem i
    }

lemma union_center_iso (F F': Multicenter A) (F.index=F'.index)
 (F.Lareideal i = F'.LargeIdeal i):
  A[Union_center F F'] ≅ Potion {a_i deg i}⊔{a_i'deg i} ReesAlgebra F := by
  sorry




end Multicenter

/-
--We only need the a_i part in the following def
def cat_dil_test_reg (F: Multicenter A) fullsubcategory of A->+*B ,
Objects := {f:A→+* B |  f (F.elem i) ∈ nonZeroDivisors B }  := by
 sorry

lemma dil_representable_functor (F: Multicenter A) :
 A[F] represents the functor cat_dil_test_reg A F → Set,
    f ↦ singleton if ∀ i, Ideal.span {χ (F.elem i)} = Ideal.map χ (F.LargeIdeal i)
             emptyset else := by
  sorry


def dil_to_localise (F: Multicenter A) : A[F] →+* A localise {a_i : i ∈ F.index}  where
  toFun := m/v. ↦ m/v.
  map_one' :=
  map_mul' :=
  map_zero' :=
  map_add' :=
  sorry

lemma dil_to_localise_mor_alg (F: Multicenter A):
  dil_to_localise  frombasering = frombaseringloc := by
  sorry

lemma dil_to_localise_unique (F: Multicenter A) (other : A[F] →+* A localise {a_i})
 ( other  frombasering = frombaseringloc):
  other = dil_to_localise F := by
  sorry

lemma dil_eq_loc (F: Multicenter A) (F.LargeIdeal i= A):
   dil_to_localise is an isomorphism of rings := by
  sorry
-/


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
