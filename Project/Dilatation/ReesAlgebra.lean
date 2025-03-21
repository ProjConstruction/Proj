import Project.Dilatation.Family
import Project.Grading.Injection

import Mathlib.RingTheory.GradedAlgebra.Basic

suppress_compilation

open DirectSum Family

section semiring

variable {A : Type*} [CommSemiring A]
variable {ι : Type*} (F : ι → Ideal A)


@[ext]
structure ReesAlgebra where
  val : ⨁ (v : ι →₀ ℕ), F^v

namespace ReesAlgebra

instance : Zero (ReesAlgebra F) where
  zero := { val := 0 }

lemma zero_def :
  (0 : ReesAlgebra F) = { val := 0 } := rfl

instance : SMul ℕ (ReesAlgebra F) where
  smul n x := { val := n • x.val }

lemma nsmul_def (n : ℕ) (x : ReesAlgebra F) :
  n • x = { val := n • x.val } := rfl

instance : Add (ReesAlgebra F) where
  add x y := { val := x.val + y.val }

lemma add_def {x y : ReesAlgebra F} :
  x + y = { val := x.val + y.val } := rfl

lemma add_val {x y : ReesAlgebra F} :
  (x + y).val = x.val + y.val := rfl

lemma injective_val : Function.Injective (val : ReesAlgebra F → ⨁ (v : ι →₀ ℕ), F^v) := by
  intro x y h
  cases x; cases y
  simp only [ReesAlgebra.val] at h
  subst h
  rfl

instance : AddCommMonoid (ReesAlgebra F) :=
  Function.Injective.addCommMonoid (val (F := F)) (injective_val F) rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

variable [DecidableEq ι]

variable {F}

def mul' : (⨁ (v : ι →₀ ℕ), F^v) →+ ((⨁ (v : ι →₀ ℕ), F^v) →+ (⨁ (v : ι →₀ ℕ), F^v)) :=
  DirectSum.toAddMonoid fun v ↦
    { toFun x := DirectSum.toAddMonoid fun w ↦
        { toFun y := DirectSum.of _ (v + w) ⟨x * y, Ideal.mem_familyPow_add x.2 y.2⟩
          map_zero' := by ext; simp [DirectSum.coe_of_apply]
          map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [mul_add]
          }
      map_zero' := by ext; simp [DirectSum.coe_of_apply]
      map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [add_mul] }

@[simp]
lemma mul'_of_of (v w :  ι →₀ ℕ) (x : F^v) (y : F^w) :
    mul' (.of _ v x) (.of _ w y) =
    .of _ (v + w) ⟨x.1 * y.1, Ideal.mem_familyPow_add x.2 y.2⟩ := by
  simp [mul']


instance : Mul (ReesAlgebra F) where
  mul x y := { val := mul' x.val y.val }

lemma mul_def (x y : ReesAlgebra F) :
  x * y = { val := mul' x.val y.val } := rfl

lemma mul_val (x y : ReesAlgebra F) :
  (x * y).val = mul' x.val y.val := rfl

@[simp]
lemma mul_of_of (v w : ι →₀ ℕ) (x y) :
    ({ val := .of _ v x } : ReesAlgebra F) * { val := .of _ w y } =
    { val := .of _ (v + w) ⟨x.1 * y.1, Ideal.mem_familyPow_add x.2 y.2⟩ } := by
  ext : 1
  exact mul'_of_of ..


instance : One (ReesAlgebra F) where
  one := { val := .of _ 0 ⟨1, by simp⟩ }

lemma one_def :
  (1 : ReesAlgebra F) = { val := .of _ 0 ⟨1, by simp⟩ } := rfl

lemma one_val :
  (1 : ReesAlgebra F).val = .of _ 0 ⟨1, by simp⟩ := rfl

instance : LeftDistribClass (ReesAlgebra F) where
  left_distrib := by intros; simp [mul_def, add_def]

instance : RightDistribClass (ReesAlgebra F) where
  right_distrib := by intros; simp [mul_def, add_def]


lemma induction_on (P : ReesAlgebra F → Prop) (H_zero : P 0) (H_basic : ∀ v x, P { val := .of _ v x })
  (H_plus : ∀ x y, P x → P y → P (x + y)) : ∀ x, P x := by
  rintro ⟨x⟩
  induction x using DirectSum.induction_on with
  |H_zero => exact H_zero
  |H_basic v x => exact H_basic v x
  |H_plus x y hx hy => exact H_plus _ _ hx hy

instance : Semigroup (ReesAlgebra F) where
  mul_assoc := by
   intro a b c
   induction a using induction_on with
   |H_zero => simp [mul_def, zero_def]
   |H_basic va ma =>
    induction b using induction_on with
     |H_zero => simp [mul_def, zero_def]
     |H_basic vb mb =>
       induction c using induction_on with
       |H_zero => simp [mul_def, zero_def]
       |H_basic vc mc =>
        simp only [mul_of_of]
        ext
        simp only [mul_assoc, coe_of_apply, add_assoc]
        split_ifs <;> rfl
       |H_plus x y hx hy =>
        simp only [mul_def, mul'_of_of, mk.injEq, add_def, map_add] at hx hy ⊢
        rw[← hx,← hy]
     |H_plus x y hx hy =>
      simp only [mul_def, mk.injEq, add_def, map_add, AddMonoidHom.add_apply] at hx hy ⊢
      rw[← hx,← hy]
   |H_plus x y hx hy =>
    simp only [mul_def, mk.injEq, add_def, map_add, AddMonoidHom.add_apply] at hx hy ⊢
    rw[← hx,← hy]

instance : MulOneClass (ReesAlgebra F) where
  one_mul := by
    intro a
    induction  a using induction_on with
    |H_zero =>
      simp [mul_def, one_def, zero_def]
    | H_basic i x =>
      rw [one_def, mul_of_of]
      ext
      simp only [one_mul, coe_of_apply, zero_add]
      split_ifs <;> rfl
    | H_plus x y hx hy =>
      rw [mul_add, hx, hy]
  mul_one := by
    intro a
    induction  a using induction_on with
    |H_zero =>
      simp [mul_def, one_def, zero_def]
    | H_basic i x =>
      rw [one_def, mul_of_of]
      ext
      simp only [mul_one, coe_of_apply, add_zero]
      split_ifs <;> rfl
    | H_plus x y hx hy =>
      rw [add_mul, hx, hy]

instance : Monoid (ReesAlgebra F) where
  one_mul := one_mul
  mul_one := mul_one


instance : CommMonoid (ReesAlgebra F) where
  mul_comm := by
   intro a b
   induction  a using induction_on with
   |H_zero =>
    simp [mul_def, zero_def]
   |H_basic va ma =>
    induction b using induction_on with
    |H_zero =>
     simp [mul_def, zero_def]
    |H_basic vb mb =>
     simp only [mul_of_of]
     ext
     simp only [mul_comm, coe_of_apply, add_comm]
     split_ifs <;> rfl
    |H_plus x y hx hy =>
     rw [mul_add, hx, hy, add_mul]
   |H_plus x y hx hy =>
    rw [mul_add, add_mul, hx, hy]

instance : MonoidWithZero (ReesAlgebra F) where
  zero_mul := by
   intro a
   simp [mul_def, zero_def]
  mul_zero := by
   intro a
   simp [mul_def, zero_def]

instance : CommSemiring (ReesAlgebra F) where
  __ := inferInstanceAs <| AddCommMonoid (ReesAlgebra F)
  left_distrib := left_distrib
  right_distrib := right_distrib
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero

variable (F) in
@[simps]
def algebraMap' : A →+* ReesAlgebra F where
  toFun a := { val := .of _ 0 ⟨a, by simp⟩ }
  map_one' := rfl
  map_mul' a b := by
    ext : 3
    rw [DirectSum.coe_of_apply, mul_of_of, DirectSum.coe_of_apply]
    simp
  map_zero' := by
    ext
    rw [DirectSum.coe_of_apply]
    simp [zero_def]
  map_add' := by
    intro a b
    ext
    simp only [add_def, add_apply, Submodule.coe_add]
    erw [DirectSum.coe_of_apply, DirectSum.coe_of_apply, DirectSum.coe_of_apply]
    split_ifs <;> simp

instance : Algebra A (ReesAlgebra F) := RingHom.toAlgebra (algebraMap' F)

lemma algebraMap_eq : (algebraMap A (ReesAlgebra F)) = (algebraMap' F) := rfl

lemma algebraMap_apply_val (a : A) :
  (algebraMap A (ReesAlgebra F) a).val = .of _ 0 ⟨a, by simp⟩  := rfl

lemma algebraMap'_apply (a : A) :
  algebraMap' F a = { val := .of _ 0 ⟨a, by simp⟩ } := rfl
lemma smul_of (a : A) (v : ι →₀ ℕ) (x) :
    (a • { val := .of _ v x } : ReesAlgebra F) = { val := .of _ v (a • x) } := by
  ext : 1
  simp only [Algebra.smul_def, algebraMap_eq, algebraMap'_apply_val, Finsupp.prod_zero_index, mul_def,
    mul'_of_of]
  ext
  simp only [coe_of_apply, zero_add]
  split_ifs <;> rfl

lemma smul_of_val (a : A) (v : ι →₀ ℕ) (x) :
    (a • { val := .of _ v x } : ReesAlgebra F).val = .of _ v (a • x) := by
  simp [smul_of]

lemma smul_val (a : A) (x : ReesAlgebra F) :
    (a • x).val = a • x.val := by
  induction x using induction_on with
  |H_zero =>
    simp [Algebra.smul_def, algebraMap_apply, zero_def, mul_val]
  |H_basic i x =>
    simp only [smul_of_val]
    ext
    simp [DirectSum.coe_of_apply, smul_apply]
    split_ifs <;> simp
  | H_plus x y hx hy =>
    simp only [smul_add, add_val] at hx hy ⊢
    rw [hx, hy]


variable (F) in
@[simps]
def single (v : ι →₀ ℕ) : F^v →ₗ[A] ReesAlgebra F where
  toFun x := { val := .of _ v x }
  map_add' x y := by ext; simp [add_def]
  map_smul' x y := by simp [smul_of]

lemma single_def (v : ι →₀ ℕ) (x) :
  single F v x = { val := .of _ v x } := rfl

lemma single_eq (v v' : ι →₀ ℕ) (eq : v = v') (x : A) (hx : x ∈ F^v) :
    single F v ⟨x, hx⟩ = single F v' ⟨x, by subst eq; exact hx⟩ := by
  subst eq
  rfl

lemma single_mul (v w : ι →₀ ℕ) (x y) :
    single F v x * single F w y = single F (v + w) ⟨x.1 * y.1, Ideal.mem_familyPow_add x.2 y.2⟩ := by
  ext : 1
  simp only [mul_val, single_def, mul'_of_of]

end ReesAlgebra

end semiring


section ring

variable {A : Type*} [CommRing A]
variable {ι : Type*} (F : ι → Ideal A)

namespace ReesAlgebra

instance : Neg (ReesAlgebra F) where
  neg x := { val := -x.val }

lemma neg_def (x : ReesAlgebra F) : -x = { val := -x.val } := rfl

instance : Sub (ReesAlgebra F) where
  sub x y := { val := x.val - y.val }

lemma sub_def (x y : ReesAlgebra F) : x - y = { val := x.val - y.val } := rfl

instance : SMul ℤ (ReesAlgebra F) where
  smul n x := { val := n • x.val }

lemma zsmul_def (n : ℤ) (x : ReesAlgebra F) : n • x = { val := n • x.val } := rfl

variable [DecidableEq ι]
instance : AddCommGroup (ReesAlgebra F) where
  __ := inferInstanceAs <| AddCommMonoid (ReesAlgebra F)
  __ := (Function.Injective.addCommGroup (val (F := F)) (injective_val F) rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) : AddCommGroup (ReesAlgebra F))


instance : CommRing (ReesAlgebra F) where
  __ := inferInstanceAs <| CommSemiring (ReesAlgebra F)
  __ := inferInstanceAs <| AddCommGroup (ReesAlgebra F)

def grading (v : ι →₀ ℕ) : Submodule A (ReesAlgebra F) := LinearMap.range (single F v)

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
    exact ⟨⟨x * y, _⟩, rfl⟩

instance : SetLike.GradedMonoid (grading F) where

def decomposeAux : (⨁ (v : ι →₀ ℕ), F^v) →ₗ[A] ⨁ (v : ι →₀ ℕ), grading F v :=
  DirectSum.toModule _ _ _ fun v ↦
  { toFun x := .of _ v ⟨_, ⟨x, rfl⟩⟩
    map_add' x y := by
      simp only [single_def, map_add]
      ext w w'
      simp only [coe_of_apply, add_apply, Submodule.coe_add]
      split_ifs <;> simp
    map_smul' a x := by
      dsimp
      ext w w'
      rw [coe_of_apply, smul_apply]
      simp only [map_smul, SetLike.val_smul, SetLike.coe_eq_coe]
      split_ifs with h
      · subst h
        simp only [of_eq_same]
      · simp [zero_def, Algebra.smul_def, algebraMap_eq, algebraMap'_apply, mul_def, mul'_of_of,
          DirectSum.coe_of_apply, if_neg h] }

def decompose : ReesAlgebra F →ₗ[A] ⨁ (v : ι →₀ ℕ), grading F v :=
  decomposeAux F ∘ₗ
    { toFun := val
      map_add' _ _ := rfl
      map_smul' _ _ := by dsimp; rw [smul_val] }

@[simp]
lemma decompose_single (v : ι →₀ ℕ) (x) :
    decompose F (single F v x) = .of _ v ⟨_, ⟨x, rfl⟩⟩ := by
  simp only [decompose, decomposeAux, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply, single_apply_val]
  erw [toModule_lof]
  rfl

@[simp]
lemma decompose_val_of (v : ι →₀ ℕ) (x) :
    decompose F { val := .of _ v x } = .of _ v ⟨_, ⟨x, rfl⟩⟩ :=
  decompose_single ..

instance : GradedAlgebra (grading F) where
  decompose' := decompose F
  left_inv x := by
    induction x using induction_on with
    |H_zero => simp
    |H_basic v x => simp [single]
    |H_plus x y hx hy => simp [hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    |H_zero => simp
    |H_basic v x => rcases x with ⟨_, ⟨x, rfl⟩⟩; simp
    |H_plus x y hx hy => simp [hx, hy]

lemma single_has_degree (v : ι →₀ ℕ) (x) :
    single F v x ∈ grading F v := by
  rw [grading, LinearMap.mem_range]
  use x

@[simps]
def degreeZeroIso : A ≃+* (ReesAlgebra.grading F 0) where
  toFun a := ⟨.single F 0 ⟨a, by simp⟩, by simp [grading]⟩
  invFun a := a.1.val 0 |>.1
  left_inv a := by simp
  right_inv a := by
    ext v
    simp only [Subtype.coe_eta, single_apply_val, SetLike.coe_eq_coe]
    ext
    rw [DirectSum.coe_of_apply]
    obtain ⟨x, hx⟩ := a.2
    rw [← hx]
    simp only [ZeroMemClass.coe_zero, single_apply_val]
    rw [DirectSum.coe_of_apply]
    simp
  map_mul' x y := by
    ext v
    simp only [single_apply_val, SetLike.GradeZero.coe_mul, single_mul, SetLike.coe_eq_coe]
    ext
    simp only [coe_of_apply, zero_add]
  map_add' x y := by
    ext v
    simp only [single_apply_val, coe_of_apply, AddMemClass.mk_add_mk, add_val, add_apply,
      Submodule.coe_add]
    split_ifs
    · rfl
    · simp

variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]
abbrev intGrading := (gradingOfInjection (grading F) (ρNatToInt ι))
instance : GradedAlgebra (intGrading F) :=
  gradingOfInjection_isGradedAlgebra (grading F) (ρNatToInt ι)

def degreeZeroIso' : A ≃+* (ReesAlgebra.intGrading F 0) :=
  degreeZeroIso F |>.trans
  (gradingOfInjection₀Iso (ReesAlgebra.grading F) (ρNatToInt ι)).symm


lemma single_has_degree' (v : ι →₀ ℕ) (x) :
    single F v x ∈ intGrading F (ρNatToInt _ v) := by
  rw [intGrading, gradingOfInjection]
  rw [dif_pos (by simp)]
  erw [Set.rangeSplitting_apply_coe]
  exact single_has_degree F v x
  exact ρNatToInt_inj

end ReesAlgebra

end ring
