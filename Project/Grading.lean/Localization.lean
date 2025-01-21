import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Localization.Basic

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A]  (𝒜 : ι → σ)

structure HomogeneousSubmonoid extends Submonoid A where
  homogeneous : ∀ {x}, x ∈ toSubmonoid → SetLike.Homogeneous 𝒜 x

namespace HomogeneousSubmonoid

variable (S : HomogeneousSubmonoid 𝒜)

variable {𝒜}

structure PreGrading (i : ι) where
  num : A
  den : S.toSubmonoid
  degNum : ι
  degDen : ι
  num_mem : num ∈ 𝒜 degNum
  den_mem : (den : A) ∈ 𝒜 degDen
  deg_frac_eq : degNum - degDen = i

namespace PreGrading

@[ext]
lemma ext {i : ι} (x y : S.PreGrading i)
    (num_eq : x.num = y.num) (den_eq : x.den = y.den)
    (degNum_eq : x.degNum = y.degNum)
    (degDen_eq : x.degDen = y.degDen) : x = y := by
  rcases x with ⟨a_x, ⟨b_x, hb_x⟩, mx, nx, hax, hbx, hx⟩
  rcases y with ⟨a_y, ⟨b_y, hb_y⟩, my, ny, hay, hby, hy⟩
  simp only [Subtype.mk.injEq, mk.injEq] at *
  subst num_eq den_eq degNum_eq degDen_eq
  aesop

variable [AddSubgroupClass σ A]
instance (i : ι) : Neg (S.PreGrading i) where
  neg x := ⟨-x.num, x.den, x.degNum, x.degDen, neg_mem x.num_mem, x.den_mem, x.deg_frac_eq⟩

@[simp]
lemma neg_num {i : ι} (x : S.PreGrading i) : (-x).num = -x.num := rfl

@[simp]
lemma neg_den {i : ι} (x : S.PreGrading i) : (-x).den = x.den := rfl

@[simp]
lemma neg_degNum {i : ι} (x : S.PreGrading i) : (-x).degNum = x.degNum := rfl

@[simp]
lemma neg_degDen {i : ι} (x : S.PreGrading i) : (-x).degDen = x.degDen := rfl

variable [DecidableEq ι] [GradedRing 𝒜]
instance (i : ι) : Add (S.PreGrading i) where
  add x y :=
  { num := x.den * y.num + y.den * x.num
    den := x.den * y.den
    degNum := x.degDen + y.degNum
    degDen := x.degDen + y.degDen
    num_mem := by
      refine add_mem (SetLike.GradedMul.mul_mem x.den_mem y.num_mem) ?_
      convert SetLike.GradedMul.mul_mem y.den_mem x.num_mem using 2

      have eq₁ := x.deg_frac_eq
      have eq₂ := y.deg_frac_eq
      rw [sub_eq_iff_eq_add] at eq₁ eq₂
      rw [eq₁, eq₂]
      abel
    den_mem := SetLike.GradedMul.mul_mem x.den_mem y.den_mem
    deg_frac_eq := by simp_rw [← y.deg_frac_eq]; abel }

@[simp]
lemma add_num {i : ι} (x y : S.PreGrading i) : (x + y).num = x.den * y.num + y.den * x.num := rfl

@[simp]
lemma add_den {i : ι} (x y : S.PreGrading i) : (x + y).den = x.den * y.den := rfl

@[simp]
lemma add_degNum {i : ι} (x y : S.PreGrading i) : (x + y).degNum = x.degDen + y.degNum := rfl

@[simp]
lemma add_degDen {i : ι} (x y : S.PreGrading i) : (x + y).degDen = x.degDen + y.degDen := rfl

instance (i : ι) : Zero (S.PreGrading i) where
  zero := ⟨0, 1, i, 0, zero_mem (𝒜 i), SetLike.GradedOne.one_mem, by simp⟩

@[simp]
lemma zero_num {i : ι} : (0 : S.PreGrading i).num = 0 := rfl

@[simp]
lemma zero_den {i : ι} : (0 : S.PreGrading i).den = 1 := rfl

@[simp]
lemma zero_degNum {i : ι} : (0 : S.PreGrading i).degNum = i := rfl

@[simp]
lemma zero_degDen {i : ι} : (0 : S.PreGrading i).degDen = 0 := rfl

@[simp]
lemma neg_zero {i : ι} : -(0 : S.PreGrading i) = 0 := by ext <;> simp

instance (i : ι) : AddZeroClass (S.PreGrading i) where
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp [← x.deg_frac_eq]

instance (i : ι) : AddSemigroup (S.PreGrading i) where
  add_assoc x y z := by
    ext
    · simp only [add_num, add_den, Submonoid.coe_mul]; ring
    · simp only [add_den, Submonoid.coe_mul]; ring
    · simp only [add_degNum, add_degDen]; abel
    · simp only [add_degDen]; abel

instance (i : ι) : SubNegMonoid (S.PreGrading i) where
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

def val (i : ι) : (S.PreGrading i) →+ Localization S.toSubmonoid where
  toFun x := Localization.mk x.num x.den
  map_zero' := Localization.mk_zero 1
  map_add' := by simp [Localization.add_mk]

def addCon (i : ι) : AddCon (S.PreGrading i) := AddCon.ker (val S i)

instance (i : ι) : Neg (addCon S i).Quotient where
  neg := (addCon S i).lift
    { toFun x := (addCon S i).mk' (-x)
      map_zero' := by
        simp only [neg_zero, AddCon.coe_mk', AddCon.coe_zero]
      map_add' x y := by
        dsimp only [AddCon.coe_mk', AddCon.coe_zero, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk]
        rw [← AddCon.coe_mk', ← map_add]
        erw [AddCon.eq]
        simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_num,
          add_num, neg_add_rev, neg_den, add_den, mul_neg, Localization.mk_eq_mk_iff,
          Localization.r_iff_exists, Submonoid.coe_mul, Subtype.exists, exists_prop]
        exact ⟨1, S.toSubmonoid.one_mem, by ring⟩ } fun x y h => by
    simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists, exists_prop,
      AddCon.coe_mk', AddCon.eq, neg_num, neg_den, mul_neg, neg_inj] at h ⊢
    exact h

instance (i : ι) : AddCommGroup (addCon S i).Quotient where
  neg := _
  zsmul := zsmulRec nsmulRec
  neg_add_cancel := by
    intro a
    obtain ⟨a, rfl⟩ := AddCon.mk'_surjective a
    simp only [AddCon.coe_mk', AddCon.lift_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← AddCon.coe_mk', ← map_add]
    erw [AddCon.eq]
    simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_num, neg_den,
      neg_num, mul_neg, add_neg_cancel, add_den, zero_num, zero_den, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists, OneMemClass.coe_one, mul_zero, Submonoid.coe_mul, exists_const]
  add_comm := by
    intro a b
    obtain ⟨a, rfl⟩ := AddCon.mk'_surjective a
    obtain ⟨b, rfl⟩ := AddCon.mk'_surjective b
    simp only [AddCon.coe_mk']
    rw [← AddCon.coe_mk', ← map_add, ← map_add]
    erw [AddCon.eq]
    simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_num, add_den]
    congr 1
    · ring
    · rw [mul_comm]

def emb (i : ι) : (addCon S i).Quotient →+ Localization S.toSubmonoid :=
  AddCon.lift _ (val ..) le_rfl

end PreGrading

variable [AddSubgroupClass σ A] [DecidableEq ι] [GradedRing 𝒜]

def Grading (i : ι) : AddSubgroup (Localization S.toSubmonoid) := (PreGrading.emb S i).range

end HomogeneousSubmonoid

namespace LocalizationGrading


end LocalizationGrading
