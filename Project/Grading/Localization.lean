import Mathlib.RingTheory.Localization.Basic

import Project.HomogeneousSubmonoid.Basic

open DirectSum

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A]  (𝒜 : ι → σ)

namespace HomogeneousSubmonoid

variable (S : HomogeneousSubmonoid 𝒜)

variable {𝒜}

structure PreLocalizationGrading (i : ι) where
  num : A
  den : S.toSubmonoid
  degNum : ι
  degDen : ι
  num_mem : num ∈ 𝒜 degNum
  den_mem : (den : A) ∈ 𝒜 degDen
  deg_frac_eq : degNum - degDen = i

namespace PreLocalizationGrading

@[ext]
lemma ext {i : ι} (x y : S.PreLocalizationGrading i)
    (num_eq : x.num = y.num) (den_eq : x.den = y.den)
    (degNum_eq : x.degNum = y.degNum)
    (degDen_eq : x.degDen = y.degDen) : x = y := by
  rcases x with ⟨a_x, ⟨b_x, hb_x⟩, mx, nx, hax, hbx, hx⟩
  rcases y with ⟨a_y, ⟨b_y, hb_y⟩, my, ny, hay, hby, hy⟩
  simp only [Subtype.mk.injEq, mk.injEq] at *
  subst num_eq den_eq degNum_eq degDen_eq
  aesop

variable [AddSubgroupClass σ A]
instance (i : ι) : Neg (S.PreLocalizationGrading i) where
  neg x := ⟨-x.num, x.den, x.degNum, x.degDen, neg_mem x.num_mem, x.den_mem, x.deg_frac_eq⟩

@[simp]
lemma neg_num {i : ι} (x : S.PreLocalizationGrading i) : (-x).num = -x.num := rfl

@[simp]
lemma neg_den {i : ι} (x : S.PreLocalizationGrading i) : (-x).den = x.den := rfl

@[simp]
lemma neg_degNum {i : ι} (x : S.PreLocalizationGrading i) : (-x).degNum = x.degNum := rfl

@[simp]
lemma neg_degDen {i : ι} (x : S.PreLocalizationGrading i) : (-x).degDen = x.degDen := rfl

variable [DecidableEq ι] [GradedRing 𝒜]
instance (i : ι) : Add (S.PreLocalizationGrading i) where
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
lemma add_num {i : ι} (x y : S.PreLocalizationGrading i) : (x + y).num = x.den * y.num + y.den * x.num := rfl

@[simp]
lemma add_den {i : ι} (x y : S.PreLocalizationGrading i) : (x + y).den = x.den * y.den := rfl

@[simp]
lemma add_degNum {i : ι} (x y : S.PreLocalizationGrading i) : (x + y).degNum = x.degDen + y.degNum := rfl

@[simp]
lemma add_degDen {i : ι} (x y : S.PreLocalizationGrading i) : (x + y).degDen = x.degDen + y.degDen := rfl

instance : One (S.PreLocalizationGrading 0) where
  one := ⟨1, 1, 0, 0, SetLike.GradedOne.one_mem, SetLike.GradedOne.one_mem, by abel⟩

@[simp]
lemma one_num : (1 : S.PreLocalizationGrading 0).num = 1 := rfl

@[simp]
lemma one_den : (1 : S.PreLocalizationGrading 0).den = 1 := rfl

@[simp]
lemma one_degNum : (1 : S.PreLocalizationGrading 0).degNum = 0 := rfl

@[simp]
lemma one_degDen : (1 : S.PreLocalizationGrading 0).degDen = 0 := rfl

instance (i : ι) : Zero (S.PreLocalizationGrading i) where
  zero := ⟨0, 1, i, 0, zero_mem (𝒜 i), SetLike.GradedOne.one_mem, by simp⟩

@[simp]
lemma zero_num {i : ι} : (0 : S.PreLocalizationGrading i).num = 0 := rfl

@[simp]
lemma zero_den {i : ι} : (0 : S.PreLocalizationGrading i).den = 1 := rfl

@[simp]
lemma zero_degNum {i : ι} : (0 : S.PreLocalizationGrading i).degNum = i := rfl

@[simp]
lemma zero_degDen {i : ι} : (0 : S.PreLocalizationGrading i).degDen = 0 := rfl

@[simp]
lemma neg_zero {i : ι} : -(0 : S.PreLocalizationGrading i) = 0 := by ext <;> simp

instance (i : ι) : AddZeroClass (S.PreLocalizationGrading i) where
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp [← x.deg_frac_eq]

instance (i : ι) : AddSemigroup (S.PreLocalizationGrading i) where
  add_assoc x y z := by
    ext
    · simp only [add_num, add_den, Submonoid.coe_mul]; ring
    · simp only [add_den, Submonoid.coe_mul]; ring
    · simp only [add_degNum, add_degDen]; abel
    · simp only [add_degDen]; abel

instance (i : ι) : SubNegMonoid (S.PreLocalizationGrading i) where
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simps]
def val (i : ι) : (S.PreLocalizationGrading i) →+ Localization S.toSubmonoid where
  toFun x := Localization.mk x.num x.den
  map_zero' := Localization.mk_zero 1
  map_add' := by simp [Localization.add_mk]

def addCon (i : ι) : AddCon (S.PreLocalizationGrading i) := AddCon.ker (val S i)

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

@[simps!]
def emb (i : ι) : (addCon S i).Quotient →+ Localization S.toSubmonoid :=
  AddCon.lift _ (val ..) le_rfl

-- sanity check
example {i : ι} (x y : S.PreLocalizationGrading i) :
    addCon S i x y ↔ Localization.mk x.num x.den = Localization.mk y.num y.den := by
  simp [addCon]

end PreLocalizationGrading

variable [AddSubgroupClass σ A] [DecidableEq ι] [GradedRing 𝒜]

def LocalizationGrading (i : ι) : AddSubgroup (Localization S.toSubmonoid) := (PreLocalizationGrading.emb S i).range

namespace LocalizationGrading

lemma one_mem : 1 ∈ S.LocalizationGrading 0 := ⟨AddCon.mk' _ 1, Localization.mk_one⟩

instance : SetLike.GradedMonoid S.LocalizationGrading where
  one_mem := HomogeneousSubmonoid.LocalizationGrading.one_mem ..
  mul_mem := by
    rintro i j _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
    obtain ⟨y, rfl⟩ := AddCon.mk'_surjective y
    simp only [AddCon.coe_mk', HomogeneousSubmonoid.PreLocalizationGrading.emb_apply, AddCon.liftOn_coe,
      HomogeneousSubmonoid.PreLocalizationGrading.val_apply, Localization.mk_mul]
    refine ⟨AddCon.mk' _
      { num := x.num * y.num
        den := x.den * y.den
        degNum := x.degNum + y.degNum
        degDen := x.degDen + y.degDen
        num_mem := SetLike.GradedMul.mul_mem x.num_mem y.num_mem
        den_mem := SetLike.GradedMul.mul_mem x.den_mem y.den_mem
        deg_frac_eq := by
          simp only [← x.deg_frac_eq, ← y.deg_frac_eq]
          abel }, ?_⟩
    simp only [AddCon.coe_mk', HomogeneousSubmonoid.PreLocalizationGrading.emb_apply, AddCon.liftOn_coe,
      HomogeneousSubmonoid.PreLocalizationGrading.val_apply]

noncomputable def decomposition :
    Localization S.toSubmonoid →+* ⨁ i : ι, S.LocalizationGrading i :=
  IsLocalization.lift (M := S.toSubmonoid) (S := Localization S.toSubmonoid)
    (g := RingHom.comp (DirectSum.toSemiring (fun i ↦
      (DirectSum.of (fun i ↦ S.LocalizationGrading i) i :
        S.LocalizationGrading i →+ ⨁ i, S.LocalizationGrading i).comp
      (⟨⟨fun x ↦ ⟨Localization.mk x.1 1,
        ⟨AddCon.mk' _ ⟨x.1, 1, i, 0, x.2, SetLike.GradedOne.one_mem, by simp⟩, rfl⟩⟩,
        by simp only [ZeroMemClass.coe_zero, AddSubgroup.mk_eq_zero]; exact Localization.mk_zero 1⟩,
        by
          intro x y
          ext
          simp only [AddMemClass.coe_add, AddSubgroup.coe_add]
          exact (Localization.add_mk_self x.1 1 y.1).symm⟩ : (𝒜 i) →+ (S.LocalizationGrading i)))
            (by
              simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                Function.comp_apply, SetLike.coe_gOne, Localization.mk_one]
              rfl)
            (by
              intro i j x y
              simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                Function.comp_apply, SetLike.coe_gMul]
              rw [DirectSum.of_mul_of]
              congr 1
              ext
              simp [Localization.mk_mul])) (DirectSum.decomposeRingEquiv 𝒜).toRingHom)
  (by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := S.homogeneous hx
    lift x to 𝒜 i using hi
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      toSemiring_apply]
    rw [show decomposeRingEquiv 𝒜 x = of (fun i ↦ 𝒜 i) i x from decompose_coe 𝒜 _]
    simp only [toAddMonoid_of, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Function.comp_apply]
    rw [isUnit_iff_exists_inv]
    use of (fun i ↦ S.LocalizationGrading i) (-i) ⟨Localization.mk 1 ⟨x, hx⟩, ⟨AddCon.mk' _
      ⟨1, ⟨x, hx⟩, 0, i, SetLike.GradedOne.one_mem, x.2, by simp⟩, by simp⟩⟩
    simp only [of_mul_of, one_def]
    change of (fun i ↦ S.LocalizationGrading i) (i + (-i)) ⟨_, _⟩ = _
    simp only [Localization.mk_mul, mul_one, one_mul]
    simp_rw [Localization.mk_self (S := S.toSubmonoid) (a := ⟨x, hx⟩)]
    have (j : ι) (h : j = 0) :
        of (fun i ↦ S.LocalizationGrading i) j
          (⟨1, h ▸ one_mem S⟩ : S.LocalizationGrading j) =
        of (fun i ↦ S.LocalizationGrading i) 0 1 := by
      subst h; rfl

    exact this (i + (-i)) (by simp))

lemma decomposition_homogeneous_mk
    {i j : ι} (a : A) (ha : a ∈ 𝒜 i) (b : S.toSubmonoid) (hb : b.1 ∈ 𝒜 j) :
    decomposition S (Localization.mk a b) =
    of _ (i - j) ⟨Localization.mk a b, ⟨AddCon.mk' _ ⟨a, b, i, j, ha, hb, rfl⟩, rfl⟩⟩ := by
  simp_rw [decomposition, Localization.mk_eq_mk', IsLocalization.lift_mk'_spec]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    toSemiring_apply]
  lift a to 𝒜 i
  · exact ha
  rcases b with ⟨b, hb'⟩
  lift b to 𝒜 j
  · exact hb
  erw [decompose_coe, toAddMonoid_of, decompose_coe, toAddMonoid_of]
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
    of_mul_of]
  simp_rw [← Localization.mk_eq_mk']
  change _ = of (fun i ↦ S.LocalizationGrading i) _ ⟨_, _⟩
  simp only [Localization.mk_mul, one_mul,
    show Localization.mk (b.1 * a.1) (⟨b, hb'⟩ : S.toSubmonoid) = Localization.mk a.1 1 by
    simp [Localization.mk_eq_mk_iff, Localization.r_iff_exists]]

  have (k : ι) (h : i = k) (x : Localization S.toSubmonoid) (hx : x ∈ S.LocalizationGrading i):
        of (fun i ↦ S.LocalizationGrading i) k
          (⟨x, h.symm ▸ hx⟩ : S.LocalizationGrading k) =
        of (fun i ↦ S.LocalizationGrading i) i ⟨x, hx⟩ := by
      subst h; rfl
  exact this (j + (i - j)) (by simp) (Localization.mk a 1) _ |>.symm

noncomputable instance : DirectSum.Decomposition S.LocalizationGrading where
  decompose' := LocalizationGrading.decomposition S
  left_inv x := by
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨a, ⟨b, hb⟩⟩
    simp only
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | h_zero =>
      rw [Localization.mk_zero, map_zero, map_zero]
    | @h_homogeneous i x =>
      obtain ⟨j, hj⟩ := S.homogeneous hb
      rw [decomposition_homogeneous_mk S x.1 x.2 ⟨b, hb⟩ hj]
      simp only [coeAddMonoidHom_of]
    | h_add a a' h h' =>
      convert congr($h + $h') using 1
      · rw [← map_add, ← map_add, Localization.add_mk_self]
      · rw [Localization.add_mk_self]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | H_zero => simp
    | H_basic i x =>
      simp only [coeAddMonoidHom_of]
      obtain ⟨y, hy⟩ := x.2
      have hy' : x = ⟨_, ⟨y, rfl⟩⟩ := by ext; exact hy.symm
      rw [← hy, hy']
      clear hy hy' x
      obtain ⟨⟨a, ⟨b, hb⟩, m, n, hm, hn, H⟩, rfl⟩ := AddCon.mk'_surjective y
      conv_lhs => simp only [decomposition, Localization.mk_eq_mk', RingEquiv.toRingHom_eq_coe,
        AddCon.coe_mk', PreLocalizationGrading.emb_apply, AddCon.liftOn_coe,
        PreLocalizationGrading.val_apply]
      erw [IsLocalization.lift_mk'_spec]
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, toSemiring_apply,
        AddCon.coe_mk', PreLocalizationGrading.emb_apply, AddCon.liftOn_coe,
        PreLocalizationGrading.val_apply]
      lift a to 𝒜 m
      · exact hm
      lift b to 𝒜 n
      · exact hn
      erw [decompose_coe, decompose_coe]
      simp only [← Localization.mk_eq_mk', toAddMonoid_of, AddMonoidHom.coe_comp,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, of_mul_of]
      change _ = of (fun i ↦ S.LocalizationGrading i) (n + i)
        ⟨Localization.mk _ _ * Localization.mk _ _, _⟩
      simp only [Localization.mk_mul, one_mul,
        show Localization.mk (b.1 * a.1) (⟨b, hb⟩ : S.toSubmonoid) = Localization.mk a.1 1 by
        simp [Localization.mk_eq_mk_iff, Localization.r_iff_exists]]
      have (k : ι) (h : m = k) (x : Localization S.toSubmonoid) (hx : x ∈ S.LocalizationGrading m):
          of (fun i ↦ S.LocalizationGrading i) k
            (⟨x, h.symm ▸ hx⟩ : S.LocalizationGrading k) =
          of (fun i ↦ S.LocalizationGrading i) m ⟨x, hx⟩ := by
        subst h; rfl
      exact this (n + i) (by rw [← H]; abel) (Localization.mk a 1) _ |>.symm
    | H_plus x y hx hy =>
      simp only [map_add, hx, hy]

noncomputable instance : GradedRing S.LocalizationGrading where

end LocalizationGrading

lemma mem_localizationGrading_iff (x : Localization S.toSubmonoid) (i : ι) :
    x ∈ S.LocalizationGrading i ↔
    ∃ (m n : ι) (_ : m - n = i) (a : 𝒜 m) (b : 𝒜 n) (hb : b.1 ∈ S.toSubmonoid),
    x = Localization.mk a.1 ⟨b, hb⟩ := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
    exact ⟨x.degNum, x.degDen, x.deg_frac_eq, ⟨x.num, x.num_mem⟩, ⟨x.den, x.den_mem⟩,
      x.den.2, rfl⟩
  · rintro ⟨m, n, rfl, ⟨a, ha⟩, ⟨b, hb⟩, hb', rfl⟩
    exact ⟨AddCon.mk' _ ⟨a, ⟨b, hb'⟩, m, n, ha, hb, rfl⟩, rfl⟩

end HomogeneousSubmonoid
