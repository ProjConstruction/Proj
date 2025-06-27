import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.GradedModule

import Project.Grading.Localization

open DirectSum LocalizedModule

variable {ι A Q σ τ : Type*}
variable [AddCommGroup ι] [CommRing A] [AddCommGroup Q]
 [SetLike σ A] [SetLike τ Q]  (𝒜 : ι → σ) (𝒬 : ι → τ)


namespace HomogeneousSubmonoid

variable (S : HomogeneousSubmonoid 𝒜)

variable {𝒜}

structure PreLocalizedModuleGrading (i : ι) where
  num : Q
  den : S.toSubmonoid
  degNum : ι
  degDen : ι
  num_mem : num ∈ 𝒬 degNum
  den_mem : (den : A) ∈ 𝒜 degDen
  deg_frac_eq : degNum - degDen = i

namespace PreLocalizedModuleGrading

 omit  [AddCommGroup Q] in

@[ext]
lemma ext {i : ι} (x y : PreLocalizedModuleGrading 𝒬 S i)
    (num_eq : x.num = y.num) (den_eq : x.den = y.den)
    (degNum_eq : x.degNum = y.degNum)
    (degDen_eq : x.degDen = y.degDen) : x = y := by
  rcases x with ⟨a_x, ⟨b_x, hb_x⟩, mx, nx, hax, hbx, hx⟩
  rcases y with ⟨a_y, ⟨b_y, hb_y⟩, my, ny, hay, hby, hy⟩
  simp only [Subtype.mk.injEq, mk.injEq] at *
  subst num_eq den_eq degNum_eq degDen_eq
  aesop

variable  [AddSubgroupClass τ Q]
instance (i : ι) : Neg (PreLocalizedModuleGrading 𝒬 S i) where
  neg x := ⟨-x.num, x.den, x.degNum, x.degDen, neg_mem x.num_mem, x.den_mem, x.deg_frac_eq⟩



@[simp]
lemma neg_num {i : ι} (x : PreLocalizedModuleGrading 𝒬 S i) : (-x).num = -x.num := rfl

@[simp]
lemma neg_den {i : ι} (x : PreLocalizedModuleGrading 𝒬 S i) : (-x).den = x.den := rfl

@[simp]
lemma neg_degNum {i : ι} (x : PreLocalizedModuleGrading 𝒬 S i) : (-x).degNum = x.degNum := rfl

@[simp]
lemma neg_degDen {i : ι} (x : PreLocalizedModuleGrading 𝒬 S i) : (-x).degDen = x.degDen := rfl

variable [Module A Q]
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]
variable [DirectSum.Decomposition 𝒬] [SetLike.GradedSMul 𝒜 𝒬]

instance (i : ι) : Add (PreLocalizedModuleGrading 𝒬 S i) where
  add x y :=
  { num := (x.den.1 •  y.num : Q) + y.den.1 • x.num
    den := x.den * y.den
    degNum := x.degDen + y.degNum
    degDen := x.degDen + y.degDen
    num_mem := by
      refine add_mem (SetLike.GradedSMul.smul_mem x.den_mem y.num_mem) ?_
      convert SetLike.GradedSMul.smul_mem y.den_mem x.num_mem using 2

      have eq₁ := x.deg_frac_eq
      have eq₂ := y.deg_frac_eq
      rw [sub_eq_iff_eq_add] at eq₁ eq₂
      rw [eq₁, eq₂]
      simp only [vadd_eq_add]
      abel
    den_mem := SetLike.GradedMul.mul_mem x.den_mem y.den_mem
    deg_frac_eq := by simp_rw [← y.deg_frac_eq]; abel }

omit [Decomposition 𝒬] in
@[simp]
lemma add_num {i : ι} (x y : PreLocalizedModuleGrading 𝒬 S i) : (x + y).num = x.den.1 • y.num + y.den.1 • x.num := rfl

omit [Decomposition 𝒬] in
@[simp]
lemma add_den {i : ι} (x y : PreLocalizedModuleGrading 𝒬 S i) : (x + y).den = x.den * y.den := rfl

omit [Decomposition 𝒬] in
@[simp]
lemma add_degNum {i : ι} (x y : PreLocalizedModuleGrading 𝒬 S i) : (x + y).degNum = x.degDen + y.degNum := rfl

omit [Decomposition 𝒬] in
@[simp]
lemma add_degDen {i : ι} (x y : PreLocalizedModuleGrading 𝒬 S i) : (x + y).degDen = x.degDen + y.degDen := rfl


instance (i : ι) : Zero (PreLocalizedModuleGrading 𝒬 S i) where
  zero := ⟨0, 1, i, 0, zero_mem (𝒬 i), SetLike.GradedOne.one_mem, by simp⟩

omit [Module A Q] [SetLike.GradedSMul 𝒜 𝒬] [Decomposition 𝒬] in
@[simp]
lemma zero_num {i : ι} : (0 : PreLocalizedModuleGrading 𝒬 S i).num = 0 := rfl

omit [Module A Q] [SetLike.GradedSMul 𝒜 𝒬] [Decomposition 𝒬] in
@[simp]
lemma zero_den {i : ι} : (0 : PreLocalizedModuleGrading 𝒬 S i).den = 1 := rfl

omit [Module A Q] [SetLike.GradedSMul 𝒜 𝒬] [Decomposition 𝒬] in
@[simp]
lemma zero_degNum {i : ι} : (0 : PreLocalizedModuleGrading 𝒬 S  i).degNum = i := rfl

omit [Module A Q] [SetLike.GradedSMul 𝒜 𝒬] [Decomposition 𝒬] in
@[simp]
lemma zero_degDen {i : ι} : (0 : PreLocalizedModuleGrading 𝒬 S  i).degDen = 0 := rfl

omit [Module A Q] [SetLike.GradedSMul 𝒜 𝒬] [Decomposition 𝒬] in
@[simp]
lemma neg_zero {i : ι} : -(0 : PreLocalizedModuleGrading 𝒬 S  i) = 0 := by ext <;> simp

instance (i : ι) : AddZeroClass (PreLocalizedModuleGrading 𝒬 S  i) where
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp [← x.deg_frac_eq]

instance (i : ι) : AddSemigroup (PreLocalizedModuleGrading 𝒬 S  i) where
  add_assoc x y z := by
    ext
    · simp only [add_num, add_den, Submonoid.coe_mul, smul_add];
      rw [add_assoc, ←  mul_smul, ← mul_smul, ← mul_smul, ← mul_smul, mul_comm z.den.1, mul_comm y.den.1]
    · simp only [add_den, Submonoid.coe_mul]; ring
    · simp only [add_degNum, add_degDen]; abel
    · simp only [add_degDen]; abel


instance (i : ι) : SubNegMonoid (PreLocalizedModuleGrading 𝒬 S i) where
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simps]
def val (i : ι) : (PreLocalizedModuleGrading 𝒬 S i) →+ LocalizedModule S.toSubmonoid Q where
  toFun x := LocalizedModule.mk x.num x.den
  map_zero' := LocalizedModule.zero_mk 1
  map_add' := by intro x y; simp [LocalizedModule.mk_add_mk, add_comm]; rfl

def addCon (i : ι) : AddCon (PreLocalizedModuleGrading 𝒬 S  i) := AddCon.ker (val 𝒬 S i)

instance (i : ι) : Neg (addCon 𝒬 S i).Quotient where
  neg := (addCon 𝒬 S i).lift
    { toFun x := (addCon 𝒬 S i).mk' (-x)
      map_zero' := by
        simp only [neg_zero, AddCon.coe_mk', AddCon.coe_zero]
      map_add' x y := by
        dsimp only [AddCon.coe_mk', AddCon.coe_zero, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk]
        rw [← AddCon.coe_mk', ← map_add]
        erw [AddCon.eq]
        simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_num,
          add_num, neg_add_rev, neg_den, add_den, smul_neg, mk_eq, smul_add, Subtype.exists,
          Submonoid.mk_smul, exists_prop]
        exact ⟨1, S.toSubmonoid.one_mem, by
        rw [add_comm]⟩ } fun x y h => by
    simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_eq,
      Subtype.exists, Submonoid.mk_smul, exists_prop, AddCon.coe_mk', AddCon.eq, neg_num, neg_den,
      smul_neg, neg_inj] at h ⊢
    exact h

instance (i : ι) : AddCommGroup (addCon 𝒬 S i).Quotient where
  neg := _
  zsmul := zsmulRec nsmulRec
  neg_add_cancel := by
    intro a
    obtain ⟨a, rfl⟩ := AddCon.mk'_surjective a
    simp only [AddCon.rel_eq_coe, AddCon.coe_mk', AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    erw [AddCon.eq]
    simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_num, neg_den,
      neg_num, smul_neg, add_neg_cancel, add_den, zero_mk, zero_num, zero_den]
  add_comm := by
    intro a b
    obtain ⟨a, rfl⟩ := AddCon.mk'_surjective a
    obtain ⟨b, rfl⟩ := AddCon.mk'_surjective b
    simp only [AddCon.coe_mk']
    rw [← AddCon.coe_mk', ← map_add, ← map_add]
    erw [AddCon.eq]
    simp only [addCon, val, AddCon.ker_rel, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_num, add_den,
      mk_eq, smul_add, Subtype.exists, Submonoid.mk_smul, exists_prop ]
    use 1
    fconstructor
    · exact Submonoid.one_mem _
    rw [add_comm, mul_comm]


@[simps!]
def emb (i : ι) : (addCon 𝒬 S i).Quotient →+ LocalizedModule S.toSubmonoid Q :=
  AddCon.lift _ (val 𝒬 S i) le_rfl

-- sanity check
example {i : ι} (x y : PreLocalizedModuleGrading 𝒬 S i) :
    addCon 𝒬 S i x y ↔ LocalizedModule.mk x.num x.den = LocalizedModule.mk y.num y.den := by
  simp [addCon]
instance (i : ι) : AddGroup (addCon 𝒬 S i).Quotient := by infer_instance

end PreLocalizedModuleGrading

variable [Module A Q]
variable [AddSubgroupClass σ A]  [AddSubgroupClass τ Q] [DecidableEq ι]
variable [Decomposition 𝒬] [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝒬]

def LocalizedModuleGrading (i : ι) : AddSubgroup (LocalizedModule S.toSubmonoid Q):=
  AddMonoidHom.range  (PreLocalizedModuleGrading.emb 𝒬 S i)

namespace LocalizedModuleGrading

instance : SetLike.GradedSMul (S.LocalizationGrading) (LocalizedModuleGrading 𝒬 S) where
  smul_mem :=  by
    rintro i j _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
    obtain ⟨y, rfl⟩ := AddCon.mk'_surjective y
    simp only [vadd_eq_add, AddCon.coe_mk', PreLocalizationGrading.emb_apply, AddCon.liftOn_coe,
      PreLocalizationGrading.val_apply, PreLocalizedModuleGrading.emb_apply,
      PreLocalizedModuleGrading.val_apply]
    refine ⟨AddCon.mk' _
      { num := x.num • y.num
        den := x.den * y.den
        degNum := x.degNum + y.degNum
        degDen := x.degDen + y.degDen
        num_mem := SetLike.GradedSMul.smul_mem x.num_mem y.num_mem
        den_mem := SetLike.GradedMul.mul_mem x.den_mem y.den_mem
        deg_frac_eq := by
          simp only [← x.deg_frac_eq, ← y.deg_frac_eq, vadd_eq_add]
          abel }, ?_⟩

    simp only [AddCon.coe_mk', PreLocalizedModuleGrading.emb_apply, AddCon.liftOn_coe,
      PreLocalizedModuleGrading.val_apply, mk_smul_mk]

noncomputable instance :
    DirectSum.Gmodule (fun i ↦ S.LocalizationGrading i) (fun i ↦ S.LocalizedModuleGrading 𝒬 i) where
  add_smul := by
    rintro i j ⟨x, hx⟩ ⟨y, hy⟩ ⟨m, hm⟩
    ext
    simp [add_smul]
  zero_smul := by
    rintro i j ⟨x, hx⟩
    ext
    simp [zero_smul]

noncomputable instance :
    Module (⨁ i : ι, S.LocalizationGrading i) (⨁ i : ι, S.LocalizedModuleGrading 𝒬 i) :=
  inferInstance

noncomputable instance :
    Module (Localization S.toSubmonoid) (⨁ i : ι, S.LocalizedModuleGrading 𝒬 i) :=
  Module.compHom (R := ⨁ i : ι, S.LocalizationGrading i) (⨁ i : ι, S.LocalizedModuleGrading 𝒬 i)
    (decomposeRingEquiv S.LocalizationGrading).toRingHom

set_option synthInstance.maxHeartbeats 40000

omit [Decomposition 𝒬] in
@[simp]
lemma localization_smul_directSum_def
    (x : Localization S.toSubmonoid) (y : ⨁ i : ι, S.LocalizedModuleGrading 𝒬 i) :
    x • y = decompose S.LocalizationGrading x • y := rfl

noncomputable instance :
    Module A (⨁ i : ι, S.LocalizedModuleGrading 𝒬 i) :=
  Module.compHom (R := Localization S.toSubmonoid) (⨁ i : ι, S.LocalizedModuleGrading 𝒬 i)
    (algebraMap A _)

omit [Decomposition 𝒬] in
@[simp]
lemma smul_directSum_def (a : A) (x : ⨁ i : ι, S.LocalizedModuleGrading 𝒬 i) :
    a • x = algebraMap A (Localization S.toSubmonoid) a • x := rfl

instance : IsScalarTower A
    (Localization S.toSubmonoid)
    (⨁ (i : ι), LocalizedModuleGrading 𝒬 S i) where
  smul_assoc x y z := by
    rw [localization_smul_directSum_def, smul_directSum_def, ← mul_smul,
      localization_smul_directSum_def, Algebra.smul_def]

variable {𝓐 : ι → AddSubgroup A} [GradedRing 𝓐]
variable (𝓠 : ι → AddSubgroup Q) [Decomposition 𝓠] [SetLike.GradedSMul 𝓐 𝓠]
variable (S : HomogeneousSubmonoid 𝓐)

noncomputable def decompositionAux1 :
    (⨁ i, 𝓠 i) →+ (⨁ (i : ι), (S.LocalizedModuleGrading 𝓠 i)) :=
  toAddMonoid fun i ↦
    { toFun x := of _ i ⟨LocalizedModule.mk x 1,
        ⟨AddCon.mk' _ ⟨x, 1, i, 0, x.2, SetLike.GradedOne.one_mem, by simp⟩, by simp⟩⟩
      map_zero' := by
        simp only [ZeroMemClass.coe_zero, zero_mk]
        ext
        simp [coe_of_apply]
      map_add' := by
        intro x y
        simp only [AddMemClass.coe_add]
        ext
        simp only [coe_of_apply, add_apply, AddSubgroup.coe_add]
        simp_rw [← AddSubgroup.coe_add]
        rw [ite_add_ite]
        simp only [add_zero, SetLike.coe_eq_coe]
        congr 1
        ext
        simp [LocalizedModule.mk_add_mk] }

noncomputable def decompositionAux2 : Q →+ (⨁ (i : ι), (S.LocalizedModuleGrading 𝓠 i)) :=
  @AddMonoidHom.comp Q (⨁ i, 𝓠 i) (⨁ (i : ι), (S.LocalizedModuleGrading 𝓠 i))
    _ _ _
    (decompositionAux1 𝓠 S)
    (decomposeAddEquiv 𝓠)


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
@[simps]
noncomputable def decompositionAux3 : Q →ₗ[A] (⨁ (i : ι), (S.LocalizedModuleGrading 𝓠 i)) where
  toFun := decompositionAux2 𝓠 S
  map_add' x y := (decompositionAux2 𝓠 S).map_add x y
  map_smul' a q := by
    dsimp only [decompositionAux2, decompositionAux1]
    induction a using DirectSum.Decomposition.inductionOn 𝓐 with
    | zero =>
      rw [zero_smul, map_zero, map_zero, smul_directSum_def, map_zero,
        localization_smul_directSum_def, decompose_zero, Gmodule.smul_def, map_zero]
      rfl
    | @homogeneous i a =>
      induction q using DirectSum.Decomposition.inductionOn 𝓠 with
      | zero =>
        rw [smul_zero, map_zero, smul_zero]
      | @homogeneous j q =>
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
        erw [show decomposeAddEquiv 𝓠 (a.1 • q.1) = decompose 𝓠 (a.1 • q.1) by rfl,
          show decomposeAddEquiv 𝓠 q.1 = decompose 𝓠 q.1 by rfl, decompose_coe]
        rw [decompose_of_mem (i := i + j) (hx := SetLike.GradedSMul.smul_mem a.2 q.2),
          toAddMonoid_of, toAddMonoid_of, smul_directSum_def, localization_smul_directSum_def,
          Gmodule.smul_def]
        dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, RingHom.id_apply]
        rw [decompose_of_mem (i := i) (hx := by refine ⟨AddCon.mk' _ ⟨a, 1, i, 0, a.2,
          SetLike.GradedOne.one_mem, by simp⟩, by simp [Localization.mk_one_eq_algebraMap]⟩),
          Gmodule.smulAddMonoidHom_apply_of_of]
        simp_rw [vadd_eq_add]
        ext k
        simp only [coe_of_apply, ← Localization.mk_one_eq_algebraMap,
          GradedMonoid.GSMul.smul, ite_apply, LocalizedModule.mk_smul_mk, mul_one]
      | add q q' hq hq' =>
        rw [smul_add, map_add, hq, hq', map_add, smul_add]
    | add a a' ha ha' =>
      rw [add_smul, map_add, ha, ha', map_add, add_smul]


lemma decompositionAux3_apply_mem_mem {i j : ι} (a : A) (ha : a ∈ 𝓐 i) (q : Q) (hq : q ∈ 𝓠 j) :
    decompositionAux3 𝓠 S (a • q) = of _ (i + j) ⟨LocalizedModule.mk (a • q) 1,
      ⟨AddCon.mk' _ ⟨a • q, 1, i + j, 0, SetLike.GradedSMul.smul_mem ha hq,
        SetLike.GradedOne.one_mem, by simp⟩, by simp⟩⟩ := by
  rw [decompositionAux3_apply, decompositionAux2, AddMonoidHom.comp_apply]
  erw [show decomposeAddEquiv 𝓠 (a • q) = decompose 𝓠 (a • q) by rfl]
  rw [decompose_of_mem (i := i + j) (hx := SetLike.GradedSMul.smul_mem ha hq),
    decompositionAux1, toAddMonoid_of]
  rfl

private noncomputable def inv (x : A) (hx1 : x ∈ S.toSubmonoid) (i : ι) (hx2 : x ∈ 𝓐 i) :
    (⨁ (i : ι), (LocalizedModuleGrading 𝓠 S i)) →+
    (⨁ (i : ι), (LocalizedModuleGrading 𝓠 S i)) :=
  toAddMonoid fun j ↦
    { toFun q := of _ (j - i) ⟨Localization.mk 1 (⟨x, hx1⟩ : S.toSubmonoid) • q, by
        rcases q with ⟨_, ⟨q, rfl⟩⟩
        induction q using AddCon.induction_on with | H q =>
        refine ⟨AddCon.mk' _ ⟨q.num, ⟨x, hx1⟩ * q.den, q.degNum, i + q.degDen, q.num_mem,
          SetLike.mul_mem_graded hx2 q.den_mem, ?_⟩, by simp [LocalizedModule.mk_smul_mk]⟩
        conv_rhs => rw [← q.deg_frac_eq]
        abel⟩
      map_zero' := by
        simp only [ZeroMemClass.coe_zero, smul_zero]
        ext
        simp only [coe_of_apply, zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero,
          ite_eq_right_iff, AddSubgroup.mk_eq_zero, implies_true]
      map_add' := by
        intro q q'
        simp only [AddSubgroup.coe_add, smul_add]
        ext
        simp only [coe_of_apply, add_apply, AddSubgroup.coe_add]
        erw [← AddSubgroup.coe_add]
        rw [ite_add_ite]
        simp only [AddMemClass.mk_add_mk, add_zero] }

omit [Decomposition 𝓠] in
lemma inv_of (x y : A) (hx1 : x ∈ S.toSubmonoid) (i j k jsk jki : ι) (hx2 : x ∈ 𝓐 i) (q : Q)
    (hq : q ∈ 𝓠 j) (hy1 : y ∈ 𝓐 k) (hy2 : y ∈ S.toSubmonoid)
    (hjsk : jsk = j - k) (hjki : jki = j - (k + i)) :
    inv 𝓠 S x hx1 i hx2 (of _ jsk <| ⟨LocalizedModule.mk q (⟨y, hy2⟩ : S.toSubmonoid),
      ⟨AddCon.mk' _ ⟨q, ⟨y, hy2⟩, j, k, hq, hy1, by simp [hjsk]⟩, by simp⟩⟩) =
    of _ jki ⟨LocalizedModule.mk q ⟨x * y, S.toSubmonoid.mul_mem hx1 hy2⟩,
      ⟨AddCon.mk' _ ⟨q, ⟨x * y, S.toSubmonoid.mul_mem hx1 hy2⟩, j, i + k, hq,
        SetLike.mul_mem_graded hx2 hy1, by simp [hjki, add_comm]⟩, by simp⟩⟩ := by
  delta inv
  simp only [toAddMonoid_of, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ext m
  simp only [mk_smul_mk, one_smul, Submonoid.mk_mul_mk, coe_of_apply, hjsk, hjki,
    show j - (k + i) = j - k - i by abel]
  split_ifs <;> simp

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
@[simps]
private noncomputable def linv (x : A) (hx1 : x ∈ S.toSubmonoid) (i : ι) (hx2 : x ∈ 𝓐 i) :
    (⨁ (i : ι), (LocalizedModuleGrading 𝓠 S i)) →ₗ[A]
    (⨁ (i : ι), (LocalizedModuleGrading 𝓠 S i)) where
  toFun := inv 𝓠 S x hx1 i hx2
  map_add' := (inv ..).map_add
  map_smul' := by
    intro a q
    dsimp only [smul_directSum_def, localization_smul_directSum_def, Gmodule.smul_def,
      AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    induction a using DirectSum.Decomposition.inductionOn 𝓐 with
    | zero =>
      simp only [map_zero, decompose_zero, AddMonoidHom.zero_apply]
    | @homogeneous ia a =>
      rw [decompose_of_mem (i := ia) (hx := by
        refine ⟨AddCon.mk' _ ⟨a, 1, ia, 0, a.2, SetLike.GradedOne.one_mem, by simp⟩, by
          simp [← Localization.mk_one_eq_algebraMap]⟩)]
      induction q using DirectSum.induction_on with
      | zero =>
        simp only [map_zero]
      | of j q =>
        simp only [Gmodule.smulAddMonoidHom_apply_of_of, vadd_eq_add]
        obtain ⟨_, ⟨q, rfl⟩⟩ := q
        induction q using AddCon.induction_on with | H q =>
        simp only [PreLocalizedModuleGrading.emb_apply, AddCon.liftOn_coe,
          PreLocalizedModuleGrading.val_apply]
        rw [inv_of (hq := q.num_mem) (hy1 := q.den_mem) (hjsk := q.deg_frac_eq.symm) (hjki := rfl)]
        rw [Gmodule.smulAddMonoidHom_apply_of_of]
        simp only [vadd_eq_add]
        simp_rw [← Localization.mk_one_eq_algebraMap]
        simp only [GradedMonoid.GSMul.smul, vadd_eq_add, LocalizedModule.mk_smul_mk, one_mul]
        rw [inv_of (hq := SetLike.GradedSMul.smul_mem a.2 q.num_mem) (hy1 := q.den_mem)]
        · simp only [← q.deg_frac_eq, vadd_eq_add]
          abel
        · simp only [vadd_eq_add]
          abel
      | add q q' hq hq' =>
        simp only [map_add, hq, hq']
    | add a a' ha ha' =>
      simp only [map_add, decompose_add, AddMonoidHom.add_apply, ha, ha']

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
noncomputable def decomposition :
    (LocalizedModule S.toSubmonoid Q) →ₗ[A] (⨁ i : ι, S.LocalizedModuleGrading 𝓠 i) :=
  LocalizedModule.lift _ (decompositionAux3 𝓠 S) <| by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := S.homogeneous hx
    rw [Module.End.isUnit_iff, Function.bijective_iff_has_inverse]
    use linv 𝓠 S x hx i hi
    constructor
    · intro q
      rw [Module.algebraMap_end_apply]
      rw [smul_directSum_def, localization_smul_directSum_def]
      rw [decompose_of_mem (i := i) (hx := by
        refine ⟨AddCon.mk' _ ⟨x, 1, i, 0, hi, SetLike.GradedOne.one_mem, by simp⟩, by
          simp [← Localization.mk_one_eq_algebraMap]⟩)]
      induction q using DirectSum.induction_on with
      | zero =>
        simp only [smul_zero, map_zero]
      | of j y =>
        obtain ⟨_, ⟨y, rfl⟩⟩ := y
        induction y using AddCon.induction_on with | H y =>
        simp only [PreLocalizedModuleGrading.emb_apply, AddCon.liftOn_coe,
          PreLocalizedModuleGrading.val_apply, Gmodule.smul_def,
          Gmodule.smulAddMonoidHom_apply_of_of, vadd_eq_add, GradedMonoid.GSMul.smul,
          algebraMap_smul, linv_apply]
        simp_rw [LocalizedModule.smul'_mk]
        rw [inv_of (hq := SetLike.GradedSMul.smul_mem hi y.num_mem) (hy1 := y.den_mem)
          (hjki := rfl)]
        · simp only [vadd_eq_add]
          ext m
          simp only [coe_of_apply, show i + y.degNum - (y.degDen + i) = y.degNum - y.degDen by abel,
            ← y.deg_frac_eq]
          split_ifs
          · simp only [mk_eq, Submonoid.mk_smul, Subtype.exists, exists_prop]
            refine ⟨1, one_mem _, ?_⟩
            simp only [one_smul, mul_smul]
            rw [smul_comm]
            rfl
          · simp
        simp only [← y.deg_frac_eq, vadd_eq_add]
        abel
      | add x y hx hy =>
        simp only [smul_add, Gmodule.smul_def, linv_apply, map_add]
        erw [hx, hy]
    · intro q
      rw [Module.algebraMap_end_apply]
      rw [smul_directSum_def, localization_smul_directSum_def]
      rw [decompose_of_mem (i := i) (hx := by
        refine ⟨AddCon.mk' _ ⟨x, 1, i, 0, hi, SetLike.GradedOne.one_mem, by simp⟩, by
          simp [← Localization.mk_one_eq_algebraMap]⟩)]
      induction q using DirectSum.induction_on with
      | zero =>
        simp only [smul_zero, map_zero]
      | of j y =>
        obtain ⟨_, ⟨y, rfl⟩⟩ := y
        induction y using AddCon.induction_on with | H y =>
        simp only [PreLocalizedModuleGrading.emb_apply, AddCon.liftOn_coe,
          PreLocalizedModuleGrading.val_apply, linv_apply, Gmodule.smul_def]
        rw [inv_of (hq := y.num_mem) (hy1 := y.den_mem) (hjki := rfl)]
        · simp only [← Localization.mk_one_eq_algebraMap, Gmodule.smulAddMonoidHom_apply_of_of,
          vadd_eq_add, GradedMonoid.GSMul.smul, mk_smul_mk, one_mul]
          ext m
          simp only [coe_of_apply]
          simp_rw [show i + (y.degNum - (y.degDen + i)) = y.degNum - y.degDen by abel,
            show y.degNum - y.degDen = j by rw [y.deg_frac_eq]]
          split_ifs
          · simp only [mk_eq, Submonoid.mk_smul, Subtype.exists, exists_prop]
            refine ⟨1, one_mem _, ?_⟩
            simp only [one_smul, mul_smul]
            rw [smul_comm]
            rfl
          · simp
        · exact y.deg_frac_eq.symm
      | add x y hx hy =>
        simp only [smul_add, Gmodule.smul_def, linv_apply, map_add] at hx hy ⊢
        erw [hx, hy]

lemma decomposition_homogeneous_mk
    {i j : ι} (a : Q) (ha : a ∈ 𝓠 i) (b : S.toSubmonoid) (hb : b.1 ∈ 𝓐 j) :
    decomposition 𝓠 S (LocalizedModule.mk a b) =
    of _ (i - j) ⟨LocalizedModule.mk a b, ⟨AddCon.mk' _ ⟨a, b, i, j, ha, hb, rfl⟩, rfl⟩⟩ := by
  delta decomposition
  rw [LocalizedModule.lift_mk]
  simp only [decompositionAux3_apply]
  delta decompositionAux2
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    decomposeAddEquiv_apply]
  rw [decompose_of_mem (hx := ha)]
  delta decompositionAux1
  rw [toAddMonoid_of]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]

  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
  rw [smul_directSum_def, localization_smul_directSum_def]
  rw [decompose_of_mem (i := j) (hx := by
    refine ⟨AddCon.mk' _ ⟨b, 1, j, 0, hb, SetLike.GradedOne.one_mem, by simp⟩, by
      simp [Localization.mk_one_eq_algebraMap]⟩)]
  simp only [Gmodule.smul_def, Gmodule.smulAddMonoidHom_apply_of_of, vadd_eq_add]
  ext m
  simp only [coe_of_apply, add_sub_cancel]
  split_ifs
  · simp only [SetLike.coe_GSMul, algebraMap_smul, smul'_mk, mk_eq, one_smul, Subtype.exists,
    Submonoid.mk_smul, exists_prop]
    refine ⟨1, one_mem _, ?_⟩
    simp only [one_smul]
    rfl
  · simp

set_option synthInstance.maxHeartbeats 500000 in
set_option maxHeartbeats 2000000 in
lemma decomposition_left_inv (x) :
    (DirectSum.coeAddMonoidHom (LocalizedModuleGrading 𝓠 S)) ((decomposition 𝓠 S) x) = x := by
  induction x using LocalizedModule.induction_on with | h x y =>
  rcases y with ⟨y, hy⟩
  induction x using DirectSum.Decomposition.inductionOn 𝓠 with
  | zero =>
    rw [LocalizedModule.zero_mk, map_zero, map_zero]
  | @homogeneous i x =>
    obtain ⟨j, hj⟩ := S.homogeneous hy
    rw [decomposition_homogeneous_mk 𝓠 S x.1 x.2 ⟨y, hy⟩ hj]
    simp only [coeAddMonoidHom_of]
  | add a a' h h' =>
    rw [show LocalizedModule.mk (a + a') ⟨y, hy⟩ =
      LocalizedModule.mk a ⟨y, hy⟩ + LocalizedModule.mk a' ⟨y, hy⟩ by
      simp only [mk_add_mk, Submonoid.mk_smul, Submonoid.mk_mul_mk, mk_eq, smul_add, Subtype.exists,
        exists_prop]
      refine ⟨1, one_mem _, ?_⟩
      simp only [one_smul, mul_smul]]
    conv_rhs => rw [← h, ← h']
    rw [map_add]
    convert (DirectSum.coeAddMonoidHom (LocalizedModuleGrading 𝓠 S)).map_add _ _

example : true := rfl


set_option synthInstance.maxHeartbeats 500000 in
set_option maxHeartbeats 2000000 in
lemma decomposition_right_inv (x) :
    (decomposition 𝓠 S) ((DirectSum.coeAddMonoidHom (LocalizedModuleGrading 𝓠 S)) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    simp only [coeAddMonoidHom_of]
    obtain ⟨y, hy⟩ := x.2
    have hy' : x = ⟨_, ⟨y, rfl⟩⟩ := by ext; exact hy.symm
    rw [← hy, hy']
    clear hy hy' x
    obtain ⟨⟨a, ⟨b, hb⟩, m, n, hm, hn, H⟩, rfl⟩ := AddCon.mk'_surjective y
    simp only [decomposition, AddCon.coe_mk', PreLocalizedModuleGrading.emb_apply,
      AddCon.liftOn_coe, PreLocalizedModuleGrading.val_apply]
    rw [lift_mk]

    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
    rw [smul_directSum_def, localization_smul_directSum_def]
    rw [decompose_of_mem (i := n) (hx := by
      refine ⟨AddCon.mk' _ ⟨b, 1, n, 0, hn, SetLike.GradedOne.one_mem, by simp⟩, by
        simp [Localization.mk_one_eq_algebraMap]⟩)]

    simp only [decompositionAux3_apply, Gmodule.smul_def, Gmodule.smulAddMonoidHom_apply_of_of,
      vadd_eq_add]
    delta decompositionAux2 decompositionAux1
    simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
      decomposeAddEquiv_apply]
    rw [decompose_of_mem (hx := hm), toAddMonoid_of]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    ext k
    simp only [coe_of_apply, ← H, add_sub_cancel]
    split_ifs
    · simp only [SetLike.coe_GSMul, algebraMap_smul]
      rw [LocalizedModule.smul'_mk, mk_eq]
      refine ⟨1, ?_⟩
      simp only [Submonoid.mk_smul, one_smul]
    · simp
  | add x y hx hy =>
    simp [map_add, hx, hy]

noncomputable instance : DirectSum.Decomposition (S.LocalizedModuleGrading 𝓠) where
  decompose' := LocalizedModuleGrading.decomposition 𝓠 S
  left_inv x := decomposition_left_inv 𝓠 S x
  right_inv x := decomposition_right_inv 𝓠 S x


-- sanity check
example (x : LocalizedModule S.toSubmonoid Q) (i : ι) :
    x ∈ S.LocalizedModuleGrading 𝓠 i ↔
    ∃ (m n : ι) (_ : m - n = i) (a : 𝓠 m) (b : 𝓐 n) (hb : b.1 ∈ S.toSubmonoid),
    x = LocalizedModule.mk a.1 (⟨b, hb⟩ : S.toSubmonoid) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
    exact ⟨x.degNum, x.degDen, x.deg_frac_eq, ⟨x.num, x.num_mem⟩, ⟨x.den, x.den_mem⟩,
      x.den.2, rfl⟩
  · rintro ⟨m, n, rfl, ⟨a, ha⟩, ⟨b, hb⟩, hb', rfl⟩
    exact ⟨AddCon.mk' _ ⟨a, ⟨b, hb'⟩, m, n, ha, hb, rfl⟩, rfl⟩

end LocalizedModuleGrading

end HomogeneousSubmonoid
