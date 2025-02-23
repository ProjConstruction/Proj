import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.Abel

import Project.ForMathlib.SubgroupBasic

namespace Submonoid

variable {A : Type*} [CommMonoid A]

open Pointwise in
@[to_additive]
instance instMul : Mul (Submonoid A) where
  mul S T :=
  { carrier := S * T
    mul_mem' {a b} ha hb := by
      simp only [Set.mem_mul, SetLike.mem_coe] at ha hb ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := ha
      obtain ⟨z, hz, w, hw, rfl⟩ := hb
      exact ⟨x * z, mul_mem hx hz, y * w, mul_mem hy hw, by
        rw [mul_assoc x y, ← mul_assoc y z, mul_comm y z, mul_assoc x, mul_assoc z]⟩
    one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩ }

@[to_additive]
lemma mem_mul_iff {S T : Submonoid A} {x : A} :
    x ∈ S * T ↔ ∃ y ∈ S, ∃ z ∈ T, y * z = x := Iff.rfl

lemma left_le_mul {S T : Submonoid A} : S ≤ S * T := by
  intro x hx
  simp only [mem_mul_iff]
  exact ⟨x, hx, 1, one_mem _, by simp⟩

lemma right_le_mul {S T : Submonoid A} : T ≤ S * T := by
  intro x hx
  simp only [mem_mul_iff]
  exact ⟨1, one_mem _, x, hx, by simp⟩

lemma mul_le_mul {S S' T T' : Submonoid A} (hS : S ≤ S') (hT : T ≤ T') : S * T ≤ S' * T' := by
  intro x hx
  simp only [mem_mul_iff] at hx ⊢
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hS hy, z, hT hz, rfl⟩

instance instOne : One (Submonoid A) where
  one := ⊥

lemma one_eq_bot : (1 : Submonoid A) = ⊥ := rfl

instance : CommMonoid (Submonoid A) where
  mul_assoc R S T := by
    ext a
    simp only [mem_mul_iff, exists_exists_and_exists_and_eq_and]
    fconstructor
    · rintro ⟨r, hr, s, hs, t, ht, rfl⟩
      exact ⟨r, hr, s, hs, t, ht, by simp [mul_assoc]⟩
    · rintro ⟨r, hr, s, hs, t, ht, rfl⟩
      exact ⟨r, hr, s, hs, t, ht, by simp [mul_assoc]⟩
  one_mul R := by
    ext x
    simp [one_eq_bot, mem_bot, mem_mul_iff]
  mul_one R := by
    ext x
    simp [one_eq_bot, mem_bot, mem_mul_iff]
  mul_comm S T := by
    ext x
    simp only [mem_mul_iff]
    fconstructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨t, ht, s, hs, by simp [mul_comm]⟩
    · rintro ⟨t, ht, s, hs, rfl⟩
      exact ⟨s, hs, t, ht, by simp [mul_comm]⟩

lemma closure_union_eq_mul (s t : Set A) : Submonoid.closure (s ∪ t) = Submonoid.closure s * Submonoid.closure t := by
  classical
  refine le_antisymm ?_ ?_
  · rw [closure_le]
    rintro x (hx|hx)
    · exact left_le_mul <| subset_closure hx
    · exact right_le_mul <| subset_closure hx
  · rintro _ ⟨x, hx, y, hy, (rfl : x * y = _)⟩
    rw [SetLike.mem_coe, Submonoid.mem_closure_iff] at hx
    rw [SetLike.mem_coe, Submonoid.mem_closure_iff] at hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [← Finsupp.prod_add_index]
    swap
    · simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq, pow_zero, implies_true]
    swap
    · simp [pow_add]
    refine prod_mem _ fun i hi ↦ ?_
    simp only [Finsupp.coe_add, Pi.add_apply]
    have mem := Finsupp.support_add hi
    simp only [Finset.mem_union] at mem
    refine pow_mem (subset_closure <| mem.recOn ?_ ?_) _ <;> intro hi
    · specialize hx _ hi; exact Or.inl ‹_›
    · specialize hy _ hi; exact Or.inr ‹_›

lemma FG.mul {S T : Submonoid A} (hS : S.FG) (hT : T.FG) : (S * T).FG := by
  rw [fg_iff] at hS hT ⊢
  obtain ⟨s, rfl, hs⟩ := hS
  obtain ⟨t, rfl, ht⟩ := hT
  refine ⟨s ∪ t, closure_union_eq_mul s t, hs.union ht⟩

end Submonoid

namespace Localization

open TensorProduct

variable {A : Type*} [CommRing A] (S T : Submonoid A)
variable (A_S : Type*) [CommRing A_S] [Algebra A A_S] [IsLocalization S A_S]
variable (A_T : Type*) [CommRing A_T] [Algebra A A_T] [IsLocalization T A_T]

lemma prod_mk {ι : Type*} (s : Finset ι) (t : ι → A) (t' : ι → S) :
    ∏ i ∈ s, mk (t i) (t' i) =
    mk (∏ i ∈ s, t i) (∏ i ∈ s, t' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Eq.symm mk_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, mk_mul, mk_eq_mk_iff, r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_finset_prod, one_mul, Submonoid.coe_mul]
    rw [Finset.prod_insert hi, Finset.prod_insert hi]

lemma split_den (x : A) (s t : S) :
    mk x s * mk 1 t = mk x (s * t) := by
  rw [mk_mul, mk_eq_mk_iff, r_iff_exists]
  use 1
  simp

noncomputable def mulToTensor : Localization (S * T) →ₐ[A] (Localization S ⊗[A] Localization T) :=
  IsLocalization.liftAlgHom
    (R := A)
    (M := S * T)
    (f := Algebra.ofId A (Localization S ⊗[A] Localization T)) <| by
    rintro ⟨_, ⟨s, hs, t, ht, rfl⟩⟩
    simp only [map_mul, IsUnit.mul_iff]
    fconstructor
    · fapply isUnit_of_mul_eq_one
      · exact Localization.mk 1 ⟨s, hs⟩ ⊗ₜ[A] 1
      · simp only [Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.smul_def, smul_mk, smul_eq_mul, mul_one]
        rw [mk_self ⟨s, hs⟩]
        rfl
    · fapply isUnit_of_mul_eq_one
      · exact 1 ⊗ₜ[A] Localization.mk 1 ⟨t, ht⟩
      · simp only [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc,
        one_mul, smul_tmul', smul_tmul, smul_mk, smul_eq_mul, mul_one]
        rw [mk_self ⟨t, ht⟩]
        rfl

variable {S T} in
@[simp]
lemma mulToTensor_mk (a s t : A) (hs : s ∈ S) (ht : t ∈ T) :
    mulToTensor S T (Localization.mk a ⟨s * t, ⟨_, hs, _, ht, rfl⟩⟩) =
    (.mk a ⟨s, hs⟩) ⊗ₜ[A] (.mk 1 ⟨t, ht⟩) := by
  conv_lhs => simp only [mulToTensor, mk_eq_mk', IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe,
    IsLocalization.lift_mk', RingHom.coe_coe, Algebra.ofId_apply,
    Algebra.TensorProduct.algebraMap_apply, RingHom.toMonoidHom_eq_coe]
  rw [Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]
  simp only [MonoidHom.restrict_apply, MonoidHom.coe_coe, RingHom.coe_coe, Algebra.ofId_apply,
    Algebra.TensorProduct.algebraMap_apply, map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [← map_mul, mul_comm (mk _ _) (algebraMap _ _ _), ← Algebra.smul_def, mul_comm s t, mul_smul]
  rw [show mk a ⟨s, hs⟩ = a • mk 1 ⟨s, hs⟩ by simp [smul_mk]]
  rw [smul_tmul, smul_mk, smul_mk, smul_mk]
  simp only [smul_eq_mul, mul_one]
  rw [mk_self ⟨t, ht⟩]
  congr 1
  simp only [← mk_one_eq_algebraMap, mk_eq_mk_iff, r_iff_exists, OneMemClass.coe_one, one_mul,
    exists_const]

variable {S T} in
@[simp]
lemma mulToTensor_mk' (a s : A) (hs : s ∈ S) :
    mulToTensor S T (Localization.mk a ⟨s, Submonoid.left_le_mul hs⟩) =
    (.mk a ⟨s, hs⟩) ⊗ₜ[A] 1 := by
  convert mulToTensor_mk (T := T) a s 1 hs (one_mem _)
  · simp
  · rw [mk_self ⟨1, one_mem _⟩]

variable {S T} in
@[simp]
lemma mulToTensor_mk'' (a t : A) (ht : t ∈ T) :
    mulToTensor S T (Localization.mk a ⟨t, Submonoid.right_le_mul ht⟩) =
    .mk a 1 ⊗ₜ[A] (.mk 1 ⟨t, ht⟩) := by
  convert mulToTensor_mk (S := S) a 1 t (one_mem _) ht
  simp

noncomputable def tensorToLocalization :
    (Localization S ⊗[A] Localization T) →ₐ[A] Localization (S * T) :=
  Algebra.TensorProduct.lift
    (IsLocalization.liftAlgHom (M := S) (f := Algebra.ofId _ _) <| by
      intro s
      fapply isUnit_of_mul_eq_one
      · exact Localization.mk 1 (Submonoid.inclusion Submonoid.left_le_mul s)
      simp only [Algebra.ofId_apply, ← mk_one_eq_algebraMap, mk_mul, mul_one, one_mul]
      erw [mk_self (Submonoid.inclusion (Submonoid.left_le_mul) s)])
    (IsLocalization.liftAlgHom (M := T) (f := Algebra.ofId _ _) <| by
      intro s
      fapply isUnit_of_mul_eq_one
      · exact Localization.mk 1 (Submonoid.inclusion Submonoid.right_le_mul s)
      simp only [Algebra.ofId_apply, ← mk_one_eq_algebraMap, mk_mul, mul_one, one_mul]
      erw [mk_self (Submonoid.inclusion (Submonoid.right_le_mul) s)]) <| by
    intro x y
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨a, s⟩
    induction y using Localization.induction_on with | H y =>
    rcases y with ⟨b, t⟩
    simp only [mk_eq_mk', IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe,
      IsLocalization.lift_mk', RingHom.coe_coe, Algebra.ofId_apply, RingHom.toMonoidHom_eq_coe,
      commute_iff_eq]
    simp only [← mk_one_eq_algebraMap, ← mul_assoc]
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_comm _ (mk b 1),
      ← mul_assoc, Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight,
      IsUnit.coe_liftRight]
    simp only [MonoidHom.restrict_apply, MonoidHom.coe_coe, RingHom.coe_coe, Algebra.ofId_apply, ←
      mk_one_eq_algebraMap]
    conv_rhs => rw [mul_comm _ (mk _ _), mul_comm _ (mk _ _)]
    rw [← mul_assoc, eq_comm,  ← mul_assoc, ← mul_assoc, Units.mul_inv_eq_iff_eq_mul,
      mul_comm _ (mk _ _), ← mul_assoc, ← mul_assoc, ← mul_assoc, Units.mul_inv_eq_iff_eq_mul,
      IsUnit.coe_liftRight, IsUnit.coe_liftRight]
    simp only [mk_mul, mul_one, MonoidHom.restrict_apply, MonoidHom.coe_coe, RingHom.coe_coe,
      Algebra.ofId_apply, ← mk_one_eq_algebraMap]
    congr 1
    ring

@[simp]
lemma tensorToLocalization_tmul_mk_mk (a b : A) (s : S) (t : T) :
    tensorToLocalization S T (.mk a s ⊗ₜ .mk b t) =
    .mk (a * b) ⟨s * t, ⟨_, s.2, _, t.2, rfl⟩⟩ := by
  simp only [tensorToLocalization, mk_eq_mk', Algebra.TensorProduct.lift_tmul,
    IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe, IsLocalization.lift_mk',
    RingHom.coe_coe, Algebra.ofId_apply, RingHom.toMonoidHom_eq_coe, ← mul_assoc,
    Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight, MonoidHom.restrict_apply, MonoidHom.coe_coe]
  rw [mul_comm _ (algebraMap _ _ _), ← mul_assoc, Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]
  simp only [← mk_one_eq_algebraMap, mk_mul, mul_one, ← mk_eq_mk', MonoidHom.restrict_apply,
    MonoidHom.coe_coe, RingHom.coe_coe, Algebra.ofId_apply, mk_eq_mk_iff, r_iff_exists,
    OneMemClass.coe_one, one_mul, Subtype.exists, exists_prop]
  refine ⟨1, one_mem _, by simp only [one_mul]; ring⟩

@[simp]
lemma tensorToLocalization_tmul_mk_one (a : A) (s : S) :
    tensorToLocalization S T (.mk a s ⊗ₜ 1) =
    .mk a ⟨s, ⟨_, s.2, _, one_mem _, by simp⟩⟩ := by
  convert tensorToLocalization_tmul_mk_mk _ _ a 1 s 1
  · exact Eq.symm mk_one
  · simp
  · simp

@[simp]
lemma tensorToLocalization_tmul_one_mk (b : A) (t : T) :
    tensorToLocalization S T (1 ⊗ₜ .mk b t) =
    .mk b ⟨t, ⟨_, one_mem _, _, t.2, by simp⟩⟩ := by
  convert tensorToLocalization_tmul_mk_mk _ _ 1 b 1 t
  · exact Eq.symm mk_one
  · simp
  · simp

noncomputable def mulEquivTensor : Localization (S * T) ≃ₐ[A] (Localization S ⊗[A] Localization T) :=
  AlgEquiv.ofAlgHom (mulToTensor S T) (tensorToLocalization S T)
    (by
      ext x
      · induction x using Localization.induction_on with | H x =>
        rcases x with ⟨a, s⟩
        simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
          show (1 : Localization T) = .mk 1 1 from mk_self 1 |>.symm,
          tensorToLocalization_tmul_mk_mk, mul_one, OneMemClass.coe_one, SetLike.coe_mem,
          mulToTensor_mk', Subtype.coe_eta, AlgHom.id_comp]
      · induction x using Localization.induction_on with | H x =>
        rcases x with ⟨a, t⟩
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply,
          show (1 : Localization S) = .mk 1 1 from mk_self 1 |>.symm,
          tensorToLocalization_tmul_mk_mk, one_mul, OneMemClass.coe_one, SetLike.coe_mem,
          mulToTensor_mk'', Subtype.coe_eta, AlgHom.coe_id, id_eq]
        rw [show mk a (1 : S) = a • 1 by rw [mk_one_eq_algebraMap, Algebra.smul_def, mul_one],
          smul_tmul, smul_mk, smul_eq_mul, mul_one]
        erw [mk_self (1 : S)])
    (by
      ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨a, ⟨_, ⟨s, hs, t, ht, rfl⟩⟩⟩
      simp only [AlgHom.coe_comp, Function.comp_apply, mulToTensor_mk a s t hs ht,
        tensorToLocalization_tmul_mk_mk, mul_one, AlgHom.coe_id, id_eq])

@[simp]
lemma mulEquivTensor_apply (x : Localization (S * T)) :
    mulEquivTensor S T x = mulToTensor S T x := rfl

@[simp]
lemma mulEquivTensor_symm_apply (x) :
    (mulEquivTensor S T).symm x = tensorToLocalization S T x := rfl


variable {S T} in
noncomputable def mapEq (eq : S = T) : Localization S →ₐ[A] Localization T :=
  IsLocalization.liftAlgHom
    (M := S)
    (f := Algebra.ofId A (Localization T)) <| by
    rintro ⟨y, hy⟩
    simp only [Algebra.ofId_apply]
    fapply isUnit_of_mul_eq_one
    · exact Localization.mk 1 ⟨y, eq ▸ hy⟩
    · simp only [← mk_one_eq_algebraMap, mk_mul, mul_one, one_mul]
      exact mk_self ⟨y, _⟩

@[simp]
lemma mapEq_mk (eq : S = T) (x) (y) : mapEq eq (Localization.mk x y) = Localization.mk x ⟨y, eq ▸ y.2⟩ := by
  simp only [mapEq, mk_eq_mk', IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe,
    IsLocalization.lift_mk', RingHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    Units.mul_inv_eq_iff_eq_mul]
  rw [IsUnit.coe_liftRight]
  simp only [Algebra.ofId_apply, ← mk_one_eq_algebraMap, ← mk_eq_mk', MonoidHom.restrict_apply,
    MonoidHom.coe_coe, RingHom.coe_coe, mk_mul, mul_one, mk_eq_mk_iff, r_iff_exists,
    OneMemClass.coe_one, one_mul, Subtype.exists, exists_prop]
  refine ⟨1, one_mem _, by ring⟩

variable {S T} in
noncomputable def equivEq (eq : S = T) : Localization S ≃ₐ[A] Localization T :=
  AlgEquiv.ofAlgHom (mapEq eq) (mapEq eq.symm)
    (by
      ext a
      induction a using Localization.induction_on with | H x =>
      simp)
    (by
      ext a
      induction a using Localization.induction_on with | H x =>
      simp)

@[simp]
lemma equivEq_apply (eq : S = T) (x) : (equivEq eq) x = mapEq eq x := rfl

@[simp]
lemma equivEq_symm_apply (eq : S = T) (x) : (equivEq eq).symm x = mapEq eq.symm x := rfl

end Localization
