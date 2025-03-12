import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.GradedMulAction

import Project.HomogeneousSubmonoid.Basic
import Project.Grading.Localization

open DirectSum

variable {ι A Q σ  τ : Type*}
variable [AddCommGroup ι] [CommRing A] [AddCommGroup Q]
 [SetLike σ A] [SetLike τ Q]  (𝒜 : ι → σ) (𝒬 : ι → τ) [Module A Q]
 [DecidableEq ι][AddSubgroupClass σ A][AddSubmonoidClass τ Q]
 [GradedRing 𝒜][DirectSum.Decomposition 𝒬][SetLike.GradedSMul 𝒜 𝒬]

def twisting (c i : ι) : τ := 𝒬 (c + i)

notation:max 𝒬"⸨"c"⸩" => twisting 𝒬 c


instance (c: ι): SetLike.GradedSMul (𝒜) (𝒬⸨c⸩) where
  smul_mem :=  by
    rintro (i j : ι) (ai)(qj) (agi) (qgj)
    simp[twisting] at qgj
    simp[twisting]
    have degreesimplif := SetLike.GradedSMul.smul_mem agi qgj
    simp at degreesimplif
    convert degreesimplif using 2
    abel


noncomputable instance (c: ι):
    DirectSum.Gmodule (fun i ↦ (𝒜 i)) (fun i ↦ (𝒬⸨c⸩ i)) where
  add_smul := by
    rintro i j ⟨x, hx⟩ ⟨y, hy⟩ ⟨m, hm⟩
    ext
    simp [add_smul]
  zero_smul := by
    rintro i j ⟨x, hx⟩
    ext
    simp [zero_smul]

noncomputable instance (c: ι):
    Module (⨁ i : ι, 𝒜 i) (⨁ i : ι, 𝒬⸨c⸩ i) :=
  inferInstance

set_option synthInstance.checkSynthOrder false in

noncomputable instance twistingmodulestructure (c: ι):
    Module (A) (⨁ i : ι,  𝒬⸨c⸩ i) :=
  Module.compHom (R := ⨁ i : ι, 𝒜 i) (⨁ i : ι, 𝒬⸨c⸩ i)
    (decomposeRingEquiv 𝒜).toRingHom


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in


noncomputable instance :
    DirectSum.Gmodule (fun i ↦ (𝒜 i)) (fun i ↦ (𝒬 i)) where
  add_smul := by
    rintro i j ⟨x, hx⟩ ⟨y, hy⟩ ⟨m, hm⟩
    ext
    simp [add_smul]
  zero_smul := by
    rintro i j ⟨x, hx⟩
    ext
    simp [zero_smul]

set_option synthInstance.checkSynthOrder false in

noncomputable instance modulestructure :
    Module (A) (⨁ i : ι,  𝒬 i) :=
  Module.compHom (R := ⨁ i : ι, 𝒜 i) (⨁ i : ι, 𝒬 i)
    (decomposeRingEquiv 𝒜).toRingHom

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

def maptwistingshift (c: ι) :
  ( ⨁ (i: ι), (𝒬 i) ) →+
  (letI := twistingmodulestructure 𝒜 𝒬 c
  ⨁ (i : ι), (𝒬⸨c⸩ i)):=DirectSum.toAddMonoid fun i ↦ ({
    toFun := fun (qi : (𝒬 i)) ↦ DirectSum.of _ (i-c) ⟨qi.1,by
     simp[twisting]⟩
    map_zero' := by
     ext g
     simp[coe_of_apply]
     aesop
    map_add' := by
     rintro x y
     ext g
     simp[coe_of_apply]
     aesop


  } : 𝒬 i →+  (letI := twistingmodulestructure 𝒜 𝒬 c
  ⨁ (i : ι), (𝒬⸨c⸩ i)) )

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

def maptwisting (c : ι)  : Q →+ (⨁ (i: ι),  𝒬⸨c⸩ i ) :=
 AddMonoidHom.comp (maptwistingshift  𝒬 c) (decomposeAddEquiv 𝒬).toAddMonoidHom

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

instance (c: ι): DirectSum.Decomposition (𝒬⸨c⸩) where
  decompose' := maptwisting 𝒬 c
  left_inv := by
   rintro x
   induction x using DirectSum.Decomposition.inductionOn 𝒬 with
   |h_zero => simp[coe_of_apply]
   |@h_homogeneous =>
    simp[maptwisting]
    simp[maptwistingshift]
   |@h_add x y ihx ihy =>
    simp [map_add, ihx, ihy]
  right_inv := by
   rintro x
   induction x using DirectSum.induction_on with
      | H_zero => simp[coe_of_apply]
      | H_basic x =>
         simp[maptwisting, maptwistingshift, DirectSum.coeAddMonoidHom_of, DirectSum.coe_of_apply]
         ext
         simp[DirectSum.coe_of_apply]
         split_ifs
         rfl
         rfl
      | H_plus  x y ihx ihy =>
          simp [map_add, ihx, ihy]
