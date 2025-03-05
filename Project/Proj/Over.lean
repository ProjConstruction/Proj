import Project.Grading.Potions
import Project.ForMathlib.SchemeIsOpenImmersion

import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GoodPotionIngredient

universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ ℱ' : Set (GoodPotionIngredient 𝒜))

scoped notation "SpecBase"ℬ => Spec (CommRingCat.of (ℬ 0))

def stalkIso (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
    (Proj ℱ).presheaf.stalk (((glueData ℱ).ι S).base x) ≅
    (Spec (CommRingCat.of S.1.Potion)).presheaf.stalk x := by
  have ioi : IsOpenImmersion ((glueData ℱ).ι S) := inferInstance
  rw [isOpenImmersion_iff_stalk] at ioi
  haveI := ioi.2 x
  exact asIso (Scheme.Hom.stalkMap ((glueData ℱ).ι S) x)

variable {ℱ} in
def Ddagger (S : ℱ) : Scheme :=
  (Proj ℱ).restrict (U := Spec (CommRingCat.of <| S.1.Potion)) (f := ((glueData ℱ).ι S).base) <| by
    have : IsOpenImmersion ((glueData ℱ).ι S) := inferInstance
    exact AlgebraicGeometry.Scheme.Hom.isOpenEmbedding _

variable {ℱ} in
def DdaggerIsoSpec (S : ℱ) : Ddagger S ≅ (Spec (CommRingCat.of S.1.Potion)) :=
  IsOpenImmersion.isoRestrict _ |>.symm

variable {ℱ} in
abbrev DdaggerToProj (S : ℱ) : Ddagger S ⟶ Proj ℱ := Scheme.ofRestrict _ _

instance (S : ℱ) : (Ddagger S).Over (Proj ℱ) where
  hom := DdaggerToProj S

lemma Ddagger_structureMorphism_over_proj_eq (S : ℱ) :
    (Ddagger S) ↘ (Proj ℱ) = DdaggerToProj S := rfl

instance (S : ℱ) : (Ddagger S).Over (SpecBase 𝒜) where
  hom := (DdaggerIsoSpec S).hom ≫ Spec.map (CommRingCat.ofHom <| algebraMap _ _)

variable {ℱ} in
lemma Ddagger_structureMorphism_over_spec_eq (S : ℱ) :
    (Ddagger S) ↘ (SpecBase 𝒜) = (DdaggerIsoSpec S).hom ≫ Spec.map (CommRingCat.ofHom <| algebraMap _ _) := rfl

def projHomOfLE (le : ℱ ⊆ ℱ') : Proj ℱ ⟶ Proj ℱ' :=
  Multicoequalizer.desc _ _
    (fun S ↦ (glueData ℱ').ι ⟨S.1, le S.2⟩) <| by
    intro S
    simp only [GlueData.diagram_left, GlueData.diagram_right]
    change (Spec.map _) ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
    simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid, ← Spec.map_comp,
      RingEquiv.toRingHom_eq_coe]
    have : Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _ :=
      (glueData ℱ').glue_condition ⟨S.1.1, le S.1.2⟩  ⟨S.2.1, le S.2.2⟩
    dsimp only at this
    simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid,
      RingEquiv.toRingHom_eq_coe, ← Spec.map_comp_assoc] at this
    exact this.symm

@[reassoc (attr := simp)]
lemma projHomOfLE_comp_ι (le : ℱ ⊆ ℱ') (S : ℱ) :
    (glueData ℱ).ι S ≫ projHomOfLE ℱ ℱ' le = (glueData ℱ').ι ⟨S.1, le S.2⟩ := by
  erw [Multicoequalizer.π_desc]

lemma projHomOfLE_eq_apply (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
    (projHomOfLE ℱ ℱ' le).base (((glueData ℱ).ι S).base x) = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base x := by
  exact congr($(projHomOfLE_comp_ι ℱ ℱ' le S).base x)

-- lemma projHomOfLE_stalkMap (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
--     Scheme.Hom.stalkMap (projHomOfLE ℱ ℱ' le) (((glueData ℱ).ι S).base x) =
--     _ ≫ (stalkIso ℱ' ⟨S.1, le S.2⟩ x).hom ≫ (stalkIso ℱ S x).inv := by sorry

instance (le : ℱ ⊆ ℱ') : IsOpenImmersion (projHomOfLE ℱ ℱ' le) := by
  rw [AlgebraicGeometry.isOpenImmersion_isLocalAtTarget.iff_of_openCover' (projHomOfLE ℱ ℱ' le)
    (glueData ℱ').openCover]
  simp only [Scheme.Cover.pullbackCover_obj, Scheme.Cover.pullbackHom]
  intro S
  rw [isOpenImmersion_iff_stalk]
  sorry
-- Ideal ℱ := {S * S'}
lemma proj_isIso_projClosure :
    IsIso (projHomOfLE _ _ Subsemigroup.subset_closure :
      Proj ℱ ⟶ Proj (𝒜 := 𝒜) (Subsemigroup.closure ℱ)) := by
  apply (config := { allowSynthFailures := true }) AlgebraicGeometry.IsOpenImmersion.to_iso
  rw [TopCat.epi_iff_surjective]
  intro x
  have := (glueData (Subsemigroup.closure ℱ : Set (GoodPotionIngredient 𝒜))).ι
  sorry

def over : Proj ℱ ⟶ SpecBase 𝒜 :=
  Multicoequalizer.desc _ _
    (fun S ↦ (Spec.map <| CommRingCat.ofHom <| algebraMap _ _)) <| by
    intro S
    simp only [GlueData.diagram_left, GlueData.diagram_right]
    change (Spec.map _) ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
    simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid, ← Spec.map_comp,
      RingEquiv.toRingHom_eq_coe]
    congr 1

instance : Scheme.Over (X := Proj ℱ) (SpecBase 𝒜) where
  hom :=  over ℱ

lemma proj_structureMorphism_eq : (Proj ℱ) ↘ (SpecBase 𝒜) = over ℱ := rfl

instance (S : ℱ) : IsOverTower (Ddagger S) (Proj ℱ) (SpecBase 𝒜) := by
  simp only [Scheme.Hom.isOver_iff]
  rw [Ddagger_structureMorphism_over_spec_eq, proj_structureMorphism_eq,
    Ddagger_structureMorphism_over_proj_eq]
  delta DdaggerToProj DdaggerIsoSpec
  simp only [Iso.symm_hom]
  symm
  rw [CategoryTheory.Iso.inv_comp_eq, ← Category.assoc]
  rw [IsOpenImmersion.isoRestrict_hom_ofRestrict]
  delta over
  erw [Multicoequalizer.π_desc]

end GoodPotionIngredient
