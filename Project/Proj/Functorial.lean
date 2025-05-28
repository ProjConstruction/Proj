import Project.Proj.Construction
import Project.Grading.GradedRingHom

import Project.Proj.OfLE

import Project.Proj.Delab

suppress_compilation

universe u
variable {τ ι R₀ A B C : Type u}
variable [AddCommGroup ι] [DecidableEq ι] [CommRing R₀]
variable [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [GradedAlgebra 𝒜]
variable [CommRing B] [Algebra R₀ B] {ℬ : ι → Submodule R₀ B}
variable [GradedAlgebra ℬ]
variable [CommRing C] [Algebra R₀ C] {𝒞 : ι → Submodule R₀ C}
variable [GradedAlgebra 𝒞]

open AlgebraicGeometry CategoryTheory Limits HomogeneousSubmonoid TensorProduct Graded

namespace GoodPotionIngredient

variable (Φ : 𝒜 →+* ℬ) (Ψ : ℬ →+* 𝒞)

set_option maxHeartbeats 1000000 in
protected def Proj.map (ℱ : τ → GoodPotionIngredient 𝒜) :
    Proj ((map Φ) ∘ ℱ) ⟶ Proj ℱ  :=
  Multicoequalizer.desc _ _
    (fun (i : τ) ↦ Spec.map (CommRingCat.ofHom ((ℱ i).potionToMap Φ)) ≫ (glueData ℱ).ι i) <| by
    rintro ⟨(i : τ), (j : τ)⟩
    simp only [glueData_J, GlueData.diagram_left, glueData_V, Function.comp_apply,
      mul_toHomogeneousSubmonoid, mul_toSubmonoid, GlueData.diagram_right, glueData_U]
    change (Spec.map _) ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
    simp only [Function.comp_apply, mul_toHomogeneousSubmonoid, mul_toSubmonoid, GlueData.diagram,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, RingEquiv.toRingHom_eq_coe, Category.assoc]
    have : Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _ :=
      (glueData ℱ).glue_condition i j
    dsimp only at this
    simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, RingEquiv.toRingHom_eq_coe,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp] at this ⊢
    conv_rhs =>
      erw [potionToMul_comp_potionToMap, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    erw [potionEquiv_comp]
    generalize_proofs _ _ h1
    swap
    · rw [mul_comm]
    have eq :
      (potionEquiv h1).toRingHom.comp
        (((ℱ j).toHomogeneousSubmonoid * (ℱ i).toHomogeneousSubmonoid).potionToMap Φ) =
      (RingHom.comp
        (RingHom.comp (potionEquiv (by rw [HomogeneousSubmonoid.map_mul]; rfl)).toRingHom
          (((ℱ i).toHomogeneousSubmonoid * (ℱ j).toHomogeneousSubmonoid).potionToMap Φ))
        (potionEquiv (mul_comm ..)).toRingHom) := by
      ext x
      induction x using Quotient.inductionOn' with | h x =>
      rfl
    rw [eq]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, mul_toSubmonoid,
      RingEquiv.toRingHom_eq_coe] at this ⊢
    rw [this]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    induction x using Quotient.inductionOn' with | h x =>
    rfl

lemma Proj.map_id (ℱ : τ → GoodPotionIngredient 𝒜) :
    GoodPotionIngredient.Proj.map (.id 𝒜) ℱ  =
    projHomOfLE
      { le := { toFun := id, inj' _ _ h := h }
        comp := funext fun i ↦ toHomogeneousSubmonoid_inj <| by
          ext a
          simp [map, HomogeneousSubmonoid.map] } := by
  apply Multicoequalizer.hom_ext
  rintro i;
  rfl

lemma Proj.map_comp (ℱ : τ → GoodPotionIngredient 𝒜) :
  Proj.map (Ψ.comp Φ) ℱ =
  projHomOfLE
  { le := { toFun := id, inj' _ _ h := h }
    comp :=  funext fun i ↦ toHomogeneousSubmonoid_inj <| by
      ext a
      simp [map, HomogeneousSubmonoid.map] } ≫ Proj.map Ψ _ ≫ Proj.map Φ ℱ := by
  apply Multicoequalizer.hom_ext
  rintro i
  simp only [GlueData.diagram_right, glueData_U, Function.comp_apply, Proj.map, colimit.ι_desc,
    GlueData.diagram_l, glueData_J, GlueData.diagram_r, Multicofork.ofπ_pt, Multicofork.ofπ_ι_app,
    projHomOfLE, id_eq, Function.Embedding.mk_id, Function.Embedding.refl_apply,
    GradedRingHom.comp_apply, colimit.ι_desc_assoc, GlueData.diagram_left, glueData_V,
    mul_toHomogeneousSubmonoid, mul_toSubmonoid, Category.assoc]
  erw [Multicoequalizer.π_desc_assoc, Category.assoc, Multicoequalizer.π_desc]
  erw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  simp only [potionToMap, LE_.potionEquivMap, Function.comp_apply, CommRingCat.hom_comp,
    RingHom.coe_comp, RingHom.coe_coe]
  rfl


end GoodPotionIngredient
