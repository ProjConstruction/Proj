import Project.Proj.Construction
import Project.Grading.GradedRingHom
import Project.ForMathlib.ImageSplitting

suppress_compilation

universe u
variable {τ ι R₀ A B : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]
variable [CommRing B] [Algebra R₀ B] {ℬ : ι → Submodule R₀ B}
variable [GradedAlgebra ℬ]

open AlgebraicGeometry CategoryTheory Limits HomogeneousSubmonoid TensorProduct Graded

namespace GoodPotionIngredient

variable (Φ : 𝒜 →+* ℬ)

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

end GoodPotionIngredient
