import Project.ForMathlib.SchemeIsOpenImmersion
import Project.Grading.Potions

import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ ℱ' : Set (GoodPotionIngredient 𝒜))

def stalkIso (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
    (Proj ℱ).presheaf.stalk (((glueData ℱ).ι S).base x) ≅
    (Spec (CommRingCat.of S.1.Potion)).presheaf.stalk x := by
  have ioi : IsOpenImmersion ((glueData ℱ).ι S) := inferInstance
  rw [isOpenImmersion_iff_stalk] at ioi
  haveI := ioi.2 x
  exact asIso (Scheme.Hom.stalkMap ((glueData ℱ).ι S) x)

end GoodPotionIngredient
