import Project.Proj.Construction

import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion


suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι : Type} {τ R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : τ → GoodPotionIngredient 𝒜)

def stalkIso (i : τ) (x : Spec (CommRingCat.of (ℱ i).Potion)) :
    (Proj ℱ).presheaf.stalk (((glueData ℱ).ι i).base x) ≅
    (Spec (CommRingCat.of (ℱ i).Potion)).presheaf.stalk x := by
  have ioi : IsOpenImmersion ((glueData ℱ).ι i) := inferInstance
  rw [isOpenImmersion_iff_stalk] at ioi
  haveI := ioi.2 x
  exact asIso (Scheme.Hom.stalkMap ((glueData ℱ).ι i) x)

end GoodPotionIngredient
