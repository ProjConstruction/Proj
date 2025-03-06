import Project.Grading.Potions

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : Set (GoodPotionIngredient 𝒜)) (U : Opens (Proj ℱ))

lemma open_eq_iSup : U = ⨆ (S : ℱ), (((glueData ℱ).openCover.map S).opensRange ⊓ U) := by
  ext x
  obtain ⟨S, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
  simp only [glueData_U, SetLike.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf,
    Scheme.Hom.coe_opensRange, Set.iUnion_coe_set, Opens.coe_mk, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_range, exists_and_right, iff_and_self]
  intro hx
  exact ⟨S.1, S.2, x, rfl⟩


end GoodPotionIngredient
