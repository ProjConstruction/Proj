import Project.Grading.Potions

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : Set (GoodPotionIngredient 𝒜)) (U : Opens (Proj ℱ))

variable {ℱ} in
abbrev interPotion (S : ℱ) : Opens (Proj ℱ) :=
  ((glueData ℱ).ι S).opensRange ⊓ U

variable {ℱ} in
lemma mem_interPotion (S : ℱ) (x : Proj ℱ) :
    x ∈ interPotion U S ↔
    x ∈ ((glueData ℱ).ι S).opensRange ∧ x ∈ U :=
  Iff.rfl

variable {ℱ} in
abbrev interPotion' (S : ℱ) : Opens ((glueData ℱ).ι S).opensRange :=
  ⟨{x | x.1 ∈ U}, by
    have : Continuous (X := ((glueData ℱ).ι S).opensRange) (Y := Proj ℱ) (Subtype.val) := by continuity
    erw [show {x | x.1 ∈ U} = (Subtype.val : ((glueData ℱ).ι S).opensRange → Proj ℱ) ⁻¹'
      (interPotion U S).1 by ext; simp [interPotion]]
    refine Continuous.isOpen_preimage (by continuity) _ ?_
    exact (interPotion U S).2⟩

variable {ℱ} in
lemma mem_interPotion' (S : ℱ) (x : ((glueData ℱ).ι S).opensRange) :
    x ∈ interPotion' U S ↔ x.1 ∈ U :=
  Iff.rfl

variable {ℱ} in
abbrev interPotion'' (S : ℱ) : Opens (Spec <| CommRingCat.of S.1.Potion) :=
  ⟨((glueData ℱ).ι S).base ⁻¹' U.1, Continuous.isOpen_preimage (by continuity) _ U.2⟩

lemma mem_interPotion'' (S : ℱ) (x : Spec <| CommRingCat.of S.1.Potion) :
    x ∈ interPotion'' U S ↔ ((glueData ℱ).ι S).base x ∈ U :=
  Iff.rfl

lemma open_eq_iSup : U = ⨆ (S : ℱ), interPotion U S := by
  ext x
  obtain ⟨S, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
  simp only [glueData_U, SetLike.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf,
    Scheme.Hom.coe_opensRange, Set.iUnion_coe_set, Opens.coe_mk, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_range, exists_and_right, iff_and_self]
  intro hx
  exact ⟨S.1, S.2, x, rfl⟩


end GoodPotionIngredient
