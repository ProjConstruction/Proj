import Project.Proj.Construction

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι : Type} {τ R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : τ → GoodPotionIngredient 𝒜) (U : Opens (Proj ℱ))

variable {ℱ} in
abbrev interPotion (i : τ) : Opens (Proj ℱ) :=
  ((glueData ℱ).ι i).opensRange ⊓ U

variable {ℱ} in
lemma mem_interPotion (i : τ) (x : Proj ℱ) :
    x ∈ interPotion U i ↔
    x ∈ ((glueData ℱ).ι i).opensRange ∧ x ∈ U :=
  Iff.rfl

variable {ℱ} in
abbrev interPotion' (i : τ) : Opens ((glueData ℱ).ι i).opensRange :=
  ⟨{x | x.1 ∈ U}, by
    have : Continuous (X := ((glueData ℱ).ι i).opensRange) (Y := Proj ℱ) (Subtype.val) := by continuity
    erw [show {x | x.1 ∈ U} = (Subtype.val : ((glueData ℱ).ι i).opensRange → Proj ℱ) ⁻¹'
      (interPotion U i).1 by ext; simp [interPotion]]
    refine Continuous.isOpen_preimage (by continuity) _ ?_
    exact (interPotion U i).2⟩

variable {ℱ} in
lemma mem_interPotion' (i : τ) (x : ((glueData ℱ).ι i).opensRange) :
    x ∈ interPotion' U i ↔ x.1 ∈ U :=
  Iff.rfl

variable {ℱ} in
abbrev interPotion'' (i : τ) : Opens (Spec <| CommRingCat.of (ℱ i).Potion) :=
  ⟨((glueData ℱ).ι i).base ⁻¹' U.1, Continuous.isOpen_preimage (by continuity) _ U.2⟩

lemma mem_interPotion'' (i : τ)  (x : Spec <| CommRingCat.of (ℱ i).Potion) :
    x ∈ interPotion'' U i ↔ ((glueData ℱ).ι i).base x ∈ U :=
  Iff.rfl

lemma open_eq_iSup : U = ⨆ (i : τ), interPotion U i := by
  ext x
  obtain ⟨i, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
  simp only [glueData_U, SetLike.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf,
    Scheme.Hom.coe_opensRange, Opens.coe_mk, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_range, exists_and_right, iff_and_self]
  intro hx
  exact ⟨i, x, rfl⟩


end GoodPotionIngredient
