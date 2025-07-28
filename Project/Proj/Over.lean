

import Mathlib.AlgebraicGeometry.Over
import Project.Proj.Construction

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι : Type} {τ R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : τ → GoodPotionIngredient 𝒜)

scoped notation "SpecBase"ℬ => Spec (CommRingCat.of (ℬ 0))

-- variable {ℱ} in
-- def Ddagger (S : ℱ) : Scheme :=
--   (Proj ℱ).restrict (U := Spec (CommRingCat.of <| S.1.Potion)) (f := ((glueData ℱ).ι S).base) <| by
--     have : IsOpenImmersion ((glueData ℱ).ι S) := inferInstance
--     exact AlgebraicGeometry.Scheme.Hom.isOpenEmbedding _

-- variable {ℱ} in
-- def DdaggerIsoSpec (S : ℱ) : Ddagger S ≅ (Spec (CommRingCat.of S.1.Potion)) :=
--   IsOpenImmersion.isoRestrict _ |>.symm

-- variable {ℱ} in
-- abbrev DdaggerToProj (S : ℱ) : Ddagger S ⟶ Proj ℱ := Scheme.ofRestrict _ _

-- instance (S : ℱ) : (Ddagger S).Over (Proj ℱ) where
--   hom := DdaggerToProj S

-- lemma Ddagger_structureMorphism_over_proj_eq (S : ℱ) :
--     (Ddagger S) ↘ (Proj ℱ) = DdaggerToProj S := rfl

-- instance (S : ℱ) : (Ddagger S).Over (SpecBase 𝒜) where
--   hom := (DdaggerIsoSpec S).hom ≫ Spec.map (CommRingCat.ofHom <| algebraMap _ _)

-- variable {ℱ} in
-- lemma Ddagger_structureMorphism_over_spec_eq (S : ℱ) :
--     (Ddagger S) ↘ (SpecBase 𝒜) = (DdaggerIsoSpec S).hom ≫ Spec.map (CommRingCat.ofHom <| algebraMap _ _) := rfl

-- def projHomOfLE (le : ℱ ⊆ ℱ') : Proj ℱ ⟶ Proj ℱ' :=
--   Multicoequalizer.desc _ _
--     (fun S ↦ (glueData ℱ').ι ⟨S.1, le S.2⟩) <| by
--     intro S
--     simp only [GlueData.diagram_left, GlueData.diagram_right]
--     change (Spec.map _) ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
--     simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid, ← Spec.map_comp,
--       RingEquiv.toRingHom_eq_coe]
--     have : Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _ :=
--       (glueData ℱ').glue_condition ⟨S.1.1, le S.1.2⟩  ⟨S.2.1, le S.2.2⟩
--     dsimp only at this
--     simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid,
--       RingEquiv.toRingHom_eq_coe, ← Spec.map_comp_assoc] at this
--     exact this.symm

-- @[reassoc (attr := simp)]
-- lemma projHomOfLE_comp_ι (le : ℱ ⊆ ℱ') (S : ℱ) :
--     (glueData ℱ).ι S ≫ projHomOfLE ℱ ℱ' le = (glueData ℱ').ι ⟨S.1, le S.2⟩ := by
--   erw [Multicoequalizer.π_desc]

-- @[simp]
-- lemma projHomOfLE_comp_ι_base (le : ℱ ⊆ ℱ') (S : ℱ) :
--     ((glueData ℱ).ι S).base ≫ (projHomOfLE ℱ ℱ' le).base = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base := by
--   ext x
--   exact congr($(projHomOfLE_comp_ι ℱ ℱ' le S).base x)

-- @[simp]
-- lemma projHomOfLE_comp_ι_base' (le : ℱ ⊆ ℱ') (S : ℱ) :
--     (projHomOfLE ℱ ℱ' le).base ∘ ((glueData ℱ).ι S).base = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base := by
--   ext x
--   exact congr($(projHomOfLE_comp_ι ℱ ℱ' le S).base x)


-- @[simp]
-- lemma projHomOfLE_comp_ι_base_apply (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
--     (projHomOfLE ℱ ℱ' le).base (((glueData ℱ).ι S).base x) = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base x := by
--   exact congr($(projHomOfLE_comp_ι ℱ ℱ' le S).base x)

-- @[reassoc]
-- lemma projHomOfLE_stalkMap_aux (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
--     Scheme.Hom.stalkMap
--       (projHomOfLE ℱ ℱ' le) (((glueData ℱ).ι S).base x) ≫
--     (stalkIso ℱ S x).hom =
--     (TopCat.Presheaf.stalkCongr _ (by simp only [projHomOfLE_comp_ι_base_apply]; rfl)).hom ≫
--       (stalkIso ℱ' ⟨S.1, le S.2⟩ x).hom  := by

--   simp only [stalkIso, asIso_hom]
--   erw [← Scheme.Hom.stalkMap_comp]
--   apply TopCat.Presheaf.stalk_hom_ext

--   intro U hxU
--   simp only [Scheme.comp_coeBase, TopCat.comp_app, TopCat.Presheaf.stalkCongr_hom,
--     TopCat.Presheaf.germ_stalkSpecializes_assoc]
--   erw [PresheafedSpace.stalkMap_germ]
--   simp only [TopCat.Presheaf.pushforward_obj_obj]
--   have := PresheafedSpace.stalkMap_germ ((glueData ℱ).ι S ≫ projHomOfLE ℱ ℱ' le).toLRSHom.toShHom
--     U x hxU
--   erw [this]
--   change ((glueData ℱ).ι S ≫ projHomOfLE ℱ ℱ' le).c.app _ ≫ ((glueData ℱ).U S).presheaf.germ _ _ _ = _
--   have : ((glueData ℱ).ι S ≫ projHomOfLE ℱ ℱ' le).c.app (op U) =
--     ((glueData ℱ').ι ⟨S.1, le S.2⟩).c.app (op U) ≫
--     (((glueData ℱ').U ⟨S.1, le S.2⟩).presheaf |>.map (eqToHom (by simp))) := by
--     have := projHomOfLE_comp_ι ℱ ℱ' le S
--     rw [Scheme.Hom.ext_iff] at this
--     obtain ⟨h_base, h_app⟩ := this
--     have := h_app U
--     simp only [glueData_U, Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, Scheme.Hom.app,
--       Scheme.comp_app, eqToHom_op, Category.assoc, TopCat.Presheaf.pushforward_obj_obj,
--       Functor.op_obj] at this ⊢
--     rw [← this]
--     simp
--   rw [this]
--   simp

-- lemma projHomOfLE_stalkMap_eq (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
--     Scheme.Hom.stalkMap
--       (projHomOfLE ℱ ℱ' le) (((glueData ℱ).ι S).base x)
--      =
--     (TopCat.Presheaf.stalkCongr _ (by simp only [projHomOfLE_comp_ι_base_apply]; rfl)).hom ≫
--       (stalkIso ℱ' ⟨S.1, le S.2⟩ x).hom ≫ (stalkIso ℱ S x).inv  := by
--   rw [← projHomOfLE_stalkMap_aux_assoc]
--   simp

-- lemma projHomOfLE_base_injective (le : ℱ ⊆ ℱ') :
--     Function.Injective (projHomOfLE ℱ ℱ' le).base := by
--   intro x x' h
--   obtain ⟨S, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
--   obtain ⟨S', x', rfl⟩ := (glueData ℱ).ι_jointly_surjective x'
--   rw [projHomOfLE_comp_ι_base_apply, projHomOfLE_comp_ι_base_apply] at h
--   have := congr($((glueData ℱ').glue_condition ⟨S.1, le S.2⟩ ⟨S'.1, le S'.2⟩).base)
--   simp? at this

--   sorry

-- lemma projHomOfLE_base_isOpenMap (le : ℱ ⊆ ℱ') :
--     IsOpenMap (projHomOfLE ℱ ℱ' le).base := by
--   intro U hU
--   lift U to (Opens (Proj ℱ)) using hU
--   rw [open_eq_iSup _ U]
--   simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Scheme.Hom.coe_opensRange,
--     Set.iUnion_coe_set, Opens.coe_mk, Set.image_iUnion]
--   apply isOpen_sUnion
--   rintro _ ⟨S, rfl⟩
--   apply isOpen_sUnion
--   rintro _ ⟨hS, rfl⟩
--   simp only
--   rw [show (glueData ℱ).openCover.map ⟨S, hS⟩ = (glueData ℱ).ι ⟨S, hS⟩ by rfl]

--   -- rw [Set.image_inter (projHomOfLE_base_injective _ _ le)]

--   -- apply IsOpen.inter
--   -- · rw [← Set.image_univ, show (glueData ℱ).openCover.map ⟨S, hS⟩ = (glueData ℱ).ι ⟨S, hS⟩ by rfl,
--   --     ← Set.image_comp]
--   --   erw [projHomOfLE_comp_ι_base']
--   have : IsOpenImmersion ((glueData ℱ').ι ⟨S, le hS⟩) := inferInstance
--   have : IsOpenMap ((glueData ℱ').ι ⟨S, le hS⟩).base := this.1.isOpenMap
--   -- suffices IsOpen (((glueData ℱ').ι ⟨S, le hS⟩).base '' ((projHomOfLE ℱ ℱ' le).base '' (Set.range ⇑((glueData ℱ).openCover.map ⟨S, hS⟩).base ∩ U.1))) by sorry
--   -- rw [this.1.isOpen_iff_of_cover]
--   --   refine this _ ?_
--   --   exact isOpen_univ
--   -- ·
--   --   sorry


-- lemma projHomOfLE_base_isOpenEmbedding (le : ℱ ⊆ ℱ') :
--     Topology.IsOpenEmbedding (projHomOfLE ℱ ℱ' le).base := by
--   apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
--   · continuity
--   · apply projHomOfLE_base_injective
--   · apply projHomOfLE_base_isOpenMap

-- instance (le : ℱ ⊆ ℱ') : IsOpenImmersion (projHomOfLE ℱ ℱ' le) := by
--   rw [isOpenImmersion_iff_stalk]
--   constructor
--   · apply projHomOfLE_base_isOpenEmbedding
--   · intro x
--     obtain ⟨S, hS, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
--     rw [projHomOfLE_stalkMap_eq]
--     infer_instance
-- -- Ideal ℱ := {S * S'}
-- lemma proj_isIso_projClosure :
--     IsIso (projHomOfLE _ _ Subsemigroup.subset_closure :
--       Proj ℱ ⟶ Proj (𝒜 := 𝒜) (Subsemigroup.closure ℱ)) := by
--   apply (config := { allowSynthFailures := true }) AlgebraicGeometry.IsOpenImmersion.to_iso
--   rw [TopCat.epi_iff_surjective]
--   intro x
--   have := (glueData (Subsemigroup.closure ℱ : Set (GoodPotionIngredient 𝒜))).ι
--   sorry

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

-- instance (S : ℱ) : IsOverTower (Ddagger S) (Proj ℱ) (SpecBase 𝒜) := by
--   simp only [Scheme.Hom.isOver_iff]
--   rw [Ddagger_structureMorphism_over_spec_eq, proj_structureMorphism_eq,
--     Ddagger_structureMorphism_over_proj_eq]
--   delta DdaggerToProj DdaggerIsoSpec
--   simp only [Iso.symm_hom]
--   symm
--   rw [CategoryTheory.Iso.inv_comp_eq, ← Category.assoc]
--   rw [IsOpenImmersion.isoRestrict_hom_ofRestrict]
--   delta over
--   erw [Multicoequalizer.π_desc]

end GoodPotionIngredient
