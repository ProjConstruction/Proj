import Project.Proj.Opens
import Project.Proj.Over
import Project.Proj.Stalk
import Project.ForMathlib.SchemeIsOpenImmersion

import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace Topology

namespace GoodPotionIngredient

universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable {ℱ ℱ' : Set (GoodPotionIngredient 𝒜)}


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
    (glueData ℱ).ι S ≫ projHomOfLE le = (glueData ℱ').ι ⟨S.1, le S.2⟩ := by
  erw [Multicoequalizer.π_desc]

@[simp]
lemma projHomOfLE_comp_ι_base (le : ℱ ⊆ ℱ') (S : ℱ) :
    ((glueData ℱ).ι S).base ≫ (projHomOfLE le).base = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base := by
  ext x
  exact congr($(projHomOfLE_comp_ι le S).base x)

@[simp]
lemma projHomOfLE_comp_ι_base' (le : ℱ ⊆ ℱ') (S : ℱ) :
    (projHomOfLE le).base ∘ ((glueData ℱ).ι S).base = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base := by
  ext x
  exact congr($(projHomOfLE_comp_ι le S).base x)


@[simp]
lemma projHomOfLE_comp_ι_base_apply (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
    (projHomOfLE le).base (((glueData ℱ).ι S).base x) = ((glueData ℱ').ι ⟨S.1, le S.2⟩).base x := by
  exact congr($(projHomOfLE_comp_ι le S).base x)

@[reassoc]
lemma projHomOfLE_stalkMap_aux (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
    Scheme.Hom.stalkMap
      (projHomOfLE le) (((glueData ℱ).ι S).base x) ≫
    (stalkIso ℱ S x).hom =
    (TopCat.Presheaf.stalkCongr _ (by simp only [projHomOfLE_comp_ι_base_apply]; rfl)).hom ≫
      (stalkIso ℱ' ⟨S.1, le S.2⟩ x).hom  := by

  simp only [stalkIso, asIso_hom]
  erw [← Scheme.Hom.stalkMap_comp]
  apply TopCat.Presheaf.stalk_hom_ext

  intro U hxU
  simp only [Scheme.comp_coeBase, TopCat.comp_app, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc]
  erw [PresheafedSpace.stalkMap_germ]
  simp only [TopCat.Presheaf.pushforward_obj_obj]
  have := PresheafedSpace.stalkMap_germ ((glueData ℱ).ι S ≫ projHomOfLE le).toLRSHom.toShHom
    U x hxU
  erw [this]
  change ((glueData ℱ).ι S ≫ projHomOfLE le).c.app _ ≫ ((glueData ℱ).U S).presheaf.germ _ _ _ = _
  have : ((glueData ℱ).ι S ≫ projHomOfLE le).c.app (op U) =
    ((glueData ℱ').ι ⟨S.1, le S.2⟩).c.app (op U) ≫
    (((glueData ℱ').U ⟨S.1, le S.2⟩).presheaf |>.map (eqToHom (by simp))) := by
    have := projHomOfLE_comp_ι le S
    rw [Scheme.Hom.ext_iff] at this
    obtain ⟨h_base, h_app⟩ := this
    have := h_app U
    simp only [glueData_U, Scheme.comp_coeBase, TopologicalSpace.Opens.map_comp_obj, Scheme.Hom.app,
      Scheme.comp_app, eqToHom_op, Category.assoc, TopCat.Presheaf.pushforward_obj_obj,
      Functor.op_obj] at this ⊢
    rw [← this]
    simp
  rw [this]
  simp

lemma projHomOfLE_stalkMap_eq (le : ℱ ⊆ ℱ') (S : ℱ) (x : Spec (CommRingCat.of S.1.Potion)) :
    Scheme.Hom.stalkMap (projHomOfLE le) (((glueData ℱ).ι S).base x) =
    (TopCat.Presheaf.stalkCongr _ (by simp only [projHomOfLE_comp_ι_base_apply]; rfl)).hom ≫
      (stalkIso ℱ' ⟨S.1, le S.2⟩ x).hom ≫ (stalkIso ℱ S x).inv  := by
  rw [← projHomOfLE_stalkMap_aux_assoc]
  simp

lemma projHomOfLE_base_injective (le : ℱ ⊆ ℱ') :
    Function.Injective (projHomOfLE le).base := by
  intro x x' h
  obtain ⟨S, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
  obtain ⟨S', x', rfl⟩ := (glueData ℱ).ι_jointly_surjective x'
  rw [projHomOfLE_comp_ι_base_apply, projHomOfLE_comp_ι_base_apply] at h
  rw [Scheme.GlueData.ι_eq_iff] at h
  obtain eq|⟨y, h₁, h₂⟩ := h
  · simp only [glueData_J, glueData_U, Sigma.mk.inj_iff, Subtype.mk.injEq] at eq
    rcases eq with ⟨eq₁, eq₂⟩
    rw [← Subtype.ext_iff] at eq₁
    subst eq₁
    simp only [heq_eq_eq] at eq₂
    subst eq₂
    rfl
  dsimp only at h₁ h₂
  rw [← h₁, ← h₂]
  exact congr($((glueData ℱ).glue_condition _ _).base y).symm

lemma projHomOfLE_base_isOpenMap_aux (le : ℱ ⊆ ℱ') (U : Opens (Proj ℱ)) (S : ℱ) :
    IsOpen <| (projHomOfLE le).base '' (interPotion U S) := by
  -- U(S) -x-> Spec A_(S) -emb-> Proj F
  --                               |
  -- U(S) -x'-> Spec A_(S) -emb'-> Proj F'
  let x : (interPotion'' U S) → ((glueData ℱ).U S) := Subtype.val
  have cont_x : Continuous x := by continuity
  let emb : ((glueData ℱ).U S) → Proj ℱ := (glueData ℱ).ι S |>.base
  have cont_emb : Continuous emb := by continuity

  let x' : (interPotion'' U S) → ((glueData ℱ').U ⟨S.1, le S.2⟩) := Subtype.val
  have cont_x' : Continuous x' := by continuity
  have x'_openMap : IsOpenMap x' := (interPotion'' U S).2.isOpenMap_subtype_val
  let emb' : ((glueData ℱ').U ⟨S.1, le S.2⟩) → Proj ℱ' := (glueData ℱ').ι ⟨S.1, le S.2⟩ |>.base
  have cont_emb' : Continuous emb' := by continuity
  have emb'_openEmb : IsOpenEmbedding emb' :=
    (inferInstance : IsOpenImmersion <| (glueData ℱ').ι ⟨S.1, le S.2⟩).1
  have emb'_openMap : IsOpenMap emb' := emb'_openEmb.isOpenMap

  have H : IsOpenMap (emb' ∘ x') := emb'_openMap.comp x'_openMap

  have comm : (projHomOfLE le).base ∘ emb ∘ x = emb' ∘ x' := by
    ext pt
    simp only [glueData_U, Function.comp_apply, emb, emb', x]
    erw [projHomOfLE_comp_ι_base_apply]
    rfl

  have eq : (projHomOfLE le).base '' (interPotion U S) = Set.range ((projHomOfLE le).base ∘ emb ∘ x) := by
    ext pt
    simp only [Opens.coe_inf, glueData_U, Scheme.Hom.coe_opensRange, Set.mem_image,
      Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, Function.comp_apply, Subtype.exists,
      Opens.mem_mk, Opens.carrier_eq_coe, Set.mem_preimage, exists_prop, emb, x]
    constructor
    · rintro ⟨pt, ⟨⟨pt, rfl⟩, hpt⟩, rfl⟩
      exact ⟨pt, hpt, rfl⟩
    · rintro ⟨pt, hpt, rfl⟩
      exact ⟨((glueData ℱ).ι S).base pt, ⟨⟨_, rfl⟩, hpt⟩, rfl⟩
  rw [eq, comm]
  exact H.isOpen_range

lemma projHomOfLE_base_isOpenMap (le : ℱ ⊆ ℱ') :
    IsOpenMap (projHomOfLE le).base := by
  intro U hU
  lift U to (Opens (Proj ℱ)) using hU
  rw [open_eq_iSup _ U]
  erw [show (projHomOfLE le).base '' (⨆ S, interPotion U S).1 =
    ⨆ (S : ℱ), (projHomOfLE le).base '' (interPotion U S) by simp [Set.image_iUnion]]
  apply isOpen_sUnion
  rintro _ ⟨S, rfl⟩
  exact projHomOfLE_base_isOpenMap_aux le U S


lemma projHomOfLE_base_isOpenEmbedding (le : ℱ ⊆ ℱ') :
    Topology.IsOpenEmbedding (projHomOfLE le).base := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · continuity
  · apply projHomOfLE_base_injective
  · apply projHomOfLE_base_isOpenMap

instance (le : ℱ ⊆ ℱ') : IsOpenImmersion (projHomOfLE le) := by
  rw [isOpenImmersion_iff_stalk]
  constructor
  · apply projHomOfLE_base_isOpenEmbedding
  · intro x
    obtain ⟨S, hS, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
    rw [projHomOfLE_stalkMap_eq]
    infer_instance

instance (le : ℱ ⊆ ℱ') : (projHomOfLE le).IsOver (SpecBase 𝒜) where
  comp_over := Multicoequalizer.hom_ext _ _ _ <| fun _ ↦ by
    erw [Multicoequalizer.π_desc, Multicoequalizer.π_desc_assoc, Multicoequalizer.π_desc]

-- lemma proj_isIso_projClosure :
--     IsIso (projHomOfLE Subsemigroup.subset_closure : Proj ℱ ⟶ Proj (Subsemigroup.closure ℱ)) := by
--   apply (config := { allowSynthFailures := true }) AlgebraicGeometry.IsOpenImmersion.to_iso
--   rw [TopCat.epi_iff_surjective]
--   intro x
--   have := (glueData (Subsemigroup.closure ℱ : Set (GoodPotionIngredient 𝒜))).ι
--   sorry

end GoodPotionIngredient
