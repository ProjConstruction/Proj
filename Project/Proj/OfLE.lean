import Project.Proj.Opens
import Project.Proj.Over
import Project.Proj.Stalk
import Project.ForMathlib.SchemeIsOpenImmersion
import Project.ForMathlib.Ideal

import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace Topology

namespace GoodPotionIngredient

universe u
variable {τ τ' ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable {ℱ : τ → GoodPotionIngredient 𝒜} {ℱ' : τ' → GoodPotionIngredient 𝒜}

variable (ℱ ℱ') in
structure LE_ where
  (t : τ ↪ τ')
  (comp : ℱ' ∘ t = ℱ)

instance : FunLike (LE_ ℱ ℱ') τ τ' where
  coe le := le.t
  coe_injective' := by
    rintro ⟨⟨t, ht⟩, comp⟩ ⟨⟨t', ht'⟩, comp'⟩ rfl
    rfl

@[simp]
lemma LE_.comp_apply (le : LE_ ℱ ℱ') (i : τ) : ℱ' (le i) = ℱ i := by
  have := le.comp
  rw [funext_iff] at this
  exact this i

def LE_.potionEquivMap (le : LE_ ℱ ℱ') (i : τ) : (ℱ' (le i)).Potion ≃+* (ℱ i).Potion :=
  RingEquiv.ofHomInv
    (HomogeneousLocalization.map _ _ (RingHom.id _) (by erw [Submonoid.comap_id]; simp) (by simp) :
      (ℱ' (le i)).Potion →+* (ℱ i).Potion)
    (HomogeneousLocalization.map _ _ (RingHom.id _) (by erw [Submonoid.comap_id]; simp) (by simp) :
      (ℱ i).Potion →+* (ℱ' (le i)).Potion)
     (by ext x; induction x using Quotient.inductionOn' with | h x => rfl)
     (by ext x; induction x using Quotient.inductionOn' with | h x => rfl)

lemma LE_.potionEquivMap_comp (le : LE_ ℱ ℱ') (i j : τ) :
      ((ℱ i).potionToMul (ℱ j).1).comp (le.potionEquivMap i).toRingHom =
      (HomogeneousLocalization.map _ _ (RingHom.id _) (by erw [Submonoid.comap_id]; simp) (by simp)).comp
        ((ℱ' (le i)).potionToMul (ℱ' (le j)).1) := by
    ext x
    induction x using Quotient.inductionOn' with | h x =>
    rfl

@[reassoc]
lemma LE_.f_comp_potionEquivMap (le : LE_ ℱ ℱ') (j j' : τ) :
  (glueData ℱ').f (le j) (le j') ≫ Spec.map (CommRingCat.ofHom (le.potionEquivMap j).symm.toRingHom) =
  ((Spec.map <| CommRingCat.ofHom (HomogeneousLocalization.map _ _ (RingHom.id _)
    (by erw [Submonoid.comap_id]; simp) (by simp))) ≫ (glueData ℱ).f j j') := by
  simp only [glueData_J, glueData_V, mul_toHomogeneousSubmonoid,
    HomogeneousSubmonoid.mul_toSubmonoid, glueData_U, glueData_f, RingEquiv.toRingHom_eq_coe, ←
    Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  rfl

@[reassoc]
lemma LE_.t_comp (le : LE_ ℱ ℱ') (j j' : τ) :
  (glueData ℱ').t (le j) (le j') ≫
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map _ _ (RingHom.id _)
    (by erw [Submonoid.comap_id]; simp) (by simp))) =
  ((Spec.map <| CommRingCat.ofHom (HomogeneousLocalization.map _ _ (RingHom.id _)
    (by erw [Submonoid.comap_id]; simp) (by simp))) ≫ (glueData ℱ).t j j') := by
  simp only [glueData_J, glueData_V, mul_toHomogeneousSubmonoid,
    HomogeneousSubmonoid.mul_toSubmonoid, glueData_t, RingEquiv.toRingHom_eq_coe, ← Spec.map_comp, ←
    CommRingCat.ofHom_comp]
  congr 2
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  rfl

def projHomOfLE (le : LE_ ℱ ℱ') : Proj ℱ ⟶ Proj ℱ' :=
  Multicoequalizer.desc _ _
    (fun i ↦ Spec.map (CommRingCat.ofHom <| le.potionEquivMap i) ≫ (glueData ℱ').ι (le i)) <| by
    rintro ⟨i, j⟩
    simp only [GlueData.diagram_left, GlueData.diagram_right]
    change (Spec.map _) ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
    simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid, ← Spec.map_comp,
      RingEquiv.toRingHom_eq_coe]
    have : Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _ :=
      (glueData ℱ').glue_condition (le i) (le j)
    dsimp only at this
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp] at this
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    dsimp only [GlueData.diagram, glueData_J, glueData_V, mul_toHomogeneousSubmonoid,
      HomogeneousSubmonoid.mul_toSubmonoid, glueData_U, glueData_f, glueData_t]
    conv_rhs => rw [RingHom.comp_assoc]
    erw [LE_.potionEquivMap_comp]
    simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid,
      RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      glueData_J] at this ⊢
    rw [← this]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    induction x using Quotient.inductionOn' with | h x =>
    rfl

@[reassoc (attr := simp)]
lemma projHomOfLE_comp_ι (le : LE_ ℱ ℱ')  (i : τ) :
    (glueData ℱ).ι i ≫ projHomOfLE le =
    Spec.map (CommRingCat.ofHom <| le.potionEquivMap i) ≫ (glueData ℱ').ι (le i) := by
  erw [Multicoequalizer.π_desc]

@[simp]
lemma projHomOfLE_comp_ι_base (le : LE_ ℱ ℱ') (i : τ) :
    ((glueData ℱ).ι i).base ≫ (projHomOfLE le).base =
    (Spec.map (CommRingCat.ofHom <| le.potionEquivMap i)).base ≫ ((glueData ℱ').ι (le i)).base := by
  ext x
  exact congr($(projHomOfLE_comp_ι ..).base x)

@[simp]
lemma projHomOfLE_comp_ι_base' (le : LE_ ℱ ℱ') (i : τ) :
    (projHomOfLE le).base ∘ ((glueData ℱ).ι i).base =
    ((glueData ℱ').ι (le i)).base ∘ (Spec.map (CommRingCat.ofHom <| le.potionEquivMap i)).base := by
  ext x
  exact congr($(projHomOfLE_comp_ι ..).base x)

@[simp]
lemma projHomOfLE_comp_ι_base_apply (le : LE_ ℱ ℱ') (i : τ) (x : Spec (CommRingCat.of (ℱ i).Potion)) :
    (projHomOfLE le).base (((glueData ℱ).ι i).base x) =
    ((glueData ℱ').ι (le i)).base ((Spec.map (CommRingCat.ofHom <| le.potionEquivMap i)).base x) := by
  exact congr($(projHomOfLE_comp_ι ..).base x)

@[reassoc]
lemma projHomOfLE_stalkMap_aux (le : LE_ ℱ ℱ') (i : τ) (x : Spec (CommRingCat.of (ℱ i).Potion)) :
    Scheme.Hom.stalkMap (projHomOfLE le) (((glueData ℱ).ι i).base x) ≫ (stalkIso ℱ i x).hom =
    (TopCat.Presheaf.stalkCongr _ (by simp only [projHomOfLE_comp_ι_base_apply]; rfl)).hom ≫
    (stalkIso ℱ' (le i) ((Spec.map (CommRingCat.ofHom <| le.potionEquivMap i)).base x)).hom ≫
    Scheme.Hom.stalkMap _ _ := by
  simp only [stalkIso, asIso_hom]
  erw [← Scheme.Hom.stalkMap_comp]
  apply TopCat.Presheaf.stalk_hom_ext

  intro U hxU
  simp only [glueData_U, Scheme.comp_coeBase, TopCat.comp_app, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc]
  erw [PresheafedSpace.stalkMap_germ_assoc]
  simp only [TopCat.Presheaf.pushforward_obj_obj]
  have := PresheafedSpace.stalkMap_germ ((glueData ℱ).ι i ≫ projHomOfLE le).toLRSHom.toShHom
    U x hxU
  erw [this]
  change ((glueData ℱ).ι i ≫ projHomOfLE le).c.app _ ≫ ((glueData ℱ).U i).presheaf.germ _ _ _ = _
  have : ((glueData ℱ).ι i ≫ projHomOfLE le).c.app (op U) =
    ((glueData ℱ').ι (le i)).c.app (op U) ≫ (by
      let f : Spec (CommRingCat.of (ℱ i).Potion) ⟶ Spec (CommRingCat.of (ℱ' (le i)).Potion) :=
        Spec.map (CommRingCat.ofHom (le.potionEquivMap i))
      refine f.c.app (op ((Opens.map ((glueData ℱ').ι (le i)).base).obj U)) ≫
        (Spec (CommRingCat.of (ℱ i).Potion)).presheaf.map (eqToHom ?_)
      simp only [glueData_U, Functor.op_obj, projHomOfLE_comp_ι, Scheme.comp_coeBase,
        Opens.map_comp_obj, op.injEq]
      rfl) := by
    have := projHomOfLE_comp_ι le i
    rw [Scheme.Hom.ext_iff] at this
    obtain ⟨h_base, h_app⟩ := this
    have := h_app U
    simp only [glueData_U, Scheme.comp_coeBase, Opens.map_comp_obj, Scheme.Hom.app, Scheme.comp_app,
      eqToHom_op, Category.assoc, TopCat.Presheaf.pushforward_obj_obj, Functor.op_obj] at this ⊢
    conv_rhs => rw [← Category.assoc]
    rw [← this]
    simp
  rw [this]
  simp

lemma projHomOfLE_stalkMap_eq (le : LE_ ℱ ℱ') (i : τ) (x : Spec (CommRingCat.of (ℱ i).Potion)) :
    Scheme.Hom.stalkMap (projHomOfLE le) (((glueData ℱ).ι i).base x) =
    (TopCat.Presheaf.stalkCongr _ (by simp only [projHomOfLE_comp_ι_base_apply]; rfl)).hom ≫
    (stalkIso ℱ' (le i) ((Spec.map (CommRingCat.ofHom <| le.potionEquivMap i)).base x)).hom ≫
    Scheme.Hom.stalkMap _ _ ≫ (stalkIso ℱ i x).inv := by
  rw [← projHomOfLE_stalkMap_aux_assoc]
  simp

lemma projHomOfLE_base_injective (le : LE_ ℱ ℱ') :
    Function.Injective (projHomOfLE le).base := by
  intro x x' h
  obtain ⟨j, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
  obtain ⟨j', x', rfl⟩ := (glueData ℱ).ι_jointly_surjective x'
  rw [projHomOfLE_comp_ι_base_apply, projHomOfLE_comp_ι_base_apply] at h
  let X := (Spec.map (CommRingCat.ofHom (le.potionEquivMap j).toRingHom)).base x
  have eq_X : x = (Spec.map (CommRingCat.ofHom (le.potionEquivMap j).symm.toRingHom)).base X := by
    simp only [glueData_U, RingEquiv.toRingHom_eq_coe, X]
    change x = (Spec.map _ ≫ Spec.map _).base x
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp
  rw [eq_X] at *
  let X' := (Spec.map (CommRingCat.ofHom (le.potionEquivMap j').toRingHom)).base x'
  have eq_X' : x' = (Spec.map (CommRingCat.ofHom (le.potionEquivMap j').symm.toRingHom)).base X' := by
    simp only [glueData_U, RingEquiv.toRingHom_eq_coe, X']
    change x' = (Spec.map _ ≫ Spec.map _).base x'
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp
  rw [eq_X'] at *
  change ((glueData ℱ').ι (le j)).base X = ((glueData ℱ').ι (le j')).base X' at h
  clear_value X X'
  clear eq_X eq_X' x x'
  rw [Scheme.GlueData.ι_eq_iff] at h
  obtain eq|⟨y, h₁, h₂⟩ := h
  · simp only [glueData_J, glueData_U, Sigma.mk.inj_iff, Subtype.mk.injEq] at eq
    rcases eq with ⟨eq₁, eq₂⟩
    replace eq₁ := le.t.2 eq₁
    subst eq₁
    simp only [heq_eq_eq] at eq₂
    subst eq₂
    rfl
  simp only at h₁ h₂
  rw [← h₁, ← h₂]
  erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← Scheme.comp_coeBase,
    ← Scheme.comp_coeBase, ← Scheme.comp_coeBase, ← Scheme.comp_coeBase, ]
  rw [← Category.assoc, LE_.f_comp_potionEquivMap, Category.assoc, ← (glueData ℱ).glue_condition j j',
    Category.assoc, LE_.f_comp_potionEquivMap_assoc, LE_.t_comp_assoc]

lemma projHomOfLE_base_isOpenMap_aux (le : LE_ ℱ ℱ') (U : Opens (Proj ℱ)) (i : τ) :
    IsOpen <| (projHomOfLE le).base '' (interPotion U i) := by
  -- U(S) -x-> Spec A_(S) -emb-> Proj F
  --                               |
  -- U(S) -x'-> Spec A_(S) -emb'-> Proj F'
  let x : (interPotion'' U i) → ((glueData ℱ).U i) := Subtype.val
  have cont_x : Continuous x := by continuity
  let emb : ((glueData ℱ).U i) → Proj ℱ := (glueData ℱ).ι i |>.base
  have cont_emb : Continuous emb := by continuity

  let x' : (interPotion'' U i) → ((glueData ℱ').U (le i)) :=
    (Spec.map <| CommRingCat.ofHom (le.potionEquivMap i)).base ∘ Subtype.val
  have cont_x' : Continuous x' := by continuity
  have x'_openMap : IsOpenMap x' := by
    have := (interPotion'' U i).2.isOpenMap_subtype_val
    haveI : IsIso (Spec.map <| CommRingCat.ofHom (le.potionEquivMap i).toRingHom) := by
      use Spec.map <| CommRingCat.ofHom (le.potionEquivMap i).symm
      simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]

    haveI t : IsOpenImmersion (Spec.map <| CommRingCat.ofHom (le.potionEquivMap i).toRingHom) :=
      inferInstance
    exact IsOpenMap.comp (t.base_open.isOpenMap) (interPotion'' U i).2.isOpenMap_subtype_val

  let emb' : ((glueData ℱ').U (le i)) → Proj ℱ' := (glueData ℱ').ι (le i) |>.base
  have cont_emb' : Continuous emb' := by continuity
  have emb'_openEmb : IsOpenEmbedding emb' :=
    (inferInstance : IsOpenImmersion <| (glueData ℱ').ι (le i)).1
  have emb'_openMap : IsOpenMap emb' := emb'_openEmb.isOpenMap

  have H : IsOpenMap (emb' ∘ x') := emb'_openMap.comp x'_openMap

  have comm : (projHomOfLE le).base ∘ emb ∘ x = emb' ∘ x' := by
    ext pt
    simp only [glueData_U, Function.comp_apply, emb, emb', x]
    erw [projHomOfLE_comp_ι_base_apply]
    rfl

  have eq : (projHomOfLE le).base '' (interPotion U i) = Set.range ((projHomOfLE le).base ∘ emb ∘ x) := by
    ext pt
    simp only [Opens.coe_inf, glueData_U, Scheme.Hom.coe_opensRange, Set.mem_image,
      Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, Function.comp_apply, Subtype.exists,
      Opens.mem_mk, Opens.carrier_eq_coe, Set.mem_preimage, exists_prop, emb, x]
    constructor
    · rintro ⟨pt, ⟨⟨pt, rfl⟩, hpt⟩, rfl⟩
      exact ⟨pt, hpt, rfl⟩
    · rintro ⟨pt, hpt, rfl⟩
      exact ⟨((glueData ℱ).ι i).base pt, ⟨⟨_, rfl⟩, hpt⟩, rfl⟩
  rw [eq, comm]
  exact H.isOpen_range

lemma projHomOfLE_base_isOpenMap (le : LE_ ℱ ℱ')  :
    IsOpenMap (projHomOfLE le).base := by
  intro U hU
  lift U to (Opens (Proj ℱ)) using hU
  rw [open_eq_iSup _ U]
  erw [show (projHomOfLE le).base '' (⨆ i, interPotion U i).1 =
    ⨆ (i : τ), (projHomOfLE le).base '' (interPotion U i) by simp [Set.image_iUnion]]
  apply isOpen_sUnion
  rintro _ ⟨S, rfl⟩
  exact projHomOfLE_base_isOpenMap_aux le U S


lemma projHomOfLE_base_isOpenEmbedding (le : LE_ ℱ ℱ') :
    Topology.IsOpenEmbedding (projHomOfLE le).base := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · continuity
  · apply projHomOfLE_base_injective
  · apply projHomOfLE_base_isOpenMap

instance (le : LE_ ℱ ℱ') : IsOpenImmersion (projHomOfLE le) := by
  rw [isOpenImmersion_iff_stalk]
  constructor
  · apply projHomOfLE_base_isOpenEmbedding
  · intro x
    obtain ⟨S, hS, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
    rw [projHomOfLE_stalkMap_eq]
    apply (config := {allowSynthFailures := true}) IsIso.comp_isIso
    apply (config := {allowSynthFailures := true}) IsIso.comp_isIso
    apply (config := {allowSynthFailures := true}) IsIso.comp_isIso
    apply (config := {allowSynthFailures := true}) Scheme.Hom.stalkMap.isIso
    use (Spec.map <| CommRingCat.ofHom <| (le.potionEquivMap S).symm.toRingHom)
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]

instance (le : LE_ ℱ ℱ') : (projHomOfLE le).IsOver (SpecBase 𝒜) where
  comp_over := Multicoequalizer.hom_ext _ _ _ <| fun x ↦ by
    erw [Multicoequalizer.π_desc, Multicoequalizer.π_desc_assoc, Category.assoc,
      Multicoequalizer.π_desc]
    simp only [GlueData.diagram_right, glueData_U, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

abbrev idealify (ℱ : τ → GoodPotionIngredient 𝒜) :
    τ ⊕ (τ × GoodPotionIngredient 𝒜) → GoodPotionIngredient 𝒜 :=
  Sum.rec ℱ (fun p ↦ ℱ p.1 * p.2)

abbrev le_idealify (ℱ : τ → GoodPotionIngredient 𝒜) : LE_ ℱ (idealify ℱ) where
  t :=
  { toFun := Sum.inl
    inj' := Sum.inl_injective }
  comp := rfl

@[simp]
lemma le_idealify_apply (x) : le_idealify ℱ x = Sum.inl x := rfl

@[simp]
lemma le_idealify_potionEquivMap (i : τ) : (le_idealify ℱ).potionEquivMap i = RingEquiv.refl _ := by
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  rfl

open HomogeneousSubmonoid in
instance proj_iso_proj_idealify :
    IsIso (projHomOfLE (le_idealify ℱ)) := by
  apply (config := { allowSynthFailures := true }) AlgebraicGeometry.IsOpenImmersion.to_iso
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨i|⟨i, T⟩, (x : Spec _), rfl⟩ :=
    (glueData _).ι_jointly_surjective x
  · refine ⟨((glueData ℱ).ι i).base x, ?_⟩
    erw [projHomOfLE_comp_ι_base_apply]
    simp
  · refine ⟨((glueData ℱ).ι i).base
      ⟨Ideal.comap (algebraMap ((ℱ i).Potion) _) <| Ideal.comap
        (localizationRingEquivPotion (finitePotionGen (ℱ i).relevant T.fg)) x.asIdeal, inferInstance⟩, ?_⟩

    erw [projHomOfLE_comp_ι_base_apply]
    rw [Scheme.GlueData.ι_eq_iff]
    right
    let e : ((ℱ i).1 * ((ℱ i).1 * T.1)).Potion ≃+* ((ℱ i).1 * T.1).Potion := potionEquiv (by simp [← mul_assoc])
    refine ⟨⟨Ideal.comap e x.asIdeal, inferInstance⟩, ?_, ?_⟩

    · refine PrimeSpectrum.ext ?_
      change Ideal.comap _ _ = _
      simp only [glueData_J, glueData_U, le_idealify_apply, mul_toHomogeneousSubmonoid,
        mul_toSubmonoid, le_idealify_potionEquivMap, RingEquiv.coe_ringHom_refl,
        CommRingCat.ofHom_id, Spec.map_id, Scheme.id.base, TopCat.id_app]
      erw [Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      ext x
      induction x using Quotient.inductionOn' with | h x =>
      simp only [mul_toSubmonoid, RingHom.coe_comp, Function.comp_apply, potionToMul_mk]
      erw [HomogeneousLocalization.map_mk]
      simp only [RingHom.id_apply, Subtype.coe_eta, HomogeneousLocalization.val_mk, id_eq]
      rw [← Localization.mk_one_eq_algebraMap]
      have eq := localizationToPotion_mk' (ℱ i).1 T.1 (finitePotionGen (ℱ i).relevant T.fg) x ∅ id (fun _ ↦ 1)
      simp only [mul_toSubmonoid, id_eq, pow_one, Finset.prod_empty, map_one, mul_one] at eq
      erw [eq]
      rfl
    · let ι := (glueData (idealify ℱ)).ι (Sum.inr ⟨i, T⟩)
      have io : IsOpenImmersion ι := inferInstance
      have io : IsOpenEmbedding ι.base := ι.isOpenEmbedding
      have inj : Function.Injective ι.base := io.injective
      apply inj
      dsimp only
      have := (glueData (idealify ℱ)).glue_condition
        (Sum.inl i)
        (Sum.inr ⟨i, T⟩)
      have := congr($(this).base ⟨Ideal.comap e x.asIdeal, inferInstance⟩)
      erw [this]
      simp only [glueData_J, SetLike.coe_sort_coe, glueData_V, mul_toHomogeneousSubmonoid,
        mul_toSubmonoid, glueData_U, glueData_f, Scheme.comp_coeBase, TopCat.comp_app]
      erw [Scheme.GlueData.ι_eq_iff]
      right
      refine ⟨⟨Ideal.comap e x.asIdeal, inferInstance⟩, ?_⟩
      simp only [glueData_J, SetLike.coe_sort_coe, glueData_U, mul_toSubmonoid,
        mul_toHomogeneousSubmonoid, glueData_V, glueData_f, glueData_t, RingEquiv.toRingHom_eq_coe,
        Scheme.comp_coeBase, TopCat.comp_app, true_and]
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ (Ideal.comap _ _) = _
      rw [Ideal.comap_comap]
      ext z
      simp only [Ideal.mem_comap, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        potionEquiv_trans_apply, mul_toSubmonoid, e]
      induction z using Quotient.inductionOn' with | h z =>
      simp only [mul_toSubmonoid, e]
      erw [HomogeneousLocalization.map_mk]
      swap
      · simp only [mul_toSubmonoid, e]
        rw [mul_comm (ℱ i).1.1, mul_assoc, Submonoid.mul_self]
        erw [Submonoid.comap_id]
      swap
      · intro _ _ h
        exact h
      simp only [mul_toSubmonoid, RingHom.id_apply, Subtype.coe_eta, e]
      rfl

section Sets

variable {ℱ ℱ' : Set <| GoodPotionIngredient 𝒜}

def LE_.of_subset (subset : ℱ ⊆ ℱ') :
    LE_ (𝒜 := 𝒜) (τ := ℱ) (τ' := ℱ') Subtype.val Subtype.val where
  t := ℱ.embeddingOfSubset ℱ' subset
  comp := rfl

def projHomOfSubset (subset : ℱ ⊆ ℱ') : Proj (τ := ℱ) Subtype.val ⟶ Proj (τ := ℱ') Subtype.val :=
  projHomOfLE (LE_.of_subset subset)

def projClosureIso :
    Proj (τ := (CommSemigroup.Ideal.closure ℱ)) (ℱ := Subtype.val) ≅
    Proj (idealify (τ := ℱ) Subtype.val) where
  hom := Multicoequalizer.desc _ _
    (fun (p : CommSemigroup.Ideal.closure ℱ) ↦
      _ ≫
      (glueData (idealify (τ := ℱ) Subtype.val)).ι (Sum.inr ⟨_, _⟩)) _
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

instance proj_iso_proj_subset :
    IsIso (projHomOfSubset (CommSemigroup.Ideal.subset_closure ℱ)) := by
  have := proj_iso_proj_idealify (τ := ℱ) (ℱ := Subtype.val)
  have eq : projHomOfSubset (CommSemigroup.Ideal.subset_closure ℱ) =
      projHomOfLE (le_idealify (τ := ℱ) Subtype.val) ≫
      (by

        sorry) := by sorry


end Sets

end GoodPotionIngredient
