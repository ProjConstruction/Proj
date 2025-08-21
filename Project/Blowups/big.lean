import Project.Dilatation.Multicenter
import Mathlib.Data.Sum.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Project.Dilatation.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Project.Dilatation.lemma
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Basic
import Project.Dilatation.Family
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Project.HomogeneousSubmonoid.Basic
import Project.ForMathlib.TensorProduct
import Project.Proj.Over
import Project.Proj.OfLE
import Project.Dilatation.Multicenter
import Mathlib.Topology.Sets.Closeds
import Mathlib.AlgebraicGeometry.PullbackCarrier

import Project.ForMathlib.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat


import Mathlib.RingTheory.RingHom.Flat

import Project.Blowups.PreClosAndClos
import Project.Blowups.Bl
import Project.Proj.Sum'


suppress_compilation

open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable {ι : Type} [DecidableEq ι] [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]
variable {X : Scheme.{u+1}}

structure conceptual_blowup (Z : Clos X) where
  scheme : Scheme
  over : Scheme.Over scheme X
  in_cars : pullback_Clos (scheme ↘ X) Z ∈ CarsAsSubsetOfClos scheme
  φ (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    T ⟶ scheme
  φ_over (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    Scheme.Hom.IsOver (φ T in_preCars) X
  φ_uniq (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    ∀ φ' : T ⟶ scheme, Scheme.Hom.IsOver φ' X → φ' = φ T in_preCars

def singletonCovering (A: CommRingCat) :
    Scheme.AffineCover IsOpenImmersion (Spec A) where
  J := PUnit
  obj _ := A
  map _ := 𝟙 _
  f _ := .unit
  covers := by simp
  map_prop _ := inferInstance

def loc_to_PreClos (A: CommRingCat) (L : ι → Ideal A) : PreClos (Spec A) where
  indnumb := ι
  subscheme i := Spec (CommRingCat.of <| A ⧸ L i)
  over i :=
  { hom := Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk (L i) }
  cov := singletonCovering A
  ideal i _ := L i
  condiso i _ :=
    ⟨Spec.map (CommRingCat.ofHom <| (Algebra.TensorProduct.rid A A (A ⧸ L i))),
      Spec.map (CommRingCat.ofHom <| (Algebra.TensorProduct.rid A A (A ⧸ L i)).symm), sorry,
      sorry⟩ ≪≫ (AlgebraicGeometry.pullbackSpecIso A (A ⧸ L i) A).symm ≪≫ pullback.congrHom rfl (Spec.map_id _)
  condover i _ := by
    sorry

def loc_to_Clos (A: CommRingCat) (L : ι → Ideal A) : Clos (Spec A) :=
  Quotient.mk' (loc_to_PreClos A L)



-- EQUALITY of morphisms of schemes IS LOCAL AT SOURCE
-- lemma  := by
--    -- AlgebraicGeometry.sourceAffineLocally_isLocal theorem
--     sorry


instance (A B : CommRingCat) [Algebra A B] : Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

instance (X Y : Scheme) [Scheme.Over X Y]
  (O : Opens X) : (X.restrict O.isOpenEmbedding).Over Y where
    hom := X.ofRestrict .. ≫ X ↘ Y

open GoodPotionIngredient HomogeneousSubmonoid
theorem ProjBlowup_UnivProp_unicity_affine
  (A: CommRingCat.{u+1}) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : IsCars _ (pullback_Clos (T ↘ Spec A) (loc_to_Clos A L)))
  -- (cond : IsPreCars _ <| pullback_PreClos _ _ (T ↘ Spec A) (loc_to_PreClos A L))
  (φ φ' : T ⟶ BlMu L)
  (φ_over : Scheme.Hom.IsOver φ (Spec A))
  (φ'_over : Scheme.Hom.IsOver φ' (Spec A)) : φ = φ' := by
  obtain ⟨Z, hZ, eq⟩ := cond
  change Quotient.mk'' _ = Quotient.mk'' _ at eq
  rw [Quotient.eq''] at eq
  obtain ⟨eq⟩ := eq
  let O (P P' : Mu L) (x : T) :
    Opens T :=
    ⟨(φ.base ⁻¹' (((glueData (τ := Mu L) (map_index L)).ι P).opensRange).1) ∩
      (φ'.base ⁻¹' (((glueData (τ := Mu L) (map_index L)).ι P').opensRange).1) ∩
        (Z.cov.map <| Z.cov.f x).opensRange.1,
        IsOpen.inter (IsOpen.inter
          (by
            apply Continuous.isOpen_preimage
            · continuity
            · exact (Scheme.Hom.opensRange ((glueData (map_index L)).ι P)).is_open')
          (by
            apply Continuous.isOpen_preimage
            · continuity
            · exact (Scheme.Hom.opensRange ((glueData (map_index L)).ι P')).is_open'))
          ((Scheme.Hom.opensRange _).is_open')⟩

  let S (P P' : Mu L) (x : T) : Scheme := T.restrict (O P P' x).isOpenEmbedding

  let SToSpecP (P P' : Mu L) (x : T) : S P P' x ⟶
    Spec (CommRingCat.of <| (map_index L P).Potion) :=
    IsOpenImmersion.lift ((glueData (map_index L)).ι P) (T.ofRestrict .. ≫ φ)
      (by
        rintro _ ⟨⟨z, ⟨⟨⟨y, hy1⟩, mem2⟩, mem3⟩⟩, rfl⟩
        simp only [Scheme.comp_coeBase, Scheme.ofRestrict_toLRSHom_base, TopCat.hom_comp,
          ContinuousMap.comp_apply, Set.mem_range]
        use y
        erw [hy1]
        rfl)

  letI isOver₀ (P P' : Mu L) (x : T) :
      (Spec (CommRingCat.of (map_index L P).Potion)).Over (Spec A) :=
    { hom := (glueData (τ := Mu L) (map_index L)).ι P ≫ (BlMu L) ↘ Spec A  }


  have isOverA₀ (P P' : Mu L) (x : T) :
    @Scheme.Hom.IsOver _ _ (SToSpecP P P' x) (Spec A) inferInstance (isOver₀ P P' x) := by sorry


  let SToSpecP' (P P' : Mu L) (x) : S P P' x ⟶ Spec (CommRingCat.of <| (map_index L P').Potion) :=
    IsOpenImmersion.lift ((glueData (map_index L)).ι P') (T.ofRestrict .. ≫ φ')
      (by
        rintro _ ⟨⟨z, ⟨⟨mem1, ⟨y, hy1⟩⟩, mem3⟩⟩, rfl⟩
        simp only [Scheme.comp_coeBase, Scheme.ofRestrict_toLRSHom_base, TopCat.hom_comp,
          ContinuousMap.comp_apply, Set.mem_range]
        use y
        erw [hy1]
        rfl)

  let SToSpecRx (P P' : Mu L) (x) :
      S P P' x ⟶
      Spec (Z.cov.obj <| Z.cov.f x) :=
    IsOpenImmersion.lift (Z.cov.map _) (T.ofRestrict ..)
      (by
        rintro _ ⟨⟨z, ⟨⟨mem1, mem2⟩, ⟨y, hy1⟩⟩⟩, rfl⟩
        simp only [Scheme.ofRestrict_toLRSHom_base, Set.mem_range]
        use y
        erw [hy1]
        rfl)

  have (x : T) :
    ∃ (P P' : Mu L) (B : CommRingCat) (_ : Algebra A B)
      (i : Spec B ⟶
        T.restrict (O P P' x).isOpenEmbedding),
      IsOpenImmersion i ∧
      Scheme.Hom.IsOver i (Spec A) ∧
      x ∈ Set.range ((i ≫ T.ofRestrict ..).base) ∧
      i ≫ T.ofRestrict _ ≫ φ = i ≫ T.ofRestrict _ ≫ φ' := by
    let y := φ.base x
    let y' := φ'.base x
    have  ⟨(P : Mu L), (Y : Spec <| _), hY⟩ := (glueData <| map_index L).ι_jointly_surjective y
    have  ⟨(P' : Mu L), (Y' : Spec <| _), hY'⟩ := (glueData <| map_index L).ι_jointly_surjective y'

    have x_in_inter : x ∈ O P P' x := ⟨⟨⟨Y, hY⟩, ⟨Y', hY'⟩⟩, Z.cov.covers x⟩

    let γ := Z.cov.f x
    let Rx : CommRingCat := Z.cov.obj γ
    let SpecRxOverT : Scheme.Over (Spec Rx) T :=
      { hom := Z.cov.map γ }
    let SpecRxOverSpecA : Scheme.Over (Spec Rx) (Spec A) :=
      { hom := Spec Rx ↘ T ≫ T ↘ Spec A}

    let x' : S P P' x := ⟨x, x_in_inter⟩
    obtain ⟨U, B, ⟨isoB : _⟩⟩ := (S P P' x).local_affine ⟨x, x_in_inter⟩

    let F : Spec B ⟶ Spec A := ⟨isoB.inv⟩ ≫ (S P P' x).restrict U.isOpenEmbedding ↘ Spec A
    let f : A ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ F.app _ ≫ (Scheme.ΓSpecIso _).hom
    let alg : Algebra A B := RingHom.toAlgebra f.hom

    have specB_over_specA_eq : Spec B ↘ Spec A = F := by
      change Spec.map (_ ≫ _ ≫ _) = _ ≫ _
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
        Spec.toLocallyRingedSpace_obj]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    let specBToSpecP : Spec B ⟶ Spec (CommRingCat.of <| (map_index L P).Potion) :=
      ⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict .. ≫ SToSpecP P P' x

    let specBToSpecP' : Spec B ⟶ Spec (CommRingCat.of <| (map_index L P').Potion) :=
      ⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict .. ≫ SToSpecP' P P' x

    let specBToSpecRx : Spec B ⟶ Spec Rx :=
      ⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict .. ≫ SToSpecRx P P' x

    haveI oi1 : IsOpenImmersion specBToSpecRx := by
      apply IsOpenImmersion.comp

    haveI flat1 : Flat specBToSpecRx := inferInstance

    let PToB : CommRingCat.of (map_index L P).Potion ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecP.app _ ≫ (Scheme.ΓSpecIso _).hom

    have PToB_def' : Spec.map PToB = specBToSpecP := by
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc, PToB]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    let RxToB : Rx ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecRx.app _ ≫ (Scheme.ΓSpecIso _).hom

    letI alg2 : Algebra A (map_index L P).Potion :=
      instAlgebraPotionFinsuppIntReesAlgebraClo_mu _ _

    letI alg2' : Algebra A (map_index L P').Potion :=
      instAlgebraPotionFinsuppIntReesAlgebraClo_mu _ _

    letI alg3 : Algebra Rx B :=
      RingHom.toAlgebra <| RxToB.hom

    let P'ToB : CommRingCat.of (map_index L P').Potion ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecP'.app _ ≫ (Scheme.ΓSpecIso _).hom

    have P'ToB_def' : Spec.map P'ToB = specBToSpecP' := by
      simp only [Opens.map_top, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc, P'ToB]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.inv_hom_id, Spec.map_id]

    let RxToB : Rx ⟶ B :=
      (Scheme.ΓSpecIso _).inv ≫ specBToSpecRx.app _ ≫ (Scheme.ΓSpecIso _).hom
    let AToRx : A ⟶ Rx :=
      (Scheme.ΓSpecIso _).inv ≫ (_ ↘ Spec A).app _ ≫ (Scheme.ΓSpecIso _).hom

    refine ⟨P, P', B, inferInstance, (⟨isoB.inv⟩ ≫ (S P P' x).ofRestrict ..), inferInstance, ?_,
      ?_, ?_⟩
    · rw [Scheme.Hom.isOver_iff, Category.assoc, specB_over_specA_eq]
      rfl
    · simp only [Spec.toLocallyRingedSpace_obj, Category.assoc, Scheme.comp_coeBase,
      Scheme.ofRestrict_toLRSHom_base, TopCat.hom_comp, ContinuousMap.comp_assoc,
      ContinuousMap.coe_comp, Set.mem_range, Function.comp_apply]
      refine ⟨isoB.hom.base ⟨⟨x, x_in_inter⟩, U.2⟩, ?_⟩
      erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply]
      rw [← Category.assoc]
      change ((isoB.hom ≫ isoB.inv).base ≫ _) _ = x
      rw [Iso.hom_inv_id]
      rfl
    ·
      have nonzerodiv (i : ι) := hZ.nonzerodiv (eq.indnumb_equiv.symm i) γ
      have prin (i : ι) := hZ.prin (eq.indnumb_equiv.symm i) γ


      obtain ⟨g'', ⟨g''_comp_eq, g''_comp_eq'⟩, g''_uniq⟩ := lemm_dila_double_union L P P' (B := B)
        (fun i => ⟨RxToB.hom <| Submodule.IsPrincipal.generator (Z.ideal (eq.indnumb_equiv.symm i) γ),
            by
              apply RingHom.Flat.preserves_nonzeroDivisors
              · have flat2 := flat1.flat_of_affine_subset ⟨⊤, sorry⟩ ⟨⊤, sorry⟩ (by intro x hx; simp)
                simp only at flat2
                simp only [Opens.map_top, CommRingCat.hom_comp, RxToB, Rx]
                refine RingHom.Flat.comp ?_ (RingHom.Flat.comp flat2 ?_) <;>
                · apply RingHom.Flat.of_bijective
                  exact ConcreteCategory.bijective_of_isIso _
              · apply nonzerodiv⟩)
        (g := AlgHom.comp
            { toRingHom := PToB.hom
              commutes' :=
                sorry }
            (Mu_mor_iso L P).toAlgHom)
        (g' := AlgHom.comp
            { toRingHom := P'ToB.hom
              commutes' := sorry }
            (Mu_mor_iso L P').toAlgHom)
        (cond1 := by
          intro i
          dsimp
          have eq0 : Ideal.map AToRx.hom (L i) =
            (Ideal.span
              {Submodule.IsPrincipal.generator
                (Z.ideal (eq.indnumb_equiv.symm i) γ)}) := by
            simp only [Ideal.span_singleton_generator, Rx]
            sorry
          rw [show algebraMap A B = RingHom.comp RxToB.hom AToRx.hom by sorry]
          rw [← Ideal.map_map, eq0, Ideal.map_span, Set.image_singleton])
        (cond2 := by simp)
        (cond2' := by simp)
      -- have g''_comp_eq_ringHom : PToB.comp (Mu_mor_iso L P).toRingHom = g''.toRingHom.comp (algebraMap _ _)
      exact calc Scheme.Hom.mk isoB.inv ≫ (S P P' x).ofRestrict _ ≫ T.ofRestrict _ ≫ φ
          _ = specBToSpecP ≫ (glueData (map_index L)).ι _ := by
            simp [specBToSpecP, SToSpecP]
          _ =
            (Spec.map (CommRingCat.ofHom <| g''.toRingHom.comp (Mu_mor_iso L (union_Mu L P P')).symm.toRingHom) :
                Spec B ⟶ Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion)) ≫
            (Spec.map (CommRingCat.ofHom <| potionMapOfLE _ _ (by sorry)) :
                  Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion) ⟶
                  Spec (CommRingCat.of <| (map_index L P).Potion)) ≫
            (glueData (map_index L)).ι _ := by
            simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
              AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
              Spec.map_comp, ← Category.assoc]
            congr 1
            simp only [Spec.toLocallyRingedSpace_obj, ← Spec.map_comp, specBToSpecP, SToSpecP]
            rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
            have : PToB.hom.comp _  = g''.toRingHom.comp (dilationToUnion_left _ _ _).toRingHom :=
              congr($(g''_comp_eq).toRingHom)
            rw [Mu_mor_iso_commutes_ringHom', ← RingHom.comp_assoc, ← RingHom.comp_assoc] at this
            simp only [AlgEquiv.toAlgHom_eq_coe, AlgHomClass.toRingHom_toAlgHom,
              AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
              RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom] at this
            erw [RingEquiv.comp_cancel] at this
            erw [← this]
            erw [PToB_def']
          _ = (Spec.map (CommRingCat.ofHom <| g''.toRingHom.comp (Mu_mor_iso L (union_Mu L P P')).symm.toRingHom) :
                Spec B ⟶ Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion)) ≫
              (glueData (map_index L)).ι _ := by
              rw [proj_glue_condition (ℱ := map_index L) P (union_Mu L P P')
                (clo_mu_union_Mu_left L P P')]
          _ = (Spec.map (CommRingCat.ofHom <| g''.toRingHom.comp (Mu_mor_iso L (union_Mu L P P')).symm.toRingHom) :
                Spec B ⟶ Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion)) ≫
            (Spec.map (CommRingCat.ofHom <| potionMapOfLE _ _ (clo_mu_union_Mu_right L P P')) :
                  Spec (CommRingCat.of <| (map_index L <| union_Mu L P P').Potion) ⟶
                  Spec (CommRingCat.of <| (map_index L P').Potion)) ≫
            (glueData (map_index L)).ι _ := by
            have := proj_glue_condition (ℱ := map_index L) P' (union_Mu L P P')
              (clo_mu_union_Mu_right L P P')
            rw [this]
          _ = specBToSpecP' ≫ (glueData (map_index L)).ι _ := by
            simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
              AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
              Spec.map_comp, ← Category.assoc]
            congr 1
            simp only [← Spec.map_comp]
            rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
            have : P'ToB.hom.comp _  = g''.toRingHom.comp (dilationToUnion_right _ _ _).toRingHom :=
              congr($(g''_comp_eq').toRingHom)
            rw [Mu_mor_iso_commutes_ringHom_right', ← RingHom.comp_assoc, ← RingHom.comp_assoc] at this
            simp only [AlgEquiv.toAlgHom_eq_coe, AlgHomClass.toRingHom_toAlgHom,
              AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
              RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom] at this
            erw [RingEquiv.comp_cancel] at this
            erw [← this]
            erw [P'ToB_def']
          _ = Scheme.Hom.mk isoB.inv ≫ (S P P' x).ofRestrict _ ≫ T.ofRestrict _ ≫ φ' := by
            simp [specBToSpecP', SToSpecP']

  have : (∀ x : T,
    ∃ (P P' : Mu L) (B : CommRingCat) (_ : Algebra A B)
      (i : Spec B ⟶ T.restrict (O P P' x).isOpenEmbedding),
      IsOpenImmersion i ∧
      Scheme.Hom.IsOver i (Spec A) ∧
      x ∈ Set.range ((i ≫ T.ofRestrict ..).base) ∧
      (i ≫ T.ofRestrict _ ≫ φ = i ≫ T.ofRestrict _ ≫ φ')) → φ = φ' := by
      -- because sheaf nonsense
      sorry
  sorry


set_option maxHeartbeats 400000 in
open Multicenter in
-- set_option diagnostics true in
lemma ProjBlowup_UnivProp_existence_affine_preclo
    (A: CommRingCat.{u + 1}) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : IsCars _ (pullback_Clos (T ↘ Spec A) (loc_to_Clos A L))) :
    ∃ φ : T ⟶ BlMu L, Scheme.Hom.IsOver φ (Spec A) := by
  classical

  have (x : T) : false := by
    obtain ⟨Z, hZ, eq⟩ := cond
    change Quotient.mk'' _ = Quotient.mk'' _ at eq
    rw [Quotient.eq''] at eq
    obtain ⟨eq⟩ := eq

    let γ := Z.cov.f x
    let B : CommRingCat := Z.cov.obj γ
    let U_γ := Spec B

    let over0 : Scheme.Over U_γ (Spec A) := { hom := Z.cov.map γ ≫ T ↘ Spec A }
    let algebra0 : Algebra A B :=
      RingHom.toAlgebra <|
        ((Scheme.ΓSpecIso _).inv ≫ (U_γ ↘ Spec A).app _ ≫ (Scheme.ΓSpecIso _).hom).hom

    -- pick a rep in the begining
    let c (i : ι) : B := hZ.prin (eq.indnumb_equiv.symm i) γ |>.generator



    have ideal_eq (i : ι) : Ideal.map (algebraMap A B) (L i) = Ideal.span { c i } := by sorry
    let mc : Multicenter B :=
    { index := ι
      ideal i := Ideal.map (algebraMap A B) (L i)
      elem i := c i }

    let dilaIso : B[mc] ≃ₐ[B] B :=
      (AlgEquiv.ofAlgHom
        (desc _ sorry sorry)
        (Algebra.ofId _ _)
        sorry
        sorry)
      -- (Multicenter.ofFamilyIso (c := ofFamily ι c) sorry)
      -- _

    let Rees := ReesAlgebra (fun i : ι => Ideal.map (algebraMap A B) (L i))


  --   let C : Rees := ∑ i : ι, .single _ (Finsupp.single i 1) _
  --   -- exists finite set S such f_{s, i} ∈ L_i for each s ∈ S and each i ∈ ι and λ_{s, i} in B for each s ∈ S and i ∈ ι,
  --   -- such that c_i = ∑ s ∈ S, f_{s, i} • λ_{s, i} -- this is because in span
  --   -- so S = ∪ s_i

    let Mu_c : Mu (fun i => Ideal.map (algebraMap A B) (L i)) :=
    { multicenter := mc
      fin := inferInstance
      Ψ := id
      sec := id
      surj := by simp
      cond := by sorry }

    let iso1 : B[mc] ≃ₐ[B] (clo_mu _ Mu_c).Potion := (Mu_mor_iso _ Mu_c)

    let iso2 : (clo_mu _ Mu_c).Potion ≃ₐ[B] HomogeneousSubmonoid.Potion
      (.closure {∏ i : ι, ReesAlgebra.single _ (Finsupp.single i 1)
        ⟨c i, by simp [ideal_eq]; aesop⟩} (by sorry) :
          HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))) :=
      AlgEquiv.ofRingEquiv (f := HomogeneousSubmonoid.potionEquivProduct (clo_mu _ Mu_c)
        ((Finset.univ (α := ι)).image fun i => ReesAlgebra.single _ (Finsupp.single i 1)
        ⟨c i, by simp [ideal_eq]; aesop⟩) sorry sorry) sorry |>.trans <| AlgEquiv.ofRingEquiv (f := potionEquiv sorry) sorry


    -- let SpecBDilaIso :
    --   Spec (CommRingCat.of (B[mc])) ≅
    --   Spec (CommRingCat.of (clo_mu _ Mu_c).Potion)  :=
    --   { hom := Spec.map <| CommRingCat.ofHom <| (Mu_mor_iso _ _).symm.toRingHom
    --     inv := Spec.map <| CommRingCat.ofHom <| (Mu_mor_iso _ Mu_c).toRingHom
    --     hom_inv_id := sorry
    --     inv_hom_id := sorry }

    have mem (i : ι) : c i ∈ Ideal.map (algebraMap A B) (L i) := by
      rw [ideal_eq]
      exact Ideal.mem_span_singleton_self (c i)
    change ∀ i, c i ∈ Submodule.span _ _ at mem
    simp_rw [Submodule.mem_span_iff_exists_finset_subset] at mem
    -- have c_repr (i : ι) : ∃ (l : A → A) (b : A → B) (s : Finset A),
    --   Function.support l ⊆ s ∧
    --   c i = ∑ i ∈ s, l i • b i := by
    --   sorry
    have c_repr (i : ι) : ∃ (lambda : A → B) (t : Finset A), (t : Set A) ⊆ L i ∧
      Function.support lambda ⊆ t ∧ ∑ a ∈ t, lambda a • algebraMap A B a = c i := by
      sorry

    choose lambda t t_subset lambda_support EQ using c_repr

    have c_repr_rees (i : ι) :
      (∑ a ∈ t i, ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) 0 ⟨lambda i a, sorry⟩ *
        ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) (Finsupp.single i 1) ⟨algebraMap A B a, sorry⟩ : Rees) =
      (ReesAlgebra.single _ (Finsupp.single i 1) ⟨c i, by simp [ideal_eq]; aesop⟩ : Rees) := by

      sorry

    have eq :
      (∏ i : ι, ReesAlgebra.single _ (Finsupp.single i 1) ⟨c i, by simp [ideal_eq]; aesop⟩ : Rees) =
      ∏ i : ι, (∑ a ∈ t i, ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) 0 ⟨lambda i a, sorry⟩ *
        ReesAlgebra.single ((fun i ↦ Ideal.map (algebraMap A B) (L i))) (Finsupp.single i 1) ⟨algebraMap A B a, sorry⟩ : Rees) := by sorry

    rw [Finset.prod_sum] at eq

    set rhs_summand : ((a : ι) → a ∈ Finset.univ → ↑A) → Rees := _
    set rhs :=  ∑ p ∈ Finset.univ.pi t, rhs_summand p
    change _ = rhs at eq
    let iso3 : (.closure {∏ i : ι, ReesAlgebra.single _ (Finsupp.single i 1)
        ⟨c i, by simp [ideal_eq]; aesop⟩} (by sorry) :
          HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion ≃ₐ[B]
      (.closure {rhs} (by sorry) :
          HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion :=
      AlgEquiv.ofRingEquiv (f := potionEquiv sorry) sorry

    let ISO := dilaIso.symm.trans <| iso1.trans iso2 |>.trans iso3

    let potionOfSum := (HomogeneousSubmonoid.closure {rhs} sorry :
      HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap ↑A ↑B) (L i))).Potion

    let mor3 : Spec B ≅ Spec (CommRingCat.of <| potionOfSum) :=
    { hom := Spec.map <| CommRingCat.ofHom <| ISO.symm
      inv := Spec.map <| CommRingCat.ofHom <| ISO
      hom_inv_id := sorry
      inv_hom_id := sorry }

    obtain ⟨F, hF⟩  := sum_open_finset
      (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))) (s := Finset.univ.pi t) (f := rhs_summand)
      (d := ∑ i : ι, Finsupp.single i 1) sorry sorry

    let rhs_summand_simplifed : ((a : ι) → a ∈ Finset.univ → ↑A) → Rees := fun p =>
      ∏ x ∈ Finset.univ.attach,
    (ReesAlgebra.single (fun i ↦ Ideal.map (algebraMap ↑A ↑B) (L i)) (Finsupp.single x.1 1))
        ⟨(algebraMap A B) (p x sorry), sorry⟩

    let aux0_component (p : (a : ι) → a ∈ Finset.univ → A) :
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand p} sorry :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion) ⟶
      Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {rhs_summand_simplifed p} sorry :
        HomogeneousSubmonoid (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i))).Potion) :=
      Spec.map <| sorry


    let aux0 :
      unionSpecFinset (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
        (d := ∑ i : ι, Finsupp.single i 1)
        (f := rhs_summand) (s := Finset.univ.pi t) sorry sorry ⟶
      unionSpecFinset (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
        (d := ∑ i : ι, Finsupp.single i 1)
        (f := rhs_summand_simplifed) (s := Finset.univ.pi t) sorry sorry :=
      Multicoequalizer.desc _ _
        (fun p => aux0_component p.1 ≫ componentToUnionSpecFinset
          (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
          (d := ∑ i : ι, Finsupp.single i 1)
          (f := rhs_summand_simplifed) (s := Finset.univ.pi t)
          _ _ _ (by simp))
        sorry

    let rhs_summand_ReesA : ((a : ι) → a ∈ Finset.univ → A) → ReesAlgebra fun i ↦ L i := fun p =>
      ∏ x ∈ Finset.univ.attach,
      (ReesAlgebra.single (fun i ↦ L i) (Finsupp.single x.1 1))
        ⟨p x sorry, sorry⟩

    let aux1 :
      unionSpecFinset (𝒜 := (ReesAlgebra.intGrading fun i ↦ Ideal.map (algebraMap A B) (L i)))
        (d := ∑ i : ι, Finsupp.single i 1)
        (f := rhs_summand_simplifed) (s := Finset.univ.pi t) sorry sorry ⟶
      unionSpecFinset (𝒜 := (ReesAlgebra.intGrading fun i ↦ L i))
        (d := ∑ i : ι, Finsupp.single i 1)
        (f := rhs_summand_ReesA)
        (s := Finset.univ.pi t)
        sorry sorry :=
      Multicoequalizer.desc _ _
        (fun i => sorry)
        sorry

    let aux2 :
      unionSpecFinset (𝒜 := (ReesAlgebra.intGrading fun i ↦ L i))
        (d := ∑ i : ι, Finsupp.single i 1)
        (f := rhs_summand_ReesA)
        (s := Finset.univ.pi t)
        sorry sorry ⟶
      BlMu L := sorry

    let finalF := F ≫ aux0 ≫ aux1 ≫ aux2
    -- let mor4 : Spec (CommRingCat.of <| potionOfSum) ⟶ unionSpec _ _ _ := by sorry


  --   sorry

  -- have gluing_material (x : T) :
  --   ∃ (B : CommRingCat)
  --     (emb : Spec B ⟶ T) (_ : Scheme.Over (Spec B) (Spec A))
  --     (_ : Scheme.Hom.IsOver emb (Spec A))
  --     (_ : IsOpenImmersion emb)
  --     (φ : Spec B ⟶ BlMu L),
  --     x ∈ Set.range emb.base ∧ Scheme.Hom.IsOver φ (Spec A) := by



  --   sorry

  -- choose B emb oB emb_over_A o_emb φ mem over using gluing_material

  -- letI (x y : T) : (pullback (emb x) (emb y)).Over (Spec A) :=
  -- { hom := pullback.fst (emb x) (emb y) ≫ (Spec (B x) ↘ Spec A) }

  -- letI (x y : T) : Flat (pullback (emb x) (emb y) ↘ Spec A) := by sorry


  -- let φ_global : T ⟶ BlMu L := AlgebraicGeometry.Scheme.Cover.glueMorphisms
  --   { J := T
  --     obj x := Spec <| B x
  --     map x := emb x
  --     f := id
  --     covers := mem
  --     map_prop := o_emb }
  --   φ
  --   (by
  --     rintro (x y : T)
  --     simp only
  --     apply ProjBlowup_UnivProp_unicity_affine
  --     · have eq0 := pullback_assoc
  --         (Z := loc_to_Clos A L) (X'' := pullback (emb x) (emb y)) (X' := T)
  --         (pullback.fst _ _ ≫ emb x) (T ↘ Spec A)
  --       simp only [Category.assoc] at eq0
  --       have is_car1 : IsCars _ (pullback_Clos (pullback.fst (emb x) (emb y) ≫ emb x) (pullback_Clos (T ↘ Spec A) (loc_to_Clos A L))) := by
  --         apply pullback_IsCars
  --         assumption
  --       rw [← eq0] at is_car1

  --       convert is_car1 using 2
  --       change pullback.fst _ _ ≫ _ = _
  --       congr 1
  --       have := emb_over_A x
  --       rw [Scheme.Hom.isOver_iff] at this
  --       exact this.symm
  --     · sorry -- this is easy
  --     · sorry -- this is easy
  --       )
  -- use φ_global

  sorry


lemma ProjBlowup_UnivProp_existence_affine
    (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃ φ : T ⟶ BlMu L, Scheme.Hom.IsOver φ (Spec A) := by
  obtain ⟨⟨-, ⟨⟨Z, hZ⟩, rfl⟩⟩, Z_in_Car, Z_eq⟩ := cond
  rename_i Z_pri
  simp only at Z_eq




  sorry
    --    chose a representative of pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) in Cars T
    --    For all x element in T (as a set)
    --        Chose an (affine) chart of the covering of the representative such that x is in the chart
    --        Let B be the ring of this chart
    --        By definitions (of pullback and of Cars),
    --             pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) restricted to Spec(B)
    --            is given by the ideal image of L in B, and there exists a nonzero divisor c in B
    --            such that Idealimage(L)=(c)
    --       Since c belongs to Idealimage(L), there exists elements l_j in L and b_j in B such that
    --            c= ∑ f(l_j) b_j where f:A → B
    --   We get PotionSch (c) = PotionSch (∑ f(l_j) b_j)
    --     (apply new trick)           ⊆ Union PotionSch ( f(l_j) b_j) ⊆ Union PotionSch ( f(l_j) )
    --  We apply functoriality of Proj (the gradedrings are Rees B f(L), Rees A L) to get a morphism
    --               Union PotionSch ( f(l_j) )→ Union PotionSch (l_j) over Spec(A)
    --  This gives a morphism  φx : Spec(B) ⟶ BlMu L over Spec(A) because Potion(c)is  isomorphic to Spec(B)
    --  We glue all the φx to get a morphism φ : T ⟶ BlMu L (use unicity) over Spec(A)



lemma ProjBlowup_UnivProp_affine
  (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃! φ :  T ⟶ BlMu L,  Scheme.Hom.IsOver φ (Spec A) := by
  obtain ⟨φ, hφ⟩ := ProjBlowup_UnivProp_existence_affine A L cond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact ProjBlowup_UnivProp_unicity_affine A L cond φ φ' hφ hφ' |>.symm

def ProjBlowup_φ (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    T ⟶ BlMu L :=
  Classical.choose (ProjBlowup_UnivProp_affine A L cond)

def ProjBlowup_φ_over (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    Scheme.Hom.IsOver (ProjBlowup_φ A L cond) (Spec A) :=
  Classical.choose_spec (ProjBlowup_UnivProp_affine A L cond) |>.1

def ProjBlowup_φ_uniq (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∀ φ' : T ⟶ BlMu L, Scheme.Hom.IsOver φ' (Spec A) → φ' = ProjBlowup_φ A L cond :=
  Classical.choose_spec (ProjBlowup_UnivProp_affine A L cond) |>.2


def  ProjBlowup_is_conceptual_blowups_affine (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι] :
    conceptual_blowup (loc_to_Clos A L) where
  scheme := BlMu L
  over := inferInstance
  in_cars := sorry
  φ T _ cond := ProjBlowup_φ A L cond
  φ_over T _ cond := ProjBlowup_φ_over A L cond
  φ_uniq T _ cond φ' hφ' := ProjBlowup_φ_uniq A L cond φ' hφ'

open Multicenter
--skip the following lemma at first
lemma dilatation_ring_flat_base_change (A B : Type (u + 1)) [CommRing A] [CommRing B] [Algebra A B] (F: Multicenter A)
    (flat : RingHom.Flat (algebraMap A B)) : Subsingleton ((B ⊗[A] A[F]) ≃ₐ[B] B[image_mult F]) := by

  --  χ flat and nonzerodiv_image implies that  𝐚^ν is a nonzerodivisor in A[F]⊗[A] B

          -- (because A[F] → A[F]⊗[A] B is flat by base change

              --- and because a^v is nonzerodiv in A[F] by dilatation (then use the new lemma saying flat preserv nonzerodivs))

  --  cond on ideals is ok

  --  apply univ property to get a unique B- morphism  <-

  --  universal property of tensor product, exists ->

  --  check that both compositions are identity

  sorry

--skip this one also
-- lemma flat_module_localization_at_prime_iff  (M: Module.A):
--  (M =0) ↔ (∀ q : maxideal.A : localization M A\ q =0 ):=
--   → is trivial
--   intro M
--   assume let x ∈ M let Nx = submodule of M generated by x
--   let I=Submodule.annihilator Nx, this is an ideal of A
--   ∀ q in maxideal.A, exists f ∈ A \ q such that f∈ I -- because x=0 in the localization
--   ∀ q in maxideal.A, I is not included in q
--   applying Ideal.exists_le_maximal we get I=A
--   so 1.x=0
--   so M=0
--   sorry
--same, can be skiped at first
-- lemma open_implies_flat_ring (χ : A →+* B):
--  (B.Spec → A.Spec is open_immerison )→ (χ : A →+* B is flat_ring_map):=
--    intro χ
--    AlgebraicGeometry.isOpenImmersion_iff_stalk
--    and AlgebraicGeometry.IsAffineOpen.isLocalization_stalk implies
--    that for all q ⊆ B prime ideals,
--    IsLocalization.AtPrime f^-1(q) A → IsLocalization.AtPrime b B
--    is an isomorphism
--   sorry

instance (A B : CommRingCat) [Algebra A B] : Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

--the following is really what we need for the experiment in a first time
lemma base_change_dil_open (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)]
  --  (i:Spec(B) → Spec(A) is Open immersion)
    (F: Multicenter A) :
  ∃! (e : pullback ((Spec <| CommRingCat.of A[F]) ↘ Spec A) (Spec B ↘ Spec A) ≅ Spec B),
    Scheme.Hom.IsOver e.hom (Spec B) := by
    --  exact open_implies_flat_ring  and dilatation_ring_flat_base_change
      sorry

--the following is also  what we need for the experiment in a first time
lemma base_change_Bl_open [Fintype ι] (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)] (L: ι → Ideal A) :
    ∃! (e : pullback (BlMu L ↘ Spec A) (Spec B ↘ Spec A) ≅

    BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))), Scheme.Hom.IsOver e.hom (Spec B) := by sorry

--     Put F: (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) → Spec(B) → Spec(A)

--     Put PB:  (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) → Spec(B)

--     Put fS: Spec(B) → Spec(A)

--     Have EQ1 pullback_Clos {(BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) } (F) (loc_to_Clos L)

--     =  pullback_Clos {(BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) } (PB)(pullback_Clos {(BlMu L) } (f) (loc_to_Clos L))

--      := by exact pullback_assoc sorry

--     Have EQ2 (pullback_Clos {(BlMu L) } (f) (loc_to_Clos L))  ≅ [over Spec(A)] loc_to_Clos (Spec B) (fun i : ι => Ideal.map (algebraMap A B) (L i))

--      := by definitons and A/I ⊗ B = B /idealimage(I) sorry

--     Have EQ3 pullback_Clos {(BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) } (F) (loc_to_Clos L)

--         ≅ [SpecA]  pullback_Clos {(BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) } (PB) ( loc_to_Clos (Spec B) (fun i : ι => Ideal.map (algebraMap A B) (L i)))

--     Have EQ4 pullback_Clos {(BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) } (PB)

--          ( loc_to_Clos (Spec B) (fun i : ι => Ideal.map (algebraMap A B) (L i))) ∈ Cars (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i)))

--             by exact blowups_Cars

--     Have EQ5 pullback_Clos {(BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) } (F) (loc_to_Clos L)  ∈ Cars (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i)))

--          by exact EQ3 and EQ4

--     EQ6:   EQ5 implies, by Universal property of blowups, that there exists a unique morphism over Spec(A)

--        φ :  (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) → BlMu L

--     EQ7: By propertties of fiber product get a map θ over Spec(B) :  (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))) → BlMu L × [Spec(A)] Spec(B)

--     SAME METHOD TO PROVE exists ψ :  BlMu L × [Spec(A)] Spec(B) → (BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i)))  over Spec(B)

--           -cf Proof.pdf for details

--     Have I1: ψ ∘ θ = id by unicity part of universal prop of blowups

--     Have I2: θ ∘ ψ = id because these are morphisms over BlMu L and because open imm are preserved by pullabck and because of  lemma_open_eq below


lemma lemma_open_eq (U : Scheme) (i : U ⟶ X) [IsOpenImmersion i]

  (f: U ⟶ U) (hi : i = f ≫ i) : f = 𝟙 _:= by
  sorry
-- since i is injective as a set map, we have f=id as a set map

--                                    it is enough to prove that for any open of U they equal as sheaf morphism

--                                    this is trivial from definition of open immersions

--                                    e.g. AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.scheme_toScheme  sorry



def ideal_loc (X: Scheme) (Z: PreClos X) (γ : Z.cov.J) : Z.indnumb → Ideal (Z.cov.obj γ) :=
  fun (i : Z.indnumb) => Z.ideal i γ


def Proj_loc  (X: Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme :=
  BlMu (A := Z.cov.obj γ) (ideal_loc X Z γ)

instance (X : Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  :
    Scheme.Over (Proj_loc X Z γ) (Spec (Z.cov.obj γ)) :=
  BlMuOverSpec (ideal_loc X Z γ)

instance (X : Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  :
    Scheme.Over (Proj_loc X Z γ) X where
  hom := (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) ≫
    Z.cov.map γ

def open_pair (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) : Scheme :=
  pullback (Z.cov.map γ) (Z.cov.map δ)

def open_pair_map (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) : open_pair X Z  γ δ  ⟶ X :=
  (pullback.fst  (Z.cov.map γ) (Z.cov.map δ)) ≫ (Z.cov.map γ)

lemma open_pair_map_equal (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) :
    open_pair_map X Z  γ δ  =
    (pullback.snd  (Z.cov.map γ) (Z.cov.map δ)) ≫ (Z.cov.map δ)  := by
  -- this is a pullback square, in partcular commutative
  sorry


lemma open_pair_map_is_open (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) :
  IsOpenImmersion <| open_pair_map X Z γ δ := by
    --pullback.fst is an open immersion because open immersion is stable by base change by
    --- AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
    ---now it is enough to use that a composition of open immersion is openimmersion
          ---- AlgebraicGeometry.IsOpenImmersion.comp
    sorry

/-
      Z_β
      |
Z_γ -> X
-/
def Proj_loc_pair (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  : Scheme :=
    pullback (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
      (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))
    --inverse image of open_pair in Bl (ideal_loc Z γ)


/-
     X
     |
U -> S
-/
abbrev restrictToOpen {X X' U S : Scheme} [X.Over S] [X'.Over S] (f : X ⟶ X') [Scheme.Hom.IsOver f S]
  (i : U ⟶ S) : (pullback (X ↘ S) i) ⟶ (pullback (X' ↘ S) i) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)

instance (X X' U S : Scheme) [X.Over S] [X'.Over S] (f : X ⟶ X') [Scheme.Hom.IsOver f S]
    (i : U ⟶ S) :
    Scheme.Hom.IsOver (restrictToOpen f i) U := by
  simp only [Scheme.Hom.isOver_iff]
  delta restrictToOpen
  change _ ≫ (pullback.snd _ _) = pullback.snd _ _
  simp

def Proj_loc_pair_mor (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]:
  Proj_loc_pair X Z γ δ ⟶ open_pair X Z γ δ  :=
    pullback.fst (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
      (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))


instance (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  (Proj_loc_pair X Z γ δ).Over (open_pair X Z γ δ) where
  hom := Proj_loc_pair_mor _ _ _ _

instance (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  (Proj_loc_pair X Z δ γ).Over (open_pair X Z γ δ) where
  hom := Proj_loc_pair_mor _ _ _ _ ≫ (pullbackSymmetry _ _).hom


/-
U ×_X U'  U
          | open immersion
          v
X' ------> X
-/
lemma Proj_loc_pair_open (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  ∃! (φ : pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom)),
      Scheme.Hom.IsOver φ (Spec C) := by sorry
  --  because it is an iso byy base_change_Bl_open

def Proj_loc_pair_open_φ (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom) :=
  Classical.choose (Proj_loc_pair_open X Z γ δ C i)

lemma Proj_loc_pair_open_φ_isOver (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.Hom.IsOver (Proj_loc_pair_open_φ X Z γ δ C i) (Spec C) :=
  Classical.choose_spec (Proj_loc_pair_open X Z γ δ C i) |>.1

lemma Proj_loc_pair_open_φ_uniq (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    ∀ φ' : pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom),
      Scheme.Hom.IsOver φ' (Spec C) → φ' = Proj_loc_pair_open_φ X Z γ δ C i :=
  Classical.choose_spec (Proj_loc_pair_open X Z γ δ C i) |>.2


def Proj_loc_pair_lemm (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]:
  ∃! (f : (Proj_loc_pair X Z γ δ) ⟶  (Proj_loc_pair X Z δ γ)),

  (∃ (pf : Scheme.Hom.IsOver f (open_pair X Z γ δ)),
    ∀ (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i],
      restrictToOpen f i =
      (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
      (pullbackSymmetry _ _).hom) := sorry
  --   restriction of f
  --  to U is given byy Proj_loc_pair_open X Z γ δ U := by
  --   because it is an iso byy base_change_Bl_open
    -- sorry

def Proj_loc_pair_swap (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    (Proj_loc_pair X Z γ δ) ⟶  (Proj_loc_pair X Z δ γ) :=
  Classical.choose (Proj_loc_pair_lemm X Z γ δ)

instance Proj_loc_pair_swap_isOver (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.Hom.IsOver (Proj_loc_pair_swap X Z γ δ) (open_pair X Z γ δ) :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.1.1

lemma Proj_loc_pair_swap_restrict (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i] :
    restrictToOpen (Proj_loc_pair_swap X Z γ δ) i =
    (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
    (pullbackSymmetry _ _).hom :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.1.2 C i

lemma Proj_loc_pair_swap_uniq (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (f : Proj_loc_pair X Z γ δ ⟶ Proj_loc_pair X Z δ γ)
  (is_over : Scheme.Hom.IsOver f (open_pair X Z γ δ))
  (affine : ∀ (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i],
    restrictToOpen f i =
    (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
    (pullbackSymmetry _ _).hom) :
    f = Proj_loc_pair_swap X Z γ δ :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.2 f ⟨is_over, affine⟩

lemma Proj_loc_pair_iso (X:Scheme)  (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  IsIso (Proj_loc_pair_swap X Z γ δ) := by sorry
  --  this is local

def PreBlGlob  (Z: PreClos X) [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme.GlueData where
  J := Z.cov.J
  U γ := Proj_loc X Z γ
  V pair := Proj_loc_pair X Z pair.1 pair.2
  f γ δ := pullback.snd _ _
  f_mono γ δ := inferInstance
  f_hasPullback := inferInstance
  f_id i := by infer_instance
  t γ δ := Proj_loc_pair_swap X Z γ δ
  t_id i := by
    dsimp
    symm
    apply Proj_loc_pair_swap_uniq
    · sorry
    · sorry
  t' i j k := sorry
  t_fac := sorry
  cocycle := sorry
  f_open := inferInstance

abbrev BlGlob (Z: PreClos X) [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme :=
  Scheme.GlueData.glued (PreBlGlob Z)

instance (Z: PreClos X) [DecidableEq Z.indnumb]
  [Fintype Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  Scheme.Over (BlGlob Z) X where
  hom := Multicoequalizer.desc _ _
    (fun γ : Z.cov.J => Proj_loc X Z γ ↘ X) <| by
    rintro ⟨γ, δ⟩
    simp only [MultispanShape.prod_L, GlueData.diagram_left, MultispanShape.prod_fst,
      GlueData.diagram_right,
      MultispanShape.prod_snd] at γ ⊢
    change pullback.snd _ _ ≫ _ = (Proj_loc_pair_swap X Z γ δ ≫ pullback.snd _ _) ≫ _
    simp only [Category.assoc]
    sorry



/-
{T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃! φ :  T ⟶ BlMu L,  Scheme.Hom.IsOver φ (Spec A) := by
-/
lemma PreProjBlowup_UnivProp_unicity (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z)
    (φ φ' : T ⟶ BlGlob Z)
    (φ_over : Scheme.Hom.IsOver φ X)
    (φ'_over : Scheme.Hom.IsOver φ' X)
    : φ = φ'  := by sorry
      --  use locall
      --  sorry

lemma PreProjBlowup_UnivProp_existence
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z) :
    ∃  φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X := by
        -- glue local map
        sorry

lemma PreProjBlowup_UnivProp
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [Fintype Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z) :
    ∃! φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X := by
  obtain ⟨φ, hφ⟩ := PreProjBlowup_UnivProp_existence Z cond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact PreProjBlowup_UnivProp_unicity Z cond φ φ' hφ hφ' |>.symm

lemma PreProjBlowup_rel (Z' Z'' : PreClos X) (eq: Quotient.mk' Z' = Quotient.mk' Z'')
    {T : Scheme} [T.Over X]
    [DecidableEq Z'.indnumb]
    [Fintype Z'.indnumb]
    [Fintype Z''.indnumb]
    [DecidableEq Z''.indnumb]
    [(i : Z'.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z'.indnumb))]
    [(i : Z''.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z''.indnumb))]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z') :
  ∃! (e : BlGlob Z' ≅ BlGlob Z''), Scheme.Hom.IsOver e.hom X := by
      --  PreProjBlowup_UnivProp
      sorry


-- abbrev GlobalBlowup (Z: Clos X) : Scheme := by classical exact BlGlob Z.out


-- #exit

-- ----NEW SECTION ON MULTICENTERED DILATATIONS FOR DEFORMATIONS

-- variable (X) in
-- structure PreDilCent where
--   (indnumb : Type u)
--   -- (clotop : indnumb → Closeds X)
--   (subschemeclo: indnumb → Scheme)
--   (subschemepri: indnumb → Scheme)
--   -- (condset : ∀ i : indnumb, clotop i ≃ₜ (subscheme i)) -- maybe unnecessary?
--   [over_clo : ∀ (i : indnumb), Scheme.Over (subschemeclo i) X]
--   [over_pri : ∀ (i : indnumb), Scheme.Over (subschemepri i) X]
--   -- eq_cond (i j : indnumb) (eq : i = j) :
--   --   Scheme.Hom.IsOver (eqToHom (by rw [eq]) : subscheme i ⟶ subscheme j) X
--   cov : Scheme.AffineCover.{u, u} (P := @IsOpenImmersion) X
--   idealclo: ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ)
--   idealpri: ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ)
--   -- the following is a condition saying that the ideal is principal
--   idealpricond : ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ) is principal
--   condisoclo : ∀ (i : indnumb) (γ : cov.J),
--     Spec (CommRingCat.of (cov.obj γ ⧸ idealclo i γ)) ≅
--     pullback (f := subschemeclo i ↘ X) (g := cov.map γ)
--   condisopri : ∀ (i : indnumb) (γ : cov.J),
--     Spec (CommRingCat.of (cov.obj γ ⧸ idealpri i γ)) ≅
--     pullback (f := subschemepri i ↘ X) (g := cov.map γ)
--   condoverclo : ∀ (i : indnumb) (γ : cov.J),
--     Scheme.Hom.IsOver (condisoclo i γ).hom
--       (Spec (CommRingCat.of (cov.obj γ)))
--   condoverpri : ∀ (i : indnumb) (γ : cov.J),
--     Scheme.Hom.IsOver (condisopri i γ).hom
--       (Spec (CommRingCat.of (cov.obj γ)))


--   --    THEN THE SAME METHODS THAN FOR BLOWUPS WILL GIVE DILATATIONS
