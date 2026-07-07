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
-- import Project.Proj.Sum'


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
