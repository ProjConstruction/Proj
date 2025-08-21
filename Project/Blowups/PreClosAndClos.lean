import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Over
import Mathlib.RingTheory.TensorProduct.Quotient

import Project.ForMathlib.CubeIdentity
import Project.ForMathlib.AlgEquivRestrictScalars
import Project.ForMathlib.Flat

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct

variable {X : Scheme.{u+1}}

section over_instances

instance (R : Type*) [CommRing R] (I : Ideal R) :
    Scheme.Over (Spec (CommRingCat.of (R ⧸ I))) (Spec <| CommRingCat.of R)  where
  hom := Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk I

lemma spec_quotient_ideal_over_eq {R : Type*} [CommRing R] (I : Ideal R) :
    (Spec (CommRingCat.of (R ⧸ I))) ↘ (Spec <| CommRingCat.of R) =
    Spec.map (CommRingCat.ofHom <| Ideal.Quotient.mk I) := rfl

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) Z where
  hom := pullback.fst f g ≫ f

lemma pullback_over_base (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ↘ Z = pullback.fst f g ≫ f := rfl

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) X where
  hom := pullback.fst f g

lemma pullback_over_left (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ↘ X = pullback.fst f g := rfl

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) Y where
  hom := pullback.snd f g

lemma pullback_over_right (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ↘ Y = pullback.snd f g := rfl

end over_instances

variable (X) in
structure PreClos where
  (indnumb : Type)
  (subscheme: indnumb → Scheme)
  [over : ∀ (i : indnumb), Scheme.Over (subscheme i) X]
  cov : Scheme.AffineCover.{u+1} (P := @IsOpenImmersion) X
  ideal: ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ)
  condiso : ∀ (i : indnumb) (γ : cov.J),
    Spec (CommRingCat.of (cov.obj γ ⧸ ideal i γ)) ≅
    pullback (f := subscheme i ↘ X) (g := cov.map γ)
  condover : ∀ (i : indnumb) (γ : cov.J),
    Scheme.Hom.IsOver (condiso i γ).hom
      (Spec (CommRingCat.of (cov.obj γ)))

attribute [instance] PreClos.over

lemma PreClos.index_eq_triangle {X : Scheme} (Z : PreClos X) (i j : Z.indnumb) (eq : i = j) :
    Scheme.Hom.IsOver (eqToHom (by rw [eq]) : Z.subscheme i ⟶ Z.subscheme j) X := by
  subst eq
  simp

-- def PreClos_on_refinement (Z: PreClos) (cov': refinment of Z.cov) : X.Preclos :=
--    indnumb : Z.indnumb
--    clotop: indnumb → closed (underlying top of X)
--    subscheme: indnumb → AlgebraicGeometry.Scheme
--    condset : clotop i = underlying top (subscheme i)
--    mor: indnumb → subscheme i →sch X
--    cov: cov'
--    ideal:   indnumb → cov.index → image ideal A γ
--    condiso: use condiso Z-/


structure relStructure (Z Z' : PreClos X) where -- := fun Z Z' =>
  indnumb_equiv :  Z.indnumb ≃ Z'.indnumb
  subscheme_iso : ∀ i, Z.subscheme i ≅ Z'.subscheme (indnumb_equiv i)
  subscheme_iso_over : ∀ i, Scheme.Hom.IsOver (subscheme_iso i).hom X

@[refl]
def relStructure.refl {X : Scheme} (Z : PreClos X) : relStructure Z Z where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Equiv.refl_apply, Scheme.Hom.isOver_iff]


@[symm]
def relStructure.symm {X : Scheme} {Z Z' : PreClos X} (R : relStructure Z Z') : relStructure Z' Z where
  indnumb_equiv := R.indnumb_equiv.symm
  subscheme_iso i := eqToIso (by simp) ≪≫ (R.subscheme_iso (R.indnumb_equiv.symm i)).symm
  subscheme_iso_over i := by
    have := R.subscheme_iso_over (R.indnumb_equiv.symm i)
    simp only [Scheme.Hom.isOver_iff] at this
    simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Scheme.Hom.isOver_iff, Category.assoc]
    rw [← this]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Scheme.Hom.isOver_iff]
    apply PreClos.index_eq_triangle
    simp

@[trans]
def relStructure.trans {X : Scheme} {Z Z' Z'' : PreClos X}
    (R : relStructure Z Z') (R' : relStructure Z' Z'') : relStructure Z Z'' where
  indnumb_equiv := R.indnumb_equiv.trans R'.indnumb_equiv
  subscheme_iso i := R.subscheme_iso _ ≪≫ R'.subscheme_iso _
  subscheme_iso_over i := by
    have o1 := R.subscheme_iso_over i
    have o2 := R'.subscheme_iso_over (R.indnumb_equiv i)
    simp only [Scheme.Hom.isOver_iff] at o1 o2 ⊢
    rw [← o1, ← o2]
    simp


variable (X) in
def rel : PreClos X → PreClos X → Prop := fun Z Z' => Nonempty (relStructure Z Z')


variable (X) in
instance relSetoid : Setoid (PreClos X) where
  r := rel X
  iseqv :=
    { refl x := ⟨.refl _⟩
      symm := Nonempty.map .symm
      trans := by
        rintro _ _ _ ⟨R⟩ ⟨R'⟩
        exact ⟨R.trans R'⟩ }

variable (X)
def Clos := Quotient (relSetoid X)

structure PrePri extends PreClos X where
  [prin : ∀ i γ, ideal i γ |>.IsPrincipal]

structure IsPrePri (Z : PreClos X) : Prop where
  prin : ∀ i γ, Z.ideal i γ |>.IsPrincipal

attribute [instance] PrePri.prin

structure PreCars extends PrePri X where
  nonzerodiv : ∀ i γ, Submodule.IsPrincipal.generator (ideal i γ) ∈ nonZeroDivisors (cov.obj γ)

structure IsPreCars (Z : PreClos X) extends IsPrePri _ Z where
  nonzerodiv : ∀ i γ, Submodule.IsPrincipal.generator (Z.ideal i γ) ∈ nonZeroDivisors (Z.cov.obj γ)

structure IsPri (Z : Clos X) : Prop where
  exists_rep : ∃ (Z' : PreClos X), IsPrePri _ Z' ∧ Quotient.mk'' Z' = Z

def Pri : Set (Clos X) := {x : Clos X | IsPri _ x}

structure IsCars (Z : Clos X) : Prop where
  exists_rep : ∃ (Z' : PreClos X), IsPreCars _ Z' ∧ Quotient.mk'' Z' = Z


def IsCars.isPri (Z : Clos X) : IsCars _ Z → IsPri _ Z := by sorry

def Cars : Set (Pri X) := {x : Pri X | IsCars _ x.1}

def CarsAsSubsetOfClos : Set (Clos X) := {x : Clos X | IsCars _ x }

def pull_loc_cov (X: Scheme) (Z: PreClos X) (X': Scheme) (g : X' ⟶  X) (γ : Z.cov.J ) :=
    Scheme.affineOpenCover (pullback g (Z.cov.map γ))

@[simps]
def  pull_cov (X: Scheme) (Z : PreClos X) (X' : Scheme) (g : X' ⟶  X) :
            Scheme.AffineCover (P := @IsOpenImmersion) X' where
    J := (γ : Z.cov.J) × (pull_loc_cov X Z X' g γ).J
    obj p := (pull_loc_cov X Z X' g p.1).obj p.2
    map p := (pull_loc_cov X Z X' g p.1).map p.2 ≫ (pullback.fst g (Z.cov.map p.1))
    f (x : X') := ⟨Z.cov.f (g.base x), by
      have h1 : x ∈ g.base ⁻¹' Set.range (Z.cov.map (Z.cov.f <| g.base x)).base :=
        Z.cov.covers (g.base x)
      rw [← Scheme.Pullback.range_fst (f := g) (g := Z.cov.map (Z.cov.f <| g.base x))] at h1
      exact (pull_loc_cov X Z X' g (Z.cov.f <| g.base x)).f <| h1.choose⟩
    covers (x : X') := by
      dsimp
      simp only [Set.mem_range, Function.comp_apply]
      have h1 : x ∈ g.base ⁻¹' Set.range (Z.cov.map (Z.cov.f <| g.base x)).base :=
        Z.cov.covers (g.base x)
      rw [← Scheme.Pullback.range_fst (f := g) (g := Z.cov.map (Z.cov.f <| g.base x))] at h1
      obtain ⟨y, hy⟩ := (pull_loc_cov X Z X' g (Z.cov.f <| g.base x)).covers h1.choose
      use y
      rw [hy]
      exact h1.choose_spec
    map_prop j :=  IsOpenImmersion.comp ((pull_loc_cov X Z X' g j.fst).map j.snd)
          (pullback.fst g (Z.cov.map j.fst))

def  pull_mor_ring (X: Scheme)  (Z : PreClos X) (X' : Scheme) (f : X' ⟶  X)
      (γβ : (pull_cov X Z X' f).J) :
    Z.cov.obj γβ.1 ⟶ (pull_loc_cov X Z X' f γβ.1).obj γβ.2 := by
  letI F := (pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.snd _ _
  exact (Scheme.ΓSpecIso _).inv ≫ Scheme.Γ.map (Opposite.op F) ≫ (Scheme.ΓSpecIso _).hom


  -- have := (Scheme.ΓSpecIso (Spec ((pull_loc_cov X Z X' f γβ.fst).obj γβ.snd))).inv
  -- U_β -> X' ×_{X} U_γ -> U_γ
    --- an element in cov.index is a pair (γ, β)
    -- We have morphisms of schemes U_β --pullback U_γ -> U_γ
    --- by composition we get a morphism of schemes U_β → U_γ
    -- since U_β and U_γ are affine, we get morphism of rings Aγ →   Aβ by the antiequivalence
    -- between the categories Affschemes and CommRings


def pull_ideal  (X:Scheme)  (Z: PreClos X) (X': Scheme) (f: X' ⟶  X)
  (γβ : (pull_cov X Z X' f).J) (i: Z.indnumb) :
  Ideal (CommRingCat.of ((pull_loc_cov X Z X' f γβ.1).obj γβ.2)) :=
  Ideal.map (pull_mor_ring X Z X' f γβ).hom (Z.ideal i γβ.1)
    -- We define ideal i γ β as the ideal image of ideal i γ under Aγ →   Aβ

def lemma_iso (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
  (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A] ((A ⧸ I)⊗[A] B) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I |>.restrictScalars A).trans <|
    Algebra.TensorProduct.comm _ _ _

set_option maxHeartbeats 400000 in
def pullback_PreClos_condiso {X' : Scheme} {f : X' ⟶  X} {Z: PreClos X}
    (γβ : (pull_cov X Z X' f).J) (i: Z.indnumb) :
    Spec (CommRingCat.of (((pull_cov X Z X' f).obj γβ) ⧸ pull_ideal X Z X' f γβ i)) ≅
    pullback (pullback (Z.subscheme i ↘ X) f ↘ X') ((pull_cov X Z X' f).map γβ) :=
  show _ ≅ pullback (pullback.snd (Z.subscheme i ↘ X) f)
    ((pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.fst f (Z.cov.map γβ.1)) by
    -- let A_γβ := pull_cov X Z X' f |>.obj γβ
    -- let U_γβ : Scheme := Spec A_γβ
    -- let A_γ := Z.cov.obj γβ.1
    -- let U_γ : Scheme := Spec A_γ
    -- let J_γ := Z.ideal i γβ.1
    -- let J_γβ := pull_ideal X Z X' f γβ i
    -- let fA : A_γ ⟶ A_γβ := pull_mor_ring X Z X' f γβ
    -- let fQuot : A_γ ⟶ (CommRingCat.of (A_γ ⧸ J_γ)) := CommRingCat.ofHom (Ideal.Quotient.mk _)
    letI : Algebra (Z.cov.obj γβ.1) (pull_cov X Z X' f |>.obj γβ) :=
      RingHom.toAlgebra (pull_mor_ring X Z X' f γβ).hom
    letI : Algebra (Z.cov.obj γβ.1)
      ((pull_cov X Z X' f |>.obj γβ) ⧸  pull_ideal X Z X' f γβ i) := RingHom.toAlgebra <|
        RingHom.comp (Ideal.Quotient.mk _) (pull_mor_ring X Z X' f γβ).hom

    -- let g : U_γβ ⟶ U_γ := Spec.map fA
    -- have : Scheme.Over U_γ X :=
    -- let o_γ : U_γ ⟶ X := Z.cov.map γβ.1

    let e0 : ((pull_cov X Z X' f |>.obj γβ) ⧸ (pull_ideal X Z X' f γβ i)) ≃ₐ[Z.cov.obj γβ.1]
      ((pull_cov X Z X' f |>.obj γβ) ⊗[Z.cov.obj γβ.1] (Z.cov.obj γβ.1 ⧸ Z.ideal i γβ.1)) :=
      AlgEquiv.trans (lemma_iso _ _ _) <| Algebra.TensorProduct.comm _ _ _
    let e1 : Spec (CommRingCat.of ((pull_cov X Z X' f |>.obj γβ) ⧸ pull_ideal X Z X' f γβ i)) ≅
      Spec (CommRingCat.of ((pull_cov X Z X' f |>.obj γβ) ⊗[Z.cov.obj γβ.1] (Z.cov.obj γβ.1 ⧸ Z.ideal i γβ.1))) :=
      { hom := Spec.map <| CommRingCat.ofHom <| e0.symm.toRingHom
        inv := Spec.map <| CommRingCat.ofHom <| e0.toRingHom
        hom_inv_id := by
          rw [← Spec.map_comp]
          convert Spec.map_id (CommRingCat.of <| (pull_cov X Z X' f |>.obj γβ) ⧸ pull_ideal X Z X' f γβ i) using 2
          simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
            AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv]
          rw [← CommRingCat.ofHom_comp]
          convert CommRingCat.ofHom_id
          ext x
          exact e0.symm_apply_apply x
        inv_hom_id := by
          rw [← Spec.map_comp]
          convert Spec.map_id
            (CommRingCat.of <| (pull_cov X Z X' f |>.obj γβ) ⊗[Z.cov.obj γβ.1] (Z.cov.obj γβ.1 ⧸ Z.ideal i γβ.1)) using 2
          simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
            AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv]
          rw [← CommRingCat.ofHom_comp]
          convert CommRingCat.ofHom_id
          ext x
          exact e0.apply_symm_apply x }
    let e3 :
      -- Spec A_γβ ×[Spec A_γ] Spec (A_γ ⧸ J_γ)
      pullback (Spec.map <| pull_mor_ring X Z X' f γβ) (Spec.map <| CommRingCat.ofHom (Ideal.Quotient.mk _)) ≅
      -- U_γβ ×[U_γ] (U_γ ×[X] Z)
      pullback (Spec.map <| pull_mor_ring X Z X' f γβ) (pullback.fst (Z.cov.map γβ.1) (Z.subscheme i ↘ X)) :=
    { hom := pullback.map _ _ _ _ (𝟙 _)
        ((Z.condiso i γβ.1).hom ≫ (pullbackSymmetry _ _).hom)
        (𝟙 _) (by simp) (by
          simp only [Category.comp_id, Category.assoc]
          rw [pullbackSymmetry_hom_comp_fst]
          have := Z.condover i γβ.1
          rw [Scheme.Hom.isOver_iff] at this
          exact this.symm)
      inv := pullback.map _ _ _ _ (𝟙 _)
        ((pullbackSymmetry _ _).hom ≫ (Z.condiso i γβ.1).inv)
        (𝟙 _) (by simp) (by
          simp only [Category.comp_id, Category.assoc]
          rw [← Iso.inv_comp_eq, pullbackSymmetry_inv_comp_fst, eq_comm, Iso.inv_comp_eq]
          have := Z.condover i γβ.1
          rw [Scheme.Hom.isOver_iff] at this
          exact this.symm)
      hom_inv_id := by
        ext <;> try simp
        have eq : (pullbackSymmetry (Z.cov.map γβ.1) (Z.subscheme i ↘ X)).hom =
          (pullbackSymmetry (Z.subscheme i ↘ X) (Z.cov.map γβ.fst)).inv := by
            ext
            · simp only [pullbackSymmetry_hom_comp_fst]
              rw [pullbackSymmetry_inv_comp_fst]
            · simp only [pullbackSymmetry_hom_comp_snd]
              rw [pullbackSymmetry_inv_comp_snd]
        rw [reassoc_of% eq, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      inv_hom_id := by
        have eq : (pullbackSymmetry (Z.cov.map γβ.1) (Z.subscheme i ↘ X)).hom =
          (pullbackSymmetry (Z.subscheme i ↘ X) (Z.cov.map γβ.fst)).inv := by
            ext
            · simp only [pullbackSymmetry_hom_comp_fst]
              rw [pullbackSymmetry_inv_comp_fst]
            · simp only [pullbackSymmetry_hom_comp_snd]
              rw [pullbackSymmetry_inv_comp_snd]
        ext
        · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          Category.comp_id, Category.id_comp]
        · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          limit.lift_π_assoc, cospan_right, Iso.inv_hom_id_assoc, pullbackSymmetry_hom_comp_fst,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]
        · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          limit.lift_π_assoc, cospan_right, Iso.inv_hom_id_assoc, Category.id_comp]
          rw [reassoc_of% eq, Iso.inv_hom_id_assoc] }


    refine e1 ≪≫ (pullbackSpecIso _ _ _).symm ≪≫ e3 ≪≫ pullback.squash₃ _ _ _ ≪≫ pullback.congrHom (by
      simp only [pull_mor_ring, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc]
      rw [pullback.condition]
      simp only [← Category.assoc]
      congr 1
      change (ΓSpec.adjunction.unit.app _ ≫ (Scheme.Spec).map _) ≫ _ = _
      simp only [Functor.id_obj, Scheme.Spec_obj, Functor.comp_obj, Functor.rightOp_obj,
        Scheme.Γ_obj, ΓSpec.adjunction_unit_app, Scheme.Γ_map, Quiver.Hom.unop_op', Scheme.comp_app,
        Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier, Spec.topObj_forget,
        Spec.sheafedSpaceObj_presheaf, Opens.map_top, Scheme.Spec_map, Spec.map_comp,
        Category.assoc]
      change _ ≫ Spec.map (Scheme.Hom.appTop _) ≫ _ = _
      -- simp only [Functor.id_obj, Scheme.Spec_obj, Functor.comp_obj, Functor.rightOp_obj,
      --   Scheme.Γ_obj, ΓSpec.adjunction_unit_app, Scheme.Γ_map, Quiver.Hom.unop_op', Scheme.comp_app,
      --   Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier, Spec.topObj_forget,
      --   Spec.sheafedSpaceObj_presheaf, Opens.map_top, Scheme.Spec_map, Spec.map_comp,
      --   Category.assoc]
      rw [← Scheme.toSpecΓ_naturality_assoc]
      change _ ≫ _ ≫ Spec.map (Scheme.Hom.appTop _) ≫ _ = _
      rw [← Scheme.toSpecΓ_naturality_assoc]
      simp only [Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier,
        Spec.topObj_forget, Spec.sheafedSpaceObj_presheaf]
      congr 1
      convert Category.comp_id _
      erw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp) rfl ≪≫ (pullback.squash₃' _ _ _).symm

set_option maxHeartbeats 800000 in
def pullback_PreClos_condover {X' : Scheme} {f : X' ⟶  X} {Z: PreClos X}
    (γβ : (pull_cov X Z X' f).J) (i: Z.indnumb) :
    Scheme.Hom.IsOver (pullback_PreClos_condiso X γβ i).hom
      (Spec (CommRingCat.of ((pull_cov X Z X' f).obj γβ))) := by
  rw [Scheme.Hom.isOver_iff]
  simp only [pull_cov_obj, pull_cov_map, pullback_PreClos_condiso, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    Ideal.Quotient.algebraMap_eq, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom,
    pullback.squash₃'_inv, Category.assoc]
  erw [pullbackLeftPullbackSndIso_inv_snd_snd (f := Z.subscheme i ↘ X) (g := f)
    (g' := (pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.fst f (Z.cov.map γβ.1))]
  simp only [pullbackSymmetry_inv_comp_snd, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id, pullback.squash₃_hom_fst]
  rw [spec_quotient_ideal_over_eq]

  letI : Algebra (Z.cov.obj γβ.1) (pull_cov X Z X' f |>.obj γβ) :=
      RingHom.toAlgebra (pull_mor_ring X Z X' f γβ).hom
  letI : Algebra (Z.cov.obj γβ.fst) ((pull_loc_cov X Z X' f γβ.fst).obj γβ.snd) :=
      RingHom.toAlgebra (pull_mor_ring X Z X' f γβ).hom
  letI : Algebra (Z.cov.obj γβ.1)
      ((pull_cov X Z X' f |>.obj γβ) ⧸  pull_ideal X Z X' f γβ i) := RingHom.toAlgebra <|
        RingHom.comp (Ideal.Quotient.mk _) (pull_mor_ring X Z X' f γβ).hom

  erw [pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp only [lemma_iso, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
  Algebra.TensorProduct.includeLeftRingHom_apply]
  change AlgEquiv.symm _ _ = _
  erw [AlgEquiv.symm_trans_apply]
  simp only [Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_trans_apply]
  rw [AlgEquiv.restrictScalars_symm]
  simp only [AlgEquiv.coe_restrictScalars']
  erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  -- change Submodule.Quotient.mk _ = _
  simp only [one_smul, Ideal.Quotient.mk_eq_mk]
  rfl


def pullback_PreClos (X' : Scheme) (f: X' ⟶  X) (Z: PreClos X)  : PreClos X'  where
  indnumb := Z.indnumb
  subscheme i := pullback (Z.subscheme i ↘ X) f
  over i := ⟨pullback.snd _ _⟩
  cov := pull_cov X Z X' f
  ideal i γβ :=  pull_ideal X Z X' f γβ i
  condiso i γβ := pullback_PreClos_condiso _ γβ i
  condover := by
    intro i γβ
    exact pullback_PreClos_condover _ γβ i

def pullback_lem (Z Z': PreClos X) (T : Scheme) (f : T ⟶ X) (e : relStructure.{u} Z Z') :
      relStructure (pullback_PreClos X T f Z)  (pullback_PreClos X T f Z') where
  indnumb_equiv := e.indnumb_equiv
  subscheme_iso i :=
  { hom := pullback.map _ _ _ _ (e.subscheme_iso _).hom (𝟙 _) (𝟙 _) (by
      simp only [Category.comp_id]
      have := e.subscheme_iso_over i
      simp only [comp_over]) (by simp)
    inv := pullback.map _ _ _ _ (e.subscheme_iso _).inv (𝟙 _) (𝟙 _) (by
      simp only [Category.comp_id]
      have := e.subscheme_iso_over i
      rw [Scheme.Hom.isOver_iff] at this
      rw [← this]
      simp only [Iso.inv_hom_id_assoc]
      rfl) (by simp)
    hom_inv_id := by rw [pullback.map_comp]; simp only [Iso.hom_inv_id, Category.comp_id,
      pullback.map_id]; rfl
    inv_hom_id := by rw [pullback.map_comp]; simp only [Iso.inv_hom_id, Category.comp_id,
      pullback.map_id]; rfl }
  subscheme_iso_over i := by
    have := e.subscheme_iso_over i
    rw [Scheme.Hom.isOver_iff] at this ⊢
    simp only
    change _ ≫ pullback.snd _ _ = pullback.snd _ _
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]


variable {X}
def pullback_Clos {X': Scheme} (f: X' ⟶  X): Clos X → Clos X' :=
  Quotient.map (pullback_PreClos X X' f) <| fun Z Z' e => Nonempty.map (pullback_lem X Z Z' X' f) e

lemma pullback_PrePri (X' : Scheme) (f: X' ⟶  X) (Z: PreClos X) (hZ : IsPrePri _ Z)  :
    IsPrePri _ <| pullback_PreClos _ _ f Z := by
  fconstructor
  rintro i ⟨γ, β⟩
  apply Submodule.IsPrincipal.map_ringHom
  exact hZ.prin i γ

lemma pullback_PreCars (X' : Scheme) (f: X' ⟶  X) [flat_f : AlgebraicGeometry.Flat f]
    (Z: PreClos X) (hZ : IsPreCars _ Z)  :
    IsPreCars _ <| pullback_PreClos _ _ f Z := by
  refine ⟨pullback_PrePri X' f Z hZ.toIsPrePri, ?_⟩
  rintro i ⟨γ, β⟩
  have := hZ.nonzerodiv i γ
  have := hZ.prin i γ
  have := pullback_PrePri X' f Z hZ.1 |>.prin i
  -- change Submodule.IsPrincipal.generator (Ideal.map _ _) ∈ _

  have : Submodule.IsPrincipal.generator ((pullback_PreClos X X' f Z).ideal i ⟨γ, β⟩) =
    ((pull_mor_ring X Z X' f ⟨γ, β⟩)) (Submodule.IsPrincipal.generator (Z.ideal i γ)) := by

    sorry
  rw [this]

  let F : pullback f (Z.cov.map γ) ⟶ X := pullback.fst _ _ ≫ f
  haveI flat_F : AlgebraicGeometry.Flat F := AlgebraicGeometry.Flat.comp _ _
  apply RingHom.Flat.preserves_nonzeroDivisors
-- exact for affine
  · have := flat_F.flat_of_affine_subset
      ⟨Z.cov.map γ |>.opensRange, isAffineOpen_opensRange (Z.cov.map γ)⟩
      ⟨(pull_loc_cov X Z X' f γ).map β |>.opensRange, isAffineOpen_opensRange _⟩ sorry
    convert RingHom.Flat.comp ?_ (RingHom.Flat.comp this ?_) using 1

    pick_goal 2
    · refine RingHom.comp (CommRingCat.Hom.hom <| X.presheaf.map <| eqToHom ?_) <|
        (IsOpenImmersion.ΓIso (Z.cov.map γ) ⊤ |>.commRingCatIsoToRingEquiv.toRingHom).comp <|
        CommRingCat.Hom.hom <| Scheme.ΓSpecIso (Z.cov.obj γ) |>.inv
      · aesop

    pick_goal 3
    · refine RingHom.comp (CommRingCat.Hom.hom <| Scheme.ΓSpecIso _ |>.hom) <|
        (IsOpenImmersion.ΓIsoTop ((pull_loc_cov X Z X' f γ).map β)) |>.commRingCatIsoToRingEquiv.symm.toRingHom.comp <|
        CommRingCat.Hom.hom <| (pullback f (Z.cov.map γ)).presheaf.map <| eqToHom ?_
      aesop
    · simp only [Opens.map_top, RingEquiv.toRingHom_eq_coe,
        Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp]
      simp only [Category.assoc, CommRingCat.hom_comp]
      rw [show (IsOpenImmersion.ΓIsoTop ((pull_loc_cov X Z X' f γ).map β)).commRingCatIsoToRingEquiv.symm =
        (IsOpenImmersion.ΓIsoTop ((pull_loc_cov X Z X' f γ).map β)).inv.hom by rfl]
      simp only [eqToHom_refl, CategoryTheory.Functor.map_id, CommRingCat.hom_id,
        RingHomCompTriple.comp_eq, ← CommRingCat.hom_comp, Category.assoc,
        Scheme.Hom.map_appLE_assoc]
      congr 1
      change _ ≫ _ ≫ _ = _
      congr 1
      simp only [Scheme.Γ_obj, Spec.locallyRingedSpaceObj_toSheafedSpace,
        Spec.sheafedSpaceObj_carrier, Spec.topObj_forget, Spec.sheafedSpaceObj_presheaf,
        Scheme.Γ_map, Quiver.Hom.unop_op', Scheme.comp_app, Opens.map_top, ← Category.assoc]
      congr 1
      simp only [Category.assoc]
      rw [← Iso.inv_comp_eq]
      simp only [IsOpenImmersion.ΓIso_inv, Opens.map_top]
      simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
        eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appLE_map_assoc]
      rw [Scheme.Hom.appIso_hom]
      simp only [eqToHom_op]
      change _ ≫ Scheme.Hom.appTop _ ≫ Scheme.Hom.appTop _ = _
      rw [show Scheme.Hom.appTop (pullback.snd f (Z.cov.map γ)) ≫ Scheme.Hom.appTop ((pull_loc_cov X Z X' f γ).map β) =
        Scheme.Hom.appTop ((pull_loc_cov X Z X' f γ).map β ≫ pullback.snd f (Z.cov.map γ)) by rfl]

      rw [show Scheme.Hom.app ((pull_loc_cov X Z X' f γ).map β) ((pull_loc_cov X Z X' f γ).map β ''ᵁ ⊤) =
        Scheme.Hom.appLE ((pull_loc_cov X Z X' f γ).map β) _ _ (by simp) by rfl]
      erw [Scheme.Hom.appLE_map']
      swap
      · simp
      swap
      · simp
      aesop_cat
    · apply RingHom.Flat.comp
      · apply RingHom.Flat.comp
        · apply RingHom.Flat.of_bijective
          exact ConcreteCategory.bijective_of_isIso ..
        · apply RingHom.Flat.of_bijective
          exact RingEquiv.bijective _
      · apply RingHom.Flat.of_bijective
        rw [Function.bijective_iff_has_inverse]
        use (CommRingCat.Hom.hom <| X.presheaf.map (eqToHom (by aesop)))
        constructor
        · intro x
          rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, eqToHom_trans, eqToHom_refl]
          simp
        · intro x
          rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, eqToHom_trans, eqToHom_refl]
          simp
    · apply RingHom.Flat.comp
      · apply RingHom.Flat.comp
        · apply RingHom.Flat.of_bijective
          exact ConcreteCategory.bijective_of_isIso ..
        · apply RingHom.Flat.of_bijective
          exact RingEquiv.bijective _
      · apply RingHom.Flat.of_bijective
        exact ConcreteCategory.bijective_of_isIso ..
  · assumption

lemma pullback_IsCars (X' : Scheme) (f: X' ⟶  X) [AlgebraicGeometry.Flat f]
    (Z: Clos X) (hZ : IsCars _ Z)  :
    IsCars _ <| pullback_Clos f Z := by
  obtain ⟨Z, hZ, rfl⟩ := hZ.exists_rep
    -- exact for affine
  sorry


def pullback_Pre_assoc  (X'' X' : Scheme)
    (f': X'' ⟶  X') (f: X' ⟶  X) (Z: PreClos X):
    rel _
      (pullback_PreClos _ _ (f' ≫ f) Z)
      (pullback_PreClos _ _ f' (pullback_PreClos _ _ f Z)) := by sorry
  -- is equivalent to pullback_PreClos (X'') ( f') (pullback_PreClos (X') (f ) (Z)):=
  -- by this is trivial by assoc of fiber products sorry

lemma pullback_assoc (X'' X' : Scheme) (f': X'' ⟶  X') (f: X' ⟶  X) (Z: Clos X):
    pullback_Clos (f' ≫ f) Z = pullback_Clos f' (pullback_Clos f Z) := by
  sorry



#exit


lemma pullback_assoc  (X'' : Scheme) (X' : Scheme) (f': X'' ⟶  X') (f: X' ⟶  X) (Z: Clos X):
  pullback_Clos (X'') (f ∘ f') Z = pullback_Clos (X'') ( f') (pullback_Clos (X') (f ) (Z)):=
  by pullback_Pre_assoc sorry
