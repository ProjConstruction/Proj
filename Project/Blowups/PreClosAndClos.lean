import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Over
import Mathlib.RingTheory.TensorProduct.Quotient

import Project.ForMathlib.CubeIdentity

suppress_compilation

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TensorProduct

variable {X : Scheme.{u}}

section over_instances

instance (R : Type*) [CommRing R] (I : Ideal R) :
    Scheme.Over (Spec (CommRingCat.of (R ⧸ I))) (Spec <| CommRingCat.of R)  where
  hom := Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk I

open CategoryTheory

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) Z where
  hom := pullback.fst f g ≫ f

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) X where
  hom := pullback.fst f g

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) Y where
  hom := pullback.snd f g

end over_instances

variable (X) in
structure PreClos where
  (indnumb : Type u)
  [fin_indnumb : Fintype indnumb]
  (subscheme: indnumb → Scheme)
  [over : ∀ (i : indnumb), Scheme.Over (subscheme i) X]
  cov : Scheme.AffineCover.{u, u} (P := @IsOpenImmersion) X
  ideal: ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ)
  condiso : ∀ (i : indnumb) (γ : cov.J),
    Spec (CommRingCat.of (cov.obj γ ⧸ ideal i γ)) ≅
    pullback (f := subscheme i ↘ X) (g := cov.map γ)
  condover : ∀ (i : indnumb) (γ : cov.J),
    Scheme.Hom.IsOver (condiso i γ).hom
      (Spec (CommRingCat.of (cov.obj γ)))

attribute [instance] PreClos.over
attribute [instance] PreClos.fin_indnumb

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

attribute [instance] PrePri.prin

structure PreCars extends PrePri X where
  nonzerodiv : ∀ i γ, Submodule.IsPrincipal.generator (ideal i γ) ∈ nonZeroDivisors (cov.obj γ)

structure IsPreCars (Z : PreClos X) : Prop where
  prin : ∀ i γ, Z.ideal i γ |>.IsPrincipal
  nonzerodiv : ∀ i γ, Submodule.IsPrincipal.generator (Z.ideal i γ) ∈ nonZeroDivisors (Z.cov.obj γ)

def Pri : Set (Clos X) := {x : Clos X | ∃ (y : PrePri X), Quotient.mk'' y.toPreClos = x}

def Cars : Set (Pri X) := {x : Pri X | ∃ (y : PreCars X), Quotient.mk'' y.toPreClos = x.val}

def CarsAsSubsetOfClos : Set (Clos X) :=
  {x : Clos X | ∃ y : Pri X, y ∈ Cars X ∧ x = y }

def pull_loc_cov (X: Scheme.{u}) (Z: PreClos.{u} X) (X': Scheme.{u}) (g : X' ⟶  X) (γ : Z.cov.J ) :=
    Scheme.affineOpenCover (pullback g (Z.cov.map γ))

@[simps]
def  pull_cov (X: Scheme.{u}) (Z : PreClos.{u} X) (X' : Scheme.{u}) (g : X' ⟶  X) :
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
      simp only [eq_mp_eq_cast, Scheme.comp_coeBase, TopCat.coe_comp, Set.mem_range,
        Function.comp_apply]
      have h1 : x ∈ g.base ⁻¹' Set.range (Z.cov.map (Z.cov.f <| g.base x)).base :=
        Z.cov.covers (g.base x)
      rw [← Scheme.Pullback.range_fst (f := g) (g := Z.cov.map (Z.cov.f <| g.base x))] at h1
      obtain ⟨y, hy⟩ := (pull_loc_cov X Z X' g (Z.cov.f <| g.base x)).covers h1.choose
      use y
      rw [hy]
      exact h1.choose_spec
    map_prop j :=  IsOpenImmersion.comp ((pull_loc_cov X Z X' g j.fst).map j.snd)
          (pullback.fst g (Z.cov.map j.fst))

def  pull_mor_ring (X: Scheme)  (Z : PreClos X) (X' : Scheme) (f: X' ⟶  X)
      (γβ : (pull_cov X Z X' f).J) :
    Z.cov.obj γβ.1 ⟶ (pull_loc_cov X Z X' f γβ.1).obj γβ.2 := by
  let F := (pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.snd _ _
  let A : AffineSchemeᵒᵖ :=
    Opposite.op ⟨Spec ((pull_loc_cov X Z X' f γβ.fst).obj γβ.snd),
      ⟨Opposite.op <| (pull_loc_cov X Z X' f γβ.fst).obj γβ.snd, ⟨Iso.refl _⟩⟩⟩
  let B : AffineSchemeᵒᵖ :=
    Opposite.op ⟨Spec (Z.cov.obj γβ.fst), ⟨Opposite.op (Z.cov.obj γβ.fst), ⟨Iso.refl _⟩⟩⟩
  let F' : B ⟶ A := Quiver.Hom.op F
  exact (Scheme.ΓSpecIso _).inv ≫ (AffineScheme.Γ.map F') ≫ (Scheme.ΓSpecIso _).hom

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

-- @[simps]
def pullback_PreClos (X': Scheme) (f: X' ⟶  X) (Z: PreClos X)  : PreClos X'  where
  indnumb := Z.indnumb
  fin_indnumb := Z.fin_indnumb
  subscheme i := pullback (Z.subscheme i ↘ X) f
  over i := ⟨pullback.snd _ _⟩
  cov := pull_cov X Z X' f
  ideal i γβ :=  pull_ideal X Z X' f γβ i
  condiso i γβ := show _ ≅ pullback (pullback.snd (Z.subscheme i ↘ X) f)
    ((pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.fst f (Z.cov.map γβ.1)) by
    let A_γβ := pull_cov X Z X' f |>.obj γβ
    let U_γβ : Scheme := Spec A_γβ
    let A_γ := Z.cov.obj γβ.1
    let U_γ : Scheme := Spec A_γ
    let J_γ := Z.ideal i γβ.1
    let J_γβ := pull_ideal X Z X' f γβ i
    let fA : A_γ ⟶ A_γβ := pull_mor_ring X Z X' f γβ
    let fQuot : A_γ ⟶ (CommRingCat.of (A_γ ⧸ J_γ)) := CommRingCat.ofHom (Ideal.Quotient.mk _)
    letI : Algebra A_γ A_γβ := RingHom.toAlgebra fA.hom
    letI : Algebra A_γ (A_γβ ⧸ J_γβ) := RingHom.toAlgebra <| RingHom.comp (Ideal.Quotient.mk _) fA.hom

    let g : U_γβ ⟶ U_γ := Spec.map fA
    -- have : Scheme.Over U_γ X :=
    let o_γ : U_γ ⟶ X := Z.cov.map γβ.1

    let e0 : (A_γβ ⧸ J_γβ) ≃ₐ[A_γ] (A_γβ ⊗[A_γ] (A_γ ⧸ J_γ)) :=
      AlgEquiv.trans (lemma_iso A_γ A_γβ J_γ) <| Algebra.TensorProduct.comm _ _ _
    let e1 : Spec (CommRingCat.of (A_γβ ⧸ J_γβ)) ≅
      Spec (CommRingCat.of (A_γβ ⊗[A_γ] (A_γ ⧸ J_γ))) :=
      { hom := Spec.map <| CommRingCat.ofHom <| e0.symm.toRingHom
        inv := Spec.map <| CommRingCat.ofHom <| e0.toRingHom
        hom_inv_id := by
          rw [← Spec.map_comp]
          convert Spec.map_id (CommRingCat.of <| A_γβ ⧸ J_γβ) using 2
          simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
            AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv]
          rw [← CommRingCat.ofHom_comp]
          convert CommRingCat.ofHom_id
          ext x
          exact e0.symm_apply_apply x
        inv_hom_id := by
          rw [← Spec.map_comp]
          convert Spec.map_id (CommRingCat.of <| A_γβ ⊗[A_γ] (A_γ ⧸ J_γ)) using 2
          simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
            AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv]
          rw [← CommRingCat.ofHom_comp]
          convert CommRingCat.ofHom_id
          ext x
          exact e0.apply_symm_apply x }
    let e3 :
      -- Spec A_γβ ×[Spec A_γ] Spec (A_γ ⧸ J_γ)
      pullback (Spec.map fA) (Spec.map fQuot) ≅
      -- U_γβ ×[U_γ] (U_γ ×[X] Z)
      pullback g (pullback.fst o_γ (Z.subscheme i ↘ X)) :=
    { hom := pullback.map _ _ _ _ (𝟙 _)
        ((Z.condiso i γβ.1).hom ≫ (pullbackSymmetry _ _).hom)
        (𝟙 _) (by simp [g]) (by
          simp only [Category.comp_id, Category.assoc, U_γ, g, U_γβ]
          rw [pullbackSymmetry_hom_comp_fst]
          have := Z.condover i γβ.1
          rw [Scheme.Hom.isOver_iff] at this
          exact this.symm)
      inv := pullback.map _ _ _ _ (𝟙 _)
        ((pullbackSymmetry _ _).hom ≫ (Z.condiso i γβ.1).inv)
        (𝟙 _) (by simp [g]) (by
          simp only [Category.comp_id, Category.assoc, A_γ, o_γ, U_γ, g, U_γβ, J_γ]
          rw [← Iso.inv_comp_eq, pullbackSymmetry_inv_comp_fst, eq_comm, Iso.inv_comp_eq]
          have := Z.condover i γβ.1
          rw [Scheme.Hom.isOver_iff] at this
          exact this.symm)
      hom_inv_id := by
        ext <;> try simp
        have eq : (pullbackSymmetry o_γ (Z.subscheme i ↘ X)).hom =
          (pullbackSymmetry (Z.subscheme i ↘ X) (Z.cov.map γβ.fst)).inv := by
            ext
            · simp only [pullbackSymmetry_hom_comp_fst, A_γ, o_γ, U_γ, g, U_γβ, J_γ]
              rw [pullbackSymmetry_inv_comp_fst]
            · simp only [pullbackSymmetry_hom_comp_snd, A_γ, o_γ, U_γ, g, U_γβ, J_γ]
              rw [pullbackSymmetry_inv_comp_snd]
        rw [reassoc_of% eq, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      inv_hom_id := by
        have eq : (pullbackSymmetry o_γ (Z.subscheme i ↘ X)).hom =
          (pullbackSymmetry (Z.subscheme i ↘ X) (Z.cov.map γβ.fst)).inv := by
            ext
            · simp only [pullbackSymmetry_hom_comp_fst, A_γ, o_γ, U_γ, g, U_γβ, J_γ]
              rw [pullbackSymmetry_inv_comp_fst]
            · simp only [pullbackSymmetry_hom_comp_snd, A_γ, o_γ, U_γ, g, U_γβ, J_γ]
              rw [pullbackSymmetry_inv_comp_snd]
        ext
        · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          Category.comp_id, Category.id_comp, A_γ, o_γ, U_γ, g, U_γβ, J_γ]
        · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          limit.lift_π_assoc, cospan_right, Iso.inv_hom_id_assoc, pullbackSymmetry_hom_comp_fst,
          pullbackSymmetry_hom_comp_snd, Category.id_comp, U_γβ, U_γ, A_γ, o_γ, g, J_γ]
        · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          limit.lift_π_assoc, cospan_right, Iso.inv_hom_id_assoc, Category.id_comp, A_γ, o_γ, U_γ,
          g, U_γβ, J_γ]
          rw [reassoc_of% eq, Iso.inv_hom_id_assoc] }


    refine e1 ≪≫ (pullbackSpecIso _ _ _).symm ≪≫ e3 ≪≫ pullback.squash₃ _ _ _ ≪≫ pullback.congrHom (by
      simp only [pull_cov_obj, pull_mor_ring, Spec.map_comp, SpecMap_ΓSpecIso_hom, Category.assoc,
        U_γβ, U_γ, A_γ, g, fA, o_γ, J_γ, A_γβ]
      rw [pullback.condition]
      simp only [← Category.assoc, fA, A_γ, o_γ, U_γ, A_γβ, g, U_γβ, J_γ]
      congr 1
      change (ΓSpec.adjunction.unit.app _ ≫ (Scheme.Γ.rightOp ⋙ Scheme.Spec).map _) ≫ _ = _
      rw [← ΓSpec.adjunction.unit.naturality]
      simp only [Functor.id_obj, AffineScheme.forgetToScheme_obj, Functor.comp_obj,
        Functor.rightOp_obj, Scheme.Γ_obj, Scheme.Spec_obj, Quiver.Hom.unop_op,
        AffineScheme.forgetToScheme_map, Functor.id_map, ΓSpec.adjunction_unit_app, Category.assoc,
        fA, A_γ, o_γ, U_γ, A_γβ, g, U_γβ, J_γ]
      rw [← Category.assoc]
      convert Category.comp_id _
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp) rfl ≪≫ (pullback.squash₃' _ _ _).symm
  condover := by
    rintro i ⟨γ, β⟩
    rw [Scheme.Hom.isOver_iff]
    -- simp?
    sorry

def pullback_lem (Z Z': PreClos.{u} X) (T : Scheme.{u}) (f : T ⟶ X) (e : relStructure.{u} Z Z') :
      relStructure (pullback_PreClos X T f Z)  (pullback_PreClos X T f Z') where
  indnumb_equiv := e.indnumb_equiv
  subscheme_iso i := by sorry
  subscheme_iso_over i := sorry


variable {X}
def pullback_Clos {X': Scheme} (f: X' ⟶  X): Clos X → Clos X' :=
  Quotient.map (pullback_PreClos X X' f) <| fun Z Z' e => Nonempty.map (pullback_lem X Z Z' X' f) e
