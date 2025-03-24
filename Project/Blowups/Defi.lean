import Project.Dilatation.Multicenter
import Mathlib.Data.Sum.Basic
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
import Project.Dilatation.Multicenter

variable {X : Type u} [Scheme X]

structure Clos where
indcov: finite set
indnumb : finite set
clotop: indnumb → closed (underlying top of X)
subscheme: indnumb → AlgebraicGeometry.Scheme
condset : clotop i = underlying top (subscheme i)
mor: indnumb → subscheme i →sch X
condcov: X = finite union over indcov of affine scheme Spec(A γ)
ideal:   indnumb → indcov → ideal A γ
condiso: for all i γ  Spec(A_γ/L_iγ)= mor^{-1} (Spec(A_γ))

structure Cars extends Clos where
nonz: indnumb → indcov → nonZeroDivisors A γ
condcar : ideal i γ = Ideal.span nonz i γ



def ideal_loc (Z: Clos X) (γ : Z.indcov) : indnumb → ideal A γ :=
  fun i ↦ ideal i γ

def Proj_loc  (Z: Clos X) (γ : Z.indcov) := Bl (ideal_loc Z γ)

def Proj_loc_pair (Z: Clos X) (γ δ : Z.indcov) :=
    inverse image of Spec(A_γ) ∩ Spec(A_δ) in Bl (ideal_loc Z γ)


lemma base_change_dil_stand (F: multicenter A) (f: A) ;
  ∃ unique iso of A-algebra A[F]⊗[A]Af ≅ Af[im F]:= by
     A[F]⊗[A]Af= A[F]f = Af[im F] by classical and univ prop
     sorry

lemma base_change_dil_open [Algebra A B]
   (i:Spec(B) → Spec(A) is Open immersion)
   (F: multicenter A) :
   ∃! (Spec(A[F]))×[Spec(A)](Spec(B))≅ Spec(B[im F]) over Spec(B):= by
     byy univ prop exists unique φ →
     exists θ <- by fiber product
     φ ∘ θ = id by univ prop
     so θ is injective
     to prove that θ is surjective enough to do it locally on target
     let x in target. Let f in A such that x in Df and Df ⊆ Spec (B).
     Then we are reduced to base_change_dil_stand
      sorry

lemma base_change_Bl_open [Algebra A B]
   (i:Spec(B) → Spec(A) is Open immersion)
   (L: ι → ideal A) :
   ∃! (Bl (L))×[Spec(A)](Spec(B))≅ Bl (im L) over Spec(B):=  by
     byy univ prop exists unique φ →
     exists θ <- by fiber product
     φ ∘ θ = id by univ prop
     so θ is injective
     to prove that θ is surjective enough to do it locally on target
     we chose a potion and apply base_change_dil_open
     sorry



lemma Proj_loc_pair_iso (Z: Clos X) (γ δ : Z.indcov) : ∃ ! Proj_loc_pair γ δ ≅ Proj_loc_pair δ γ
       such that for each covering the restriction is the unique mor from univ prop :=
       write Spec A γ ∩ spec Aδ as union of Spec A β (open affine cov)
       for each β construct a map using base_change_Bl_open we get two morphism on each side
       to prove that iti is an iso we proceed locally using diltation
       sorry

def BlGlob  (Z: Clos X) :=  Scheme.GlueData where
  J := Clos.indcov
  U γ := Proj_loc γ
  V pair := Proj_loc pair.1 pair.2
  f γ δ := Proj_loc_pair_iso
  f_id i :=
  f_open i j :=
  t i j :=
  t_id i :=
  t' i j k :=
  t_fac i j k :=
  cocycle i j k :=

-- set_option maxHeartbeats 1000000 in
