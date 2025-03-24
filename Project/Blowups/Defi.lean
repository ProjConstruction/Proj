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

lemma Proj_loc_pair_iso (Z: Clos X) (γ δ : Z.indcov) : Proj_loc_pair γ δ ≅ Proj_loc_pair δ γ :=
       by
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
