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
