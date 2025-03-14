import Project.Dilatation.Multicenter
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



universe u
variable {A : Type} [CommRing A]
variable {ι : Type} (L : ι → Ideal A)
[DecidableEq ι]


-- instance : AddCommGroup (ι →₀ ℤ) := Finsupp.instAddCommGroup (α := ι) (G := ℕ)

open GoodPotionIngredient
def Bl  := Proj (ι := ι →₀ ℤ) (R₀ := A) (A := ReesAlgebra L) (𝒜 := (ReesAlgebra.grading L))
         (τ := GoodPotionIngredient (ReesAlgebra.grading L) ) id
