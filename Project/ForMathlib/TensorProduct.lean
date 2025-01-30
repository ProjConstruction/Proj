import Mathlib.RingTheory.TensorProduct.Basic

variable (R : Type*) [CommRing R]
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

namespace TensorProduct

variable {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → B)

lemma prod_tmul_prod :
    (∏ i in s, a i) ⊗ₜ[R] (∏ i in s, b i) = ∏ i in s, a i ⊗ₜ[R] b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, ← ih, Algebra.TensorProduct.tmul_mul_tmul]

end TensorProduct
