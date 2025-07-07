import Mathlib.Algebra.Algebra.Tower

namespace AlgEquiv

universe u v w u₁

lemma restrictScalars_symm (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [CommSemiring R]
  [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
  [IsScalarTower R S A] [IsScalarTower R S B] (f : A ≃ₐ[S] B) :
  (f.restrictScalars R).symm = f.symm.restrictScalars R := rfl

end AlgEquiv
