import Mathlib.Algebra.Algebra.Tower

namespace AlgEquiv

universe u v w u₁

lemma restrictScalars_symm (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [CommSemiring R]
  [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
  [IsScalarTower R S A] [IsScalarTower R S B] (f : A ≃ₐ[S] B) :
  (f.restrictScalars R).symm = f.symm.restrictScalars R := rfl

end AlgEquiv

namespace RingEquiv

lemma eq_comp_symm {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (e : T ≃+* R) (g : T →+* S) :
    f = RingHom.comp g e.symm ↔
    f.comp e = g := by
  constructor
  · rintro rfl
    ext x
    simp
  · rintro rfl
    ext x
    simp

lemma comp_symm_eq {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (e : R ≃+* T) (g : T →+* S) :
    f.comp e.symm = g ↔ f = RingHom.comp g e
    := by
  constructor
  · rintro rfl
    ext x
    simp
  · rintro rfl
    ext x
    simp

@[simp]
lemma comp_cancel {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    (f f' : R →+* S) (e : T ≃+* R) :
    f.comp (e : T →+* R) = f'.comp e ↔ f = f'
    := by

  constructor
  · rintro h
    have := congr($(h).comp e.symm.toRingHom)
    simp only [toRingHom_eq_coe] at this
    rw [RingHom.comp_assoc, RingEquiv.comp_symm, RingHom.comp_assoc, RingEquiv.comp_symm] at this
    simp only [RingHomCompTriple.comp_eq] at this
    exact this
  · rintro rfl
    rfl

end RingEquiv
