import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

variable {ι A B F : Type*} [CommSemiring A] [CommSemiring B] [FunLike F A B] [RingHomClass F A B]

namespace Ideal

lemma prod_span' (f : ι → A) (s : Finset ι) :
    Ideal.span {∏ i ∈ s, f i} = ∏ i ∈ s, Ideal.span {f i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← span_singleton_mul_span_singleton, ih,
      Finset.prod_insert hi]

lemma prod_map (f : ι → Ideal A) (s : Finset ι) (χ : F) :
    Ideal.map χ (∏ i ∈ s, f i) = ∏ i ∈ s, Ideal.map χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [map_top]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, map_mul, Finset.prod_insert hi, ih]

end Ideal
