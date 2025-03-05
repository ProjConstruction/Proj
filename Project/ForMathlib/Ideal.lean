import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.Order.CompleteLattice

variable (A : Type*) [CommSemigroup A]

namespace CommSemigroup

structure Ideal extends Subsemigroup A where
  is_ideal : ∀ (a b : A), a ∈ toSubsemigroup → a * b ∈ toSubsemigroup

namespace Ideal

instance : SetLike (Ideal A) A where
  coe a := a.carrier
  coe_injective' := λ ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h => by cases h; rfl

instance : PartialOrder (Ideal A) where
  le_refl a := by rfl
  le_trans a b c h h' x hx := h' (h hx)
  le_antisymm a b h h' := by
    apply SetLike.ext
    intro x
    exact { mp x := h x, mpr x := h' x }

instance : Max (Ideal A) where
  max I J :=
    { toSubsemigroup := I.toSubsemigroup ⊔ J.toSubsemigroup
      is_ideal := sorry }

instance : CompleteLattice (Ideal A) :=
  sorry

end Ideal

end CommSemigroup
