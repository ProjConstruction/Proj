import Mathlib.Data.Set.Operations
import Mathlib.Tactic.GeneralizeProofs

variable {A B : Type*} (f : A → B)

namespace Set

noncomputable def imageSplitting (S : Set A) : (f '' S) → S :=
  fun x ↦ ⟨Classical.choose x.2, Classical.choose_spec x.2 |>.1⟩

@[simp]
theorem imageSplitting_apply {S : Set A} (x : f '' S) :
    f (imageSplitting f S x).1 = x := Classical.choose_spec x.2 |>.2

@[simp]
theorem imageSplitting_comp (S : Set A) :
    f ∘ Subtype.val ∘ imageSplitting f S = Subtype.val := by
  ext x; simp

end Set
