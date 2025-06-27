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


@[simp]
theorem rangeSplitting_apply_coe (f : A → B) (inj : Function.Injective f)  (x : A) :
    Set.rangeSplitting f ⟨f x, by simp⟩ = x := by
  apply inj
  rw [Set.apply_rangeSplitting f]

@[simp]
theorem rangeSplitting_apply_zero [Zero A] [Zero B] (f : A → B) (inj : Function.Injective f) (hf : f 0 = 0)   :
    Set.rangeSplitting f ⟨0, ⟨0, hf⟩⟩ = 0 := by
  apply inj
  simp [Set.apply_rangeSplitting f, hf]


end Set
