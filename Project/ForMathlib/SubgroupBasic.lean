import Mathlib.Algebra.Group.Subgroup.Basic

variable {G : Type*} [CommGroup G] (N : Submonoid G)

namespace Subgroup

@[to_additive]
lemma closure_submonoid :
    Subgroup.closure (N : Set G) = { x | ∃ a b : N, (x : G) = (a : G) * (b : G)⁻¹ } := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro h
    apply Subgroup.closure_induction (p := _) (x := x) (hx := h)
    · rintro x hx
      refine ⟨⟨x, hx⟩, 1, by simp⟩
    · refine ⟨1, 1, by simp⟩
    · rintro x y hx hy ⟨a, b, eq₁⟩ ⟨c, d, eq₂⟩
      refine ⟨a * c, b * d, eq₁ ▸ eq₂ ▸ ?_⟩
      simp [mul_assoc, inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    · rintro x hx ⟨a, b, eq⟩; exact ⟨b, a, eq ▸ by simp⟩
  · rintro ⟨a, b, rfl⟩
    aesop

end Subgroup
