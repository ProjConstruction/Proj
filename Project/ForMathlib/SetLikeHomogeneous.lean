import Mathlib.RingTheory.GradedAlgebra.Basic

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A]  (𝒜 : ι → σ)
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]

namespace SetLike.Homogeneous

lemma exists_homogeneous_of_dvd {a c : A}
    (hom_a : SetLike.Homogeneous 𝒜 a)
    (hom_c : SetLike.Homogeneous 𝒜 c) (dvd : a ∣ c) :
    ∃ b, a * b = c ∧ SetLike.Homogeneous 𝒜 b := by
  obtain ⟨b, hb⟩ := dvd
  obtain ⟨i, hi⟩ := hom_a
  obtain ⟨j, hj⟩ := hom_c
  lift a to 𝒜 i using hi
  lift c to 𝒜 j using hj
  refine ⟨DirectSum.decompose 𝒜 b (j - i), ?_, homogeneous_coe _⟩
  have eq := congr(DirectSum.decompose 𝒜 $hb (i + (j - i)))
  rw [DirectSum.decompose_mul_add_left, Subtype.ext_iff] at eq
  simp only [DirectSum.decompose_coe, coe_gMul] at eq
  rw [← eq]
  rw [DirectSum.coe_of_apply, show i + (j - i) = j by abel, if_pos rfl]

end SetLike.Homogeneous
