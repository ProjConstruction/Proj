import Project.Grading.TensorProduct
import Project.Grading.HomogeneousSubmonoid
import Project.ForMathlib.SubgroupBasic

import Mathlib.GroupTheory.Finiteness


variable {M M' R A A' : Type*}
variable [DecidableEq M] [AddCommGroup M] [AddGroup.FG M]
variable [DecidableEq M'] [AddCommGroup M'] [AddGroup.FG M']
variable [CommRing R] [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
variable (𝒜 : M → Submodule R A) (𝒜' : M' → Submodule R A')
variable [GradedAlgebra 𝒜] [GradedAlgebra 𝒜']

open TensorProduct

open HomogeneousSubmonoid

lemma proposition_2_5_1
    (x : A ⊗[R] A') (homogeneous : SetLike.Homogeneous (𝒜 ⊗ₓ 𝒜') x)
    (relevant : elemIsRelevant x homogeneous) :
    ∃ (k : ℕ)
      (c : (M × M) →₀ (A × A'))
      (hom : ∀ (p : M × M), SetLike.Homogeneous 𝒜 (c p).1)
      (hom' : ∀ (p : M × M), SetLike.Homogeneous 𝒜' (c p).2)
      (rel : ∀ (p : M × M), elemIsRelevant (c p).1 (hom p))
      (rel' : ∀ (p : M × M), elemIsRelevant (c p).2 (hom' p)),
      x^k = ∑ p ∈ c.support, (c p).1 ⊗ₜ (c p).2:= by
  rcases homogeneous with ⟨⟨m, n⟩, homogeneous⟩
  obtain ⟨k, hk⟩ := relevant (m, n)
  simp only [Prod.smul_mk] at hk
  obtain ⟨c, hc1, hc2⟩ := AddSubgroup.mem_closure_iff_exists _ _ |>.1 hk
  simp only [Prod.forall] at hc1
  choose xᵢ hxᵢ0 hxᵢ1 hxᵢ2 using hc1
  simp only [gradingByProduct, LinearMap.mem_range] at hxᵢ2
  choose y hy using hxᵢ2
  -- simp only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hxᵢ
  sorry
