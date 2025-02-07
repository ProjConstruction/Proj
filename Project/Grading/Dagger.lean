import Project.Grading.HomogeneousSubmonoid
import Project.Grading.GradedRingHom


variable {ι A B σ τ : Type*}
variable [AddCommGroup ι] [AddGroup.FG ι] [DecidableEq ι]
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ι → τ) [GradedRing ℬ]

open HomogeneousSubmonoid Graded

variable (Ψ : 𝒜 →+* ℬ)

namespace GradedRingHom

variable {𝒜 ℬ}

lemma map_relevant {a : A} {hom_a : SetLike.Homogeneous 𝒜 a} (rel_a : ElemIsRelevant a hom_a) :
    ElemIsRelevant (Ψ a) (Ψ.map_homogeneous hom_a) := by
  rw [elemIsRelevant_iff] at rel_a ⊢
  obtain ⟨n, x, d, mem, fin, k, eq⟩ := rel_a
  refine ⟨n, Ψ ∘ x, d, fun i ↦ Ψ.map_mem (mem i), fin, k, ?_⟩
  simp only [Function.comp_apply, ← map_prod, eq, map_pow]

-- [TODO]: there should be a `HomogeneousIdeal.map`
lemma map_dagger : (𝒜 †).toIdeal.map Ψ ≤ (ℬ †).toIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  rintro a (ha : a ∈ Ideal.span _)
  change Ψ a ∈ Ideal.span _
  induction ha using Submodule.span_induction with
  | zero => simp
  | mem x hx =>
    obtain ⟨hom_x, rel_x⟩ := hx
    exact Ideal.subset_span ⟨Ψ.map_homogeneous hom_x, Ψ.map_relevant rel_x⟩
  | add a b ha hb iha ihb =>
    simpa using Ideal.add_mem _ iha ihb
  | smul r a ha iha =>
    simpa using Ideal.mul_mem_left _ _ iha

end GradedRingHom
