import Project.HomogeneousSubmonoid.Relevant
import Project.Grading.GradedRingHom

variable {ι A B σ τ : Type*}
variable [AddCommGroup ι] [AddGroup.FG ι] [DecidableEq ι]
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ι → τ) [GradedRing ℬ]

namespace HomogeneousSubmonoid

def dagger : HomogeneousIdeal 𝒜 where
  __ := Ideal.span { x | ∃ (h : SetLike.Homogeneous 𝒜 x), ElemIsRelevant x h }
  is_homogeneous' := Ideal.homogeneous_span _ _ (by rintro x ⟨h, _⟩; exact h)

scoped postfix:max "†" => dagger

end HomogeneousSubmonoid

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
lemma map_dagger_le : (𝒜 †).toIdeal.map Ψ ≤ (ℬ †).toIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  erw [Ideal.span_le]
  rintro x (hx : x ∈ _)
  obtain ⟨hom_x, rel_x⟩ := hx
  exact Ideal.subset_span ⟨Ψ.map_homogeneous hom_x, Ψ.map_relevant rel_x⟩

lemma radical_dagger_eq_of_surjective (surj : Function.Surjective Ψ) :
    ((𝒜 †).toIdeal.map Ψ).radical = (ℬ †).toIdeal.radical := by
  refine le_antisymm (Ideal.radical_mono Ψ.map_dagger_le) ?_
  erw [Ideal.radical_le_radical_iff, Ideal.span_le]
  rintro b (hb : b ∈ _)
  obtain ⟨⟨i, hom_b⟩, rel_b⟩ := hb
  obtain ⟨a, rfl⟩ := surj b
  rw [elemIsRelevant_iff] at rel_b
  obtain ⟨n, x, d, mem, fin, k, eq⟩ := rel_b
  have H (i : Fin n): ∃ (a' : A), a' ∈ 𝒜 (d i) ∧ Ψ a' = (x i) := by
    obtain ⟨x', hx'⟩ := surj (x i)
    obtain ⟨a', ha', ha''⟩ := Ψ.homogeneous_of_apply_homogeneous (a := x') (i := d i)
      (by rw [hx']; apply mem)
    refine ⟨a', ha', hx' ▸ ha''⟩
  choose a' ha' ha'' using H
  let a_tilde := ∏ i : Fin n, a' i
  have h_tilde : Ψ a_tilde = (Ψ a)^k := by
    simp only [a_tilde, map_prod, ha'', eq]
  refine ⟨k, h_tilde ▸ Ideal.subset_span ⟨a_tilde,
    Ideal.subset_span ⟨SetLike.Homogeneous.prod' _ _ fun i ↦ ⟨d i, ha' i⟩, ?_⟩, rfl⟩⟩
  rw [elemIsRelevant_iff]
  refine ⟨n, a', d, ha', fin, 1, by simp [a_tilde]⟩


end GradedRingHom
