import Project.HomogeneousSubmonoid.Relevant
import Project.Grading.GradedRingHom

variable {ι A B σ τ : Type*}
variable [AddCommGroup ι] [AddGroup.FG ι] [DecidableEq ι]
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ι → τ) [GradedRing ℬ]

namespace HomogeneousSubmonoid

def dagger : HomogeneousIdeal 𝒜 where
  __ := Ideal.span { x | ∃ (h : SetLike.IsHomogeneousElem 𝒜 x), ElemIsRelevant x h }
  is_homogeneous' := Ideal.homogeneous_span _ _ (by rintro x ⟨h, _⟩; exact h)

scoped postfix:max "†" => dagger

end HomogeneousSubmonoid

open HomogeneousSubmonoid Graded

variable (Ψ : 𝒜 →+* ℬ)

namespace GradedRingHom

variable {𝒜 ℬ}

lemma map_relevant {a : A} {hom_a : SetLike.IsHomogeneousElem 𝒜 a} (rel_a : ElemIsRelevant a hom_a) :
    ElemIsRelevant (Ψ a) (Ψ.map_homogeneous hom_a) := by
  rw [elemIsRelevant_iff] at rel_a ⊢
  obtain ⟨n, x, d, mem, fin, k, eq⟩ := rel_a
  refine ⟨n, Ψ ∘ x, d, fun i ↦ Ψ.map_mem (mem i), fin, k, ?_⟩
  simp only [Function.comp_apply, ← map_prod, eq, map_pow]

-- [TODO]: there should be a `HomogeneousIdeal.map`
lemma map_dagger_le : (𝒜 †).toIdeal.map Ψ ≤ (ℬ †).toIdeal := by
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

lemma radical_dagger_eq_of_surjective (surj : Function.Surjective Ψ) :
    ((𝒜 †).toIdeal.map Ψ).radical = (ℬ †).toIdeal.radical := by
  refine le_antisymm (Ideal.radical_mono Ψ.map_dagger_le) ?_
  suffices ineq : (ℬ †).toIdeal ≤ ((𝒜 †).toIdeal.map Ψ).radical by
    exact Ideal.radical_le_radical_iff.mpr ineq
  rintro f (hf : f ∈ Ideal.span _)
  induction hf using Submodule.span_induction with
  | zero => simp
  | mem f hf =>
    obtain ⟨⟨i, hom_f⟩, rel_f⟩ := hf
    obtain ⟨f, rfl⟩ := surj f
    rw [elemIsRelevant_iff] at rel_f
    obtain ⟨n, x, d, mem, fin, k, eq⟩ := rel_f
    have H (i : Fin n): ∃ (f' : A), f' ∈ 𝒜 (d i) ∧ Ψ f' = (x i) := by
      obtain ⟨x', hx'⟩ := surj (x i)
      obtain ⟨f', hf', hf''⟩ := Ψ.homogeneous_of_apply_homogeneous (a := x') (i := d i)
        (by rw [hx']; apply mem)
      refine ⟨f', hf', hx' ▸ hf''⟩
    choose f' hf' hf'' using H
    let f_tilde := ∏ i : Fin n, f' i
    have h_tilde : Ψ f_tilde = (Ψ f)^k := by
      simp only [f_tilde, map_prod, hf'', eq]
    refine ⟨k, h_tilde ▸ Ideal.subset_span ⟨f_tilde,
      Ideal.subset_span ⟨SetLike.IsHomogeneousElem.prod' _ _ fun i ↦ ⟨d i, hf' i⟩, ?_⟩, rfl⟩⟩
    rw [elemIsRelevant_iff]
    refine ⟨n, f', d, hf', fin, 1, by simp [f_tilde]⟩
  | add f g hf hg ihf ihg =>
    simpa using Ideal.add_mem _ ihf ihg
  | smul r f hf ih =>
    simpa using Ideal.mul_mem_left _ _ ih

end GradedRingHom
