import Project.HomogeneousSubmonoid.Basic
open DirectSum TensorProduct
open scoped NNReal

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A] {𝒜 : ι → σ}
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]

namespace HomogeneousSubmonoid

variable (S : HomogeneousSubmonoid 𝒜)

noncomputable def convDegEmbedding : (ℝ≥0 ⊗[ℕ] S.deg) →ₗ[ℝ≥0] (ℝ ⊗[ℤ] ι) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun r :=
        { toFun i := r.1 ⊗ₜ i.1
          map_add' x y := by simp [← tmul_add]
          map_smul' s x := by
            simp only [NNReal.val_eq_coe, AddSubmonoidClass.coe_nsmul, eq_natCast, Nat.cast_id]
            rw [smul_tmul']
            erw [show s • r.1 = (s : ℤ) • r.1 from rfl]
            rw [smul_tmul]
            congr 1
            simp }
      map_add' r s := by ext; simp [add_tmul]
      map_smul' r s := by
        ext
        simp only [smul_eq_mul, NNReal.val_eq_coe, NNReal.coe_mul, LinearMap.coe_mk,
          AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply, smul_tmul']
        rfl }

@[simp]
lemma convDegEmbedding_apply_tmul (r : ℝ≥0) (i : S.deg) :
    convDegEmbedding S (r ⊗ₜ i) = r.1 ⊗ₜ i.1 := rfl

noncomputable def convDeg : Submodule ℝ≥0 (ℝ ⊗[ℤ] ι) := LinearMap.range (convDegEmbedding S)

noncomputable def convDeg' : Submodule ℝ≥0 (ℝ ⊗[ℤ] ι) :=
  Submodule.span ℝ≥0 {x | ∃ (a : ℝ≥0) (i : ι) (_ : i ∈ S.deg) , x = a.1 ⊗ₜ i }

scoped notation:max ι"["S"⟩ℝ≥0" => convDeg (ι := ι) S

lemma mem_convDeg [Nontrivial A] (x) :
    x ∈ ι[S⟩ℝ≥0 ↔
    ∃ (s : ι →₀ ℝ≥0), (∀ i ∈ s.support, i ∈ S.deg) ∧ x = ∑ i ∈ s.support, (s i).1 ⊗ₜ i := by
  classical
  fconstructor
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero =>
      refine ⟨0, ?_, by simp⟩
      intro i hi
      simp only [Finsupp.support_zero, Finset.not_mem_empty] at hi
    | tmul a i =>
      rcases i with ⟨i, hi⟩
      refine ⟨Finsupp.single i a, ?_, ?_⟩
      · intro i hi
        simp only [Finsupp.mem_support_iff, Finsupp.single_apply, ne_eq, ite_eq_right_iff,
          Classical.not_imp] at hi
        rwa [← hi.1]
      simp only [convDegEmbedding_apply_tmul, NNReal.val_eq_coe]
      rw [eq_comm, Finset.sum_eq_single i]
      · simp
      · intro j hj H
        simp [Finsupp.single_eq_of_ne H.symm]
      aesop
    | add x y ihx ihy =>
      obtain ⟨s,hs, eq⟩ := ihx
      obtain ⟨t, ht, eq'⟩ := ihy
      simp only [NNReal.val_eq_coe, Finsupp.mem_support_iff, ne_eq, map_add] at eq eq' ⊢
      simp_rw [eq, eq']
      refine ⟨s + t, ⟨?_, ?_⟩⟩
      · intro j hj
        simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.coe_add, Pi.add_apply,
          AddLeftCancelMonoid.add_eq_zero, not_and] at hs ht hj
        tauto
      simp only [Finsupp.coe_add, Pi.add_apply, NNReal.coe_add, add_tmul, Finset.sum_add_distrib]
      nth_rewrite 1 [show (s + t).support = s.support ∪ ((s + t).support \ s.support) by
        ext; aesop]
      nth_rewrite 2 [show (s + t).support = t.support ∪ ((s + t).support \ t.support) by
        ext; aesop]
      rw [Finset.sum_union_eq_left, Finset.sum_union_eq_left]
      · aesop
      · intro a ha ha'
        simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at ha'
        simp only [ha', NNReal.coe_zero, zero_tmul]
  · rintro ⟨a, ha, hi, rfl⟩
    refine Submodule.sum_mem _ fun i hi => ?_
    exact ⟨a i ⊗ₜ[ℕ] ⟨i, ha i hi⟩, rfl⟩

end HomogeneousSubmonoid
