import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable (x : Submonoid A)

namespace HomogeneousLocalization

namespace NumDenSameDeg

@[simp]
lemma deg_prod {ι : Type*} (s : Finset ι) (f : ι → NumDenSameDeg 𝒜 x) :
    NumDenSameDeg.deg (∏ i ∈ s, f i) = ∑ i in s, NumDenSameDeg.deg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, deg_mul, ih]

@[simp]
lemma num_prod {ι : Type*} (s : Finset ι) (f : ι → NumDenSameDeg 𝒜 x) :
    NumDenSameDeg.num (∏ i ∈ s, f i) = ⟨∏ i ∈ s, NumDenSameDeg.num (f i), by
      rw [deg_prod]
      apply SetLike.prod_mem_graded
      aesop⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, deg_one]
    rfl
  | @insert i s hi ih =>
    ext
    rw [Subtype.ext_iff] at ih
    simp only at ih ⊢
    rw [Finset.prod_insert hi, Finset.prod_insert hi, num_mul, ih]

@[simp]
lemma den_prod {ι : Type*} (s : Finset ι) (f : ι → NumDenSameDeg 𝒜 x) :
    NumDenSameDeg.den (∏ i ∈ s, f i) = ⟨∏ i ∈ s, NumDenSameDeg.den (f i), by
      rw [deg_prod]
      apply SetLike.prod_mem_graded
      aesop⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, deg_one]
    rfl
  | @insert i s hi ih =>
    ext
    rw [Subtype.ext_iff] at ih
    simp only at ih ⊢
    rw [Finset.prod_insert hi, Finset.prod_insert hi, den_mul, ih]

end NumDenSameDeg

lemma prod_mk {ι : Type*} (s : Finset ι) (f : ι → NumDenSameDeg 𝒜 x) :
    ∏ i ∈ s, HomogeneousLocalization.mk (f i) =
    .mk (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, ← HomogeneousLocalization.mk_mul, Finset.prod_insert hi]

end HomogeneousLocalization
