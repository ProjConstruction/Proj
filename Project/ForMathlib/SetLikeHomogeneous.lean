import Mathlib.RingTheory.GradedAlgebra.Basic

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A]  (𝒜 : ι → σ)
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]

namespace SetLike.IsHomogeneousElem

lemma exists_homogeneous_of_dvd {a c : A}
    (hom_a : SetLike.IsHomogeneousElem 𝒜 a)
    (hom_c : SetLike.IsHomogeneousElem 𝒜 c) (dvd : a ∣ c) :
    ∃ b, a * b = c ∧ SetLike.IsHomogeneousElem 𝒜 b := by
  obtain ⟨b, hb⟩ := dvd
  obtain ⟨i, hi⟩ := hom_a
  obtain ⟨j, hj⟩ := hom_c
  lift a to 𝒜 i using hi
  lift c to 𝒜 j using hj
  refine ⟨DirectSum.decompose 𝒜 b (j - i), ?_, isHomogeneousElem_coe _⟩
  have eq := congr(DirectSum.decompose 𝒜 $hb (i + (j - i)))
  rw [DirectSum.decompose_mul_add_left, Subtype.ext_iff] at eq
  simp only [DirectSum.decompose_coe, coe_gMul] at eq
  rw [← eq]
  rw [DirectSum.coe_of_apply, show i + (j - i) = j by abel, if_pos rfl]

lemma prod {s : Finset A} (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    SetLike.IsHomogeneousElem 𝒜 (∏ i ∈ s, i)  := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.prod_empty,
    forall_const]
    use 0
    exact SetLike.GradedOne.one_mem
  · intro a s ha hs' ih
    rw [Finset.prod_insert ha]
    simp only [Finset.mem_insert, forall_eq_or_imp] at ih
    exact .mul ih.1 <| hs' ih.2

lemma prod' {n : ℕ} (v : Fin n → A) (hs : ∀ i, SetLike.IsHomogeneousElem 𝒜 (v i)) :
    SetLike.IsHomogeneousElem 𝒜 (∏ i, v i) := by
  classical
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    use 0
    exact SetLike.GradedOne.one_mem
  | succ n ih =>
    simp only [Fin.prod_univ_castSucc]
    apply SetLike.IsHomogeneousElem.mul ?_ ?_
    . apply ih
      intro i
      apply hs
    · apply hs

lemma pow {a : A} (ha : SetLike.IsHomogeneousElem 𝒜 a) (n : ℕ) :
    SetLike.IsHomogeneousElem 𝒜 (a ^ n) := by
  obtain ⟨m, h⟩ := ha
  induction n with
  | zero =>
    simp only [pow_zero]
    use 0
    exact SetLike.GradedOne.one_mem
  | succ n ih =>
    simp only [pow_succ]
    apply SetLike.IsHomogeneousElem.mul ih ⟨_, h⟩

lemma prod'' {ι : Type*} (f : ι → A) {s : Finset ι} (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 (f x)) :
    SetLike.IsHomogeneousElem 𝒜 (∏ i ∈ s, f i)  := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact isHomogeneousElem_one 𝒜
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    apply SetLike.IsHomogeneousElem.mul ?_ ?_
    · exact hs i (by simp)
    exact ih fun x hx => hs x (by aesop)

end SetLike.IsHomogeneousElem
