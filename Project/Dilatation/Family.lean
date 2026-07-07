import Mathlib.RingTheory.Ideal.Operations

section

variable {A G : Type*} [CommMonoid A] [Zero G] [Pow A G]
variable {ι : Type*}
def familyPow (f : ι → A) (v : ι →₀ G) : A := v.prod fun i k ↦ f i ^ k

def instFamilyPow : HPow (ι → A) (ι →₀ G) A where
  hPow f v := familyPow f v

scoped[Family] attribute [instance] instFamilyPow

open Family

lemma familyPow_def (f : ι → A) (v : ι →₀ ℕ) : f^v = v.prod fun i k ↦ f i ^ k := rfl

lemma familyPow_add (f : ι → A) (v w : ι →₀ ℕ) : f^(v + w) = f^v * f^w := by
  classical
  simp only [familyPow_def]
  rw [Finsupp.prod_add_index (by simp) (by simp [pow_add])]

@[simp]
lemma familyPow_zero (f : ι → A) : f^(0 : ι →₀ ℕ) = (1 : A) := by
  simp only [familyPow_def]
  rw [Finsupp.prod_zero_index]

lemma familyPow_nsmul (f : ι → A) (v : ι →₀ ℕ) (n : ℕ) : f^(n • v) = (f ^ v)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_smul, familyPow_add, pow_add, pow_one, one_smul, ih]

@[simp]
lemma familyPow_single (f : ι → A) (i : ι) : f^(Finsupp.single i 1) = f i := by
  simp [familyPow_def]

@[simp]
lemma familyPow_single' (f : ι → A) (i : ι) (n : ℕ) : f^(Finsupp.single i n) = (f i)^n := by
  simp [familyPow_def]

lemma familyPow_sum {index : Type*} (v : index → (ι →₀ ℕ)) (f : ι → A) (s : Finset index) :
  f^(∑ i ∈ s, v i) = ∏ i ∈ s, f^(v i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.sum_cons, familyPow_add, Finset.prod_cons, ih]

end

namespace Ideal

variable {A : Type*} [CommSemiring A]
variable {ι : Type*} (F : ι → Ideal A) (a : ι → A)


open Family

lemma familyPow_def (v : ι →₀ ℕ) : F^v = v.prod fun i k ↦ F i ^ k := rfl

variable {F} in
lemma mem_familyPow_add {v w : ι →₀ ℕ} {x y : A} (hx : x ∈ F^v) (hy : y ∈ F^w) :
  x * y ∈ F^(v+w) := by
  classical
  rw [familyPow_add]
  exact Ideal.mul_mem_mul hx hy

variable {F a} in
lemma mem_familyPow_of_mem {v : ι →₀ ℕ} (mem : ∀ i ∈ v.support, a i ∈ F i) : a^v ∈ F^v :=
  Ideal.prod_mem_prod fun _ hi ↦ Ideal.pow_mem_pow (mem _ hi) _

end Ideal

namespace Submonoid

open Family

variable {M : Type*} [CommMonoid M] (s : Set M)

lemma mem_closure_iff_family_pow (x : M) :
    x ∈ closure s ↔ ∃ (n : M →₀ ℕ), (∀ i ∈ n.support, i ∈ s) ∧ (id : M → M)^n = x := by
  fconstructor
  · apply Submonoid.closure_induction
    · intro x hx
      use Finsupp.single x 1
      simp only [Finsupp.mem_support_iff, ne_eq, familyPow_single, id_eq, and_true]
      intro y hy
      simp only [Finsupp.single_apply_eq_zero, one_ne_zero, imp_false, not_not] at hy
      subst hy
      assumption
    · use Finsupp.single 1 0
      simp
    · intro x y hx hy ⟨m, hm1, hm2⟩ ⟨n, hn1, hn2⟩
      subst hm2 hn2
      refine ⟨m + n, ?_⟩
      simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq,
        AddLeftCancelMonoid.add_eq_zero, not_and, familyPow_add, and_true]
      intro i hi
      by_cases h : m i = 0
      · apply hn1
        simpa using hi h
      · apply hm1
        simpa
  · rintro ⟨n, hn, rfl⟩
    exact Submonoid.prod_mem _ fun i hi ↦ Submonoid.pow_mem _ (subset_closure <| hn _ hi) _


end Submonoid

-- lemma elemFamilyPow (v : ι →₀ ℕ) : A := v.prod fun i k ↦ a i ^ k
