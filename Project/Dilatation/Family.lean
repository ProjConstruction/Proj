import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Project.Dilatation.lemma
import Mathlib.RingTheory.Ideal.Operations

section

variable {A G : Type*} [CommMonoid A] [Zero G] [Pow A G]
variable {ι : Type*}
def familyPow (f : ι → A) (v : ι →₀ G) : A := v.prod fun i k ↦ f i ^ k

def instFamilyPow : HPow (ι → A) (ι →₀ G) A where
  hPow f v := familyPow f v

scoped[Family] attribute [instance] instFamilyPow

open Family

lemma familyPow_def (f : ι → A) (v : ι →₀ G) : f^v = v.prod fun i k ↦ f i ^ k := rfl

lemma familyPow_add (f : ι → A) (v w : ι →₀ ℕ) : f^(v + w) = f^v * f^w := by
  classical
  simp only [familyPow_def]
  rw [Finsupp.prod_add_index (by simp) (by simp [pow_add])]

@[simp]
lemma familyPow_zero (f : ι → A) : f^(0 : ι →₀ ℕ) = (1 : A) := by
  simp only [familyPow_def]
  rw [Finsupp.prod_zero_index]

@[simp]
lemma familyPow_single (f : ι → A) (i : ι) : f^(Finsupp.single i 1) = f i := by
  simp [familyPow_def]

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

-- lemma elemFamilyPow (v : ι →₀ ℕ) : A := v.prod fun i k ↦ a i ^ k
