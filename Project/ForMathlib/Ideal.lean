import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.Order.CompleteLattice
import Mathlib.Algebra.Group.Pointwise.Set.Basic

variable (A : Type*) [CommSemigroup A]

namespace CommSemigroup

structure Ideal where
  carrier : Set A
  is_ideal : ∀ (a b : A), a ∈ carrier → a * b ∈ carrier

namespace Ideal

variable {A}

instance : SetLike (Ideal A) A where
  coe a := a.carrier
  coe_injective' := λ ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl

lemma mul_mem_left (I : Ideal A) {a : A} (ha : a ∈ I) (b : A) : a * b ∈ I :=
  I.is_ideal a b ha

lemma mul_mem_right (I : Ideal A) (a : A) {b : A} (hb : b ∈ I) : a * b ∈ I := by
    rw [mul_comm]
    exact I.mul_mem_left hb a

instance : MulMemClass (Ideal A) A where
  mul_mem {I} x y hx _ := I.is_ideal x y hx

def asSubsemigroup (I : Ideal A) : Subsemigroup A where
  carrier := I
  mul_mem' {_ _} h h' := mul_mem h h'

lemma le_iff {I J : Ideal A} : I ≤ J ↔ (I : Set A) ⊆ J := Iff.rfl

instance : Max (Ideal A) where
  max I J :=
    { carrier := I ∪ J
      is_ideal := by
        rintro a b (h|h)
        · exact Set.subset_union_left <| I.mul_mem_left h b
        · exact Set.subset_union_right <| J.mul_mem_left h b }

@[simp]
lemma coe_sup (I J : Ideal A) : ((I ⊔ J : Ideal A) : Set A) = (I : Set A) ∪ J := rfl

lemma mem_sup {I J : Ideal A} {x : A} : x ∈ I ⊔ J ↔ x ∈ I ∨ x ∈ J := Iff.rfl

instance : Min (Ideal A) where
  min I J :=
    { carrier := I ∩ J
      is_ideal := by
        rintro a b ⟨ha, hb⟩
        exact ⟨I.mul_mem_left ha b, mul_comm a b ▸ J.mul_mem_right _ hb⟩ }

@[simp]
lemma coe_inf (I J : Ideal A) : ((I ⊓ J : Ideal A) : Set A) = (I : Set A) ∩ J := rfl

lemma mem_inf {I J : Ideal A} {x : A} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J := Iff.rfl

instance : SemilatticeSup (Ideal A) where
  sup a b := a ⊔ b
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le := by
    intro I J K h h'
    rw [le_iff, coe_sup]
    exact Set.union_subset h h'

instance : SemilatticeInf (Ideal A) where
  inf a b := a ⊓ b
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf := by
    intro I J K h h'
    rw [le_iff, coe_inf]
    exact Set.subset_inter h h'

instance : SupSet (Ideal A) where
  sSup S :=
  { carrier := ⋃ (I : Ideal A) (h : I ∈ S), (I : Set A)
    is_ideal := by
      rintro a b ⟨_, ⟨t, rfl⟩, ⟨_, ⟨⟨ht, rfl⟩, (h : a ∈ t)⟩⟩⟩
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
      refine ⟨t, ht, t.mul_mem_left h _⟩}

@[simp]
lemma coe_sSup (S : Set (Ideal A)) :
  ((sSup S : Ideal A) : Set A) = ⋃ (I ∈ S), (I : Set A) := rfl

lemma mem_sSup {S : Set (Ideal A)} {x : A} : x ∈ sSup S ↔ ∃ I ∈ S, x ∈ (I : Set A) := by
  rw [← SetLike.mem_coe]
  simp

@[simp]
lemma coe_biSup (S : Set (Ideal A)) :
  ((⨆ (I ∈ S), I : Ideal A) : Set A) = ⋃ (I ∈ S), (I : Set A) := by
  erw [coe_sSup]
  simp only [Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq']
  ext x; constructor
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
  · simp only [forall_exists_index]
    rintro I ⟨_, ⟨T, rfl⟩, h⟩
    simp only [Set.mem_range, exists_prop, Set.mem_iUnion, SetLike.mem_coe] at h
    aesop
  · simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, forall_exists_index, and_imp]
    rintro I h hx
    refine ⟨I, ⟨I, (by simpa using ⟨I, by aesop⟩), ?_⟩⟩
    aesop

lemma mem_biSup {S : Set (Ideal A)} {x : A} : x ∈ ⨆ (I ∈ S), (I : Ideal A) ↔ ∃ I ∈ S, x ∈ (I : Set A) := by
  rw [← SetLike.mem_coe]
  simp

@[simp]
lemma coe_iSup {ι : Type*} (f : ι → Ideal A) :
    ((⨆ i, f i : Ideal A) : Set A) = ⋃ i, (f i : Set A) := by
  simp only [iSup, sSup, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq']
  rfl

lemma mem_iSup {ι : Type*} {f : ι → Ideal A} {x : A} : x ∈ ⨆ i, f i ↔ ∃ i, x ∈ f i := by
  rw [← SetLike.mem_coe]
  simp

instance : InfSet (Ideal A) where
  sInf S :=
  { carrier := ⋂ (I : Ideal A) (h : I ∈ S), (I : Set A)
    is_ideal := by
      rintro a b h
      rintro _ ⟨I, rfl⟩ t ⟨ht, rfl⟩
      exact I.mul_mem_left (h _ (by aesop)) b }

@[simp]
lemma coe_sInf (S : Set (Ideal A)) :
  ((sInf S : Ideal A) : Set A) = ⋂ (I ∈ S), (I : Set A) := rfl

lemma mem_sInf {S : Set (Ideal A)} {x : A} : x ∈ sInf S ↔ ∀ I ∈ S, x ∈ (I : Set A) := by
  rw [← SetLike.mem_coe]
  simp

@[simp]
lemma coe_biInf (S : Set (Ideal A)) :
  (((⨅ I ∈ S, I : Ideal A)) : Set A) = ⋂ (I ∈ S), (I : Set A) := by
  erw [coe_sInf]
  simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']
  ext x; constructor
  · simp only [Set.mem_iInter, SetLike.mem_coe]
    rintro h I hI
    specialize h I
    erw [mem_sInf] at h
    exact h I ⟨hI, rfl⟩
  · simp only [Set.mem_iInter, SetLike.mem_coe]
    intro H I
    erw [mem_sInf]
    rintro J ⟨hJ, rfl⟩
    exact H _ hJ

lemma mem_biInf {S : Set (Ideal A)} {x : A} : x ∈ ⨅ (I ∈ S), (I : Ideal A) ↔ ∀ I ∈ S, x ∈ (I : Set A) := by
  rw [← SetLike.mem_coe]
  rw [coe_biInf S]
  simp

@[simp]
lemma coe_iInf {ι : Type*} (f : ι → Ideal A) :
    ((⨅ i, f i : Ideal A) : Set A) = ⋂ i, (f i : Set A) := by
  simp only [iInf, sInf, Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']
  rfl

lemma mem_iInf {ι : Type*} {f : ι → Ideal A} {x : A} : x ∈ ⨅ i, f i ↔ ∀ i, x ∈ f i := by
  rw [← SetLike.mem_coe]
  simp

instance : CompleteSemilatticeSup (Ideal A) where
  le_sSup := by
    intro S t ht
    rw [le_iff, coe_sSup]
    apply Set.subset_iUnion_of_subset t
    aesop
  sSup_le := by
    intro S I h
    rw [le_iff, coe_sSup]
    apply Set.iUnion_subset
    aesop

instance : CompleteSemilatticeInf (Ideal A) where
  sInf_le := by
    intro S I h
    rw [le_iff, coe_sInf]
    apply Set.iInter_subset_of_subset I
    aesop
  le_sInf := by
    intro S t ht
    rw [le_iff, coe_sInf]
    apply Set.subset_iInter
    aesop

instance : Lattice (Ideal A) where
  __ := inferInstanceAs <| SemilatticeSup (Ideal A)
  __ := inferInstanceAs <| SemilatticeInf (Ideal A)

instance : Top (Ideal A) where
  top := { carrier := Set.univ, is_ideal := fun _ _ _ => Set.mem_univ _ }

@[simp]
lemma coe_top : ((⊤ : Ideal A) : Set A) = Set.univ := rfl

lemma mem_top (x : A) : x ∈ (⊤ : Ideal A) := Set.mem_univ x

@[simp]
lemma mem_top_iff_true (x : A) : x ∈ (⊤ : Ideal A) ↔ True := Iff.rfl

instance : Bot (Ideal A) where
  bot := { carrier := ∅, is_ideal := by aesop }

@[simp]
lemma coe_bot : ((⊥ : Ideal A) : Set A) = ∅ := rfl

lemma not_mem_bot (x : A) : x ∉ (⊥ : Ideal A) := Set.not_mem_empty x

@[simp]
lemma mem_bot_iff_false (x : A) : x ∈ (⊥ : Ideal A) ↔ False := Iff.rfl

instance : CompleteLattice (Ideal A) where
  __ := inferInstanceAs <| Lattice (Ideal A)
  __ := inferInstanceAs <| CompleteSemilatticeSup (Ideal A)
  __ := inferInstanceAs <| CompleteSemilatticeInf (Ideal A)
  le_top _ _ _ := by simp
  bot_le _ _ _ := by simp_all

def closure (s : Set A) : Ideal A :=
  sInf { I | s ⊆ I }

lemma closure_eq_sInf (s : Set A) : closure s = (sInf { I | s ⊆ I } : Ideal A) := rfl

open Pointwise in
lemma subset_closure (s : Set A) : s ⊆ closure s := by
  intro x hx
  rw [closure_eq_sInf, SetLike.mem_coe, mem_sInf]
  aesop

open Pointwise in
lemma closure_eq (s : Set A) : closure s =
  ⟨s ∪ s * Set.univ, by
    rintro a b (h|⟨c, hc, d, -, (rfl : c * d = a)⟩)
    · right
      exact ⟨a, h, b, ⟨⟩, rfl⟩
    · right
      rw [mul_assoc]
      exact ⟨c, hc, d * b, ⟨⟩, rfl⟩⟩ := by
  refine le_antisymm ?_ ?_
  · apply sInf_le
    intro x hx
    left
    exact hx
  · refine le_sInf ?_
    rintro I (hI : s ⊆ I) a (h|⟨c, hc, d, -, (rfl : _ * _ = _)⟩)
    · exact hI h
    · exact I.mul_mem_left (hI hc) d

open Pointwise in
@[elab_as_elim]
lemma closure_induction {s : Set A}
    {p : A → Prop} (basic : ∀ x ∈ s, p x) (ideal : ∀ x y, x ∈ s → p x → p (x * y)) :
    ∀ x, x ∈ closure s → p x := by
  intro x hx
  rw [closure_eq] at hx
  rcases hx with (hx|⟨c, hc, d, ⟨⟩, (rfl : _ * _ = _ )⟩) <;> aesop

open Pointwise in
@[elab_as_elim]
lemma closure_induction' {s : Set A}
    {p : ∀ a : A, a ∈ closure s → Prop}
    (basic : ∀ x, ∀ (h : x ∈ s), p x (subset_closure _ h))
    (ideal : ∀ x y, ∀ (h : x ∈ s), p x (subset_closure _ h) → p (x * y)
      (Ideal.mul_mem_left _ (subset_closure _ h) y)) :
    ∀ x, ∀ h : x ∈ closure s, p x h := by
  intro x hx
  rw [closure_eq] at hx
  rcases hx with (hx|⟨c, hc, d, ⟨⟩, (rfl : _ * _ = _ )⟩) <;> aesop

example (s : Set A) : ∀ x ∈ closure s, x = x := by
  intro x hx
  induction x, hx using closure_induction' with
  | basic => rfl
  | ideal x y mem ih => rfl

open Pointwise in
lemma mem_closure {s : Set A} {x : A} : x ∈ closure s ↔ x ∈ s ∪ s * Set.univ := by
  rw [closure_eq]
  rfl

end Ideal

end CommSemigroup
