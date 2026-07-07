import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

variable {G : Type*} [CommGroup G] (N : Submonoid G)

namespace Subgroup

@[to_additive]
lemma closure_submonoid :
    Subgroup.closure (N : Set G) = { x | ∃ a b : N, (x : G) = (a : G) * (b : G)⁻¹ } := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro h
    apply Subgroup.closure_induction (p := _) (x := x) (hx := h)
    · rintro x hx
      refine ⟨⟨x, hx⟩, 1, by simp⟩
    · refine ⟨1, 1, by simp⟩
    · rintro x y hx hy ⟨a, b, eq₁⟩ ⟨c, d, eq₂⟩
      refine ⟨a * c, b * d, eq₁ ▸ eq₂ ▸ ?_⟩
      simp [mul_assoc, inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    · rintro x hx ⟨a, b, eq⟩; exact ⟨b, a, eq ▸ by simp⟩
  · rintro ⟨a, b, rfl⟩
    aesop

end Subgroup

namespace AddGroup

variable (M N : Type*) [AddCommGroup M] [AddCommGroup N] [AddGroup.FG M] [AddGroup.FG N]

lemma exists_finite_generating_set_of_FG (s : Set M) (h : AddSubgroup.closure s = ⊤) :
    ∃ (t : Finset M), (t : Set M) ⊆ s ∧ AddSubgroup.closure (t : Set M) = ⊤ := by
  have fg : AddGroup.FG M := by infer_instance
  rw [fg_def] at fg
  obtain ⟨T, hT⟩ := fg
  if T_empty : T = ∅
  then
  subst T_empty
  simp only [Finset.coe_empty, AddSubgroup.closure_empty] at hT
  exact ⟨∅, by simp, hT ▸ by simp⟩
  else
  have (m : M) (mem : m ∈ T) :
      ∃ (c : M →₀ ℤ), (c.support : Set M) ⊆ s ∧ ∑ i ∈ c.support, c i • i = m := by
    have mem : m ∈ AddSubgroup.closure s := h ▸ ⟨⟩
    simp only [← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
      Submodule.mem_span_set] at mem
    exact mem
  choose c hc_subset hc_eq using this
  have T_nonempty : T.attach.Nonempty := by simpa using Finset.nonempty_iff_ne_empty.mpr T_empty
  let 𝓉 : Finset M := Set.Finite.toFinset (s := ⋃ (i : T), (c _ i.2).support) (Set.toFinite _)
  refine ⟨𝓉, by simpa [𝓉], ?_⟩
  rw [eq_top_iff]
  rintro x -
  have mem : x ∈ AddSubgroup.closure T := hT ▸ ⟨⟩
  simp only [← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set] at mem
  obtain ⟨d, hd, (rfl : ∑ _ ∈ _, _ = x)⟩ := mem
  refine sum_mem fun i hi ↦ ?_
  specialize hc_subset i (hd hi)
  refine zsmul_mem ?_ _
  rw [← hc_eq _ (hd hi)]
  refine sum_mem fun j hj ↦ zsmul_mem ?_ _
  refine AddSubgroup.subset_closure ?_
  simp only [Set.Finite.coe_toFinset, Set.mem_iUnion, Finset.mem_coe, Subtype.exists, 𝓉]
  exact ⟨i, hd hi, hj⟩

omit [FG M] in
lemma exists_finite_generating_set_of_FG' (s : Set M) (h : AddGroup.FG <| AddSubgroup.closure s) :
    ∃ (t : Finset M), (t : Set M) ⊆ s ∧
      AddSubgroup.closure (t : Set M) = AddSubgroup.closure s := by
  have fg : (AddSubgroup.closure s).FG := by exact
    (fg_iff_addSubgroup_fg (AddSubgroup.closure s)).mp h
  obtain ⟨T, hT⟩ := fg
  if T_empty : T = ∅
  then
  subst T_empty
  simp only [Finset.coe_empty, AddSubgroup.closure_empty] at hT
  exact ⟨∅, by simp, hT ▸ by simp⟩
  else
  have (m : M) (mem : m ∈ AddSubgroup.closure s) :
      ∃ (c : M →₀ ℤ), (c.support : Set M) ⊆ s ∧ ∑ i ∈ c.support, c i • i = m := by
    simp only [← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
      Submodule.mem_span_set] at mem
    exact mem
  choose c hc_subset hc_eq using this
  have T_nonempty : T.attach.Nonempty := by simpa using Finset.nonempty_iff_ne_empty.mpr T_empty
  let 𝓉 : Finset M := Set.Finite.toFinset (s := ⋃ (i : T), (c i.1 <| by
    rw [← hT]
    exact AddSubgroup.subset_closure i.2).support) (Set.toFinite _)
  have le1 : 𝓉 ≤ s := by
    simp only [Set.Finite.coe_toFinset, Set.le_eq_subset, Set.iUnion_subset_iff, Subtype.forall, 𝓉]
    intro m hm
    apply hc_subset m
  refine ⟨𝓉, le1, ?_⟩

  refine le_antisymm (AddSubgroup.closure_mono le1) ?_
  intro x hx
  have mem : x ∈ AddSubgroup.closure T := hT ▸ hx
  simp only [← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set] at mem
  obtain ⟨d, hd, (rfl : ∑ _ ∈ _, _ = x)⟩ := mem
  refine sum_mem fun i hi ↦ ?_
  specialize hc_subset i (by
    rw [← hT]
    exact AddSubgroup.subset_closure (hd hi))
  refine zsmul_mem ?_ _
  rw [← hc_eq i (by
    rw [← hT]
    exact AddSubgroup.subset_closure (hd hi))]
  refine sum_mem fun j hj ↦ zsmul_mem ?_ _
  refine AddSubgroup.subset_closure ?_
  simp only [Set.Finite.coe_toFinset, Set.mem_iUnion, Finset.mem_coe, Subtype.exists, 𝓉]
  exact ⟨i, hd hi, hj⟩

instance : AddGroup.FG (M × N) := by
  classical
  obtain ⟨⟨s, h⟩⟩ : FG M := inferInstance
  obtain ⟨⟨t, h'⟩⟩ : FG N := inferInstance
  refine ⟨⟨(s.product {(0 : N)}) ∪ (Finset.product {(0 : M)} t), ?_⟩⟩
  rw [eq_top_iff] at h h' ⊢
  rintro ⟨m, n⟩ -
  specialize @h m ⟨⟩
  specialize @h' n ⟨⟩
  rw [show (m, n) = (m, 0) + (0, n) by simp]
  refine add_mem ?_ ?_
  · refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h
    · intro x hx
      refine AddSubgroup.subset_closure ?_
      aesop
    · exact zero_mem _
    · intro x y hx hy hx' hy'
      convert add_mem hx' hy' using 1
      simp
    · intro x hx hx'
      convert neg_mem hx' using 1
      simp
  · refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h'
    · intro x hx
      refine AddSubgroup.subset_closure ?_
      aesop
    · exact zero_mem _
    · intro x y hx hy hx' hy'
      convert add_mem hx' hy' using 1
      simp
    · intro x hx hx'
      convert neg_mem hx' using 1
      simp

instance (ι : Type*) [Fintype ι] : AddGroup.FG (ι →₀ ℤ) := sorry

end AddGroup

namespace Subgroup.FG

variable {A B : Type*} [Group A] [Group B] {S : Subgroup A}

@[to_additive]
lemma map (h : S.FG) (f : A →* B)  : (S.map f).FG := by
  classical
  obtain ⟨s, rfl⟩ := h
  refine ⟨s.image f, le_antisymm ?_ ?_⟩
  · rw [closure_le]
    rintro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    simp only [coe_map, Set.mem_image, SetLike.mem_coe]
    exact ⟨x, Subgroup.subset_closure hx, rfl⟩

  · rw [map_le_iff_le_comap, closure_le]
    rintro x hx
    simp only [Finset.coe_image, coe_comap, Set.mem_preimage, SetLike.mem_coe]
    apply Subgroup.subset_closure
    simpa using ⟨x, hx, rfl⟩

end Subgroup.FG

namespace Submonoid

variable (M : Type*) [CommMonoid M]

lemma mem_closure_iff (S : Set M) (x) :
    x ∈ closure S ↔ ∃ (n : M →₀ ℕ) (_ : ∀ i ∈ n.support, i ∈ S), n.prod (fun y i ↦ y ^ i) = x := by
  fconstructor
  · apply Submonoid.closure_induction
    · intro x hx
      refine ⟨Finsupp.single x 1, ?_, by simp⟩
      intro i hi
      simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.single_apply_eq_zero, one_ne_zero,
        imp_false, not_not] at hi
      subst hi
      assumption
    · use 0
      simp
    · rintro _ _ hx hy ⟨x, hx', rfl⟩ ⟨y, hy', rfl⟩
      refine ⟨x + y, ?_, ?_⟩
      · simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq,
        AddLeftCancelMonoid.add_eq_zero, not_and]
        intro z hz
        by_cases hz' : x z = 0
        · specialize hz hz'
          exact @hy' z (by simpa)
        · exact hx' z (by simpa)
      rw [Finsupp.prod_add_index'] <;> simp [pow_add]
  · rintro ⟨m, hm, rfl⟩
    exact prod_mem _ fun i hi ↦ pow_mem (subset_closure <| hm i hi) _

end Submonoid
