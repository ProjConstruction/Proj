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

variable (M : Type*) [AddCommGroup M] [AddGroup.FG M]

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
      mem_span_set] at mem
    exact mem
  choose c hc_subset hc_eq using this
  have T_nonempty : T.attach.Nonempty := by simpa using Finset.nonempty_iff_ne_empty.mpr T_empty
  let 𝓉 : Finset M := Set.Finite.toFinset (s := ⋃ (i : T), (c _ i.2).support) (Set.toFinite _)
  refine ⟨𝓉, by simpa [𝓉], ?_⟩
  rw [eq_top_iff]
  rintro x -
  have mem : x ∈ AddSubgroup.closure T := hT ▸ ⟨⟩
  simp only [← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
    mem_span_set] at mem
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
      mem_span_set] at mem
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
    mem_span_set] at mem
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

end AddGroup
