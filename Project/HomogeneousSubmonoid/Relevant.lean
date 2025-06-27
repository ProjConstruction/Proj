import Project.HomogeneousSubmonoid.Basic

open DirectSum

variable {ι A B σ σ' : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A] {𝒜 : ι → σ}
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]
variable [CommRing B] [SetLike σ' B]  {ℬ : ι → σ'}
variable [AddSubgroupClass σ' B] [GradedRing ℬ]

variable (S T : HomogeneousSubmonoid 𝒜)

namespace HomogeneousSubmonoid

def IsRelevant : Prop := ∀ (i : ι), ∃ (n : ℕ), 0 < n ∧ n • i ∈ ι[S.bar]

lemma IsRelevant.mul {S T : HomogeneousSubmonoid 𝒜}
    (S_rel : S.IsRelevant) (T_rel : T.IsRelevant) : (S * T).IsRelevant := by
  intro i
  obtain ⟨m, hm1, hm2⟩ := S_rel i
  obtain ⟨n, hn1, hn2⟩ := T_rel i
  delta agrDeg at hm2 hn2 ⊢
  simp_rw [← SetLike.mem_coe, AddSubgroup.closure_addSubmonoid] at hm2 hn2 ⊢
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hm2
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩, hcd⟩ := hn2
  have le1 : S.bar.deg ≤ (S * T).bar.deg := deg_mono _ _ <| bar_mono _ _ <| left_le_mul S T
  have le2 : T.bar.deg ≤ (S * T).bar.deg := deg_mono _ _ <| bar_mono _ _ <| right_le_mul S T
  refine ⟨m + n, by omega, ⟨⟨a + c, add_mem (le1 ha) (le2 hc)⟩,
    ⟨b + d, add_mem (le1 hb) (le2 hd)⟩, ?_⟩⟩
  simp only [← sub_eq_add_neg, add_smul, neg_add_rev, add_sub] at hab hcd ⊢
  rw [hab, hcd]
  abel

open scoped Graded in
variable {S} in
lemma IsRelevant.map (S_rel : S.IsRelevant) (Φ : 𝒜 →+* ℬ)  :
    (S.map Φ).IsRelevant := by
  intro i
  obtain ⟨n, hn1, hn2⟩ := S_rel i
  refine ⟨n, hn1, ?_⟩
  suffices S.bar.agrDeg ≤ (S.map Φ).bar.agrDeg by exact this hn2
  refine AddSubgroup.closure_mono ?_
  intro x hx
  simp only [coe_deg, mem_bar, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨y, ⟨hy1, z, hz1, hz2⟩, hy2⟩ := hx
  exact ⟨Φ y, ⟨Φ.map_homogeneous hy1, Φ z, (mem_map_of_mem _ hz1), map_dvd _ hz2⟩, Φ.map_mem hy2⟩

lemma isRelevant_iff_isTorsion_quotient : S.IsRelevant ↔ AddMonoid.IsTorsion (ι ⧸ ι[S.bar]) := by
  fconstructor
  · intro H x
    induction x using Quotient.inductionOn' with | h x =>
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn, hx⟩ := H x
    refine ⟨n, hn, ?_⟩
    change Quotient.mk'' (n • x) = _
    rwa [QuotientAddGroup.eq_zero_iff]
  · intro H i
    specialize H i
    rw [isOfFinAddOrder_iff_nsmul_eq_zero] at H
    obtain ⟨n, hn, hni⟩ := H
    refine ⟨n, hn, ?_⟩
    change Quotient.mk'' (n • i) = _ at hni
    rwa [QuotientAddGroup.eq_zero_iff] at hni

lemma IsRelevant.ofLE (h : T ≤ S) (T_rel : T.IsRelevant) : S.IsRelevant := by
  rw [isRelevant_iff_isTorsion_quotient] at T_rel ⊢
  apply AddIsTorsion.of_surjective
    (f :=  QuotientAddGroup.map T.bar.agrDeg S.bar.agrDeg (AddMonoidHom.id ι) (by
      intro x hx; exact agrDeg_mono (bar_mono _ _ h) hx)) (tG := T_rel)
  intro x
  induction x using QuotientAddGroup.induction_on with | H x =>
  use x
  rfl

lemma isRelevant_iff_finite_quotient_of_FG [AddGroup.FG ι] :
    S.IsRelevant ↔ Finite (ι ⧸ ι[S.bar]) := by
  rw [isRelevant_iff_isTorsion_quotient]
  fconstructor
  · intro H
    exact AddCommGroup.finite_of_fg_torsion _ H
  · intro H
    apply is_add_torsion_of_finite

lemma isRelevant_iff_finiteIndex_of_FG [AddGroup.FG ι] :
    S.IsRelevant ↔ ι[S.bar].FiniteIndex := by
  rw [isRelevant_iff_finite_quotient_of_FG]
  fconstructor
  · intro H
    exact ι[S.bar].finiteIndex_of_finite_quotient
  · intro H
    exact ι[S.bar].finite_quotient_of_finiteIndex

abbrev SetIsRelevant (s : Set A) (hs : ∀ i ∈ s, SetLike.IsHomogeneousElem 𝒜 i) : Prop :=
  closure s hs |>.IsRelevant

abbrev ElemIsRelevant (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a) : Prop :=
  closure {a} (by simpa) |>.IsRelevant

attribute [to_additive] Subgroup.closure_mul_image_mul_eq_top
attribute [to_additive] Subgroup.closure_mul_image_eq
attribute [to_additive] Subgroup.closure_mul_image_eq_top
attribute [to_additive] Subgroup.closure_mul_image_eq_top'
attribute [to_additive] Subgroup.exists_finset_card_le_mul
attribute [to_additive] Subgroup.fg_of_index_ne_zero

lemma exists_factorisation_of_elemIsRelevant
    [AddGroup.FG ι] (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a) (a_rel : ElemIsRelevant a ha) :
    ∃ (n : ℕ) (x : Fin n → A) (d : Fin n → ι)
      (_ : ∀ (i : Fin n), x i ∈ 𝒜 (d i)),
      (AddSubgroup.closure (Set.range d)).FiniteIndex ∧
      (∃ (k : ℕ), ∏ i : Fin n, x i = a ^ k) := by
  classical
  rw [ElemIsRelevant, isRelevant_iff_finiteIndex_of_FG] at a_rel
  haveI fg : AddGroup.FG ι[(closure {a} (by simpa)).bar] := by
    exact AddSubgroup.fg_of_index_ne_zero _
  obtain ⟨s, hs1, hs2⟩ :=
    AddGroup.exists_finite_generating_set_of_FG' ι
    (closure (𝒜 := 𝒜) {a} (by simpa)).bar.deg fg
  have hs3 : ∀ i : s, ∃ (y : A), y ∈ 𝒜 i ∧ (∃ (n : ℕ), y ∣ a^n) := by
    rintro ⟨i, hi⟩
    specialize hs1 hi
    simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, ne_eq] at hs1
    obtain ⟨y, ⟨_, ⟨z, hz1, hz2⟩⟩, hy⟩ := hs1
    simp only [mem_toSubmonoid_iff, mem_closure_singleton (ha := ha)] at hz1
    obtain ⟨n, rfl⟩ := hz1
    exact ⟨y, hy, n, hz2⟩

  choose y y_mem y_dvd using hs3
  choose n y_dvd using y_dvd
  let N : ℕ := s.card
  let d : Fin N → ι := Subtype.val ∘ (Finset.equivFin s).symm
  let x : Fin N → A := y ∘ (Finset.equivFin s).symm
  let k : Fin N → ℕ := n ∘ (Finset.equivFin s).symm
  let K : ℕ := ∑ i : Fin N, k i
  have dvd : (∏ i : Fin N, x i) ∣ a ^ K := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    rintro ⟨i, hi⟩ -
    apply y_dvd
  obtain ⟨b, hb, ⟨j, hj⟩⟩ := SetLike.IsHomogeneousElem.exists_homogeneous_of_dvd 𝒜 (by
    refine SetLike.IsHomogeneousElem.prod' 𝒜 x fun j ↦ ?_
    simpa [x] using ⟨_, y_mem _⟩) (by
    refine SetLike.IsHomogeneousElem.pow 𝒜 ?_ _
    assumption) dvd
  refine ⟨N + 1, Fin.cons b x, Fin.cons j d, ?_, ?_, ⟨K, ?_⟩⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa
    · intro m
      apply y_mem

  · have : AddSubgroup.closure s ≤ AddSubgroup.closure (Set.range (Fin.cons j d)) := by
      apply AddSubgroup.closure_mono
      intro i hi
      simp only [Fin.range_cons, Set.mem_insert_iff, Set.mem_range, Function.comp_apply, d, N]
      if h : i = j
      then left; exact h
      else
      right
      use s.equivFin ⟨i, hi⟩
      simp only [Equiv.symm_apply_apply, N, d]
    rw [hs2] at this
    convert AddSubgroup.finiteIndex_of_le this
    exact a_rel
  · simp [← hb, mul_comm]

lemma elemIsRelevant_of_homogeneous_of_factorisation
    [AddGroup.FG ι] (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a)
    (n : ℕ) (x : Fin n → A) (d : Fin n → ι)
    (mem : ∀ (i : Fin n), x i ∈ 𝒜 (d i))
    (finiteIndex : (AddSubgroup.closure (Set.range d)).FiniteIndex)
    (k : ℕ) (eq : ∏ i : Fin n, x i = a ^ k) :  ElemIsRelevant a ha := by
  rw [ElemIsRelevant, isRelevant_iff_finiteIndex_of_FG]
  set H := _; change AddSubgroup.FiniteIndex H
  suffices le : AddSubgroup.closure (Set.range d) ≤ H by
    exact AddSubgroup.finiteIndex_of_le le
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  refine AddSubgroup.subset_closure ?_
  simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, ne_eq]
  exact ⟨x i, ⟨⟨d i, mem i⟩, ⟨a ^ k, by simp [mem_closure_singleton (ha := ha)], by
    rw [← eq]; apply Finset.dvd_prod_of_mem; aesop⟩⟩, mem i⟩

lemma elemIsRelevant_iff [AddGroup.FG ι]
    (a : A) (ha : SetLike.IsHomogeneousElem 𝒜 a) :
    ElemIsRelevant a ha ↔
    ∃ (n : ℕ) (x : Fin n → A) (d : Fin n → ι)
      (_ : ∀ (i : Fin n), x i ∈ 𝒜 (d i)),
      (AddSubgroup.closure (Set.range d)).FiniteIndex ∧
      (∃ (k : ℕ), ∏ i : Fin n, x i = a ^ k) := by
  fconstructor
  · intro h
    exact exists_factorisation_of_elemIsRelevant _ ha h
  · rintro ⟨n, x, d, mem, finiteIndex, k, eq⟩
    exact elemIsRelevant_of_homogeneous_of_factorisation _ ha n x d mem finiteIndex k eq

lemma ElemIsRelevant.mul {a b : A}
    {hom_a : SetLike.IsHomogeneousElem 𝒜 a} {hom_b : SetLike.IsHomogeneousElem 𝒜 b}
    (rel_a : ElemIsRelevant a hom_a) (rel_b : ElemIsRelevant b hom_b) :
    ElemIsRelevant (a * b) (hom_a.mul hom_b) := by
  intro i
  obtain ⟨n, hn, hn'⟩ := rel_a i
  obtain ⟨m, hm, hm'⟩ := rel_b i
  refine ⟨n + m, (by positivity), ?_⟩
  rw [agrDeg, ← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set] at hn'
  obtain ⟨s, hs, (eq_s : ∑ _ ∈ _, _ • _ = _)⟩ := hn'
  rw [agrDeg, ← Submodule.span_int_eq_addSubgroup_closure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set] at hm'
  obtain ⟨t, ht, (eq_t : ∑ _ ∈ _, _ • _ = _)⟩ := hm'
  rw [add_smul, ← eq_s, ← eq_t]
  refine add_mem ?_ ?_
  · refine sum_mem fun j hj => ?_
    specialize hs hj
    refine zsmul_mem (AddSubgroup.subset_closure ?_) _
    simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq,
      AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk] at hs
    obtain ⟨a', ⟨-, ⟨z, hz1, hz⟩⟩, ha'⟩ := hs
    rw [mem_closure_singleton (ha := hom_a)] at hz1
    obtain ⟨n, rfl⟩ := hz1
    refine ⟨a', ?_, ha'⟩
    simp   only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    refine ⟨⟨j, ha'⟩, ((a * b) ^ n), ?_, ?_⟩
    · rw [mem_closure_singleton (ha := hom_a.mul hom_b)]
      use n
    rw [mul_pow]
    exact Dvd.dvd.mul_right hz (b ^ n)
  · refine sum_mem fun j hj => ?_
    specialize ht hj
    refine zsmul_mem (AddSubgroup.subset_closure ?_) _
    simp only [deg, bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq,
      AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk] at ht
    obtain ⟨a', ⟨-, ⟨z, hz1, hz⟩⟩, ha'⟩ := ht
    rw [mem_closure_singleton (ha := hom_b)] at hz1
    obtain ⟨n, rfl⟩ := hz1
    refine ⟨a', ?_, ha'⟩
    simp   only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    refine ⟨⟨j, ha'⟩, ((a * b) ^ n), ?_, ?_⟩
    · rw [mem_closure_singleton (ha := hom_a.mul hom_b)]
      use n
    rw [mul_pow]
    exact Dvd.dvd.mul_left hz (a ^ n)

end HomogeneousSubmonoid
