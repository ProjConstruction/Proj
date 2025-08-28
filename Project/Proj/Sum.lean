import Project.Proj.Over

import Mathlib.AlgebraicGeometry.Restrict

suppress_compilation

universe u
variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]


open HomogeneousSubmonoid AlgebraicGeometry GoodPotionIngredient


instance (B : Type u) [CommRing B] [Algebra (𝒜 0) B] :
  Scheme.Over (Spec <| CommRingCat.of B) (SpecBase 𝒜) where
    hom := Spec.map <| CommRingCat.ofHom <| algebraMap _ _

abbrev sum_potion {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (_ : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) :=
    Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ i : Fin n, a i} <| by
      rintro a rfl
      refine ⟨d, sum_mem ?_⟩
      aesop)

abbrev s_elem {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
    sum_potion a deg rel :=
  Quotient.mk''
    { deg := d
      num := ⟨a i, deg i⟩
      den := ⟨∑ i, a i, sum_mem <| by aesop⟩
      den_mem := by
        simp only [mem_toSubmonoid_iff]
        exact Submonoid.mem_closure_singleton_self }

/-
A_({a * b}) = A_(a ^ ℕ * b ^ ℕ)
-/
instance {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
    Algebra (sum_potion a deg rel)
    (Potion
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ j : Fin n, a j} (by sorry) *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i} (by sorry))) :=
  RingHom.toAlgebra <| potionToMul _ _

def s_lemma {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
  Localization.Away (s_elem a deg rel i) ≃ₐ[sum_potion a deg rel]
  Potion
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ j : Fin n, a j} _ *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i} _) := by
  let e := HomogeneousSubmonoid.localizationAlgEquivPotion (𝒜 := 𝒜)
    (S := HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ i : Fin n, a i} <| by
      rintro a rfl
      refine ⟨d, sum_mem ?_⟩
      aesop)
    (T := HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i} (by sorry))
    (T' := {
      index := PUnit.{1}
      elem := fun _ => a i
      elem_mem := by sorry
      gen := by sorry
      n := fun _ => 1
      s := fun _ => ∑ i, a i
      s' := fun _ => 1
      s_mem_bar := sorry
      s'_mem_bar := fun _ => one_mem _
      i := fun _ => d
      i' := fun _ => 0
      t_deg := by aesop
      s_deg := by sorry
      s'_deg := sorry
    })
  refine AlgEquiv.trans (Localization.equivEq ?_) e

  -- magic of potion
  sorry

abbrev unionSpec {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) : Scheme :=
  Proj (𝒜 := 𝒜) (τ := ULift <| Fin n) fun i =>
    { toHomogeneousSubmonoid := .closure { a i.down } <| by
        cases i
        simpa using ⟨d, by aesop⟩
      relevant := rel _
      fg := ⟨{a i.down}, by simp; rfl⟩ }

def Spec.restrictBasicOpen (R : CommRingCat) (x : R) :
  (Spec R).restrict (PrimeSpectrum.basicOpen x |>.isOpenEmbedding) ≅
  Spec (CommRingCat.of (Localization.Away x)) :=
  AlgebraicGeometry.basicOpenIsoSpecAway _

lemma opens_subset_union_mul {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) :
    (Scheme.Hom.opensRange
      ((glueData (𝒜 := 𝒜) (ℱ := id)).ι ⟨HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ i : Fin n, a i} <| by
      rintro a rfl
      refine ⟨d, sum_mem ?_⟩
      aesop, sorry, sorry⟩ : Spec (CommRingCat.of <| sum_potion a deg rel) ⟶ Proj (ℱ := id)) : Set _) ⊆
    (⋃ i : Fin n,
      (Scheme.Hom.opensRange
        ((glueData (𝒜 := 𝒜) (ℱ := id)).ι
          ⟨HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ j : Fin n, a j} sorry *
            HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i} sorry, sorry, sorry⟩ :
              Spec (CommRingCat.of <|
              (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ j : Fin n, a j} sorry *
                HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i} sorry).Potion) ⟶ Proj (ℱ := id))).1) := by
  intro x hx
  simp only [glueData_U, id_eq, Scheme.Hom.coe_opensRange, Set.mem_range] at hx
  obtain ⟨x, rfl⟩ := hx

  have eq : ∑ i : Fin n, s_elem a deg rel i = 1 := by
    delta s_elem
    ext
    simp only [HomogeneousLocalization.val_one]
    rw [← HomogeneousLocalization.sum_val]
    simp only [HomogeneousLocalization.val_mk]
    erw [← Localization.mk_sum (M := Submonoid.closure {∑ i, a i}) a (Finset.univ) ⟨∑ i, a i, Submonoid.subset_closure (by simp)⟩]
    simp only [Localization.mk_self_mk]
  have := PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := fun i : Fin n => s_elem a deg rel i) |>.2 (by
    rw [Ideal.eq_top_iff_one, ← eq]
    apply Ideal.sum_mem
    rintro i -
    refine Ideal.subset_span ?_
    simp)

  let U : Scheme.OpenCover (Spec (CommRingCat.of <| sum_potion a deg rel)) :=
    Scheme.openCoverOfISupEqTop _ (fun i : Fin n => PrimeSpectrum.basicOpen (s_elem a deg rel i))
      this

  let i := U.f x
  simp only [glueData_U, id_eq, mul_toSubmonoid, TopologicalSpace.Opens.carrier_eq_coe,
    Scheme.Hom.coe_opensRange, Set.mem_iUnion, Set.mem_range]
  use i
  have := U.covers x
  simp only [Set.mem_range] at this
  obtain ⟨y, hy⟩ := this
  let g := s_lemma a deg rel i
  let G := Spec.map (CommRingCat.ofHom g.symm.toRingHom)
  dsimp? [U] at y
  refine ⟨G.base <| Spec.restrictBasicOpen (CommRingCat.of <| sum_potion a deg rel) (s_elem a deg rel i) |>.hom.base y,
    ?_⟩
  conv_rhs => rw [← hy]
  aesop_cat

-- lemma sum_lemma_open' {n : ℕ} {d : ι} (a : Fin n → A)
--     (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
--     (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) :
--   ∃ (f : ∀ i : Fin n, Spec (CommRingCat.of (Localization.Away (s_elem a deg rel i))) ⟶ unionSpec a deg rel),
--     (∀ i : Fin n, Scheme.Hom.IsOver (f i) (SpecBase 𝒜)) ∧ True  := by
--   let f (i : Fin n) : Spec (CommRingCat.of (Localization.Away (s_elem a deg rel i))) ⟶ unionSpec a deg rel := by
--     (GoodPotionIngredient.glueData _).ι _
--     sorry
--   sorry

open CategoryTheory

lemma sum_open {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) :
  ∃ (f : Spec (CommRingCat.of <| sum_potion a deg rel) ⟶ unionSpec a deg rel),
    Scheme.Hom.IsOver f (SpecBase 𝒜) := by
  let F : Spec (CommRingCat.of <| sum_potion a deg rel) ⟶ Proj (𝒜 := 𝒜) (ℱ := id) :=
    (glueData (𝒜 := 𝒜) (ℱ := id)).ι ⟨HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ i : Fin n, a i} <| by
      rintro a rfl
      refine ⟨d, sum_mem ?_⟩
      aesop, sorry, sorry⟩

  sorry
  -- have eq : ∑ i : Fin n, s_elem a deg rel i = 1 := by
  --   delta s_elem
  --   ext
  --   simp only [HomogeneousLocalization.val_one]
  --   rw [← HomogeneousLocalization.sum_val]
  --   simp only [HomogeneousLocalization.val_mk]
  --   erw [← Localization.mk_sum (M := Submonoid.closure {∑ i, a i}) a (Finset.univ) ⟨∑ i, a i, Submonoid.subset_closure (by simp)⟩]
  --   simp only [Localization.mk_self_mk]
  -- have := PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := fun i : Fin n => s_elem a deg rel i) |>.2 (by
  --   rw [Ideal.eq_top_iff_one, ← eq]
  --   apply Ideal.sum_mem
  --   rintro i -
  --   refine Ideal.subset_span ?_
  --   simp)

  -- let U : Scheme.OpenCover (Spec (CommRingCat.of <| sum_potion a deg rel)) :=
  --   Scheme.openCoverOfISupEqTop _ (fun i : Fin n => PrimeSpectrum.basicOpen (s_elem a deg rel i))
  --     this

  -- refine ⟨AlgebraicGeometry.Scheme.Cover.glueMorphisms U
  --   (fun i : Fin n => (AlgebraicGeometry.basicOpenIsoSpecAway _).hom ≫
  --       (sum_lemma_open a deg rel i).choose)
  --   ?_, ?_⟩
  -- · rintro i j
  --   dsimp
  --   sorry
  -- · rw [Scheme.Hom.isOver_iff]
  --   apply U.hom_ext
  --   intro i
  --   rw [U.ι_glueMorphisms_assoc, Category.assoc]
  --   generalize_proofs _ _ _ _ _ _ _ _ h
  --   have := h.choose_spec.2
  --   rw [Scheme.Hom.isOver_iff] at this
  --   rw [this]
  --   simp only [Scheme.openCoverOfISupEqTop_obj, Scheme.openCoverOfISupEqTop_map, comp_over, U]
  --   change _ ≫ Spec.map _ = _ ≫ Spec.map _
  --   rw [AlgebraicGeometry.Scheme.Opens.over_def]
  --   symm
  --   rw [← Iso.inv_comp_eq]
  --   simp only [basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]
  --   rw [← Spec.map_comp]
  --   rfl

#exit
lemma sum_open' {d : ι} (a : Finset A)
    (deg : ∀ x ∈ a, x ∈ 𝒜 d)
    (rel : ∀ x ∈ a, ElemIsRelevant x ⟨d, deg _ _⟩) :
  ∃ (f : Spec (CommRingCat.of <| sum_potion a deg rel) ⟶ unionSpec a deg rel),
    Scheme.Hom.IsOver f (SpecBase 𝒜) := by
  have eq : ∑ i : Fin n, s_elem a deg rel i = 1 := by
    delta s_elem
    ext
    simp only [HomogeneousLocalization.val_one]
    rw [← HomogeneousLocalization.sum_val]
    simp only [HomogeneousLocalization.val_mk]
    erw [← Localization.mk_sum (M := Submonoid.closure {∑ i, a i}) a (Finset.univ) ⟨∑ i, a i, Submonoid.subset_closure (by simp)⟩]
    simp only [Localization.mk_self_mk]
  have := PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := fun i : Fin n => s_elem a deg rel i) |>.2 (by
    rw [Ideal.eq_top_iff_one, ← eq]
    apply Ideal.sum_mem
    rintro i -
    refine Ideal.subset_span ?_
    simp)

  let U : Scheme.OpenCover (Spec (CommRingCat.of <| sum_potion a deg rel)) :=
    Scheme.openCoverOfISupEqTop _ (fun i : Fin n => PrimeSpectrum.basicOpen (s_elem a deg rel i))
      this

  refine ⟨AlgebraicGeometry.Scheme.Cover.glueMorphisms U
    (fun i : Fin n => (AlgebraicGeometry.basicOpenIsoSpecAway _).hom ≫
        (sum_lemma_open a deg rel i).choose)
    ?_, ?_⟩
  · rintro i j
    dsimp
    sorry
  · rw [Scheme.Hom.isOver_iff]
    apply U.hom_ext
    intro i
    rw [U.ι_glueMorphisms_assoc, Category.assoc]
    generalize_proofs _ _ _ _ _ _ _ _ h
    have := h.choose_spec.2
    rw [Scheme.Hom.isOver_iff] at this
    rw [this]
    simp only [Scheme.openCoverOfISupEqTop_obj, Scheme.openCoverOfISupEqTop_map, comp_over, U]
    change _ ≫ Spec.map _ = _ ≫ Spec.map _
    rw [AlgebraicGeometry.Scheme.Opens.over_def]
    symm
    rw [← Iso.inv_comp_eq]
    simp only [basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]
    rw [← Spec.map_comp]
    rfl
