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

def s_lemma {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
  Localization.Away (s_elem a deg rel i) ≃ₐ[𝒜 0]
  Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i * ∑ j : Fin n, a j} <| by
    rintro - rfl
    exact SetLike.IsHomogeneousElem.mul ⟨d, by aesop⟩ ⟨d, sum_mem <| by aesop⟩) := by
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

lemma sum_lemma_open {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
  ∃ (f :
    Spec (CommRingCat.of (Localization.Away (s_elem a deg rel i))) ⟶ unionSpec a deg rel),
      IsOpenImmersion f ∧ Scheme.Hom.IsOver f (SpecBase 𝒜) := by sorry

open CategoryTheory

def Spec.restrictBasicOpen (R : CommRingCat) (x : R) :
  (Spec R).restrict (PrimeSpectrum.basicOpen x |>.isOpenEmbedding) ≅
  Spec (CommRingCat.of (Localization.Away x)) :=
  AlgebraicGeometry.basicOpenIsoSpecAway _

lemma sum_open {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) :
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
  · sorry
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
