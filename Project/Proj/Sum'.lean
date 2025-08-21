import Project.Proj.Over

import Mathlib.AlgebraicGeometry.Restrict

suppress_compilation

universe u
variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable {τ : Type u} (f : τ → A)

open HomogeneousSubmonoid AlgebraicGeometry GoodPotionIngredient


instance (B : Type u) [CommRing B] [Algebra (𝒜 0) B] :
  Scheme.Over (Spec <| CommRingCat.of B) (SpecBase 𝒜) where
    hom := Spec.map <| CommRingCat.ofHom <| algebraMap _ _

abbrev sum_potion_finset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (_ : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :=
    Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ a ∈ s, f a} <| by
      rintro - rfl
      refine ⟨d, sum_mem ?_⟩
      apply deg)

-- abbrev s_elem {n : ℕ} {d : ι} (a : Fin n → A)
--     (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
--     (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
--     (i : Fin n) :
--     sum_potion a deg rel :=
--   Quotient.mk''
--     { deg := d
--       num := ⟨a i, deg i⟩
--       den := ⟨∑ i, a i, sum_mem <| by aesop⟩
--       den_mem := by
--         simp only [mem_toSubmonoid_iff]
--         exact Submonoid.mem_closure_singleton_self }

-- def s_lemma {n : ℕ} {d : ι} (a : Fin n → A)
--     (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
--     (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
--     (i : Fin n) :
--   Localization.Away (s_elem a deg rel i) ≃ₐ[𝒜 0]
--   Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i * ∑ j : Fin n, a j} <| by
--     rintro - rfl
--     exact SetLike.IsHomogeneousElem.mul ⟨d, by aesop⟩ ⟨d, sum_mem <| by aesop⟩) := by
--   sorry

abbrev unionSpecFinset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) : Scheme :=
  Proj (𝒜 := 𝒜) (τ := s) fun i =>
    { toHomogeneousSubmonoid := .closure { f i.1 } <| by
        cases i
        simpa using ⟨d, by aesop⟩
      relevant := rel _ i.2
      fg := ⟨{f i.1}, by simp; rfl⟩ }

abbrev componentToUnionSpecFinset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {f i} (by
      rintro - rfl
      exact ⟨d, by aesop⟩) : HomogeneousSubmonoid 𝒜).Potion) ⟶
    unionSpecFinset f s deg rel :=
  (glueData (𝒜 := 𝒜) (τ := s) fun i =>
    { toHomogeneousSubmonoid := .closure { f i.1 } <| by
        cases i
        simpa using ⟨d, by aesop⟩
      relevant := rel _ i.2
      fg := ⟨{f i.1}, by simp; rfl⟩ }).ι ⟨i, hi⟩

-- lemma sum_lemma_open {n : ℕ} {d : ι} (a : Fin n → A)
--     (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
--     (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
--     (i : Fin n) :
--   ∃ (f :
--     Spec (CommRingCat.of (Localization.Away (s_elem a deg rel i))) ⟶ unionSpec a deg rel),
--       IsOpenImmersion f ∧ Scheme.Hom.IsOver f (SpecBase 𝒜) := by sorry

-- open CategoryTheory

-- def Spec.restrictBasicOpen (R : CommRingCat) (x : R) :
--   (Spec R).restrict (PrimeSpectrum.basicOpen x |>.isOpenEmbedding) ≅
--   Spec (CommRingCat.of (Localization.Away x)) :=
--   AlgebraicGeometry.basicOpenIsoSpecAway _

lemma sum_open_finset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :
  ∃ (f : Spec (CommRingCat.of <| sum_potion_finset f s deg rel) ⟶ unionSpecFinset f s deg rel),
    Scheme.Hom.IsOver f (SpecBase 𝒜) := by
  sorry
