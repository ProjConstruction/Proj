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
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) :=
    Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ i : Fin n, a i} sorry)

abbrev s_elem {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
    sum_potion a deg rel :=
  Quotient.mk''
    { deg := d
      num := ⟨a i, deg i⟩
      den := ⟨∑ i, a i, sorry⟩
      den_mem := sorry }

def s_lemma {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩)
    (i : Fin n) :
  Localization.Away (s_elem a deg rel i) ≃ₐ[𝒜 0]
  Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {a i * ∑ j : Fin n, a j} sorry) := by
  sorry

abbrev unionSpec {n : ℕ} {d : ι} (a : Fin n → A)
    (deg : ∀ i : Fin n, a i ∈ 𝒜 d)
    (rel : ∀ i : Fin n, ElemIsRelevant (a i) ⟨d, deg i⟩) : Scheme :=
  Proj (𝒜 := 𝒜) (τ := ULift <| Fin n) fun i =>
    { toHomogeneousSubmonoid := .closure { a i.down } sorry
      relevant := by sorry
      fg := by sorry }

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
    sorry)

  let U : Scheme.OpenCover (Spec (CommRingCat.of <| sum_potion a deg rel)) :=
    Scheme.openCoverOfISupEqTop _ (fun i : Fin n => PrimeSpectrum.basicOpen (s_elem a deg rel i))
      this
  -- Spec (CommRingCat.of <| sum_potion a deg rel)
  -- ≅
  -- gluing Spec (CommRingCat.of (Localization.Away (s_elem a deg rel i)))
  -- If I have a cover U_i for X
  -- and U_i -> Y
  -- how do I get X -> Y
  -- refine ⟨AlgebraicGeometry.Scheme.Cover.glueMorphisms ?_, ?_⟩
  have := Scheme.Cover.fromGlued (X := Spec (CommRingCat.of <| sum_potion a deg rel)) U.ulift
  sorry
  #exit
  refine ⟨AlgebraicGeometry.Scheme.Cover.glueMorphisms U
    (fun i : Fin n => (AlgebraicGeometry.basicOpenIsoSpecAway _).hom ≫
        (sum_lemma_open a deg rel i).choose)
    ?_, ?_, ?_⟩
  · sorry
  · apply (config := {allowSynthFailures := true}) IsOpenImmersion.comp
    sorry
  · sorry


--  Put D(a_k'):= Spec ((Localization sum_potion (a_1...a_n) s_elem k ) )

--                                            (a basic open of Spec(sum_potion))

--             Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

--                    Union k=1...n D(a_k') = Spec(sum_potion)

--             Have open immersion D(a_k') → ( (a_k)).PotionSch over Spec(A_0)

--               --by sum_lemm_open

--             Have open immersion  Union k=1...n D(a_k') → Union_k=1..n  ( ( a_k)).PotionSch over Spec(A_0)

--                -- by union/gluing

--             Have open immersion  Spec(sum_potion)  → Union ( ( a_k)).PotionSch over Spec(A_0)

--                  -- by Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

--                    --BigUnion k=1...n D(a_k') = Spec(sum_potion)


#exit

           ∃(∑ _{k=1}^n a_k).PotionSch → ∪ _k (a_k).PotionSch open immersion over Spec(A_0) :=  by

            Have Eq= s_elem  1 +...+s_elem  k +... +s_elem  n =1  in sum_potion (a_1, … , a_n )

            Put D(a_k'):= Spec ((Localization sum_potion (a_1...a_n) s_elem k ) )

                                           (a basic open of Spec(sum_potion))

            Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

                   Union k=1...n D(a_k') = Spec(sum_potion)

            Have open immersion D(a_k') → ( (a_k)).PotionSch over Spec(A_0)

              --by sum_lemm_open

            Have open immersion  Union k=1...n D(a_k') → Union_k=1..n  ( ( a_k)).PotionSch over Spec(A_0)

               -- by union/gluing

            Have open immersion  Spec(sum_potion)  → Union ( ( a_k)).PotionSch over Spec(A_0)

                 -- by Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

                   --BigUnion k=1...n D(a_k') = Spec(sum_potion)

            sorry

/-


  --(A_(∑ a_k))_{a_k'}= A_(a_k(∑ a_k)) (localization of potion ring isom potion of subtile product)

  lemma sum_lemm :  (a_1, … , a_n ) relevant of degree i (k ∈ {1...n}):

    (Localization sum_potion (a_1...a_n) s_elem k )

           ≅_[A_0] (a_k (∑ _{k=1}^n a_k)).PotionPotionRing  := by

           Exact Magic of potion

           sorry

  -- Spec( (A_(∑ a_k))_{a_k'}) → open immersion → Spec(A_(a_k))

  lemma sum_lemm_open  (a_1, … , a_n ) relevant of degree i (k ∈ 1...n): ∃ open immersion

    Spec( (Localization sum_potion (a_1...a_n) sum_elem k ) ) →

           ( (a_k)).PotionSch over Spec(A_0) := by

           apply sum_lemm and Potion( bc ) ⊆ Potion (c)

           sorry

   --Spec(A_(∑ a_k)) ---> open immersion ---> Union Spec(A_(a_k)) (Potion schemes)

  lemma sum_open : (a_1, … , a_n ) relevant of degree i :

           ∃(∑ _{k=1}^n a_k).PotionSch → ∪ _k (a_k).PotionSch open immersion over Spec(A_0) :=  by

            Have Eq= s_elem  1 +...+s_elem  k +... +s_elem  n =1  in sum_potion (a_1, … , a_n )

            Put D(a_k'):= Spec ((Localization sum_potion (a_1...a_n) s_elem k ) )

                                           (a basic open of Spec(sum_potion))

            Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

                   Union k=1...n D(a_k') = Spec(sum_potion)

            Have open immersion D(a_k') → ( (a_k)).PotionSch over Spec(A_0)

              --by sum_lemm_open

            Have open immersion  Union k=1...n D(a_k') → Union_k=1..n  ( ( a_k)).PotionSch over Spec(A_0)

               -- by union/gluing

            Have open immersion  Spec(sum_potion)  → Union ( ( a_k)).PotionSch over Spec(A_0)

                 -- by Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

                   --BigUnion k=1...n D(a_k') = Spec(sum_potion)

            sorry

-/
