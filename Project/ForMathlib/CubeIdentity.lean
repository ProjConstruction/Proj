import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

open CategoryTheory Limits

universe u v

variable {𝒞 : Type u} [Category.{v} 𝒞]
variable [HasPullbacks 𝒞]

variable {A B C D : 𝒞} (fB : B ⟶ A) (fC : C ⟶ A) (fD : D ⟶ A)


noncomputable def pullback.squash₃ (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ C):
  -- A ×[B] (B ×[C] D)
  pullback f (pullback.fst g h)
  ≅
  -- A ×[C] D
  pullback (f ≫ g) h := pullbackRightPullbackFstIso g h f


@[reassoc (attr := simp)]
lemma pullback.squash₃_hom_fst (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ C) :
    (pullback.squash₃ f g h).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [squash₃]

@[reassoc (attr := simp)]
lemma pullback.squash₃_inv_fst (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ C) :
    (pullback.squash₃ f g h).inv ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [squash₃]


@[reassoc (attr := simp)]
lemma pullback.squash₃_hom_snd (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ C) :
    (pullback.squash₃ f g h).hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp [squash₃]

@[reassoc (attr := simp)]
lemma pullback.squash₃_inv_snd (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ C) :
    (pullback.squash₃ f g h).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [squash₃]

@[simps! hom inv]
noncomputable def pullback.squash₃' (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ C):
  -- (A ×[B] C) ×[C] D
  pullback (pullback.snd f g) h
  ≅
  -- D ×[B] A
  pullback (h ≫ g) f :=
  (pullbackLeftPullbackSndIso f g h) ≪≫ pullbackSymmetry _ _

@[reassoc (attr := simp)]
lemma pullback.squash₃'_hom_fst (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ C) :
    (pullback.squash₃' f g h).hom ≫ pullback.fst _ _ = pullback.snd _ _ := by
  simp [squash₃']

@[reassoc (attr := simp)]
lemma pullback.squash₃'_inv_fst (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ C) :
    (pullback.squash₃' f g h).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.snd _ _  := by
  simp [squash₃']

@[reassoc (attr := simp)]
lemma pullback.squash₃'_hom_snd (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ C) :
    (pullback.squash₃' f g h).hom ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp [squash₃']

@[reassoc (attr := simp)]
lemma pullback.squash₃'_inv_snd (f : A ⟶ B) (g : C ⟶ B) (h : D ⟶ C) :
    (pullback.squash₃' f g h).inv ≫ pullback.snd _ _ = pullback.fst _ _ := by
  simp [squash₃']

@[simps]
noncomputable def pullback.squash₄ :
  -- (B ×[A] C) ×[C] (D ×[A] C)
  pullback
    (pullback.snd fB fC) -- B ×[A] C ⟶ C
    (pullback.snd fD fC) -- D ×[A] C ⟶ D
  ≅
  -- B ×[A] C ×[A] D
  pullback
    (pullback.fst fB fC ≫ fB) -- B × [A] C -> B -> A
    fD where
  hom := pullback.map _ _ _ _ (𝟙 _) (pullback.fst _ _) fC
    (by
      simp only [Category.id_comp]
      exact pullback.condition.symm)
    (by simpa using pullback.condition.symm)
  inv := pullback.lift (pullback.fst _ _)
    ((pullbackSymmetry _ _).hom ≫ pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ pullback.snd _ _) (by
        simp_rw [pullback.condition, Category.assoc]))
    (by simp)
  hom_inv_id := by
    ext
    · simp
    · simp
    · simp
    · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackSymmetry_hom_comp_snd_assoc, limit.lift_π_assoc, cospan_left, Category.comp_id,
      Category.id_comp]
      simp only [pullback.condition, Category.assoc]
  inv_hom_id := by
    ext
    · simp
    · simp
    · simp

@[simps]
noncomputable def pullback.klotski₀ :
  -- (B × [A] D) ×[A] C
  pullback (pullback.fst fB fD ≫ fB) fC ≅
  -- (B ×[A] C) ×[C] D
  pullback (pullback.fst fB fC ≫ fB) fD where
  hom := pullback.lift
    (pullback.lift
      (pullback.fst _ _ ≫ pullback.fst _ _)
      (pullback.snd _ _) (by
        simp only [Category.assoc]
        simp_rw [pullback.condition, ← pullback.condition]))
    ((pullbackSymmetry _ _).hom ≫ pullback.snd _ _ ≫ pullback.snd _ _)
    (by
      simp only [limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
        Category.assoc, pullbackSymmetry_hom_comp_snd_assoc]
      simp_rw [pullback.condition])
  inv := pullback.lift
    (pullback.lift
      (pullback.fst _ _ ≫ pullback.fst _ _)
      (pullback.snd _ _)
      (by
        simp only [Category.assoc]
        simp_rw [pullback.condition, ← pullback.condition]))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by
      simp only [limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
        Category.assoc]
      simp_rw [pullback.condition])
  hom_inv_id := by
    ext
    · simp
    · simp
    · simp
  inv_hom_id := by
    ext
    · simp
    · simp
    · simp

@[simps]
noncomputable def pullback.klotski₁ :
  -- (B ×[A] C) ×[C] D
  pullback (pullback.fst fB fC ≫ fB) fD
  ≅
  -- (C ×[A] B) × [B] D
  pullback (pullback.fst fC fB ≫ fC) fD where
    hom := pullback.map _ _ _ _ (pullbackSymmetry _ _ |>.hom) (𝟙 _) (𝟙 _)
      (by simp [pullback.condition]) (by simp)
    inv := pullback.map _ _ _ _ (pullbackSymmetry _ _ |>.inv) (𝟙 _) (𝟙 _)
      (by simp [pullback.condition]) (by simp)
    hom_inv_id := by ext <;> simp
    inv_hom_id := by ext <;> simp


noncomputable def pullback.cube₀ :
  -- (B ×[A] D) ×[D] (C ×[A] D)
  pullback
    (pullback.snd fB fD) -- B ×[A] D ⟶ D
    (pullback.snd fC fD) -- C ×[A] D ⟶ D
  ≅
  -- (B ×[A] C) ×[C] (D ×[A] C)
  pullback
      (pullback.snd fB fC) -- B ×[A] C ⟶ C
      (pullback.snd fD fC) -- D ×[A] C ⟶ C
    :=
  pullback.squash₄ _ _ _ ≪≫
  (pullback.klotski₀ _ _ _) ≪≫
  (pullback.squash₄ _ _ _).symm

noncomputable def pullback.cube₁ :
  -- (B ×[A] C) ×[C] (D ×[A] C)
  pullback
      (pullback.snd fB fC) -- B ×[A] C ⟶ C
      (pullback.snd fD fC) -- D ×[A] C ⟶ C
  ≅
  -- (C ×[A] B) × [B] (D ×[A] B)
  pullback
    (pullback.snd fC fB) -- C ×[A] B ⟶ B
    (pullback.snd fD fB) -- D ×[A] B
    :=
  pullback.squash₄ _ _ _ ≪≫
  (pullback.klotski₁ _ _ _) ≪≫
  (pullback.squash₄ _ _ _).symm
