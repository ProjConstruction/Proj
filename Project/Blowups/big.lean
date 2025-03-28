import Project.Dilatation.Multicenter
import Mathlib.Data.Sum.Basic
import Project.Dilatation.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Project.Dilatation.lemma
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Basic
import Project.Dilatation.Family
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Project.HomogeneousSubmonoid.Basic
import Project.ForMathlib.TensorProduct
import Project.Proj.Over
import Project.Proj.OfLE
import Project.Dilatation.Multicenter
import Mathlib.Topology.Sets.Closeds



suppress_compilation
universe u
variable {A : Type (u+1)} [CommRing A]
variable {B : Type (u+1)} [CommRing B]
variable {ι : Type (u+1)} [Fintype ι] (L : ι → Ideal A) [DecidableEq ι]
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]


open GoodPotionIngredient
def Bl  := Proj (τ := GoodPotionIngredient (ReesAlgebra.intGrading L)) id


structure Mu : Type (u + 1) where
multicenter : Multicenter A
[fin : Fintype multicenter.index]
Ψ : multicenter.index → ι
sec : ι → multicenter.index
surj : ∀ i, Ψ (sec i) = i
cond : ∀ i, multicenter.LargeIdeal i = L (Ψ i)

attribute [instance] Mu.fin


omit [Fintype ι] [DecidableEq ι] [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt ι))] in
instance Bl.nonempty_index [Nonempty ι] (P : Mu L) : Nonempty P.multicenter.index := by
  apply Nonempty.map P.sec
  assumption

omit [Fintype ι] [DecidableEq ι] [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt ι))] in
lemma Bl.isEmpty_index [IsEmpty ι] (P : Mu L) : IsEmpty P.multicenter.index := by
  by_contra rid
  simp only [not_isEmpty_iff] at rid
  have : IsEmpty (P.multicenter.index → ι) := by
    infer_instance
  exact this.elim P.Ψ

omit [Fintype ι] [DecidableEq ι] [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))] in
lemma Mu.surjective (P: Mu L) : Function.Surjective P.Ψ := by
  intro i
  use P.sec i
  exact P.surj i

variable {index' : Type u} [Fintype index']
variable {index}
@[simps]
def union_center (F : Multicenter A) (F' : Multicenter A):
    Multicenter A :=
  { index := F.index ⊕ F'.index
    ideal := fun i => match i with
      | Sum.inl i => F.ideal i
      | Sum.inr i => F'.ideal i
    elem := fun i => match i with
      | Sum.inl i => F.elem i
      | Sum.inr i => F'.elem i }

@[simp]
lemma union_center_largeIdeal_left (F F' : Multicenter A) (i : F.index) :
 (union_center F F').LargeIdeal (Sum.inl i) = F.LargeIdeal i := rfl

@[simp]
lemma union_center_largeIdeal_right (F : Multicenter A) (F' : Multicenter A) (i : F'.index) :
 (union_center F F').LargeIdeal (Sum.inr i) = F'.LargeIdeal i := rfl

def union_Mu (P : Mu L) (P' : Mu L) : Mu L :=
  { multicenter := union_center P.multicenter P'.multicenter,
    fin := instFintypeSum _ _
    Ψ := Sum.rec (P.Ψ) (P'.Ψ),
    sec := Sum.inl ∘ P.sec
    surj := by
      intro i
      simpa [Function.comp_apply] using P.surj i
    cond := by
      rintro (i|i)
      · simp [P.cond i]
      · simp [P'.cond i] }

variable [DecidableEq index] [DecidableEq index']

def clo_mu (P: Mu L)  :
    HomogeneousSubmonoid (ReesAlgebra.intGrading L):=
  HomogeneousSubmonoid.closure
      { ReesAlgebra.single L (Finsupp.single (P.Ψ i) 1) ⟨P.multicenter.elem i, by
        rw [familyPow_single, ← P.cond i]
        apply Multicenter.elem_mem_LargeIdeal⟩ | (i : P.multicenter.index) } <| by
  rintro _ ⟨i, rfl⟩
  use (Finsupp.single (P.Ψ i) 1)
  simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply]
  split_ifs with h
  · rcases h with ⟨n, hn⟩
    have eq₀ : n = Finsupp.single (P.Ψ i) 1 := by
      ext j
      rw [Finsupp.ext_iff] at hn
      specialize hn j
      simp only [Finsupp.single_apply] at hn ⊢
      split_ifs at hn ⊢ with h
      · simpa [ρNatToInt] using hn
      · simpa [ρNatToInt] using hn

    refine ⟨⟨P.multicenter.elem i, ?_⟩, ?_⟩
    · simp_rw [← hn]
      generalize_proofs _ h1
      have eq : Set.rangeSplitting ⇑(ρNatToInt ι) ⟨(ρNatToInt ι) n, h1⟩ = n := by
        apply ρNatToInt_inj
        rw [Set.apply_rangeSplitting (ρNatToInt ι)]
      rw [eq, eq₀]

      rw [familyPow_single, ← P.cond i]
      apply Multicenter.elem_mem_LargeIdeal

    · apply ReesAlgebra.single_eq
      subst eq₀
      apply ρNatToInt_inj
      simp_rw [← hn]
      rw [Set.apply_rangeSplitting (ρNatToInt ι)]
  · refine h ?_ |>.elim
    use Finsupp.single (P.Ψ i) 1
    ext j
    simp [ρNatToInt]


omit [Fintype ι] in
lemma mu_clo_isEmpty [IsEmpty ι] (P: Mu L)  :
    clo_mu L P = HomogeneousSubmonoid.bot := by
  ext x
  simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    HomogeneousSubmonoid.mem_toSubmonoid_iff, HomogeneousSubmonoid.mem_bot]
  refine ⟨?_, by rintro rfl; exact one_mem _⟩
  intro H
  refine Submonoid.closure_induction (hx := H) ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact (Bl.isEmpty_index L P).elim i
  · rfl
  · rintro x y hx hy rfl rfl
    simp

open Family

omit [Fintype ι] in
lemma mem_clo_mu (P : Mu L) (x) :
    x ∈ clo_mu L P ↔
      ∃ (n : P.multicenter.index →₀ ℕ), x =
      (fun i ↦ .single L (Finsupp.single (P.Ψ i) 1)
      ⟨P.multicenter.elem i, by
        simp only [familyPow_single]
        rw [← P.cond]
        exact Multicenter.elem_mem_LargeIdeal P.multicenter i⟩ : P.multicenter.index → ReesAlgebra L) ^ n := by
  obtain (E|⟨i⟩) := isEmpty_or_nonempty ι
  · fconstructor
    · rintro h
      rw [mu_clo_isEmpty] at h
      simp only [HomogeneousSubmonoid.mem_bot] at h
      subst h
      use 0
      simp
    · rintro ⟨n, hn, rfl⟩
      refine prod_mem fun i hi ↦ ?_
      exact (Bl.isEmpty_index L P).elim i
  fconstructor
  · intro hx
    refine Submonoid.closure_induction (hx := hx) ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      use Finsupp.single i 1
      simp only [familyPow_single]
    · use Finsupp.single (Bl.nonempty_index L P).some 0
      simp
    · rintro x y hx hy ⟨m, rfl⟩ ⟨n, rfl⟩
      use m + n
      rw [familyPow_add]

  · rintro ⟨n, hn, rfl⟩
    refine prod_mem fun i hi ↦ Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
    use i

omit [Fintype ι] in
lemma clo_mu_bar_agrDeg (P: Mu L) :
    (clo_mu L P).bar.agrDeg = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [← Finsupp.sum_single x]
  refine sum_mem fun i hi ↦ ?_
  rw [show Finsupp.single i (x i) = x i • Finsupp.single i 1 by simp]
  refine zsmul_mem ?_ _
  refine AddSubgroup.subset_closure ⟨.single L (Finsupp.single i 1)
    ⟨P.multicenter.elem (P.sec i), by
      simp only [familyPow_single', pow_one]
      rw [show L i = L (P.Ψ (P.sec i)) by rw [P.surj], ← P.cond]
      exact Multicenter.elem_mem_LargeIdeal P.multicenter (P.sec i)⟩, ⟨?_, ?_⟩, ?_⟩
  · use Finsupp.single i 1
    simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply]
    rw [dif_pos ⟨Finsupp.single i 1, by simp⟩]
    simp_rw [← show ρNatToInt ι (Finsupp.single i 1) = Finsupp.single i 1 by simp]
    rw [Set.rangeSplitting_apply_coe (inj := ρNatToInt_inj)]
    refine ⟨⟨P.multicenter.elem (P.sec i), ?_⟩, rfl⟩
    simp only [familyPow_single', pow_one]
    rw [show L i = L (P.Ψ (P.sec i)) by rw [P.surj], ← P.cond]
    exact Multicenter.elem_mem_LargeIdeal P.multicenter (P.sec i)
  · refine ⟨_, Submonoid.subset_closure ⟨P.sec i, ?_⟩, by rfl⟩
    apply ReesAlgebra.single_eq
    rw [P.surj i]
  · simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply]
    rw [dif_pos ⟨Finsupp.single i 1, by simp⟩]
    simp_rw [← show ρNatToInt ι (Finsupp.single i 1) = Finsupp.single i 1 by simp]
    rw [Set.rangeSplitting_apply_coe (inj := ρNatToInt_inj)]
    refine ⟨⟨P.multicenter.elem (P.sec i), ?_⟩, rfl⟩
    simp only [familyPow_single', pow_one]
    rw [show L i = L (P.Ψ (P.sec i)) by rw [P.surj], ← P.cond]
    exact Multicenter.elem_mem_LargeIdeal P.multicenter (P.sec i)

lemma clo_mu_rel (P: Mu L) : (clo_mu L P).IsRelevant := by
  rw [HomogeneousSubmonoid.isRelevant_iff_finiteIndex_of_FG, clo_mu_bar_agrDeg]
  infer_instance

-- A -> (Rees L)[0] -> (clo_mu L P).Potion
def mu_potion_algebraMap (P: Mu L)  :
    A →+* ((clo_mu L P).Potion) :=
  RingHom.comp (algebraMap _ _) (ReesAlgebra.degreeZeroIso' L |>.toRingHom)


instance (P: Mu L) : Algebra A ((clo_mu L P).Potion) :=
  RingHom.toAlgebra (mu_potion_algebraMap L P)

omit [Fintype ι] in
lemma mu_potion_algebraMap_eq (P: Mu L) :
  algebraMap A (clo_mu L P).Potion = mu_potion_algebraMap L P := rfl

open Multicenter Multicenter.Dilatation
def clo_mu_mor (P: Mu L) :
  A[P.multicenter] →ₐ[A] (clo_mu L P).Potion :=
   Multicenter.desc P.multicenter
    (by
      intro i
      intro x hx
      induction x using Quotient.inductionOn' with | h x =>
      change HomogeneousLocalization.mk x = 0
      change HomogeneousLocalization.mk x * HomogeneousLocalization.mk _ = 0 at hx


      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ReesAlgebra.degreeZeroIso'_apply,
        HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
        HomogeneousLocalization.val_mk, Set.mem_range, ρNatToInt_apply, id_eq, eq_mpr_eq_cast,
        cast_eq, SetLike.GradeZero.coe_one, Localization.mk_mul, Submonoid.mk_mul_mk, mul_one,
        HomogeneousLocalization.val_zero, ← Localization.mk_zero 1, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists, OneMemClass.coe_one, one_mul, mul_zero, Subtype.exists,
        HomogeneousSubmonoid.mem_toSubmonoid_iff, exists_prop] at hx ⊢
      obtain ⟨s, hs1, hs2⟩ := hx
      rw [mem_clo_mu] at hs1
      obtain ⟨n, rfl⟩ := hs1
      rw [ReesAlgebra.single_familyPow] at hs2

      obtain ⟨w, hw⟩ := ReesAlgebra.eq_single_of_homogeneous' L x.num ⟨_, x.num.2⟩
      rw [hw] at hs2 ⊢
      rw [ReesAlgebra.single_mul, ReesAlgebra.single_mul, ReesAlgebra.single_eq_zero] at hs2
      simp only [Submodule.mk_eq_zero] at hs2
      refine ⟨(∏ x ∈ n.support, .single _ (Finsupp.single (P.Ψ x) 1) ⟨P.multicenter.elem x, by
        simp only [familyPow_single', pow_one]
        rw [← P.cond]
        exact elem_mem_LargeIdeal P.multicenter x⟩ ^ n x) *
        .single _ (Finsupp.single (P.Ψ i) 1) ⟨P.multicenter.elem i, by
          simp only [familyPow_single', pow_one]
          rw [← P.cond]
          exact elem_mem_LargeIdeal P.multicenter i⟩, mul_mem (Submonoid.prod_mem _ fun j hj ↦
            Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _) (Submonoid.subset_closure ?_), ?_⟩
      · simp
      · simp
      simp_rw [ReesAlgebra.single_npow]
      rw [ReesAlgebra.single_prod, ReesAlgebra.single_mul, ReesAlgebra.single_mul,
        ReesAlgebra.single_eq_zero]
      simp only [Submodule.mk_eq_zero, ← hs2]
      ring)
    (by
      intro i

      refine le_antisymm ?_ ?_
      · rw [Ideal.span_le]
        rintro _ rfl
        apply Ideal.mem_map_of_mem
        exact elem_mem_LargeIdeal P.multicenter i
      · rw [Multicenter.LargeIdeal, Ideal.add_eq_sup, Ideal.map_sup, sup_le_iff, Ideal.map_span]
        simp only [Set.image_singleton, le_refl, and_true]
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap]
        have eq : algebraMap A (clo_mu L P).Potion x =
          algebraMap A (clo_mu L P).Potion (P.multicenter.elem i) *
          HomogeneousLocalization.mk
            { deg := Finsupp.single (P.Ψ i) (1 : ℤ),
              num := ⟨.single _ (Finsupp.single (P.Ψ i) 1) ⟨x, ?num_deg⟩, ?num_deg'⟩
              den := ⟨.single _ (Finsupp.single (P.Ψ i) 1) ⟨P.multicenter.elem i, ?den_deg⟩, ?den_deg'⟩
              den_mem := ?den_mem } := by
          ext
          simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk]
          erw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
          simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ReesAlgebra.degreeZeroIso'_apply,
            Set.mem_range, ρNatToInt_apply, id_eq, eq_mpr_eq_cast, cast_eq,
            SetLike.GradeZero.coe_one, Localization.mk_mul, Submonoid.mk_mul_mk, one_mul,
            Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists,
            HomogeneousSubmonoid.mem_toSubmonoid_iff, exists_prop]
          refine ⟨1, one_mem _, ?_⟩
          simp only [ReesAlgebra.single_mul, one_mul]
          apply ReesAlgebra.single_eq'
          · rw [add_comm]
          · rfl
        pick_goal 4
        · simp only [familyPow_single', pow_one]
          rw [← P.cond, Multicenter.LargeIdeal, Ideal.add_eq_sup]
          exact le_sup_left (a := P.multicenter.ideal i)
            (b := Ideal.span {P.multicenter.elem i}) hx
        · simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range,
            ρNatToInt_apply]
          rw [dif_pos ⟨Finsupp.single (P.Ψ i) 1, by simp⟩]
          refine ⟨⟨x, ?_⟩, ?_⟩
          · generalize_proofs _ h
            rw [show Set.rangeSplitting (ρNatToInt ι) ⟨Finsupp.single (P.Ψ i) 1, h⟩ =
              Finsupp.single (P.Ψ i) 1 from ρNatToInt_inj (by
                rw [Set.apply_rangeSplitting (ρNatToInt ι)]
                simp)]
            simp only [familyPow_single', pow_one]
            rw [← P.cond]
            exact le_sup_left (a := P.multicenter.ideal i)
              (b := Ideal.span {P.multicenter.elem i}) hx
          · apply ReesAlgebra.single_eq
            apply ρNatToInt_inj
            rw [Set.apply_rangeSplitting (ρNatToInt ι)]
            simp
        pick_goal 3
        · simp only [familyPow_single', pow_one]
          rw [← P.cond]
          exact elem_mem_LargeIdeal P.multicenter i
        · simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range,
            ρNatToInt_apply]
          rw [dif_pos ⟨Finsupp.single (P.Ψ i) 1, by simp⟩]
          refine ⟨⟨P.multicenter.elem i, ?_⟩, ?_⟩
          · generalize_proofs _ h
            rw [show Set.rangeSplitting (ρNatToInt ι) ⟨Finsupp.single (P.Ψ i) 1, h⟩ =
              Finsupp.single (P.Ψ i) 1 from ρNatToInt_inj (by
                rw [Set.apply_rangeSplitting (ρNatToInt ι)]
                simp)]
            simp only [familyPow_single', pow_one]
            rw [← P.cond]
            exact elem_mem_LargeIdeal P.multicenter i
          · apply ReesAlgebra.single_eq
            apply ρNatToInt_inj
            rw [Set.apply_rangeSplitting (ρNatToInt ι)]
            simp
        · apply Submonoid.subset_closure
          use i
        rw [eq]
        apply Ideal.mul_mem_right
        apply Ideal.subset_span
        rfl)

def Mu_mor_iso (P: Mu L) :
    A[P.multicenter] ≃ₐ[A] (clo_mu L P).Potion :=
  AlgEquiv.ofBijective sorry sorry
-- lemma Mu_mor_iso (P: Mu L ): Mu_mor is an iso :=
--   by  in


def map_index (P: Mu L) :
    GoodPotionIngredient (ReesAlgebra.intGrading L) where
  toHomogeneousSubmonoid := clo_mu L P
  relevant := clo_mu_rel L P
  fg := sorry


open AlgebraicGeometry

def BlMu : Scheme :=
  Proj (τ := Mu L) (map_index L)

def BlMuToBl : BlMu L ⟶ Bl L :=
  projHomOfLE
    { t :=
      { toFun := map_index L
        inj' := sorry }
      comp := rfl }

-- open CategoryTheory
-- instance Dila_cov_proj : IsIso (BlMuToBl index L) := by
--      --in the paper
--     sorry

lemma inter_Po (P P' : Mu L) :
    ((glueData (τ := Mu L) (map_index L)).ι P).opensRange ⊓
    ((glueData (τ := Mu L) (map_index L)).ι P').opensRange =
    ((glueData (τ := Mu L) (map_index L)).ι (union_Mu L P P')).opensRange := by
          -- D(S) ∩ D(T) =D(ST)
  sorry



def dilToDilUnion (P P': Mu L) : A[P.multicenter] →ₐ[A] A[(union_Mu L P P').multicenter] :=
  Multicenter.desc _ sorry sorry

instance (P P': Mu L) : Algebra A[P.multicenter] A[(union_Mu L P P').multicenter] :=
  RingHom.toAlgebra (dilToDilUnion L P P')

lemma dilToDilUnion_as_algebraMap (P P': Mu L) : algebraMap A[P.multicenter] A[(union_Mu L P P').multicenter] =
  dilToDilUnion L P P' := rfl

def dilToDilUnion' (P P': Mu L) : A[P'.multicenter]→ₐ[A] A[(union_Mu L P P').multicenter] :=
  Multicenter.desc _ sorry sorry

instance (P P': Mu L) : Algebra A[P'.multicenter] A[(union_Mu L P P').multicenter] :=
  RingHom.toAlgebra (dilToDilUnion' L P P')

lemma dilToDilUnion'_as_algebraMap (P P': Mu L) : algebraMap A[P'.multicenter] A[(union_Mu L P P').multicenter] =
  dilToDilUnion' L P P' := rfl

lemma lemm_dila  [Algebra A B] (P P': Mu L) (c : ι →  nonZeroDivisors B) (i : ι)
    (g: A[P.multicenter]→ₐ[A] B)
    (g':  A[P'.multicenter]→ₐ[A] B)
    (cond1: Ideal.map (algebraMap A B) (L i) = Ideal.span  {(c i).1})
    (cond2: (Algebra.ofId A B)= AlgHom.comp g (Algebra.ofId A A[P.multicenter]) )
    (cond2': (Algebra.ofId A B)= AlgHom.comp g' (Algebra.ofId A A[P'.multicenter])) :
    ∃! (g'' : A[(union_Mu L P P').multicenter] →ₐ[A] B),
      g = AlgHom.comp g'' (Algebra.ofId A[P.multicenter] A[(union_Mu L P P').multicenter] |>.restrictScalars _) ∧
      g' = AlgHom.comp g'' (Algebra.ofId A[P'.multicenter] A[(union_Mu L P P').multicenter] |>.restrictScalars _) := by
    -- desc union_center P P'
  sorry



variable {X : Scheme}

open TopologicalSpace CategoryTheory.Limits

instance (R : Type*) [CommRing R] (I : Ideal R) :
    Scheme.Over (Spec (CommRingCat.of (R ⧸ I))) (Spec <| CommRingCat.of R)  where
  hom := Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk I

open CategoryTheory

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) Z where
  hom := pullback.fst f g ≫ f

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) X where
  hom := pullback.fst f g

instance (X Y Z : Scheme) (f : X ⟶ Z) (g : Y ⟶ Z) :
    Scheme.Over (pullback f g) Y where
  hom := pullback.snd f g

/-


            cov.obj j
              |
              v
subschem i ->  X
-/
variable (X) in
structure PreClos where
  (indnumb : Type u)
  [fin_indnumb : Fintype indnumb]
  (clotop : indnumb → Closeds X)
  (subscheme: indnumb → Scheme)
  (condset : ∀ i : indnumb, clotop i ≃ₜ (subscheme i)) -- maybe unnecessary?
  [over : ∀ (i : indnumb), Scheme.Over (subscheme i) X]
  cov : Scheme.AffineCover (P := @IsOpenImmersion) X
  ideal: ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ)
  condiso : ∀ (i : indnumb) (γ : cov.J),
    Spec (CommRingCat.of (cov.obj γ ⧸ ideal i γ)) ≅
    pullback (f := subscheme i ↘ X) (g := cov.map γ)
  condover : ∀ (i : indnumb) (γ : cov.J),
    Scheme.Hom.IsOver (condiso i γ).hom
      (Spec (CommRingCat.of (cov.obj γ)))

attribute [instance] PreClos.over
/- -/
-- def PreClos_on_refinement (Z: PreClos) (cov': refinment of Z.cov) : X.Preclos :=
--    indnumb : Z.indnumb
--    clotop: indnumb → closed (underlying top of X)
--    subscheme: indnumb → AlgebraicGeometry.Scheme
--    condset : clotop i = underlying top (subscheme i)
--    mor: indnumb → subscheme i →sch X
--    cov: cov'
--    ideal:   indnumb → cov.index → image ideal A γ
--    condiso: use condiso Z-/


structure relStructure (Z Z' : PreClos X) where -- := fun Z Z' =>
  indnumb_equiv :  Z.indnumb ≃ Z'.indnumb
  clotop_homeomorph : ∀ i, Z.clotop i ≃ₜ Z'.clotop (indnumb_equiv i)
  subscheme_iso : ∀ i, Z.subscheme i ≅ Z'.subscheme (indnumb_equiv i)
  subscheme_iso_over : ∀ i, Scheme.Hom.IsOver (subscheme_iso i).hom X
  /-
  Z.clotop i       ≃ₜ      Z'.clotop (indnumb_equiv i)
     |                            |
  Z.subscheme i    ≅      Z'.subscheme (indnumb_equiv i)
  -/
  condset_eq : ∀ (i : Z.indnumb) (x : Z.clotop i),
      Z'.condset (indnumb_equiv i) (clotop_homeomorph i x) =
      (subscheme_iso i).hom.base (Z.condset i x)

variable (X) in
def rel : PreClos X → PreClos X → Prop := fun Z Z' => Nonempty (relStructure Z Z')


variable (X) in
def relSetoid : Setoid (PreClos X) where
  r := rel X
  iseqv :=
    { refl := sorry
      symm := sorry
      trans := sorry }

-- lemma rel_trans :

-- lemma rel_sym

-- lemma rel_refl

variable (X) in
def Clos := Quotient (relSetoid X)

variable (X)
structure PrePri extends PreClos X where
  [prin : ∀ i γ, ideal i γ |>.IsPrincipal]

attribute [instance] PrePri.prin

structure PreCars extends PrePri X where
  nonzerodiv : ∀ i γ, Submodule.IsPrincipal.generator (ideal i γ) ∈ nonZeroDivisors (cov.obj γ)

def Pri := {x : Clos X | ∃ (y : PrePri X), Quotient.mk'' y.toPreClos = x}

def Cars := {x : Pri X | ∃ (y : PreCars X), Quotient.mk'' y.toPreClos = x.val}



def pull_back_PreClos(Z: PreClos X) (X': Scheme) (f: X' ⟶  X): PreClos X'  where
  indnumb := Z.indnumb
  fin_indnumb := by sorry
  clotop := (i : indnumb) ↦ f.pullback (Z.clotop i)
  subscheme := i ↦ f.pullback (Z.subscheme i)
  condset := by sorry
  over := by sorry
  cov := disjoint union of affine open cover for each open (not necessarily affine)  of f.pullback Z.cov
  ---  Z.cov = cup U_γ . pullback Z.cov = cup pullback U_γ.
  --- for all gamma let C_γ be an affine open  covering of  pullback U_γ
  ---- consider U C_γ : this is will work!
  ideal:=   indnumb → cov.index → pullback ideal A γ (not trivial  but can provide very elementary argument )
    --- an element in cov.index is a pair (γ, β)
    -- We have morphisms of schemes U_β --pullback U_γ -> U_γ
    --- by composition we get a morphism of schemes U_β → U_γ
    -- since U_β and U_γ are affine, we get morphism of rings Aγ →   Aβ by the antiequivalence
    -- between the categories Affschemes and CommRings
    -- We define ideal i γ β as the ideal image of ideal i γ under Aγ →   Aβ
  condiso:= --affine routine via pullback and
            -- AlgebraicGeometry.AffineScheme.equivCommRingCat
  condover := by sorry

lemma pul_back_lem (Z Z': PreClos X) (T : Scheme) (f: T ⟶ X) (Z rel Z') :
      (pull_back_PreClos X Z T f) rel (pull_back_PreClos X Z' T f) := by
        triviall
        sorry


def pull_back_Clos(Z: Clos X) (X': Scheme) (f: X' ⟶  X): Clos X' :=
    class of PreClos


structure conceptual_blowup (Z: Clos X) where
   scheme: Scheme
   over : Scheme.Over scheme X
   cond1:  (pull_back_Clos X Z scheme over)  belongs to Cars.scheme
   cond2: forr all T → X such that pull_back_Clos is Cartier there exists a unique X-mor T → X



def loc_to_PreClos (L: ι(finite) → ideal A) : PreClos Spec(A):=
   indcov: singleton
   indnumb: ι
   clotop: i ↦ underlying Spec(A/ L i)
   subscheme : i ↦ Spec(A/L i)
   condset: tauto
   mor: i ↦ Spec.hom A → AA/Li
   condcov X =x
   ideal: i ↦ * ↦mapsto L i
   condiso: tauto

def loc_to_Clos (L: ι(finite) → ideal A) : Clos Spec(A):= class of preclos


lemma ProjBlowup_UnivProp_unicity_affine :  (f: T → Spec(A))
     (cond: pullback on T loc_to_clos L is in Cars T)
     (φ φ': T →over Spec(A) BlMu L ): φ=φ'  := by
     Let x ∈ T.
     Reduce to local neighborhood
     put y=φx
     put y'=φ'x
     obtain P ∈ Mu L such that y ∈ Mu P
     obtain p' ∈ Mu L such that y ∈ Mu P'
     Let U=Spec(B) be an affine neighborhood of x in φ^-1 (Po P) ∩ φ'^-1 (Po P').
     consider the restrictions of φ and φ' to U
     Phi factors through Po P, Phi' factors through Po P'
     apply lemma 2
     apply univ prop of dilatations
     sorry

lemma ProjBlowup_UnivProp_existence_affine (f: T → Spec(A))
     (cond: pullback on T loc_to_clos L is in Cars T) : ∃  T →over Spec(A) BlMu L := by
        produce locally some map using dilatation
        glue them using Glue and ProjBlowup_UnivProp_unicity_affine
        sorry

lemma ProjBlowup_UnivProp_affine (f: T → Spec(A))
     (cond: pullback on T loc_to_clos L is in Cars T) :∃!  T →over Spec(A) BlMu L  by
       ProjBlowup_UnivProp_unicity_affine + ProjBlowup_UnivProp_existence_affine
       sorry

lemma dilatation_ring_flat_base_change (χ : A →+* B) (F: Multicenter A):
 χ ∈ RingHom.Flat  : ∃! A[F]⊗[A] B ≅ₐ[B] B[image_mult F] := by
   χ flat and nonzerodiv_image implies that  𝐚^ν is a nonzerodivisor in A[F]⊗[A] B
   cond on ideals is ok
   apply univ property to get a unique B- morphism  <-
   universal property of tensor product, exists ->
   check that both compositions are identity
  sorry

lemma flat_module_localization_at_prime_iff (M: Module.A):
 (M =0) ↔ (∀ q : maxideal.A : localization M A\ q =0 ):=
  → is trivial
  intro M
  assume let x ∈ M let Nx = submodule of M generated by x
  let I=Submodule.annihilator Nx, this is an ideal of A
  ∀ q in maxideal.A, exists f ∈ A \ q such that f∈ I -- because x=0 in the localization
  ∀ q in maxideal.A, I is not included in q
  applying Ideal.exists_le_maximal we get I=A
  so 1.x=0
  so M=0
  sorry

lemma open_implies_flat_ring (χ : A →+* B):
 (B.Spec → A.Spec is open_immerison )→ (χ : A →+* B is flat_ring_map):=
   intro χ
   AlgebraicGeometry.isOpenImmersion_iff_stalk
   and AlgebraicGeometry.IsAffineOpen.isLocalization_stalk implies
   that for all q ⊆ B prime ideals,
   IsLocalization.AtPrime f^-1(q) A → IsLocalization.AtPrime b B
   is an isomorphism
  sorry



lemma base_change_dil_open [Algebra A B]
   (i:Spec(B) → Spec(A) is Open immersion)
   (F: multicenter A) :
   ∃! (Spec(A[F]))×[Spec(A)](Spec(B))≅ Spec(B[image_mult (B:=B) F]) over Spec(B):= by
     exact open_implies_flat_ring  and dilatation_ring_flat_base_change
      sorry

lemma base_change_Bl_open [Algebra A B]
   (i:Spec(B) → Spec(A) is Open immersion)
   (L: ι → ideal A) :
   ∃! (Bl (L))×[Spec(A)](Spec(B))≅ Bl (im L) over Spec(B):=  by
     byy univ prop exists unique φ →
     exists θ <- by fiber product
     φ ∘ θ = id by univ prop
     so θ is injective
     to prove that θ is surjective enough to do it locally on target
     we chose a potion and apply base_change_dil_open
     sorry


def ideal_loc (Z: Clos X) (γ : Z.indcov) : indnumb → ideal A γ :=
   fun i ↦ ideal i γ

def Proj_loc  (Z: Clos X) (γ : Z.indcov) := Bl (ideal_loc Z γ)

def open_pair (Z: Clos X) (γ δ : Z.indcov) := Spec(A_γ) ∩ Spec(A_δ)

def Proj_loc_pair (Z: Clos X) (γ δ : Z.indcov) :=
    inverse image of open_pair in Bl (ideal_loc Z γ)

def Proj_loc_pair_open (Z: Clos X) (γ δ : Z.indcov) (U: open affine of open_pair γ δ) :
   ∃! (inverse image of U inn Proj_loc_pair Z γ δ)  →
   (inverse image of U inn Proj_loc_pair Proj_loc_pair Z δ γ) over U :=
   because it is an iso byy base_change_Bl_open


def Proj_loc_pair_lemm (Z: Clos X) (γ δ : Z.indcov) :
  ∃!   Proj_loc_pair Z γ δ →  Proj_loc_pair Z δ γ such that forr all U, restriction
   to U is given byy Proj_loc_pair_open := by
   because it is an iso byy base_change_Bl_open
   sorry


lemma Proj_loc_pair_iso (Z: Clos X) (γ δ : Z.indcov) :Proj_loc_pair_lemm is Iso :=
   this is local

def BlGlob  (Z: Clos X) :=  Scheme.GlueData where
  J := Clos.indcov
  U γ := Proj_loc γ
  V pair := Proj_loc pair.1 pair.2
  f γ δ := Proj_loc_pair_iso γ δ
  f_id i :=
  f_open i j :=
  t i j :=
  t_id i :=
  t' i j k :=
  t_fac i j k :=
  cocycle i j k :=


lemma ProjBlowup_UnivProp_unicity : (Z: Clos X) (f: T → X)
     (cond: pullback on T oof Z is in Cars T)
     (φ φ': T →over X BlGlob Y): φ=φ'  := by
       use locall
       sorry

lemma ProjBlowup_UnivProp_existence (Z: Clos X) (f: T → X)
     (cond: pullback on T oof Z is in Cars T) : ∃  T →over X BlGlob Y := by
        glue local map
        sorry

lemma ProjBlowup_UnivProp (Z: Clos X) (f: T → X)
     (cond: pullback on T oof Z is in Cars T) : ∃!  T →over X BlGlob Y by
       ProjBlowup_UnivProp_unicity + ProjBlowup_UnivProp_existence
       sorry


-- set_option maxHeartbeats 1000000 in
