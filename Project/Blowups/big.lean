import Project.Dilatation.Multicenter
import Mathlib.Data.Sum.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
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
import Mathlib.AlgebraicGeometry.PullbackCarrier

import Mathlib.RingTheory.RingHom.Flat



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
def clo_mu_mor (P: Mu L) : A[P.multicenter] →ₐ[A] (clo_mu L P).Potion :=
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

open CategoryTheory

instance BlMuOverSpec : Scheme.Over (BlMu L) (Spec <| CommRingCat.of A) where
  hom := (GoodPotionIngredient.over (ℱ := map_index L)) ≫
    Spec.map (CommRingCat.ofHom <| ReesAlgebra.degreeZeroIso' L)


instance BlMuOverSpec' (A : CommRingCat) (L : ι → Ideal A) :
    Scheme.Over (BlMu L) (Spec A) :=
  BlMuOverSpec L

lemma BlMu_over_Spec :
    BlMu L ↘ (Spec (CommRingCat.of A)) =
    (GoodPotionIngredient.over (ℱ := map_index L)) ≫
    Spec.map (CommRingCat.ofHom <| ReesAlgebra.degreeZeroIso' L) := rfl

lemma BlMu_over_Spec' (A : CommRingCat) (L : ι → Ideal A) :
    BlMu L ↘ (Spec A) =
    (GoodPotionIngredient.over (ℱ := map_index L)) ≫
    Spec.map (CommRingCat.ofHom <| ReesAlgebra.degreeZeroIso' L) := rfl


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

lemma lemm_dila_double_union  [Algebra A B] (P P': Mu L) (c : ι →  nonZeroDivisors B) (i : ι)
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
  -- (clotop : indnumb → Closeds X)
  (subscheme: indnumb → Scheme)
  -- (condset : ∀ i : indnumb, clotop i ≃ₜ (subscheme i)) -- maybe unnecessary?
  [over : ∀ (i : indnumb), Scheme.Over (subscheme i) X]
  -- eq_cond (i j : indnumb) (eq : i = j) :
  --   Scheme.Hom.IsOver (eqToHom (by rw [eq]) : subscheme i ⟶ subscheme j) X
  cov : Scheme.AffineCover.{u, u} (P := @IsOpenImmersion) X
  ideal: ∀ (_ : indnumb) (γ : cov.J), Ideal (cov.obj γ)
  condiso : ∀ (i : indnumb) (γ : cov.J),
    Spec (CommRingCat.of (cov.obj γ ⧸ ideal i γ)) ≅
    pullback (f := subscheme i ↘ X) (g := cov.map γ)
  condover : ∀ (i : indnumb) (γ : cov.J),
    Scheme.Hom.IsOver (condiso i γ).hom
      (Spec (CommRingCat.of (cov.obj γ)))

attribute [instance] PreClos.over
attribute [instance] PreClos.fin_indnumb

lemma PreClos.index_eq_triangle {X : Scheme} (Z : PreClos X) (i j : Z.indnumb) (eq : i = j) :
    Scheme.Hom.IsOver (eqToHom (by rw [eq]) : Z.subscheme i ⟶ Z.subscheme j) X := by
  subst eq
  simp

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
  -- clotop_homeomorph : ∀ i, Z.clotop i ≃ₜ Z'.clotop (indnumb_equiv i)
  subscheme_iso : ∀ i, Z.subscheme i ≅ Z'.subscheme (indnumb_equiv i)
  subscheme_iso_over : ∀ i, Scheme.Hom.IsOver (subscheme_iso i).hom X
  /-
  Z.clotop i       ≃ₜ      Z'.clotop (indnumb_equiv i)
     |                            |
  Z.subscheme i    ≅      Z'.subscheme (indnumb_equiv i)
  -/
  -- condset_eq : ∀ (i : Z.indnumb) (x : Z.clotop i),
  --     Z'.condset (indnumb_equiv i) (clotop_homeomorph i x) =
  --     (subscheme_iso i).hom.base (Z.condset i x)

@[refl]
def relStructure.refl {X : Scheme} (Z : PreClos X) : relStructure Z Z where
  indnumb_equiv := Equiv.refl _
  subscheme_iso _ := Iso.refl _
  subscheme_iso_over _ := by simp [Equiv.refl_apply, Scheme.Hom.isOver_iff]


@[symm]
def relStructure.symm {X : Scheme} {Z Z' : PreClos X} (R : relStructure Z Z') : relStructure Z' Z where
  indnumb_equiv := R.indnumb_equiv.symm
  subscheme_iso i := eqToIso (by simp) ≪≫ (R.subscheme_iso (R.indnumb_equiv.symm i)).symm
  subscheme_iso_over i := by
    have := R.subscheme_iso_over (R.indnumb_equiv.symm i)
    simp only [Scheme.Hom.isOver_iff] at this
    simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Scheme.Hom.isOver_iff, Category.assoc]
    rw [← this]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Scheme.Hom.isOver_iff]
    apply PreClos.index_eq_triangle
    simp


variable (X) in
def rel : PreClos X → PreClos X → Prop := fun Z Z' => Nonempty (relStructure Z Z')


variable (X) in
instance relSetoid : Setoid (PreClos X) where
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

structure IsPreCars (Z : PreClos X) : Prop where
  prin : ∀ i γ, Z.ideal i γ |>.IsPrincipal
  nonzerodiv : ∀ i γ, Submodule.IsPrincipal.generator (Z.ideal i γ) ∈ nonZeroDivisors (Z.cov.obj γ)



def Pri : Set (Clos X) := {x : Clos X | ∃ (y : PrePri X), Quotient.mk'' y.toPreClos = x}

def Cars : Set (Pri X) := {x : Pri X | ∃ (y : PreCars X), Quotient.mk'' y.toPreClos = x.val}

def CarsAsSubsetOfClos : Set (Clos X) :=
  {x : Clos X | ∃ y : Pri X, y ∈ Cars X ∧ x = y }

def pull_loc_cov (X: Scheme.{u}) (Z: PreClos.{u} X) (X': Scheme.{u}) (g : X' ⟶  X) (γ : Z.cov.J ) :=
    Scheme.affineOpenCover (pullback g (Z.cov.map γ))

@[simps]
def  pull_cov (X: Scheme.{u}) (Z : PreClos.{u} X) (X' : Scheme.{u}) (g : X' ⟶  X) :
            Scheme.AffineCover (P := @IsOpenImmersion) X' where
    J := (γ : Z.cov.J) × (pull_loc_cov X Z X' g γ).J
    obj p := (pull_loc_cov X Z X' g p.1).obj p.2
    map p := (pull_loc_cov X Z X' g p.1).map p.2 ≫ (pullback.fst g (Z.cov.map p.1))
    f (x : X') := ⟨Z.cov.f (g.base x), by
      have h1 : x ∈ g.base ⁻¹' Set.range (Z.cov.map (Z.cov.f <| g.base x)).base :=
        Z.cov.covers (g.base x)
      rw [← Scheme.Pullback.range_fst (f := g) (g := Z.cov.map (Z.cov.f <| g.base x))] at h1
      exact (pull_loc_cov X Z X' g (Z.cov.f <| g.base x)).f <| h1.choose⟩
    covers (x : X') := by
      dsimp
      simp only [eq_mp_eq_cast, Scheme.comp_coeBase, TopCat.coe_comp, Set.mem_range,
        Function.comp_apply]
      have h1 : x ∈ g.base ⁻¹' Set.range (Z.cov.map (Z.cov.f <| g.base x)).base :=
        Z.cov.covers (g.base x)
      rw [← Scheme.Pullback.range_fst (f := g) (g := Z.cov.map (Z.cov.f <| g.base x))] at h1
      obtain ⟨y, hy⟩ := (pull_loc_cov X Z X' g (Z.cov.f <| g.base x)).covers h1.choose
      use y
      rw [hy]
      exact h1.choose_spec
    map_prop j :=  IsOpenImmersion.comp ((pull_loc_cov X Z X' g j.fst).map j.snd)
          (pullback.fst g (Z.cov.map j.fst))

def  pull_mor_ring (X: Scheme)  (Z : PreClos X) (X' : Scheme) (f: X' ⟶  X)
      (γβ : (pull_cov X Z X' f).J) :
    Z.cov.obj γβ.1 ⟶ (pull_loc_cov X Z X' f γβ.1).obj γβ.2 := by
  let F := (pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.snd _ _
  let A : AffineSchemeᵒᵖ :=
    Opposite.op ⟨Spec ((pull_loc_cov X Z X' f γβ.fst).obj γβ.snd),
      ⟨Opposite.op <| (pull_loc_cov X Z X' f γβ.fst).obj γβ.snd, ⟨Iso.refl _⟩⟩⟩
  let B : AffineSchemeᵒᵖ :=
    Opposite.op ⟨Spec (Z.cov.obj γβ.fst), ⟨Opposite.op (Z.cov.obj γβ.fst), ⟨Iso.refl _⟩⟩⟩
  let F' : B ⟶ A := Quiver.Hom.op F
  exact (Scheme.ΓSpecIso _).inv ≫ (AffineScheme.Γ.map F') ≫ (Scheme.ΓSpecIso _).hom

  -- have := (Scheme.ΓSpecIso (Spec ((pull_loc_cov X Z X' f γβ.fst).obj γβ.snd))).inv
  -- U_β -> X' ×_{X} U_γ -> U_γ
    --- an element in cov.index is a pair (γ, β)
    -- We have morphisms of schemes U_β --pullback U_γ -> U_γ
    --- by composition we get a morphism of schemes U_β → U_γ
    -- since U_β and U_γ are affine, we get morphism of rings Aγ →   Aβ by the antiequivalence
    -- between the categories Affschemes and CommRings


def pull_ideal  (X:Scheme)  (Z: PreClos X) (X': Scheme) (f: X' ⟶  X)
  (γβ : (pull_cov X Z X' f).J) (i: Z.indnumb) :
  Ideal (CommRingCat.of ((pull_loc_cov X Z X' f γβ.1).obj γβ.2)) :=
  Ideal.map (pull_mor_ring X Z X' f γβ).hom (Z.ideal i γβ.1)
    -- We define ideal i γ β as the ideal image of ideal i γ under Aγ →   Aβ


open TensorProduct
-- ---a lemma (similar to TensorProduct.tensorQuotEquivQuotSMul )
-- -- I do not add a lot of details as it is maybe already in Mathlib
-- def lemma_map (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I: Ideal A) :
--     B →ₐ[A] (A ⧸ I) ⊗[A] B :=
--   Algebra.TensorProduct.includeRight


-- lemma lemma_surj (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
--     Function.Surjective <| lemma_map A B I := by
--   intro x
--   induction x using TensorProduct.induction_on with
--   | zero => exact ⟨0, by simp⟩
--   | tmul a b =>
--     induction a using Quotient.inductionOn with | h a =>
--     refine ⟨a • b, ?_⟩
--     simp only [lemma_map, map_smul, Algebra.TensorProduct.includeRight_apply, smul_tmul']
--     rw [Algebra.smul_def, mul_one]
--     rfl
--   | add x y hx hy =>
--     obtain ⟨x, rfl⟩ := hx
--     obtain ⟨y, rfl⟩ := hy
--     exact ⟨x + y, by simp⟩

-- -- TODO: update mathlib and finish this
-- lemma lemma_kernel (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
--     RingHom.ker (lemma_map A B I) = Ideal.map (algebraMap A B) I := by
--   refine le_antisymm ?_ ?_
--   · intro b hb
--     simp only [lemma_map, RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply] at hb
--     -- have := Algebra.TensorProduct.quotIdealMapEquivTensorQuot
--     sorry
--   · rw [Ideal.map_le_iff_le_comap]
--     intro a ha
--     simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
--       Algebra.TensorProduct.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
--     rw [show Ideal.Quotient.mk I a = 0 by rwa [Ideal.Quotient.eq_zero_iff_mem], zero_tmul]

def lemma_iso (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
  (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A] ((A ⧸ I)⊗[A] B) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I |>.restrictScalars A).trans <|
    Algebra.TensorProduct.comm _ _ _


def pullback_PreClos (X': Scheme) (f: X' ⟶  X) (Z: PreClos X)  : PreClos X'  where
  indnumb := Z.indnumb
  fin_indnumb := Z.fin_indnumb
  -- clotop i := ⟨f.base ⁻¹' (Z.clotop i), IsClosed.preimage f.base.2 (Z.clotop i).2⟩
  subscheme i := pullback (Z.subscheme i ↘ X) f
  -- condset i := by
  --   have := Z.condset i
  --   sorry
  over i := ⟨pullback.snd _ _⟩
  cov := pull_cov X Z X' f
  ideal i γβ :=  pull_ideal X Z X' f γβ i
  condiso i γβ := show _ ≅ pullback (pullback.snd (Z.subscheme i ↘ X) f)
    ((pull_loc_cov X Z X' f γβ.1).map γβ.2 ≫ pullback.fst f (Z.cov.map γβ.1)) by
    have eq1 :
      pullback.snd (Z.subscheme i ↘ X) (Z.cov.map γβ.fst) =
      (Z.condiso i γβ.fst).inv ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal i γβ.fst))) := by
      rw [eq_comm, Iso.inv_comp_eq, eq_comm]
      simpa only [Scheme.Hom.isOver_iff] using Z.condover i γβ.1
    /-
          X'
          |
    Zᵢ -> X

    -/
    -- have := ((pull_loc_cov X Z X' f γ)).map β
    -- have := AlgebraicGeometry.pullbackSpecIso
    sorry
    --affine routine via pullback and
    -- AlgebraicGeometry.AffineScheme.equivCommRingCat
            -- pull_lemm_cond_iso
            -- hand note
  condover := by
    rintro i ⟨γ, β⟩



    -- simp?
    sorry

def pullback_lem (Z Z': PreClos X) (T : Scheme) (f : T ⟶ X) (e : relStructure Z Z') :
       relStructure (pullback_PreClos X T f Z)  (pullback_PreClos X T f Z') where
  indnumb_equiv := e.indnumb_equiv
  subscheme_iso i := by sorry
  subscheme_iso_over i := sorry


variable {X}
def pullback_Clos {X': Scheme} (f: X' ⟶  X): Clos X → Clos X' :=
  Quotient.map (pullback_PreClos X X' f) <| fun Z Z' e => Nonempty.map (pullback_lem X Z Z' X' f) e

structure conceptual_blowup (Z : Clos X) where
  scheme : Scheme
  over : Scheme.Over scheme X
  in_cars : pullback_Clos (scheme ↘ X) Z ∈ CarsAsSubsetOfClos scheme
  φ (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    T ⟶ scheme
  φ_over (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    Scheme.Hom.IsOver (φ T in_preCars) X
  φ_uniq (T : Scheme) [T.Over X] (in_preCars : pullback_Clos (T ↘ X) Z  ∈ (CarsAsSubsetOfClos T)) :
    ∀ φ' : T ⟶ scheme, Scheme.Hom.IsOver φ' X → φ' = φ T in_preCars

def singletonCovering (A: CommRingCat) :
    Scheme.AffineCover IsOpenImmersion (Spec A) where
  J := PUnit
  obj _ := A
  map _ := 𝟙 _
  f _ := .unit
  covers := by simp
  map_prop _ := inferInstance

def loc_to_PreClos (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι] : PreClos (Spec A) where
  indnumb := ι
  fin_indnumb := inferInstance
  subscheme i := Spec (CommRingCat.of <| A ⧸ L i)
  over i :=
  { hom := Spec.map <| CommRingCat.ofHom <| Ideal.Quotient.mk (L i) }
  cov := singletonCovering A
  ideal i _ := L i
  condiso i _ :=
    ⟨Spec.map (CommRingCat.ofHom <| (Algebra.TensorProduct.rid A A (A ⧸ L i))),
      Spec.map (CommRingCat.ofHom <| (Algebra.TensorProduct.rid A A (A ⧸ L i)).symm), sorry,
      sorry⟩ ≪≫ (AlgebraicGeometry.pullbackSpecIso A (A ⧸ L i) A).symm ≪≫ pullback.congrHom rfl (Spec.map_id _)
  condover i _ := by
    sorry

def loc_to_Clos (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι] :
    Clos (Spec A) := Quotient.mk' <| loc_to_PreClos A L

lemma ProjBlowup_UnivProp_unicity_affine
  (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T)
  (φ φ' : T ⟶ BlMu L)
  (φ_over : Scheme.Hom.IsOver φ (Spec A))
  (φ'_over : Scheme.Hom.IsOver φ' (Spec A)) : φ = φ'  := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  -- refine TopCat.Sheaf.hom_ext T.presheaf (BlMu L).sheaf
  sorry
    --  Let x ∈ T.
    --  Reduce to local neighborhood
    --  put y=φx
    --  put y'=φ'x
    --  obtain P ∈ Mu L such that y ∈ Mu P
    --  obtain p' ∈ Mu L such that y ∈ Mu P'
    --  Let U=Spec(B) be an affine neighborhood of x in φ^-1 (Po P) ∩ φ'^-1 (Po P').
    --  consider the restrictions of φ and φ' to U
    --  Phi factors through Po P, Phi' factors through Po P'
    --  apply lemm_dila_double_union to get a unique morphism
    --  apply univ prop of dilatations

lemma ProjBlowup_UnivProp_existence_affine
  (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
  ∃ φ : T ⟶ BlMu L, Scheme.Hom.IsOver φ (Spec A) := sorry

lemma ProjBlowup_UnivProp_affine
  (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
  {T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃! φ :  T ⟶ BlMu L,  Scheme.Hom.IsOver φ (Spec A) := by
  obtain ⟨φ, hφ⟩ := ProjBlowup_UnivProp_existence_affine A L cond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact ProjBlowup_UnivProp_unicity_affine A L cond φ φ' hφ hφ' |>.symm

def ProjBlowup_φ (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    T ⟶ BlMu L :=
  Classical.choose (ProjBlowup_UnivProp_affine A L cond)

def ProjBlowup_φ_over (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    Scheme.Hom.IsOver (ProjBlowup_φ A L cond) (Spec A) :=
  Classical.choose_spec (ProjBlowup_UnivProp_affine A L cond) |>.1

def ProjBlowup_φ_uniq (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι]
    {T : Scheme} [T.Over (Spec A)]
    (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∀ φ' : T ⟶ BlMu L, Scheme.Hom.IsOver φ' (Spec A) → φ' = ProjBlowup_φ A L cond :=
  Classical.choose_spec (ProjBlowup_UnivProp_affine A L cond) |>.2


def  ProjBlowup_is_conceptual_blowups_affine (A: CommRingCat) (L : ι → Ideal A) [fin : Fintype ι] :
    conceptual_blowup (loc_to_Clos A L) where
  scheme := BlMu L
  over := inferInstance
  in_cars := sorry
  φ T _ cond := ProjBlowup_φ A L cond
  φ_over T _ cond := ProjBlowup_φ_over A L cond
  φ_uniq T _ cond φ' hφ' := ProjBlowup_φ_uniq A L cond φ' hφ'

--skip the following lemma at first
lemma dilatation_ring_flat_base_change [Algebra A B] (F: Multicenter A)
    (flat : RingHom.Flat (algebraMap A B)) : Subsingleton ((B ⊗[A] A[F]) ≃ₐ[B] B[image_mult F]) := by
  --  χ flat and nonzerodiv_image implies that  𝐚^ν is a nonzerodivisor in A[F]⊗[A] B
  --  cond on ideals is ok
  --  apply univ property to get a unique B- morphism  <-
  --  universal property of tensor product, exists ->
  --  check that both compositions are identity
  sorry

--skip this one also
-- lemma flat_module_localization_at_prime_iff  (M: Module.A):
--  (M =0) ↔ (∀ q : maxideal.A : localization M A\ q =0 ):=
--   → is trivial
--   intro M
--   assume let x ∈ M let Nx = submodule of M generated by x
--   let I=Submodule.annihilator Nx, this is an ideal of A
--   ∀ q in maxideal.A, exists f ∈ A \ q such that f∈ I -- because x=0 in the localization
--   ∀ q in maxideal.A, I is not included in q
--   applying Ideal.exists_le_maximal we get I=A
--   so 1.x=0
--   so M=0
--   sorry
--same, can be skiped at first
-- lemma open_implies_flat_ring (χ : A →+* B):
--  (B.Spec → A.Spec is open_immerison )→ (χ : A →+* B is flat_ring_map):=
--    intro χ
--    AlgebraicGeometry.isOpenImmersion_iff_stalk
--    and AlgebraicGeometry.IsAffineOpen.isLocalization_stalk implies
--    that for all q ⊆ B prime ideals,
--    IsLocalization.AtPrime f^-1(q) A → IsLocalization.AtPrime b B
--    is an isomorphism
--   sorry

instance (A B : CommRingCat) [Algebra A B] : Scheme.Over (Spec B) (Spec A) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap A B))

--the following is really what we need for the experiment in a first time
lemma base_change_dil_open (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)]
  --  (i:Spec(B) → Spec(A) is Open immersion)
    (F: Multicenter A) :
  ∃! (e : pullback ((Spec <| CommRingCat.of A[F]) ↘ Spec A) (Spec B ↘ Spec A) ≅ Spec B),
    Scheme.Hom.IsOver e.hom (Spec B) := by
    --  exact open_implies_flat_ring  and dilatation_ring_flat_base_change
      sorry

--the following is also  what we need for the experiment in a first time
lemma base_change_Bl_open (A B : CommRingCat) [Algebra A B]
    [IsOpenImmersion (Spec B ↘ Spec A)] (L: ι → Ideal A) :
  ∃! (e : pullback (BlMu L ↘ Spec A) (Spec B ↘ Spec A) ≅
      BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))),
    Scheme.Hom.IsOver e.hom (Spec B) := by sorry
  --    byy univ prop exists unique φ →
  --    exists θ <- by fiber product
  --    φ ∘ θ = id by univ prop
  --    so θ is injective
  --    to prove that θ is surjective enough to do it locally on target
  --    we chose a potion and apply base_change_dil_open


def ideal_loc (X: Scheme) (Z: PreClos X) (γ : Z.cov.J) : Z.indnumb → Ideal (Z.cov.obj γ) :=
  fun (i : Z.indnumb) => Z.ideal i γ


def Proj_loc  (X: Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme :=
  BlMu (A := Z.cov.obj γ) (ideal_loc X Z γ)

instance (X : Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  :
    Scheme.Over (Proj_loc X Z γ) (Spec (Z.cov.obj γ)) :=
  BlMuOverSpec (ideal_loc X Z γ)

instance (X : Scheme) (Z: PreClos X) (γ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  :
    Scheme.Over (Proj_loc X Z γ) X where
  hom := (Proj_loc X Z γ) ↘ (Spec (Z.cov.obj γ)) ≫
    Z.cov.map γ

def open_pair (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) : Scheme :=
  pullback (Z.cov.map γ) (Z.cov.map δ)

def open_pair_map (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) : open_pair X Z  γ δ  ⟶ X :=
  (pullback.fst  (Z.cov.map γ) (Z.cov.map δ)) ≫ (Z.cov.map γ)

lemma open_pair_map_equal (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) :
    open_pair_map X Z  γ δ  =
    (pullback.snd  (Z.cov.map γ) (Z.cov.map δ)) ≫ (Z.cov.map δ)  := by
  -- this is a pullback square, in partcular commutative
  sorry


lemma open_pair_map_is_open (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J) :
  IsOpenImmersion <| open_pair_map X Z γ δ := by
    --pullback.fst is an open immersion because open immersion is stable by base change by
    --- AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
    ---now it is enough to use that a composition of open immersion is openimmersion
          ---- AlgebraicGeometry.IsOpenImmersion.comp
    sorry

/-
      Z_β
      |
Z_γ -> X
-/
def Proj_loc_pair (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]  : Scheme :=
    pullback (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
      (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))
    --inverse image of open_pair in Bl (ideal_loc Z γ)


/-
     X
     |
U -> S
-/
abbrev restrictToOpen {X X' U S : Scheme} [X.Over S] [X'.Over S] (f : X ⟶ X') [Scheme.Hom.IsOver f S]
  (i : U ⟶ S) : (pullback (X ↘ S) i) ⟶ (pullback (X' ↘ S) i) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)

instance (X X' U S : Scheme) [X.Over S] [X'.Over S] (f : X ⟶ X') [Scheme.Hom.IsOver f S]
    (i : U ⟶ S) :
    Scheme.Hom.IsOver (restrictToOpen f i) U := by
  simp only [Scheme.Hom.isOver_iff]
  delta restrictToOpen
  change _ ≫ (pullback.snd _ _) = pullback.snd _ _
  simp

def Proj_loc_pair_mor (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]:
  Proj_loc_pair X Z γ δ ⟶ open_pair X Z γ δ  :=
    pullback.fst (pullback.fst (Z.cov.map γ) (Z.cov.map δ))
      (Proj_loc X Z γ ↘ Spec (Z.cov.obj γ))


instance (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  (Proj_loc_pair X Z γ δ).Over (open_pair X Z γ δ) where
  hom := Proj_loc_pair_mor _ _ _ _

instance (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  (Proj_loc_pair X Z δ γ).Over (open_pair X Z γ δ) where
  hom := Proj_loc_pair_mor _ _ _ _ ≫ (pullbackSymmetry _ _).hom


/-
U ×_X U'  U
          | open immersion
          v
X' ------> X
-/
lemma Proj_loc_pair_open (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  ∃! (φ : pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom)),
      Scheme.Hom.IsOver φ (Spec C) := by sorry
  --  because it is an iso byy base_change_Bl_open

def Proj_loc_pair_open_φ (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom) :=
  Classical.choose (Proj_loc_pair_open X Z γ δ C i)

lemma Proj_loc_pair_open_φ_isOver (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.Hom.IsOver (Proj_loc_pair_open_φ X Z γ δ C i) (Spec C) :=
  Classical.choose_spec (Proj_loc_pair_open X Z γ δ C i) |>.1

lemma Proj_loc_pair_open_φ_uniq (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i]
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    ∀ φ' : pullback i (Proj_loc_pair_mor X Z γ δ) ⟶
      pullback i (Proj_loc_pair_mor X Z δ γ ≫ (pullbackSymmetry _ _).hom),
      Scheme.Hom.IsOver φ' (Spec C) → φ' = Proj_loc_pair_open_φ X Z γ δ C i :=
  Classical.choose_spec (Proj_loc_pair_open X Z γ δ C i) |>.2


def Proj_loc_pair_lemm (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]:
  ∃! (f : (Proj_loc_pair X Z γ δ) ⟶  (Proj_loc_pair X Z δ γ)),

  (∃ (pf : Scheme.Hom.IsOver f (open_pair X Z γ δ)),
    ∀ (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i],
      restrictToOpen f i =
      (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
      (pullbackSymmetry _ _).hom) := sorry
  --   restriction of f
  --  to U is given byy Proj_loc_pair_open X Z γ δ U := by
  --   because it is an iso byy base_change_Bl_open
    -- sorry

def Proj_loc_pair_swap (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    (Proj_loc_pair X Z γ δ) ⟶  (Proj_loc_pair X Z δ γ) :=
  Classical.choose (Proj_loc_pair_lemm X Z γ δ)

instance Proj_loc_pair_swap_isOver (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
    Scheme.Hom.IsOver (Proj_loc_pair_swap X Z γ δ) (open_pair X Z γ δ) :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.1.1

lemma Proj_loc_pair_swap_restrict (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i] :
    restrictToOpen (Proj_loc_pair_swap X Z γ δ) i =
    (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
    (pullbackSymmetry _ _).hom :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.1.2 C i

lemma Proj_loc_pair_swap_uniq (X: Scheme) (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
  (f : Proj_loc_pair X Z γ δ ⟶ Proj_loc_pair X Z δ γ)
  (is_over : Scheme.Hom.IsOver f (open_pair X Z γ δ))
  (affine : ∀ (C : CommRingCat) (i : Spec C ⟶ open_pair X Z γ δ) [IsOpenImmersion i],
    restrictToOpen f i =
    (pullbackSymmetry _ _).hom ≫ Proj_loc_pair_open_φ X Z γ δ C i ≫
    (pullbackSymmetry _ _).hom) :
    f = Proj_loc_pair_swap X Z γ δ :=
  Classical.choose_spec (Proj_loc_pair_lemm X Z γ δ) |>.2 f ⟨is_over, affine⟩

lemma Proj_loc_pair_iso (X:Scheme)  (Z: PreClos X) (γ δ : Z.cov.J)
  [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  IsIso (Proj_loc_pair_swap X Z γ δ) := by sorry
  --  this is local

def PreBlGlob  (Z: PreClos X) [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme.GlueData where
  J := Z.cov.J
  U γ := Proj_loc X Z γ
  V pair := Proj_loc_pair X Z pair.1 pair.2
  f γ δ := pullback.snd _ _
  f_mono γ δ := inferInstance
  f_hasPullback := inferInstance
  f_id i := by infer_instance
  t γ δ := Proj_loc_pair_swap X Z γ δ
  t_id i := by
    dsimp
    symm
    apply Proj_loc_pair_swap_uniq
    · sorry
    · sorry
  t' i j k := sorry
  t_fac := sorry
  cocycle := sorry
  f_open := inferInstance

abbrev BlGlob (Z: PreClos X) [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] : Scheme :=
  Scheme.GlueData.glued (PreBlGlob Z)

instance (Z: PreClos X) [DecidableEq Z.indnumb]
  [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))] :
  Scheme.Over (BlGlob Z) X where
  hom := Multicoequalizer.desc _ _
    (fun γ : Z.cov.J => Proj_loc X Z γ ↘ X) <| by
    rintro ⟨γ, δ⟩
    simp only [MultispanShape.prod_L, GlueData.diagram_left, MultispanShape.prod_fst,
      GlueData.diagram_right,
      MultispanShape.prod_snd] at γ ⊢
    change pullback.snd _ _ ≫ _ = (Proj_loc_pair_swap X Z γ δ ≫ pullback.snd _ _) ≫ _
    simp only [Category.assoc]
    sorry



/-
{T : Scheme} [T.Over (Spec A)]
  (cond : pullback_Clos (T ↘ Spec A) (loc_to_Clos A L) ∈  CarsAsSubsetOfClos T) :
    ∃! φ :  T ⟶ BlMu L,  Scheme.Hom.IsOver φ (Spec A) := by
-/
lemma PreProjBlowup_UnivProp_unicity (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z)
    (φ φ' : T ⟶ BlGlob Z)
    (φ_over : Scheme.Hom.IsOver φ X)
    (φ'_over : Scheme.Hom.IsOver φ' X)
    : φ = φ'  := by sorry
      --  use locall
      --  sorry

lemma PreProjBlowup_UnivProp_existence
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z) :
    ∃  φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X := by
        -- glue local map
        sorry

lemma PreProjBlowup_UnivProp
    (Z: PreClos X)
    [DecidableEq Z.indnumb]
    [(i : Z.indnumb →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt Z.indnumb))]
    {T : Scheme} [T.Over X]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z) :
    ∃! φ : T ⟶ BlGlob Z, Scheme.Hom.IsOver φ X := by
  obtain ⟨φ, hφ⟩ := PreProjBlowup_UnivProp_existence Z cond
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact PreProjBlowup_UnivProp_unicity Z cond φ φ' hφ hφ' |>.symm

lemma PreProjBlowup_rel (Z' Z'' : PreClos X) (eq: Quotient.mk' Z' = Quotient.mk' Z'')
    {T : Scheme} [T.Over X]
    [DecidableEq Z'.indnumb]
    [DecidableEq Z''.indnumb]
    [(i : Z'.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z'.indnumb))]
    [(i : Z''.indnumb →₀ ℤ) → Decidable (i ∈ Set.range ⇑(ρNatToInt Z''.indnumb))]
    (cond:  IsPreCars _ <| pullback_PreClos _ _ (T ↘ X) Z') :
  ∃! (e : BlGlob Z' ≅ BlGlob Z''), Scheme.Hom.IsOver e.hom X := by
      --  PreProjBlowup_UnivProp
      sorry


abbrev GlobalBlowup (Z: Clos X) : Scheme := by classical exact BlGlob Z.out
