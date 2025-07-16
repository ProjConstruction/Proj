import Project.Dilatation.ReesAlgebra
import Project.Dilatation.Multicenter
import Project.Proj.Over
import Project.Proj.OfLE

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

lemma clo_mu_mor_inj (P : Mu L) : Function.Injective (clo_mu_mor L P) := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  rintro x (hx : _ = _)
  show _ = Dilatation.mk _
  induction x using Dilatation.induction_on with | h x =>
  rcases x with ⟨v, l, h⟩
  simp only [clo_mu_mor, desc, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    descFun_mk] at hx
  rw [Dilatation.mk_eq_mk]

  have := congr((algebraMap A (clo_mu L P).Potion) (P.multicenter.elem ^ v) * $hx)
  simp only [P.multicenter.def_unique_elem_spec, mul_zero] at this
  rw [HomogeneousLocalization.ext_iff_val] at this
  simp only [HomogeneousLocalization.val_zero] at this
  erw [HomogeneousLocalization.val_mk] at this
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ReesAlgebra.degreeZeroIso'_apply,
    SetLike.GradeZero.coe_one] at this
  erw [← Localization.mk_zero 1, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at this
  simp only [OneMemClass.coe_one, one_mul, mul_zero, Subtype.exists,
    HomogeneousSubmonoid.mem_toSubmonoid_iff, exists_prop] at this
  obtain ⟨β, hβ, hβl⟩ := this
  obtain ⟨r, t, ht, hr, hβ⟩ := Submonoid.mem_closure_iff_exists_finset_subset |>.1 hβ
  choose i hi using ht

  use v + ∑ x in t.attach, Finsupp.single (i x.2) (r x.1)
  simp only [add_zero, familyPow_add, familyPow_sum, familyPow_single', pow_one, zero_mul]
  have hβ' := calc β
    _ = ∏ a ∈ t.attach, a.1 ^ r a.1 := by simp [hβ]
    _ = ∏ a ∈ t.attach, (ReesAlgebra.single L (Finsupp.single (P.Ψ (i a.2)) 1))
      ⟨P.multicenter.elem (i a.2), _⟩ ^ r a.1 := by
        refine Finset.prod_congr rfl fun a ha ↦ ?_
        rw [hi]
  simp only [ReesAlgebra.single_npow, ReesAlgebra.single_prod] at hβ'
  simp only [hβ', ReesAlgebra.single_mul, ReesAlgebra.single_eq_zero, Submodule.mk_eq_zero] at hβl
  simp only [mul_comm l]
  rw [mul_assoc, hβl, mul_zero]

omit [Fintype ι] in
lemma clo_mu_mor_surj (P : Mu L) : Function.Surjective (clo_mu_mor L P) := by
  intro x
  induction x using Quotient.inductionOn' with | h x =>
  rcases x with ⟨v, ⟨l, l_deg⟩, ⟨β, β_deg⟩, β_mem⟩

  obtain ⟨r, t, ht, hr, hβ⟩ := Submonoid.mem_closure_iff_exists_finset_subset |>.1 β_mem
  choose i hi using ht
  have hβ' := calc β
    _ = ∏ a ∈ t.attach, a.1 ^ r a.1 := by simp [hβ]
    _ = ∏ a ∈ t.attach, (ReesAlgebra.single L (Finsupp.single (P.Ψ (i a.2)) 1))
      ⟨P.multicenter.elem (i a.2), _⟩ ^ r a.1 := by
        refine Finset.prod_congr rfl fun a ha ↦ ?_
        rw [hi]
  simp only [ReesAlgebra.single_npow, ReesAlgebra.single_prod] at hβ'

  have : β ∈ ReesAlgebra.grading _ (∑ j ∈ t.attach, r j.1 • Finsupp.single (P.Ψ (i j.2)) 1) := by
    rw [hβ']
    apply ReesAlgebra.single_has_degree
  simp only [ReesAlgebra.intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply] at β_deg
  by_cases β_eq_zero : β = 0
  · subst β_eq_zero
    simp only [HomogeneousSubmonoid.mem_toSubmonoid_iff] at β_mem

    use 0
    simp only [map_zero]
    ext
    simp only [HomogeneousLocalization.val_zero, HomogeneousLocalization.val_mk]
    rw [← Localization.mk_zero 1]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use ⟨0, β_mem⟩
    simp
  split_ifs at β_deg with hv
  · rcases hv with ⟨v, rfl⟩
    simp only [HomogeneousSubmonoid.mem_toSubmonoid_iff] at β_mem
    rw [Set.rangeSplitting_apply_coe (inj := ρNatToInt_inj)] at β_deg
    have v_eq := DirectSum.degree_eq_of_mem_mem _ β_deg this β_eq_zero

    rw [ReesAlgebra.intGrading, gradingOfInjection, dif_pos ⟨v, rfl⟩, Set.rangeSplitting_apply_coe (inj := ρNatToInt_inj),
      ReesAlgebra.grading, LinearMap.mem_range] at l_deg
    obtain ⟨⟨l, hl⟩, rfl⟩ := l_deg
    refine ⟨Dilatation.mk ⟨∑ j ∈ t.attach, r j.1 • Finsupp.single (i j.2) 1, l, ?_⟩, ?_⟩
    -- obtain ⟨x, hx⟩ := l_deg
    · simp only [Finsupp.smul_single, smul_eq_mul, mul_one, familyPow_sum, familyPow_single',
      P.cond]
      rw [v_eq] at hl
      simpa [familyPow_sum] using hl
    · delta clo_mu_mor Multicenter.desc
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, descFun_mk, ρNatToInt_apply]
      apply def_unique_elem_unique
      ext
      simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk]
      change Localization.mk _ _ * Localization.mk _ _ = Localization.mk _ _
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ReesAlgebra.degreeZeroIso'_apply,
        SetLike.GradeZero.coe_one, Localization.mk_mul, Submonoid.mk_mul_mk, one_mul,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists,
        HomogeneousSubmonoid.mem_toSubmonoid_iff, exists_prop]
      refine ⟨1, one_mem _, ?_⟩
      simp only [one_mul]
      rw [hβ', ReesAlgebra.single_mul, ReesAlgebra.single_mul]
      simp only
      ext : 1
      simp only [ReesAlgebra.single_apply_val]
      ext w
      rw [DirectSum.coe_of_apply, DirectSum.coe_of_apply]
      simp only [v_eq, Finsupp.smul_single, smul_eq_mul, mul_one, zero_add, add_zero]
      split_ifs
      · simp [familyPow_sum]
      · rfl
  · simp only [Submodule.mem_bot] at β_deg
    subst β_deg
    simp only [HomogeneousSubmonoid.mem_toSubmonoid_iff] at β_mem

    use 0
    simp only [map_zero]
    ext
    simp only [HomogeneousLocalization.val_zero, HomogeneousLocalization.val_mk]
    rw [← Localization.mk_zero 1]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use ⟨0, β_mem⟩
    simp

def Mu_mor_iso (P: Mu L) :
    A[P.multicenter] ≃ₐ[A] (clo_mu L P).Potion :=
  AlgEquiv.ofBijective (clo_mu_mor ..) <| ⟨clo_mu_mor_inj L P, clo_mu_mor_surj L P⟩


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
        inj' := by
          intro P P' h
          rw [GoodPotionIngredient.ext_iff] at h
          change HomogeneousSubmonoid.closure _ = HomogeneousSubmonoid _ at h
          sorry }
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
