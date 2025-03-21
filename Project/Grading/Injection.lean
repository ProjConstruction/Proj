import Mathlib.RingTheory.GradedAlgebra.Basic

import Project.ForMathlib.ImageSplitting

suppress_compilation

variable {ι ι' R A : Type*}
variable [AddCommMonoid ι] [AddCommMonoid ι']
variable [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ι → Submodule R A)
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ρ : ι →+ ι') [inj : Fact <| Function.Injective ρ] [∀ i : ι', Decidable (i ∈ Set.range ρ)]

def gradingOfInjection : ι' → Submodule R A := fun i =>
  if mem : i ∈ Set.range ρ then 𝒜 (Set.rangeSplitting ρ ⟨i, mem⟩) else ⊥

variable [DecidableEq ι']

instance gradingOfInjection_isGradedMonoid : SetLike.GradedMonoid (gradingOfInjection 𝒜 ρ) where
  one_mem := by
    delta gradingOfInjection
    rw [dif_pos ⟨0, by simp⟩]
    convert SetLike.GradedOne.one_mem (A := 𝒜)
    swap
    · infer_instance
    swap
    · infer_instance
    apply inj.out
    rw [Set.apply_rangeSplitting ρ ⟨0, ⟨0, by simp⟩⟩]
    simp
  mul_mem := by
    intro i j a b ha hb
    delta gradingOfInjection at ha hb
    split_ifs at ha with ha'
    · rcases ha' with ⟨i, rfl⟩
      split_ifs at hb with hb'
      · rcases hb' with ⟨j, rfl⟩
        rw [Set.rangeSplitting_apply_coe _ inj.out] at ha
        rw [Set.rangeSplitting_apply_coe _ inj.out] at hb
        delta gradingOfInjection
        rw [dif_pos ⟨i + j, by simp⟩]
        simp_rw [← map_add]
        rw [Set.rangeSplitting_apply_coe _ inj.out]
        exact SetLike.mul_mem_graded (A := 𝒜) ha hb
      · simp only [Submodule.mem_bot] at hb
        subst hb
        simp
    · simp only [Submodule.mem_bot] at ha
      subst ha
      simp

open DirectSum

def decomposeOfInjectionAux : (⨁ i, 𝒜 i) →+ (⨁ i, gradingOfInjection 𝒜 ρ i) :=
  DirectSum.toAddMonoid fun i ↦
    { toFun x := DirectSum.of _ (ρ i) ⟨x, by
        simp only [gradingOfInjection, Set.mem_range, exists_apply_eq_apply, ↓reduceDIte]
        rw [Set.rangeSplitting_apply_coe _ inj.out]
        exact x.2⟩
      map_zero' := by
        simp only [ZeroMemClass.coe_zero]
        ext i
        simp [DirectSum.coe_of_apply]
      map_add' := by
        intros x y
        ext j
        -- simp only [AddMemClass.coe_add, add_apply]
        simp only [Submodule.coe_add, coe_of_apply, add_apply]
        split_ifs with h h'
        · rfl
        · rfl
        · simp }

instance gradingOfInjection_decomposition :
    DirectSum.Decomposition (gradingOfInjection 𝒜 ρ) where
  decompose' := decomposeOfInjectionAux 𝒜 ρ  ∘ decompose 𝒜
  left_inv := by
    classical
    intro x
    simp only [Function.comp_apply]
    conv_lhs => rw [← DirectSum.sum_support_decompose (ℳ := 𝒜) x]
    simp only [decomposeOfInjectionAux, decompose_sum, decompose_coe, map_sum, toAddMonoid_of,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeAddMonoidHom_of]
    rw [DirectSum.sum_support_decompose (ℳ := 𝒜) x]
  right_inv := by
    intro x
    induction x using DirectSum.induction_on with
    | H_zero => simp
    | @H_basic i x =>
      rcases x with ⟨x, hx⟩
      by_cases mem : i ∈ Set.range ρ
      · rcases mem with ⟨i, rfl⟩
        simp only [gradingOfInjection, Set.mem_range, exists_apply_eq_apply, ↓reduceDIte] at hx
        rw [Set.rangeSplitting_apply_coe _ inj.out] at hx
        simp only [coeAddMonoidHom_of, Function.comp_apply]
        rw [decompose_of_mem 𝒜 hx]
        simp only [decomposeOfInjectionAux, toAddMonoid_of, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      · simp only [gradingOfInjection, Set.mem_range, dif_neg mem, Submodule.mem_bot] at hx
        subst hx
        simp only [coeAddMonoidHom_of, Function.comp_apply, decompose_zero, map_zero]
        ext
        simp only [zero_apply, ZeroMemClass.coe_zero, coe_of_apply]
        split_ifs <;> rfl
    | H_plus x y hx hy =>
      simp only [Function.comp_apply, map_add, decompose_add] at hx hy ⊢
      rw [hx, hy]

instance gradingOfInjection_isGradedAlgebra : GradedAlgebra (gradingOfInjection 𝒜 ρ) where
  __ := gradingOfInjection_isGradedMonoid 𝒜 ρ
  __ := gradingOfInjection_decomposition 𝒜 ρ

@[simps]
def gradingOfInjection₀Iso : (gradingOfInjection 𝒜 ρ) 0 ≃+* 𝒜 0 where
  toFun a := ⟨a.1, by
    convert a.2
    delta gradingOfInjection
    rw [dif_pos ⟨0, by simp⟩]
    congr 1
    apply inj.out
    rw [Set.apply_rangeSplitting ρ ⟨0, ⟨0, by simp⟩⟩]
    simp⟩
  invFun a := ⟨a.1, by
    convert a.2
    delta gradingOfInjection
    rw [dif_pos ⟨0, by simp⟩]
    congr 1
    apply inj.out
    rw [Set.apply_rangeSplitting ρ ⟨0, ⟨0, by simp⟩⟩]
    simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable (ι) in
@[simps]
def ρNatToInt : (ι →₀ ℕ) →+ (ι →₀ ℤ) where
  toFun v := Finsupp.mapRange Int.ofNat rfl v
  map_zero' := by simp
  map_add' v w := by
    ext i
    simp

omit [AddCommMonoid ι] [DecidableEq ι] in
lemma ρNatToInt_inj : Function.Injective (ρNatToInt ι) := by
  intro v w h
  simp only [ρNatToInt_apply] at h
  ext i
  have := congr($h i)
  simp only [Finsupp.mapRange_apply, Int.ofNat_eq_coe, Nat.cast_inj] at this
  exact this

instance : Fact (Function.Injective (ρNatToInt ι)) := ⟨ρNatToInt_inj⟩
