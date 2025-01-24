import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

variable {ιA ιB R A B : Type*}
variable [DecidableEq ιA] [AddCommGroup ιA]
variable [DecidableEq ιB] [AddCommGroup ιB]
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable (𝒜 : ιA → Submodule R A) (ℬ : ιB → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

namespace TensorProduct

open scoped DirectSum

noncomputable def gradingByProduct : ιA × ιB → Submodule R (A ⊗[R] B) := fun p ↦
  LinearMap.range (TensorProduct.map (𝒜 p.1).subtype (ℬ p.2).subtype)

scoped infix:min "⊗" => gradingByProduct

instance : SetLike.GradedMonoid (𝒜 ⊗ ℬ) where
  one_mem := ⟨1 ⊗ₜ 1, rfl⟩
  mul_mem := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    simp only [Prod.mk_add_mk]
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul, Submodule.zero_mem]
    | tmul a b =>
      -- simp only [map_tmul, Submodule.coe_subtype]
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, mul_zero, Submodule.zero_mem]
      | tmul a' b' =>
        simp only [map_tmul, Submodule.coe_subtype, Algebra.TensorProduct.tmul_mul_tmul]
        exact ⟨⟨a.1 * a'.1, SetLike.GradedMul.mul_mem a.2 a'.2⟩ ⊗ₜ
          ⟨b.1 * b'.1, SetLike.GradedMul.mul_mem b.2 b'.2⟩, rfl⟩
      | add y y' hy hy' =>
        simp only [map_tmul, Submodule.coe_subtype, map_add, mul_add]
        exact Submodule.add_mem _ hy hy'
    | add x x' hx hx' =>
      simp only [map_add, add_mul]
      exact Submodule.add_mem _ hx hx'

-- noncomputable def decompositionByProductAux : (A ⊗[R] B) →ₗ[R] (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) :=
-- map (DirectSum.decomposeLinearEquiv _ |>.toLinearMap)
--   (DirectSum.decomposeLinearEquiv _ |>.toLinearMap)

noncomputable def decompositionByProduct : (A ⊗[R] B) →ₗ[R] (⨁ (p : ιA × ιB), (𝒜 ⊗ ℬ) p) :=
TensorProduct.lift
  (DirectSum.toModule _ _ _ fun i ↦
    { toFun a := DirectSum.toModule _ _ _ fun j ↦
      { toFun b := DirectSum.lof R (ιA × ιB) (fun p => (𝒜 ⊗ ℬ) p) (i, j) ⟨a.1 ⊗ₜ b.1, ⟨a ⊗ₜ b, rfl⟩⟩
        map_add' := by
          intros
          simp only [Submodule.coe_add, ← map_add]
          congr 1
          ext
          simp only [tmul_add, Submodule.coe_add]
        map_smul' := by
          intros
          simp only [← map_smul]
          congr 1
          ext
          simp }
      map_add' := by
        rintro ⟨a, ha⟩ ⟨a', ha'⟩
        ext j ⟨b, hb⟩ ⟨i', j'⟩
        simp only [AddMemClass.mk_add_mk, LinearMap.coe_comp, Function.comp_apply,
          DirectSum.toModule_lof, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          DirectSum.add_apply, Submodule.coe_add]
        by_cases h : i = i' ∧ j = j'
        · rcases h with ⟨h₁, h₂⟩
          subst h₁
          subst h₂
          simp [add_tmul]

        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne,
          DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
        simp only [ZeroMemClass.coe_zero, add_zero]
        · aesop
        · aesop
        · aesop
      map_smul' := by
        rintro r ⟨a, ha⟩
        ext j ⟨b, hb⟩ ⟨i', j'⟩
        simp only [SetLike.mk_smul_mk, LinearMap.coe_comp, Function.comp_apply,
          DirectSum.toModule_lof, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply, SetLike.coe_eq_coe]
        rw [← map_smul]
        congr 1  }) ∘ₗ
  map (DirectSum.decomposeLinearEquiv 𝒜 |>.toLinearMap) (DirectSum.decomposeLinearEquiv ℬ |>.toLinearMap)

@[simp]
lemma decompositionByProduct_apply_tmul_homogeneous
      (a : A) (b : B) (i : ιA) (j : ιB) (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ j) :
    decompositionByProduct 𝒜 ℬ (a ⊗ₜ b) =
    DirectSum.lof R (ιA × ιB) (fun p => (𝒜 ⊗ ℬ) p) (i, j) ⟨_, ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, rfl⟩⟩ := by
  lift a to 𝒜 i
  · exact ha
  lift b to ℬ j
  · exact hb
  simp only [decompositionByProduct, LinearMap.coe_comp, Function.comp_apply, map_tmul,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe, lift.tmul,
    Subtype.coe_eta, Submodule.coe_subtype]
  erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
  rfl

noncomputable instance : DirectSum.Decomposition (𝒜 ⊗ ℬ) where
  decompose' := decompositionByProduct ..
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      apply DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_ a
      · simp
      · intro i a
        apply DirectSum.Decomposition.inductionOn ℬ ?_ ?_ ?_ b
        · simp
        · intro j b
          rw [decompositionByProduct_apply_tmul_homogeneous (ha := a.2) (hb := b.2)]
          simp only [Subtype.coe_eta, map_tmul, Submodule.coe_subtype]
          erw [DirectSum.coeAddMonoidHom_of]
        · intro b b' hb hb'
          simp [tmul_add, hb, hb']
      · intro a a' ha ha'
        simp [ha, ha', add_tmul]
    | add x y hx hy =>
      simp [hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | H_zero => simp
    | H_basic p x =>
      obtain ⟨i, j⟩ := p
      obtain ⟨_, ⟨x, rfl⟩⟩ := x
      simp only [DirectSum.coeAddMonoidHom_of]
      rw [← DirectSum.lof_eq_of R (ιA × ιB) (fun p => (𝒜 ⊗ ℬ) p)]
      induction x using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        ext ⟨m, n⟩
        simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero, DirectSum.coe_of_apply,
          Prod.mk.injEq, DirectSum.lof_eq_of]
        aesop
      | tmul a b =>
        simp only [map_tmul, Submodule.coe_subtype]
        rw [decompositionByProduct_apply_tmul_homogeneous (ha := a.2) (hb := b.2)]
        simp only [Subtype.coe_eta, map_tmul, Submodule.coe_subtype]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
        rw [← map_add]
        rfl
    | H_plus x y hx hy =>
      simp [hx, hy]

noncomputable instance : GradedAlgebra (𝒜 ⊗ ℬ) where

end TensorProduct
