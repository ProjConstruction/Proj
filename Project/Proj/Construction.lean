import Project.Potions.GoodPotionIngredient
import Mathlib.Util.CountHeartbeats

suppress_compilation

universe u
variable {ι R₀ A : Type u}
variable [AddCommMonoid ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

open AlgebraicGeometry CategoryTheory HomogeneousSubmonoid TensorProduct

namespace GoodPotionIngredient

open Limits in
@[simps]
def glueData {τ : Type u} (ℱ : τ → GoodPotionIngredient 𝒜) : Scheme.GlueData where
  J := τ
  U i := Spec <| CommRingCat.of <| (ℱ i).Potion
  V pair := Spec <| CommRingCat.of <| (ℱ pair.1 * ℱ pair.2).Potion
  f i j := Spec.map <| CommRingCat.ofHom <| (ℱ i).potionToMul (ℱ j).toHomogeneousSubmonoid
  f_id i := by
    dsimp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid]
    rw [show CommRingCat.ofHom ((ℱ i).potionToMul (ℱ i).toHomogeneousSubmonoid) =
      (ℱ i).potionToMulSelf.toCommRingCatIso.hom by rfl]
    infer_instance
  f_open i j := isOpenImmersion (ℱ i) (ℱ j)
  t i j := Spec.map <| CommRingCat.ofHom <|  potionEquiv (mul_comm ..) |>.toRingHom
  t_id i := by
    erw [← Scheme.Spec.map_id]
    simp
  t' i j k :=
      (AlgebraicGeometry.pullbackSpecIso _ _ _).hom ≫
      Spec.map (CommRingCat.ofHom <| t' (ℱ i) (ℱ j) (ℱ k)) ≫
      (AlgebraicGeometry.pullbackSpecIso _ _ _).inv
  t_fac i j k := by
    dsimp only
    simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, ← mul_potion_algebraMap_eq,
      Category.assoc, pullbackSpecIso_inv_snd, RingEquiv.toRingHom_eq_coe]
    rw [← Iso.eq_inv_comp]
    rw [pullbackSpecIso_inv_fst_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact t'_fac (ℱ i) (ℱ j) (ℱ k)
  cocycle i j k := by
    dsimp only
    simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, mul_potion_algebraMap_eq,
      RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    rw [← Category.assoc, Iso.comp_inv_eq_id]
    convert Category.comp_id _ using 2
    convert Spec.map_id (CommRingCat.of <| (ℱ i * ℱ j).Potion ⊗[(ℱ i).Potion] (ℱ i * ℱ k).Potion) using 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    convert CommRingCat.ofHom_id using 2
    ext x
    simpa using congr($(t'_cocycle (ℱ i) (ℱ j) (ℱ k)) x)

-- set_option maxHeartbeats 1000000 in
-- open Limits in
-- @[simps]
-- def glueData (ℱ : Set (GoodPotionIngredient 𝒜)) : Scheme.GlueData where
--   J := ℱ
--   U S := Spec <| CommRingCat.of S.1.Potion
--   V pair := Spec <| CommRingCat.of (pair.1.1 * pair.2.1).Potion
--   f S T := Spec.map <| CommRingCat.ofHom <| S.1.1.potionToMul T.1.1
--   f_id S := by
--     dsimp only
--     rw [show CommRingCat.ofHom (S.1.1.potionToMul S.1.1) =
--       S.1.potionToMulSelf.toCommRingCatIso.hom by rfl]
--     infer_instance
--   f_open := by
--     rintro (S T : ℱ)
--     exact isOpenImmersion S.1 T.1
--   t S T := Spec.map <| CommRingCat.ofHom <| (HomogeneousSubmonoid.potionEquiv <| by rw [mul_comm]).toRingHom
--   t_id S := by
--     erw [← Scheme.Spec.map_id]
--     simp
--   t' R S T :=
--     (AlgebraicGeometry.pullbackSpecIso _ _ _).hom ≫
--     Spec.map (CommRingCat.ofHom <| t' R.1 S.1 T.1) ≫
--     (AlgebraicGeometry.pullbackSpecIso _ _ _).inv
--   t_fac R S T := by
--     dsimp only
--     simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, ← mul_potion_algebraMap_eq,
--       Category.assoc, pullbackSpecIso_inv_snd, RingEquiv.toRingHom_eq_coe]
--     rw [← Iso.eq_inv_comp]
--     rw [pullbackSpecIso_inv_fst_assoc]
--     rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
--     congr 2
--     exact t'_fac R.1 S.1 T.1
--   cocycle R S T := by
--     dsimp only
--     simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, mul_potion_algebraMap_eq,
--       RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
--       Iso.inv_hom_id_assoc]
--     rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
--     rw [← Category.assoc, Iso.comp_inv_eq_id]
--     convert Category.comp_id _ using 2
--     convert Spec.map_id (CommRingCat.of <| (R.1 * S.1).Potion ⊗[R.1.Potion] (R.1 * T.1).Potion) using 2
--     rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
--     convert CommRingCat.ofHom_id using 2
--     ext x
--     simpa using congr($(t'_cocycle R.1 S.1 T.1) x)

def Proj {τ : Type u} (ℱ : τ → GoodPotionIngredient 𝒜) : Scheme := glueData ℱ |>.glued

end GoodPotionIngredient
