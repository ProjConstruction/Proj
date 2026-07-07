import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.Algebra.Category.Ring.Constructions

open AlgebraicGeometry CategoryTheory

universe u

instance (X Y : TopCat) [ie : IsEmpty X] : Unique (X ⟶ Y) where
  default := TopCat.ofHom
    { toFun i := False.elim <| ie.elim i
      continuous_toFun := by continuity }
  uniq := by
    intro f
    ext x
    exact False.elim <| ie.elim x

open ZeroObject Zero

-- def emptyScheme (X : Scheme.{u}) [ie : IsEmpty X] : X ≅ Spec (CommRingCat.of <| PUnit.{u + 1}) where
--   hom := _
--   inv := _
--   hom_inv_id := _
--   inv_hom_id := _

instance (X : Scheme) [ie : IsEmpty X] : Limits.IsInitial X := sorry

instance (X Y : Scheme) [ie : IsEmpty X] : Unique (X ⟶ Y) where
  default := _
  uniq := _
