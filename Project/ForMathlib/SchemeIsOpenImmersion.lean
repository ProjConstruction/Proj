import Mathlib.AlgebraicGeometry.OpenImmersion

namespace AlgebraicGeometry.IsOpenImmersion

open CategoryTheory

variable {X Z : Scheme} (f : X ⟶ Z) [H : IsOpenImmersion f]

@[reassoc (attr := simp)]
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Z.ofRestrict _ = f := by
  apply_fun Scheme.Hom.toLRSHom
  · exact LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.1
  · rintro ⟨f⟩ ⟨g⟩ h
    simp
    exact h

end AlgebraicGeometry.IsOpenImmersion

namespace AlgebraicGeometry.Scheme

open CategoryTheory TopologicalSpace

lemma Hom.stalkMap_comp  {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    Scheme.Hom.stalkMap (f ≫ g) x = Scheme.Hom.stalkMap g (f.base x) ≫ Scheme.Hom.stalkMap f x := by
  apply LocallyRingedSpace.stalkMap_comp

lemma Hom.ext_iff {X Y : Scheme} (f g : X ⟶ Y) : f = g ↔
  (∃ (h_base : f.base = g.base),
    (∀ U, f.app U ≫ X.presheaf.map
      (eqToHom congr((Opens.map $h_base.symm).obj U)).op = g.app U)) := by
  constructor
  · rintro rfl; aesop
  · rintro ⟨h_base, h_app⟩
    ext : 1 <;> aesop

end AlgebraicGeometry.Scheme
