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
