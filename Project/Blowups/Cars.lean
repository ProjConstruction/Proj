import Project.Dilatation.ReesAlgebra
import Project.Dilatation.Multicenter
import Project.Proj.Over
import Project.Proj.OfLE

import Project.Blowups.Bl
import Project.Blowups.UniqueBlowup
import Project.Blowups.PreClosAndClos

suppress_compilation

universe u
variable {A : Type (u+1)} [CommRing A]
variable {B : Type (u+1)} [CommRing B]
variable {ι : Type} [Fintype ι] (L : ι → Ideal A) [DecidableEq ι]
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]


open GoodPotionIngredient AlgebraicGeometry CategoryTheory.Limits

lemma blowups_Cars (A : CommRingCat) (L : ι → Ideal A) :
    IsCars _ <|
      pullback_Clos (BlMu L ↘ (Spec (CommRingCat.of A))) (loc_to_Clos A L) := by
              --  covering index : Mu L
              --  Covering by Potion
              --  Then its just properties of dilatations : LA[L/c]=cA[L/c]
    sorry


#exit
lemma base_change_Bl_open [Fintype ι] (A B : CommRingCat) [Algebra A B]
  [IsOpenImmersion (Spec B ↘ Spec A)] (L: ι → Ideal A) :
  ∃! (e : pullback (BlMu L ↘ Spec A) (Spec B ↘ Spec A) ≅
    BlMu (L := fun i : ι => Ideal.map (algebraMap A B) (L i))),
  Scheme.Hom.IsOver e.hom (Spec B) := by

  sorry
