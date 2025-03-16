import Project.Proj.Construction
import Mathlib.Lean.Expr.ExtraRecognizers

open Lean PrettyPrinter.Delaborator SubExpr

#check GoodPotionIngredient.Proj
@[app_delab GoodPotionIngredient.Proj]
def proj_delab : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``GoodPotionIngredient.Proj 12
    let set? := (e.getArg! 10).coeTypeSet?
    match set? with
    | some _ =>
    let optionsPerPos ← withNaryArg 7 do
      return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    let optionsPerPos ← withNaryArg 10 do
      return optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true

    withTheReader Context ({· with optionsPerPos}) delab
    | _ =>
    let optionsPerPos ← withNaryArg 7 do
      return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    let optionsPerPos ← withNaryArg 10 do
      return optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    withTheReader Context ({· with optionsPerPos}) delab

section test

open GoodPotionIngredient
universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (F : Set (GoodPotionIngredient 𝒜))
example : true := by
  let e₁ := Proj (𝒜 := 𝒜) (τ := F) Subtype.val
  let e₂ := Proj (𝒜 := 𝒜) (τ := GoodPotionIngredient 𝒜) id
  rfl

end test
