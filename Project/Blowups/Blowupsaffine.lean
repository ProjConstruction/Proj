


lemma ProjBlowup_UnivProp_unicity_affine :  ( Spec(B) ↘ BlMu L over Spec(A) )
(φ φ': Spec(B) →over Spec(A) BlMu L ): φ=φ' := by
  Let x ∈ T.
  Reduce to local neighborhood
  put y=φx
  put y'=φ'x
  obtain P ∈ Mu L such that y ∈ Mu P
  obtain p' ∈ Mu L such that y ∈ Mu P'
  Let U=Spec(B) be an affine neighborhood of x in φ^-1 (Po P) ∩ φ'^-1 (Po P').
  consider the restrictions of φ and φ' to U
  Phi factors through Po P, Phi' factors through Po P'
  apply lemma 2
  apply univ prop of dilatations
  sorry

lemma ProjBlowup_UnivProp_existence_affine
/-obtain ⟨j, x, rfl⟩ := (glueData ℱ).ι_jointly_surjective x
  obtain ⟨j', x', rfl⟩ := (glueData ℱ).ι_jointly_surjective x'-/
