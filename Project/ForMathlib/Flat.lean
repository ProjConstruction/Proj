import Mathlib.RingTheory.RingHom.Flat

#check RingHom.Flat

lemma RingHom.Flat.preserves_nonzeroDivisors {R S F : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (flat : RingHom.Flat f) {r : R} (hr : r ∈ nonZeroDivisors R) :
    f r ∈ nonZeroDivisors S := by
  algebraize [f]
  let mr : R →ₗ[R] R := Algebra.lsmul R _ _ r
  have : Function.Injective mr := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    simp only [LinearMap.mem_ker, Algebra.lsmul_coe, smul_eq_mul, Ideal.mem_bot, mr] at hx ⊢
    exact hr x (by rwa [mul_comm])

  intro s hs
  have hs' : r • s = 0 := by
    rw [Algebra.smul_def, mul_comm]
    exact hs

  have tmr := Module.Flat.rTensor_preserves_injective_linearMap (M := S) mr this
  rw [← LinearMap.ker_eq_bot, eq_bot_iff] at tmr
  simpa using @tmr (1 ⊗ₜ s) (by
    simp only [LinearMap.mem_ker, LinearMap.rTensor_tmul, Algebra.lsmul_coe, smul_eq_mul, mul_one,
      mr]
    rw [show r ⊗ₜ[R] s = 1 ⊗ₜ[R] (r • s) by
      rw [← TensorProduct.smul_tmul]
      simp only [smul_eq_mul, mul_one, mr], hs', TensorProduct.tmul_zero])
