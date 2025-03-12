import Project.Potions.Localization

suppress_compilation

universe u
variable {ι R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (𝒜) in
structure GoodPotionIngredient extends (HomogeneousSubmonoid 𝒜) where
  relevant : toHomogeneousSubmonoid.IsRelevant
  fg : toSubmonoid.FG

namespace GoodPotionIngredient

open AlgebraicGeometry

lemma toHomogeneousSubmonoid_inj :
    Function.Injective (toHomogeneousSubmonoid : GoodPotionIngredient 𝒜 → _) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  subst h
  rfl

open Pointwise in
instance : Mul (GoodPotionIngredient 𝒜) where
  mul x y :=
  { toHomogeneousSubmonoid := x.toHomogeneousSubmonoid * y.toHomogeneousSubmonoid
    relevant := x.relevant.mul y.relevant
    fg := x.fg.mul y.fg }

instance : Semigroup (GoodPotionIngredient 𝒜) where
  mul_assoc := by
    intro R S T
    refine toHomogeneousSubmonoid_inj ?_
    exact mul_assoc _ _ _

@[simp]
lemma mul_toHomogeneousSubmonoid (x y : GoodPotionIngredient 𝒜) :
    (x * y).toHomogeneousSubmonoid = x.toHomogeneousSubmonoid * y.toHomogeneousSubmonoid := rfl

instance : CommSemigroup (GoodPotionIngredient 𝒜) where
  mul_assoc R S T := by
    apply_fun GoodPotionIngredient.toHomogeneousSubmonoid using toHomogeneousSubmonoid_inj
    simp [mul_assoc]
  mul_comm R S := by
    apply_fun GoodPotionIngredient.toHomogeneousSubmonoid using toHomogeneousSubmonoid_inj
    simp [mul_comm]

open CategoryTheory AlgebraicGeometry TensorProduct

instance isOpenImmersion (S T : GoodPotionIngredient 𝒜) :
    IsOpenImmersion (Spec.map <| CommRingCat.ofHom <| S.1.potionToMul T.1) :=
  HomogeneousSubmonoid.IsOpenImmersion.of_isRelevant_FG _ _ S.relevant T.fg

instance (S T : GoodPotionIngredient 𝒜) : Algebra S.Potion (S * T).Potion :=
  RingHom.toAlgebra (S.potionToMul T.1)

open HomogeneousSubmonoid

instance instAlgebra₃ (R S T : GoodPotionIngredient 𝒜) : Algebra S.Potion (R * S * T).Potion :=
  RingHom.toAlgebra <| RingHom.comp (potionEquiv (by
    rw [mul_comm, mul_assoc, mul_comm T.1, ← mul_assoc]
    rfl)).toRingHom (S.potionToMul (R.1 * T.1))

@[simp]
lemma instAlgebra₃_algebraMap_eq (R S T : GoodPotionIngredient 𝒜) :
    algebraMap S.Potion (R * S * T).Potion =
    (potionEquiv (by rw [mul_comm, mul_assoc, mul_comm T.1, ← mul_assoc]; rfl)).toRingHom.comp
    (S.potionToMul (R.1 * T.1)) := rfl

def mixingAux₀ {R S T : GoodPotionIngredient 𝒜}
    (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1) :
    (S * T).Potion ⊗[S.Potion] (S * R).Potion ≃ₐ[S.Potion]
    (Localization T'.genSubmonoid) ⊗[S.Potion] (Localization R'.genSubmonoid) :=
  Algebra.TensorProduct.congr
    (S.localizationAlgEquivPotion T').symm
    (S.localizationAlgEquivPotion R').symm

def mixingAux₁ {R S T : GoodPotionIngredient 𝒜}
    (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1) :
    (Localization T'.genSubmonoid) ⊗[S.Potion] (Localization R'.genSubmonoid) ≃ₐ[S.Potion]
    Localization (T'.genSubmonoid * R'.genSubmonoid) :=
  Localization.mulEquivTensor _ _ |>.symm

def mixingAux₂ {R S T : GoodPotionIngredient 𝒜}
    (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1) :
    Localization (T'.genSubmonoid * R'.genSubmonoid) ≃ₐ[S.Potion]
    Localization (T'.disjUnion R').genSubmonoid :=
  Localization.equivEq (PotionGen.disjUnion_genSubmonoid T' R').symm

def mixingAux₃ {R S T : GoodPotionIngredient 𝒜}
    (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1) :
    Localization (T'.disjUnion R').genSubmonoid ≃ₐ[S.Potion]
    (S * (T * R)).Potion :=
  S.localizationAlgEquivPotion (T'.disjUnion R')

def mixingAux₄ (R S T : GoodPotionIngredient 𝒜) :
    (S * (T * R)).Potion ≃ₐ[S.Potion] (R * S * T).Potion :=
  AlgEquiv.ofRingEquiv (f := potionEquiv (by rw [mul_assoc, mul_comm R, ← mul_assoc])) <| by
    intro x
    simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, mul_potion_algebraMap_eq]
    induction x using Quotient.inductionOn' with | h x =>
    simp only [potionEquiv, mul_toSubmonoid, toMul_mk, RingEquiv.ofHomInv_apply]
    erw [HomogeneousLocalization.map_mk]

def mixing {R S T : GoodPotionIngredient 𝒜} (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1) :
    (S * T).Potion ⊗[S.Potion] (S * R).Potion ≃ₐ[S.Potion] (R * S * T).Potion :=
  mixingAux₀ R' T' |>.trans <|
  mixingAux₁ R' T' |>.trans <|
  mixingAux₂ R' T' |>.trans <|
  mixingAux₃ R' T' |>.trans <|
  mixingAux₄ R S T

set_option maxHeartbeats 1000000 in
lemma mixing_left (R S T : GoodPotionIngredient 𝒜) (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1)
    (x : (S * T).Potion) :
    mixing R' T' (x ⊗ₜ 1) =
    potionEquiv (by rw [mul_comm R, mul_assoc, mul_comm R, ← mul_assoc]; rfl) (potionToMul _ R.1 x) := by
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, mixing, AlgEquiv.trans_apply]
  delta mixingAux₄
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, AlgEquiv.ofRingEquiv_apply]
  erw [Equiv.apply_eq_iff_eq_symm_apply]
  erw [potionEquiv_symm_apply]
  swap
  · rw [mul_comm _ R.1, ← mul_assoc, mul_comm S.1]
  simp only [mul_toSubmonoid, potionEquiv_trans_apply]
  simp only [mixingAux₀, mul_toHomogeneousSubmonoid, mul_toSubmonoid,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_coe, map_one]
  simp only [mixingAux₁, Localization.mulEquivTensor_symm_apply]
  set y := (localizationAlgEquivPotion T').symm x
  have hy : x = (localizationAlgEquivPotion T') y := by simp [y]
  simp only [hy, mul_toSubmonoid]
  clear_value y
  clear hy x
  induction y using Localization.induction_on with | H y =>
  rcases y with ⟨y, t⟩
  simp only [Localization.tensorToLocalization_tmul_mk_one]
  simp only [mixingAux₃, localizationAlgEquivPotion, mul_toSubmonoid, mixingAux₂,
    Localization.equivEq_apply, Localization.mapEq_mk, AlgEquiv.ofRingEquiv_apply,
    localizationRingEquivPotion_apply]
  induction y using Quotient.inductionOn' with | h x =>
  rcases t with ⟨t, ht⟩
  erw [Submonoid.mem_closure_iff] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have ht' := hc
  choose i hi using hc
  simp only
  set f : (i : S.Potion) → i ∈ c.support → S.bar.Potion := _
  change ∀ (x : S.Potion) (hx : x ∈ c.support), x = S.equivBarPotion.symm (f x hx) at hi
  rw [show Localization.mk (HomogeneousLocalization.mk x) ⟨_, ht⟩ =
    (HomogeneousLocalization.mk x) • ∏ x ∈ c.support.attach,
      Localization.mk 1 ⟨(S.equivBarPotion.symm <| f x.1 x.2) ^ (c x.1),
        pow_mem (Submonoid.subset_closure (by
        simp only [Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, f]
        use i x.1 x.2)) _⟩ by
      rw [Localization.prod_mk]
      simp only [Finset.prod_const_one, f]
      rw [Localization.smul_mk]
      simp only [smul_eq_mul, mul_one, f]
      congr 1
      ext : 1
      simp only [Finsupp.prod, SubmonoidClass.coe_finset_prod, f]
      rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl ?_
      rintro ⟨x, hx⟩ _
      simp only [f]
      conv_rhs => rw [← hi _ hx]]
  simp only [← localizationAlgEquivPotion_apply]
  rw [map_smul]
  simp only [localizationAlgEquivPotion_apply]
  simp_rw [show (1 : S.Potion) = .mk 1 by rfl]
  have := localizationToPotion_mk' (𝒜 := 𝒜) S.1 T.1 T' 1 c.support.attach (fun x ↦ i _ x.2) (fun x ↦ c x.1)
  simp only [mul_toSubmonoid, HomogeneousLocalization.mk_one, Localization.prod_mk,
    Finset.prod_const_one, f]
  erw [this]
  have : (1 : (S * T).Potion) = .mk ⟨_, _, _, _⟩ := HomogeneousLocalization.one_eq (𝒜 := 𝒜) (x := (S * T).toSubmonoid)
  erw [← this]

  simp only [mul_toSubmonoid, map_prod, map_pow, one_mul, f]
  simp only [Finsupp.prod, f]
  have eq := localizationToPotion_mk' (𝒜 := 𝒜) S.1 _ (T'.disjUnion R') x c.support.attach
    (fun x ↦ .inl <| i _ x.2) (fun x ↦ c x.1)
  simp only [mul_toSubmonoid, map_prod, map_pow, f] at eq
  simp_rw [show ∏ x ∈ c.support, x ^ c x = ∏ x ∈ c.support.attach,
      (S.equivBarPotion.symm <| f x.1 x.2) ^ (c x.1) by
      rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl ?_
      intro j _
      rw [← hi _ j.2]]
  simp only [f]
  convert eq using 1
  · congr 2
    ext : 1
    simp only [SubmonoidClass.coe_finset_prod, f]
    rfl
  · erw [smul_eq_mul]
    simp only [mul_toSubmonoid, toMul_mk, map_mul, map_prod, map_pow, f]
    rw [toMul_mk, potionEquiv_mk]
    simp only [mul_toSubmonoid, Subtype.coe_eta, f]
    congr 1
    refine Finset.prod_congr rfl ?_
    rintro ⟨x, hx⟩ _
    simp only [f]
    congr 1
    simp only [PotionGen.disjUnion, f]
    have := T'.s'_mem_bar (i _ hx)
    simp only [mem_bar] at this
    obtain ⟨hom, y, hy, dvd⟩ := this
    obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜  ⟨_, T'.s'_deg (i _ hx)⟩
      (S.1.homogeneous hy) dvd
    rw [equivBarPotion_symm_apply (z_mem := hj) (hz := by
      rw [mul_assoc]
      apply mul_mem
      · apply pow_mem
        exact right_le_mul _ _ (T'.elem_mem _)
      exact left_le_mul _ _ hy)]

    rw [equivBarPotion_symm_apply (z_mem := hj) (hz := by
      rw [mul_assoc]
      apply mul_mem
      · apply pow_mem
        exact right_le_mul _ _ <| left_le_mul _ _ (T'.elem_mem _)
      exact left_le_mul _ _ hy)]
    rw [toMul_mk, potionEquiv_mk]

set_option maxHeartbeats 1000000 in
lemma mixing_right (R S T : GoodPotionIngredient 𝒜) (R' : PotionGen S.1 R.1) (T' : PotionGen S.1 T.1)
    (x : (S * R).Potion) :
    mixing R' T' (1 ⊗ₜ x) =
    potionEquiv (by simp [mul_comm R]) (potionToMul _ T.1 x) := by
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, mixing, AlgEquiv.trans_apply]
  delta mixingAux₄
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, AlgEquiv.ofRingEquiv_apply]
  erw [Equiv.apply_eq_iff_eq_symm_apply]
  erw [potionEquiv_symm_apply]
  swap
  · rw [mul_comm _ R.1, ← mul_assoc, mul_comm S.1]
  simp only [mul_toSubmonoid, potionEquiv_trans_apply]
  simp only [mixingAux₀, mul_toHomogeneousSubmonoid, mul_toSubmonoid,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_coe, map_one]
  simp only [mixingAux₁, Localization.mulEquivTensor_symm_apply]
  set y := (localizationAlgEquivPotion R').symm x
  have hy : x = (localizationAlgEquivPotion R') y := by simp [y]
  simp only [hy, mul_toSubmonoid]
  clear_value y
  clear hy x
  induction y using Localization.induction_on with | H y =>
  rcases y with ⟨y, t⟩
  simp only [Localization.tensorToLocalization_tmul_mk_one]
  simp only [mixingAux₃, localizationAlgEquivPotion, mul_toSubmonoid, mixingAux₂,
    Localization.equivEq_apply, Localization.mapEq_mk, AlgEquiv.ofRingEquiv_apply,
    localizationRingEquivPotion_apply]
  induction y using Quotient.inductionOn' with | h x =>
  rcases t with ⟨t, ht⟩
  erw [Submonoid.mem_closure_iff] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have ht' := hc
  choose i hi using hc
  simp only [Localization.tensorToLocalization_tmul_one_mk, Localization.mapEq_mk]
  set f : (i : S.Potion) → i ∈ c.support → S.bar.Potion := _
  change ∀ (x : S.Potion) (hx : x ∈ c.support), x = S.equivBarPotion.symm (f x hx) at hi
  rw [show Localization.mk (HomogeneousLocalization.mk x) ⟨_, ht⟩ =
    (HomogeneousLocalization.mk x) • ∏ x ∈ c.support.attach,
      Localization.mk 1 ⟨(S.equivBarPotion.symm <| f x.1 x.2) ^ (c x.1),
        pow_mem (Submonoid.subset_closure (by
        simp only [Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, f]
        use i x.1 x.2)) _⟩ by
      rw [Localization.prod_mk]
      simp only [Finset.prod_const_one, f]
      rw [Localization.smul_mk]
      simp only [smul_eq_mul, mul_one, f]
      congr 1
      ext : 1
      simp only [Finsupp.prod, SubmonoidClass.coe_finset_prod, f]
      rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl ?_
      rintro ⟨x, hx⟩ _
      simp only [f]
      conv_rhs => rw [← hi _ hx]]
  simp only [← localizationAlgEquivPotion_apply]
  rw [map_smul]
  simp only [localizationAlgEquivPotion_apply]
  simp_rw [show (1 : S.Potion) = .mk 1 by rfl]
  have := localizationToPotion_mk' (𝒜 := 𝒜) S.1 _ R' 1 c.support.attach (fun x ↦ i _ x.2) (fun x ↦ c x.1)
  simp only [mul_toSubmonoid, HomogeneousLocalization.mk_one, Localization.prod_mk,
    Finset.prod_const_one, f]
  erw [this]
  have : (1 : (S * R).Potion) = .mk ⟨_, _, _, _⟩ := HomogeneousLocalization.one_eq (𝒜 := 𝒜) (x := (S * R).toSubmonoid)
  erw [← this]

  simp only [mul_toSubmonoid, map_prod, map_pow, one_mul, f]
  simp only [Finsupp.prod, f]
  have eq := localizationToPotion_mk' (𝒜 := 𝒜) S.1 _ (T'.disjUnion R') x c.support.attach
    (fun x ↦ .inr <| i _ x.2) (fun x ↦ c x.1)
  simp only [mul_toSubmonoid, map_prod, map_pow, f] at eq
  simp_rw [show ∏ x ∈ c.support, x ^ c x = ∏ x ∈ c.support.attach,
      (S.equivBarPotion.symm <| f x.1 x.2) ^ (c x.1) by
      rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl ?_
      intro j _
      rw [← hi _ j.2]]
  simp only [f]
  convert eq using 1
  · congr 2
    ext : 1
    simp only [SubmonoidClass.coe_finset_prod, f]
    rfl
  · erw [smul_eq_mul]
    simp only [mul_toSubmonoid, toMul_mk, map_mul, map_prod, map_pow, f]
    rw [toMul_mk, potionEquiv_mk]
    simp only [mul_toSubmonoid, Subtype.coe_eta, f]
    congr 1
    refine Finset.prod_congr rfl ?_
    rintro ⟨x, hx⟩ _
    simp only [f]
    congr 1
    simp only [PotionGen.disjUnion, f]
    have := R'.s'_mem_bar (i _ hx)
    simp only [mem_bar] at this
    obtain ⟨hom, y, hy, dvd⟩ := this
    obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜  ⟨_, R'.s'_deg (i _ hx)⟩
      (S.1.homogeneous hy) dvd
    rw [equivBarPotion_symm_apply (z_mem := hj) (hz := by
      rw [mul_assoc]
      apply mul_mem
      · apply pow_mem
        exact right_le_mul _ _ (R'.elem_mem _)
      exact left_le_mul _ _ hy)]

    rw [equivBarPotion_symm_apply (z_mem := hj) (hz := by
      rw [mul_assoc]
      apply mul_mem
      · apply pow_mem
        exact right_le_mul _ _ <| right_le_mul _ _ (R'.elem_mem _)
      exact left_le_mul _ _ hy)]
    rw [toMul_mk, potionEquiv_mk]

def t'Aux₀ (R S T : GoodPotionIngredient 𝒜) :
    (S * T).Potion ⊗[S.Potion] (S * R).Potion ≃+* (R * S * T).Potion :=
  mixing (finitePotionGen S.relevant R.fg) (finitePotionGen S.relevant T.fg)

@[simp]
lemma t'Aux₀_SR (R S T : GoodPotionIngredient 𝒜) (x : (S * R).Potion) :
    t'Aux₀ R S T (1 ⊗ₜ x) =
    potionEquiv (by simp [mul_comm R.1]) (potionToMul _ T.1 x) := by
  delta t'Aux₀
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, AlgEquiv.coe_ringEquiv]
  erw [mixing_right _ _ _ (finitePotionGen S.relevant R.fg) (finitePotionGen S.relevant T.fg) x]
  rfl

def t'Aux₁ (R S T : GoodPotionIngredient 𝒜) :
    (R * S).Potion ⊗[R.Potion] (R * T).Potion ≃+* (R * S * T).Potion :=
  (mixing (finitePotionGen R.relevant T.fg) (finitePotionGen R.relevant S.fg)).toRingEquiv.trans <|
    potionEquiv (by rw [mul_comm T, mul_assoc, mul_comm T, ← mul_assoc])

@[simp]
lemma t'Aux₁_RS (R S T : GoodPotionIngredient 𝒜) (x : (R * S).Potion) :
    t'Aux₁ R S T (x ⊗ₜ 1) =
    potionEquiv (by simp [mul_comm T.1]) (potionToMul _ T.1 x) := by
  delta t'Aux₁
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, AlgEquiv.toRingEquiv_eq_coe,
    RingEquiv.coe_trans, AlgEquiv.coe_ringEquiv, Function.comp_apply, potionEquiv_refl,
    RingEquiv.refl_apply]
  erw [mixing_left]
  simp

def t' (R S T : GoodPotionIngredient 𝒜) :
    ((S * T).Potion ⊗[S.Potion] (S * R).Potion) ≃+*
    ((R * S).Potion ⊗[R.Potion] (R * T).Potion) :=
  (t'Aux₀ R S T).trans (t'Aux₁ R S T).symm

@[simp]
lemma t'_apply_SR (R S T : GoodPotionIngredient 𝒜) (x : (S * R).Potion) :
    t' R S T (1 ⊗ₜ x) = (potionEquiv (by rw [mul_comm]) x) ⊗ₜ 1 := by
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, t', RingEquiv.coe_trans,
    Function.comp_apply]
  erw [t'Aux₀_SR R S T x]
  apply_fun (R.t'Aux₁ S T)
  erw [RingEquiv.apply_symm_apply]
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid]
  erw [t'Aux₁_RS R S T _]
  induction x using Quotient.inductionOn' with | h x =>
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, potionEquiv_refl, RingEquiv.refl_apply]
  erw [toMul_mk]
  erw [toMul_mk]
  rw [potionEquiv_mk']
  simp

lemma t'_cocycle (R S T : GoodPotionIngredient 𝒜) :
    (T.t' R S).trans ((S.t' T R).trans (R.t' S T))  = RingEquiv.refl _ := by
  delta t'
  ext x
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, t'Aux₀, t'Aux₁,
    AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_trans, AlgEquiv.coe_ringEquiv, Function.comp_apply,
    RingEquiv.symm_trans_apply, RingEquiv.refl_apply]
  erw [Equiv.symm_apply_eq]
  erw [Equiv.symm_apply_eq]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AlgEquiv.coe_ringEquiv,
    mul_toHomogeneousSubmonoid, mul_toSubmonoid]
  erw [RingEquiv.apply_symm_apply]
  erw [RingEquiv.apply_symm_apply]
  erw [Equiv.symm_apply_eq]
  erw [Equiv.symm_apply_eq]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  simp only [potionEquiv_trans_apply, mul_toSubmonoid, potionEquiv_refl, RingEquiv.refl_apply]

lemma t'_fac (R S T : GoodPotionIngredient 𝒜) :
    ((R.t' S T)).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
    Algebra.TensorProduct.includeLeftRingHom.comp
    (potionEquiv <| by rw [mul_comm]).toRingHom := by
  ext x
  simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, RingEquiv.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  erw [t'_apply_SR]
  rfl

end GoodPotionIngredient
