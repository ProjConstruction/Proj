import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry CategoryTheory

namespace Localization

variable {R : Type*} [CommRing R] (s : Finset R) {t : Set R} (fin : Set.Finite t)

instance awayProd_isLocalization_closure :
    IsLocalization (Submonoid.closure s : Submonoid R)
      (Localization.Away (∏ i ∈ s, i : R)) where
  map_units' := by
    classical
    rintro ⟨x, hx⟩
    refine Submonoid.closure_induction ?_ ?_ ?_ hx
    · intro x hx
      refine isUnit_of_mul_eq_one _ (.mk (∏ i ∈ s \ {x}, i) ⟨∏ i ∈ s, i, ⟨1, by simp⟩⟩) ?_
      simp only [← mk_one_eq_algebraMap, ne_eq, mk_mul, one_mul, ← mk_one, mk_eq_mk_iff,
        Prod.mk_one_one, r_iff_exists, Prod.snd_one, OneMemClass.coe_one, Prod.fst_one, mul_one,
        Subtype.exists, exists_prop]
      refine ⟨1, one_mem _, ?_⟩
      simp only [one_mul]
      conv_rhs => rw [show s = insert x (s \ {x}) by
        ext y
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        refine ⟨fun h ↦ (em <| y = x).rec Or.inl fun h' ↦ Or.inr (by tauto),
          Or.rec (by rintro rfl; exact hx) (by tauto)⟩]
      simp
    · simp
    · intro x y _ _ hx hy
      simp only [map_mul, IsUnit.mul_iff]
      tauto
  surj' z := z.induction_on <| by
    rintro ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩
    simp only [← mk_one_eq_algebraMap, mk_mul, mul_one, mk_eq_mk_iff, r_iff_exists,
      OneMemClass.coe_one, one_mul, Subtype.exists, exists_prop, Prod.exists]
    refine ⟨a, (∏ i ∈ s, i) ^ n, pow_mem (prod_mem fun i hi ↦ Submonoid.subset_closure hi) _,
      1, one_mem _, ?_⟩
    simp [mul_comm]
  exists_of_eq := by
    rintro x y h
    simp only [← mk_one_eq_algebraMap, mk_eq_mk_iff, r_iff_exists, OneMemClass.coe_one, one_mul,
      Subtype.exists, exists_prop] at h
    obtain ⟨_, ⟨i, rfl⟩, h⟩ := h
    simp only at h
    exact ⟨⟨(∏ i ∈ s, i)^i, pow_mem (prod_mem (by aesop)) _⟩, h⟩

noncomputable def closureFinsetEquiv :
  Localization (Submonoid.closure s : Submonoid R) ≃ₐ[R] Localization.Away (∏ i ∈ s, i : R) :=
  IsLocalization.algEquiv (Submonoid.closure s : Submonoid R) _ _

@[simp]
lemma clousreFinset_comp :
    (closureFinsetEquiv s).toAlgHom.comp (Algebra.ofId R _) = Algebra.ofId R _ := by ext

@[simp]
lemma closureFinset_symm_comp :
  (closureFinsetEquiv s).symm.toAlgHom.comp (Algebra.ofId R _) = Algebra.ofId R _ := by ext

instance awayProd_isLocalization_closure' :
    IsLocalization (Submonoid.closure t)
      (Localization.Away (∏ i ∈ fin.toFinset, i : R)) := by
  convert awayProd_isLocalization_closure fin.toFinset
  exact Eq.symm (Set.Finite.coe_toFinset fin)

noncomputable def closureFiniteEquiv :
  Localization (Submonoid.closure t) ≃ₐ[R] Localization.Away (∏ i ∈ fin.toFinset, i : R) :=
  IsLocalization.algEquiv (Submonoid.closure t) _ _


@[simp]
lemma clousreFinite_comp :
    (closureFiniteEquiv fin).toAlgHom.comp (Algebra.ofId R _) = Algebra.ofId R _ := by ext

@[simp]
lemma closureFininite_symm_comp :
  (closureFiniteEquiv fin).symm.toAlgHom.comp (Algebra.ofId R _) = Algebra.ofId R _ := by ext


end Localization

namespace AlgebraicGeometry

variable {R : Type*} [CommRing R] (s : Finset R) {t : Set R} (ht : Set.Finite t)

instance : IsOpenImmersion <| Spec.map <| CommRingCat.ofHom <|
    algebraMap R (Localization (Submonoid.closure s : Submonoid R)) := by
  let f : CommRingCat.of R ⟶ _ := CommRingCat.ofHom <| algebraMap R (Localization (Submonoid.closure s : Submonoid R))
  let g : CommRingCat.of R ⟶ _ := CommRingCat.ofHom <| algebraMap R (Localization.Away (∏ i ∈ s, i))
  let e := (Localization.closureFinsetEquiv s).toCommRingCatIso
  have eq : f = g ≫ e.inv := by
    ext : 1
    exact congr($(Localization.closureFinset_symm_comp s).toRingHom).symm
  change IsOpenImmersion <| Spec.map f
  rw [eq]
  simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe,
    CommRingCat.ofHom_comp, Spec.map_comp]
  apply IsOpenImmersion.comp

include ht in
lemma IsOpenImmersion.of_map_localization_finite_closure :
    IsOpenImmersion <| Spec.map <| CommRingCat.ofHom <|
    algebraMap R (Localization (Submonoid.closure t)) := by
  let f : CommRingCat.of R ⟶ _ := CommRingCat.ofHom <| algebraMap R (Localization (Submonoid.closure t))
  let g : CommRingCat.of R ⟶ _ := CommRingCat.ofHom <| algebraMap R (Localization.Away (∏ i ∈ ht.toFinset, i))
  let e := (Localization.closureFiniteEquiv ht).toCommRingCatIso
  have eq : f = g ≫ e.inv := by
    ext : 1
    exact congr($(Localization.closureFininite_symm_comp ht).toRingHom).symm
  change IsOpenImmersion <| Spec.map f
  rw [eq]
  simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe,
    CommRingCat.ofHom_comp, Spec.map_comp]
  apply IsOpenImmersion.comp



end AlgebraicGeometry
