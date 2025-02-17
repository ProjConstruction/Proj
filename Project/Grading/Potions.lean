import Project.Grading.HomogeneousSubmonoid

import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

suppress_compilation

namespace HomogeneousSubmonoid

variable {ι R A : Type*}
variable [AddCommGroup ι] [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]
variable (S T : HomogeneousSubmonoid 𝒜)

abbrev Potion := HomogeneousLocalization 𝒜 S.toSubmonoid

def toMul : S.Potion →+* (S * T).Potion :=
  HomogeneousLocalization.map _ _ (RingHom.id _) (by
    erw [Submonoid.comap_id, ← le_iff]
    exact le_mul_left S T) fun i a hi ↦ hi

@[simp]
lemma toMul_mk (x) : S.toMul T (.mk x) = .mk ⟨x.deg, x.num, x.den, le_mul_left _ _ x.den_mem⟩ := rfl

instance : Algebra S.Potion (S * T).Potion := RingHom.toAlgebra (toMul S T)

def toBarPotion : S.Potion →+* S.bar.Potion :=
  HomogeneousLocalization.map _ _ (.id A) (by
      erw [Submonoid.comap_id, ← le_iff]
      exact le_bar S) fun i a hi ↦ hi

@[simp]
lemma toBarPotion_mk (x) :
  toBarPotion (S := S) (.mk x) = .mk
  { deg := x.deg
    num := x.num
    den := x.den
    den_mem := S.le_bar x.den_mem } := rfl

lemma toBarPotion_surjective : Function.Surjective (toBarPotion S) := by
  rintro x
  induction x using Quotient.inductionOn' with | h x =>
  rcases x with ⟨i, ⟨m, hm⟩, ⟨n, hn⟩, hn'⟩
  simp only [mem_toSubmonoid_iff, mem_bar] at hn'
  obtain ⟨hn', y, hy, dvd⟩ := hn'
  obtain ⟨z, rfl, ⟨j, hz⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 hn'
    (S.homogeneous hy) dvd
  refine ⟨.mk ⟨i + j, ⟨m * z, SetLike.mul_mem_graded hm hz⟩,
    ⟨n * z, SetLike.mul_mem_graded hn hz⟩, hy⟩, ?_⟩
  simp only [toBarPotion_mk]
  apply Quotient.sound'
  simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists, mem_toSubmonoid_iff,
    mem_bar, exists_prop]
  exact ⟨1, ⟨SetLike.homogeneous_one _,
    ⟨1, one_mem _, by rfl⟩⟩, by group⟩

lemma toBarPotion_injective : Function.Injective (toBarPotion S) := by
  rintro x y h
  induction x using Quotient.inductionOn' with | h x =>
  induction y using Quotient.inductionOn' with | h y =>
  rcases x with ⟨i, ⟨m, hm⟩, ⟨n, hn⟩, hn'⟩
  rcases y with ⟨i', ⟨m', hm'⟩, ⟨n', hn'⟩, hn''⟩
  simp only [mem_toSubmonoid_iff, toBarPotion_mk] at hn' hn'' h ⊢
  rw [HomogeneousLocalization.mk, HomogeneousLocalization.mk, Quotient.eq'', Setoid.ker_def,
    HomogeneousLocalization.NumDenSameDeg.embedding,
    HomogeneousLocalization.NumDenSameDeg.embedding,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
  obtain ⟨⟨c, ⟨⟨j, hc⟩, ⟨_, hz, ⟨z, rfl⟩⟩⟩⟩, eq⟩ := h
  simp only [mem_toSubmonoid_iff, mem_bar] at hc hz eq ⊢
  apply Quotient.sound'
  rw [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
    HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  simp only [Subtype.exists, mem_toSubmonoid_iff, exists_prop]
  refine ⟨c * z, hz, ?_⟩
  convert congr(z * $eq) using 1 <;> ring


def equivBarPotion : S.Potion ≃+* S.bar.Potion :=
  RingEquiv.ofBijective (toBarPotion S) ⟨toBarPotion_injective S, toBarPotion_surjective S⟩

lemma equivBarPotion_apply (x) :
  equivBarPotion S x = toBarPotion S x := rfl

lemma equivBarPotion_symm_apply
    (i j : ι) (m n : A) (m_mem : m ∈ 𝒜 i) (n_mem : n ∈ 𝒜 i) (z : A) (z_mem : z ∈ 𝒜 j) (hz : n * z ∈ S) :
    (equivBarPotion S).symm (.mk ⟨i, ⟨m, m_mem⟩, ⟨n, n_mem⟩, ⟨⟨i, n_mem⟩, ⟨n * z, hz, ⟨z, rfl⟩⟩⟩⟩) =
    .mk ⟨i + j, ⟨m * z, SetLike.mul_mem_graded m_mem z_mem⟩,
      ⟨n * z, SetLike.mul_mem_graded n_mem z_mem⟩, hz⟩ := by
    apply_fun S.equivBarPotion
    simp only [RingEquiv.apply_symm_apply, equivBarPotion_apply, toBarPotion_mk]
    apply Quotient.sound'
    rw [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
      HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    ring


instance : Algebra S.Potion S.bar.Potion :=
  RingHom.toAlgebra S.equivBarPotion

def localizationToPotion
    (T' : Set A)
    (T'_gen : Submonoid.closure T' = T.toSubmonoid)
    (n : T' → ℕ) (s s' : T' → A)
    (s_mem_bar : ∀ t, s t ∈ S.bar) (s'_mem_bar : ∀ t, s' t ∈ S.bar)
    (i i' : T' → ι)
    (t_deg : ∀ t : T', (t : A)^(n t) ∈ 𝒜 (i t - i' t))
    (s_deg : ∀ t, s t ∈ 𝒜 (i t)) (s'_deg : ∀ t, s' t ∈ 𝒜 (i' t)) :
    Localization (Submonoid.closure {x | ∃ (t : T'), x =
      .mk { deg := i t
            num := ⟨t ^ n t * s' t, by simpa using SetLike.mul_mem_graded (t_deg t) (s'_deg t)⟩
            den := ⟨s t, s_deg t⟩
            den_mem := s_mem_bar t } } : Submonoid S.bar.Potion) →+*
    (S * T).Potion :=
  @IsLocalization.lift
    (R := S.bar.Potion)
    (M :=  _)
    (S :=  _)
    (P := (S * T).Potion)
    (g := (RingHom.comp (S.toMul T) S.equivBarPotion.symm)) _ _ _ _
    (Localization.isLocalization (R := S.bar.Potion) (M := (Submonoid.closure {x | ∃ (t : T'), x =
      .mk { deg := i t
            num := ⟨t ^ n t * s' t, by simpa using SetLike.mul_mem_graded (t_deg t) (s'_deg t)⟩
            den := ⟨s t, s_deg t⟩
            den_mem := s_mem_bar t } } : Submonoid S.bar.Potion))) <| by
    rintro ⟨y, hy⟩
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    refine Submonoid.closure_induction (hx := hy) ?_ ?_ ?_
    · rintro x hx
      simp only [Subtype.exists, Set.mem_setOf_eq] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      let i := i ⟨t, ht⟩
      let i' := i' ⟨t, ht⟩
      let n := n ⟨t, ht⟩
      let s := s ⟨t, ht⟩
      let s' := s' ⟨t, ht⟩
      have s_mem_bar' : s ∈ S.bar := s_mem_bar ⟨t, ht⟩
      have s_mem_bar : s ∈ S.bar := s_mem_bar ⟨t, ht⟩
      have s'_mem_bar' : s' ∈ S.bar := s'_mem_bar ⟨t, ht⟩
      have s'_mem_bar : s' ∈ S.bar := s'_mem_bar ⟨t, ht⟩
      simp only [mem_bar] at s_mem_bar' s'_mem_bar'
      obtain ⟨s_hom, y, hy, dvd⟩ := s_mem_bar'
      obtain ⟨s'_hom, y', hy', dvd'⟩ := s'_mem_bar'
      obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 s_hom (S.2 hy) dvd
      obtain ⟨z', rfl, ⟨j', hj'⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 s'_hom (S.2 hy') dvd'
      have t_deg : (t : A)^(n) ∈ 𝒜 (i - i') := t_deg ⟨t, ht⟩
      have s_deg : s ∈ 𝒜 i := s_deg ⟨t, ht⟩
      have s'_deg : s' ∈ 𝒜 i' := s'_deg ⟨t, ht⟩
      change IsUnit <| S.toMul T <| S.equivBarPotion.symm <| .mk ⟨i, ⟨t^n * s', _⟩, ⟨s, _⟩, _⟩
      rw [equivBarPotion_symm_apply (z_mem := hj) (hz := hy), toMul_mk]
      simp only [eq_mp_eq_cast]
      refine isUnit_of_mul_eq_one _ (.mk ⟨i + j', ⟨s * z', SetLike.mul_mem_graded s_deg hj'⟩,
        ⟨t ^ n * s' * z',
          SetLike.mul_mem_graded (by simpa using SetLike.mul_mem_graded t_deg s'_deg) hj'⟩,
        ⟨s' * z', hy', t^n, pow_mem (T'_gen ▸ Submonoid.subset_closure ht) _, by ring⟩⟩) ?_
      rw [← HomogeneousLocalization.mk_mul, HomogeneousLocalization.one_eq]
      apply Quotient.sound'
      simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding, eq_mp_eq_cast,
        Nat.rawCast.eq_1, Nat.cast_id, Nat.add_zero, HomogeneousLocalization.NumDenSameDeg.deg_mul,
        HomogeneousLocalization.NumDenSameDeg.num_mul,
        HomogeneousLocalization.NumDenSameDeg.den_mul,
        HomogeneousLocalization.NumDenSameDeg.deg_one,
        HomogeneousLocalization.NumDenSameDeg.num_one,
        HomogeneousLocalization.NumDenSameDeg.den_one, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists, one_mul, mul_one, Subtype.exists, mem_toSubmonoid_iff,
        exists_prop]
      exact ⟨1, one_mem _, by ring⟩
    · simp only [map_one, isUnit_one]
    · intro x y hx hy ihx ihy
      simp only [map_mul, IsUnit.mul_iff]
      tauto



end HomogeneousSubmonoid
