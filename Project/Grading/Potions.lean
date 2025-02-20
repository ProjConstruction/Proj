import Project.Grading.HomogeneousSubmonoid
import Project.Grading.IsoBar

import Project.ForMathlib.HomogeneousLocalization

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

@[simp]
lemma mul_potion_algebraMap_eq : (algebraMap S.Potion (S * T).Potion) = S.toMul T := rfl

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

@[simp]
lemma toBarPotion_mk' (x) :
  toBarPotion (S := S) (Quotient.mk'' x) = .mk
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

lemma toMul_equivBarPotion_symm (x) :
    S.toMul T (S.equivBarPotion.symm <| .mk x) =
    (S * T).equivBarPotion.symm (.mk
      { deg := x.deg
        num := x.num
        den := x.den
        den_mem := bar_mono _ _ (le_mul_left S T) x.den_mem }) := by
  rcases x with ⟨i, ⟨m, hm⟩, ⟨n, hn⟩, hn'⟩
  simp only [mem_toSubmonoid_iff, mem_bar] at hn'
  obtain ⟨hn', y, hy, dvd⟩ := hn'
  obtain ⟨z, rfl, ⟨j, hz⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 hn'
    (S.homogeneous hy) dvd
  rw [equivBarPotion_symm_apply (z_mem := hz) (hz := hy), toMul_mk]
  simp only
  rw [equivBarPotion_symm_apply (z_mem := hz) (hz := le_mul_left S T hy)]

instance : Algebra S.Potion S.bar.Potion :=
  RingHom.toAlgebra S.equivBarPotion

@[simp]
lemma bar_potion_algebraMap_eq : (algebraMap S.Potion S.bar.Potion) = S.equivBarPotion := rfl

structure potionGen where
  (carrier : Set A)
  (subset : carrier ⊆ T)
  (gen : Submonoid.closure carrier = T.toSubmonoid)
  (n : carrier → ℕ+)
  (s s' : carrier → A)
  (s_mem_bar : ∀ t, s t ∈ S.bar)
  (s'_mem_bar : ∀ t, s' t ∈ S.bar)
  (i i' : carrier → ι)
  (t_deg : ∀ t : carrier, (t : A)^(n t : ℕ) ∈ 𝒜 (i t - i' t))
  (s_deg : ∀ t, s t ∈ 𝒜 (i t))
  (s'_deg : ∀ t, s' t ∈ 𝒜 (i' t))

instance : CoeSort (potionGen S T) (Type _) := ⟨fun T => T.carrier⟩

variable {S T} in
def potionGen.toSubmonoid (T' : potionGen S T) : Submonoid S.Potion :=
  Submonoid.closure
    {x | ∃ (t : T'), x =
      S.equivBarPotion.symm (HomogeneousLocalization.mk
        { deg := T'.i t,
          num := ⟨t.1 ^ (T'.n t : ℕ) * T'.s' t,
            by simpa using SetLike.mul_mem_graded (T'.t_deg t) (T'.s'_deg t)⟩,
          den := ⟨T'.s t, T'.s_deg t⟩,
          den_mem := T'.s_mem_bar t }) }

variable {S T} in
def localizationToPotion (T' : potionGen S T) :
    Localization T'.toSubmonoid →+*
    (S * T).Potion :=
  @IsLocalization.lift
    (R := S.Potion)
    (M :=  _)
    (S :=  _)
    (P := (S * T).Potion)
    (g := S.toMul T) _ _ _ _
    (Localization.isLocalization (R := S.Potion) (M := T'.toSubmonoid)) <| by
    rintro ⟨y, hy⟩
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    refine Submonoid.closure_induction (hx := hy) ?_ ?_ ?_
    · rintro x hx
      simp only [Subtype.exists, Set.mem_setOf_eq] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      let i := T'.i ⟨t, ht⟩
      let i' := T'.i' ⟨t, ht⟩
      let n := T'.n ⟨t, ht⟩
      let s := T'.s ⟨t, ht⟩
      let s' := T'.s' ⟨t, ht⟩
      have s_mem_bar' : s ∈ S.bar := T'.s_mem_bar ⟨t, ht⟩
      have s_mem_bar : s ∈ S.bar := T'.s_mem_bar ⟨t, ht⟩
      have s'_mem_bar' : s' ∈ S.bar := T'.s'_mem_bar ⟨t, ht⟩
      have s'_mem_bar : s' ∈ S.bar := T'.s'_mem_bar ⟨t, ht⟩
      simp only [mem_bar] at s_mem_bar' s'_mem_bar'
      obtain ⟨s_hom, y, hy, dvd⟩ := s_mem_bar'
      obtain ⟨s'_hom, y', hy', dvd'⟩ := s'_mem_bar'
      obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 s_hom (S.2 hy) dvd
      obtain ⟨z', rfl, ⟨j', hj'⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 s'_hom (S.2 hy') dvd'
      have t_deg : (t : A)^(n : ℕ) ∈ 𝒜 (i - i') := T'.t_deg ⟨t, ht⟩
      have s_deg : s ∈ 𝒜 i := T'.s_deg ⟨t, ht⟩
      have s'_deg : s' ∈ 𝒜 i' := T'.s'_deg ⟨t, ht⟩
      change IsUnit <| S.toMul T <| S.equivBarPotion.symm <| .mk ⟨i, ⟨t^(n : ℕ) * s', _⟩, ⟨s, _⟩, _⟩
      rw [equivBarPotion_symm_apply (z_mem := hj) (hz := hy), toMul_mk]
      simp only [eq_mp_eq_cast]
      refine isUnit_of_mul_eq_one _ (.mk ⟨i + j', ⟨s * z', SetLike.mul_mem_graded s_deg hj'⟩,
        ⟨t ^ (n : ℕ) * s' * z',
          SetLike.mul_mem_graded (by simpa using SetLike.mul_mem_graded t_deg s'_deg) hj'⟩,
        ⟨s' * z', hy', t^(n : ℕ), pow_mem (T'.gen ▸ Submonoid.subset_closure ht) _, by ring⟩⟩) ?_
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

variable {S T} in
lemma localizationToPotion_injective (T' : potionGen S T) :
    Function.Injective (localizationToPotion T') := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro x hx
  induction x using Localization.induction_on with | H x =>
  rcases x with ⟨a, b, hb⟩
  have hb' := hb
  rw [potionGen.toSubmonoid, Submonoid.mem_closure_iff] at hb'
  obtain ⟨y, hy, rfl⟩ := hb'
  have hy' := hy
  simp only [Subtype.exists, Set.mem_setOf_eq] at hy'
  choose t ht1 ht2 using hy'
  simp only [eq_mp_eq_cast, Ideal.mem_bot]
  induction a using Quotient.inductionOn' with | h a =>
  rcases a with ⟨j, ⟨num, h_num⟩, ⟨den, h_den⟩, (den_mem : den ∈ S)⟩
  simp only [eq_mp_eq_cast, RingHom.mem_ker] at hx ⊢
  rw [localizationToPotion, Localization.mk_eq_mk', IsLocalization.lift_mk'] at hx
  simp only [toMul_mk, RingHom.toMonoidHom_eq_coe, Units.mul_left_eq_zero] at hx
  rw [HomogeneousLocalization.zero_eq] at hx
  erw [Quotient.eq'] at hx
  simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
    HomogeneousLocalization.NumDenSameDeg.deg_zero, HomogeneousLocalization.NumDenSameDeg.num_zero,
    ZeroMemClass.coe_zero, HomogeneousLocalization.NumDenSameDeg.den_zero] at hx
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hx
  simp only [one_mul, mul_zero, Subtype.exists, mem_toSubmonoid_iff, exists_prop] at hx
  obtain ⟨_, ⟨𝔰, h𝔰, 𝔱, h𝔱, rfl⟩, (eq1 : 𝔰 * 𝔱 * num = 0)⟩ := hx
  rw [← Localization.mk_zero (x := 1), Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  simp only [OneMemClass.coe_one, one_mul, mul_zero, Subtype.exists, exists_prop]
  simp only [← T'.gen, SetLike.mem_coe, Submonoid.mem_closure_iff, exists_prop] at h𝔱
  obtain ⟨d, hd, rfl⟩ := h𝔱
  obtain ⟨i𝔰, 𝔰_deg⟩ := S.2 h𝔰
  refine ⟨∏ t ∈ d.support.attach, S.equivBarPotion.symm (.mk ⟨i𝔰 + T'.i ⟨_, hd _ t.2⟩,
    ⟨𝔰 * (t ^ (T'.n ⟨_, hd _ t.2⟩ : ℕ) * T'.s' ⟨_, hd _ t.2⟩), SetLike.mul_mem_graded 𝔰_deg <| by
      simpa using SetLike.mul_mem_graded (T'.t_deg ⟨_, hd _ t.2⟩) (T'.s'_deg ⟨_, hd _ t.2⟩)⟩,
    ⟨𝔰 * T'.s ⟨_, hd _ t.2⟩, SetLike.mul_mem_graded 𝔰_deg <| T'.s_deg ⟨_, hd _ t.2⟩⟩,
    mul_mem (S.le_bar h𝔰) <| T'.s_mem_bar _⟩) ^ (d t.1), prod_mem fun t ht ↦ by
      refine pow_mem (Submonoid.subset_closure ?_) _
      simp only [Subtype.exists, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq]
      refine ⟨t.1, hd _ t.2, Quotient.sound' <| by
        simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
          Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists, mem_toSubmonoid_iff,
          mem_bar, exists_prop]
        refine ⟨1, ⟨SetLike.homogeneous_one _, 1, one_mem _, by rfl⟩, ?_⟩
        ring⟩, ?_⟩
  change _ * HomogeneousLocalization.mk _ = 0
  rw [show HomogeneousLocalization.mk
    { deg := j, num := ⟨num, h_num⟩, den := ⟨den, h_den⟩, den_mem := den_mem } =
    S.equivBarPotion.symm (.mk ⟨j, ⟨num, h_num⟩, ⟨den, h_den⟩, S.le_bar den_mem⟩) by
    apply_fun S.equivBarPotion
    simp [RingEquiv.apply_symm_apply, equivBarPotion_apply]]
  simp only [← map_pow, ← map_prod, ← map_mul, EmbeddingLike.map_eq_zero_iff]
  simp_rw [← HomogeneousLocalization.mk_pow, HomogeneousLocalization.prod_mk,
    ← HomogeneousLocalization.mk_mul]
  rw [HomogeneousLocalization.zero_eq]
  apply Quotient.sound'
  simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding, eq_mp_eq_cast,
    HomogeneousLocalization.NumDenSameDeg.deg_mul, HomogeneousLocalization.NumDenSameDeg.num_mul,
    HomogeneousLocalization.NumDenSameDeg.num_prod, HomogeneousLocalization.NumDenSameDeg.deg_pow,
    HomogeneousLocalization.NumDenSameDeg.num_pow, HomogeneousLocalization.NumDenSameDeg.den_mul,
    HomogeneousLocalization.NumDenSameDeg.den_prod, HomogeneousLocalization.NumDenSameDeg.den_pow,
    HomogeneousLocalization.NumDenSameDeg.deg_zero, HomogeneousLocalization.NumDenSameDeg.num_zero,
    ZeroMemClass.coe_zero, HomogeneousLocalization.NumDenSameDeg.den_zero,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, one_mul, mul_zero, Subtype.exists,
    mem_toSubmonoid_iff, mem_bar, exists_prop]
  by_cases Hd : d = 0
  · subst Hd
    simp only [Finsupp.prod_zero_index, mul_one, Finsupp.support_zero, Finset.attach_empty,
      Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul] at eq1 ⊢
    exact ⟨𝔰, ⟨S.2 ‹_›, 𝔰, ‹_›, by rfl⟩, eq1⟩


  refine ⟨1, ⟨SetLike.homogeneous_one _, 1, one_mem _, by rfl⟩, ?_⟩
  simp only [one_mul]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]

  simp only [Finsupp.prod] at eq1
  rw [show ∑ i ∈ d.support.attach, d ↑i = ∑ i ∈ d.support, d i by
    conv_rhs => rw [← Finset.sum_attach]]
  have Hd' : 0 < ∑ i ∈ d.support, d i := by
    by_contra! rid
    simp only [nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ne_eq,
      _root_.not_imp_self] at rid
    refine Hd (by ext; exact rid _)

  rw [show ∑ i ∈ d.support, d i = (∑ i ∈ d.support, d i - 1) + 1 from
    Nat.succ_pred_eq_of_pos Hd' |>.symm, pow_add, pow_one]
  simp_rw [← pow_mul]
  rw [show ∏ x ∈ d.support.attach, x.1 ^ (T'.n ⟨_, hd _ x.2⟩ * d x) =
    ∏ x ∈ d.support.attach, (x.1 ^ d x * x.1 ^ ((T'.n ⟨_, hd _ x.2⟩ - 1 : ℕ) * d x)) by
    refine Finset.prod_congr rfl ?_;
    intro x hx
    have : 0 < (T'.n ⟨x, hd _ x.2⟩ : ℕ) := (T'.n ⟨x, hd _ x.2⟩).2
    conv_lhs => rw [show (T'.n ⟨x, hd _ x.2⟩ : ℕ) = (T'.n ⟨x, hd _ x.2⟩ - 1 : ℕ) + 1 from
      Nat.succ_pred_eq_of_pos this |>.symm]
    rw [← pow_add]
    congr 1
    rw [add_mul, one_mul, add_comm], Finset.prod_mul_distrib,
    show (∏ x ∈ d.support.attach, ↑x ^ d ↑x) = ∏ x ∈ d.support, x ^ d x by
      conv_rhs => rw [← Finset.prod_attach],
    show ∀ (a b c d e f : A), a * b * ((c * d) * e) * f = a * ((b * c) * f) * (d * e) by
      intros; ring, eq1]
  simp

variable {S T} in
lemma localizationToPotion_surjective (T' : potionGen S T) :
    Function.Surjective (localizationToPotion T') := by
  intro x
  induction x using Quotient.inductionOn' with | h x =>
  rcases x with ⟨i, ⟨a, ha⟩, ⟨n, h𝔰𝔱⟩, ⟨𝔰, h𝔰, 𝔱, h𝔱, (rfl : 𝔰 * 𝔱 = n)⟩⟩
  by_cases zero_mem : 0 ∈ T
  · use 0
    simp only [map_zero]
    symm
    rw [HomogeneousLocalization.zero_eq]
    refine Quotient.sound' ?_
    rw [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
      HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    simp only [HomogeneousLocalization.NumDenSameDeg.deg_zero,
      HomogeneousLocalization.NumDenSameDeg.den_zero, one_mul,
      HomogeneousLocalization.NumDenSameDeg.num_zero, ZeroMemClass.coe_zero, mul_zero,
      Subtype.exists, mem_toSubmonoid_iff, exists_prop]
    exact ⟨0, ⟨1, one_mem _, 0, zero_mem, by simp⟩, zero_mul _⟩
  simp only [← T'.gen, SetLike.mem_coe, Submonoid.mem_closure_iff, exists_prop] at h𝔱
  obtain ⟨d, hd, rfl⟩ := h𝔱
  by_cases trivial_case : (𝔰 * d.prod fun y i ↦ y ^ i) = 0
  · simp only [trivial_case]
    refine ⟨0, ?_⟩
    simp only [map_zero]
    symm
    exact HomogeneousLocalization.mk_eq_zero_of_den _ rfl


  obtain ⟨i𝔰, 𝔰_deg⟩ := S.2 h𝔰
  have H : ∀ i ∈ d.support, SetLike.Homogeneous 𝒜 i := fun i hi ↦ T.2 <| T'.subset <| hd _ hi
  choose degt hdegt using H
  have h𝔰𝔱' : (𝔰 * d.prod fun y i ↦ y ^ i) ∈ 𝒜 (i𝔰 + ∑ t ∈ d.support.attach, d t • degt _ t.2) := by
    refine SetLike.mul_mem_graded 𝔰_deg ?_
    rw [Finsupp.prod, ← Finset.prod_attach]
    apply SetLike.prod_mem_graded
    rintro ⟨t, ht⟩ -
    apply SetLike.pow_mem_graded
    exact hdegt t ht
  have i_eq := DirectSum.degree_eq_of_mem_mem (ℳ := 𝒜) h𝔰𝔱 h𝔰𝔱' trivial_case

  let num : S.Potion := S.equivBarPotion.symm <| .mk ⟨i𝔰 + ∑ t ∈ d.support.attach, d t • T'.i ⟨_, hd _ t.2⟩,
    ⟨a * ∏ t ∈ d.support.attach,
      (T'.s' ⟨_, hd _ t.2⟩ ^ d t) * (t.1 ^ (d t • (T'.n ⟨_, hd _ t.2⟩ - 1 : ℕ))), by
      rw [Finset.prod_mul_distrib]
      by_cases triv : ∏ t ∈ d.support.attach, t.1 ^ (d t • (T'.n ⟨_, hd _ t.2⟩ - 1 : ℕ)) = 0
      · rw [triv]
        simp
      have non_triv (t : d.support) :  t.1 ^ (d t • (T'.n ⟨_, hd _ t.2⟩ - 1 : ℕ)) ≠ 0 := by
        contrapose! triv
        fapply Finset.prod_eq_zero (i := t) (by aesop) triv
      have mem1 : ∏ t ∈ d.support.attach, t.1 ^ (d t • (T'.n ⟨_, hd _ t.2⟩ - 1 : ℕ)) ∈
        𝒜 (∑ t ∈ d.support.attach, d t • (T'.n ⟨_, hd _ t.2⟩ - 1 : ℕ) • degt _ t.2) := by
        apply SetLike.prod_mem_graded
        rintro ⟨t, ht⟩ -
        rw [← smul_assoc]
        exact SetLike.pow_mem_graded (d t • (T'.n ⟨_, hd _ ht⟩ - 1 : ℕ)) (hdegt t ht)


      have mem2 : ∏ t ∈ d.support.attach, (T'.s' ⟨_, hd _ t.2⟩ ^ d t) ∈ 𝒜 (∑ t ∈ d.support.attach,
        d t • T'.i' ⟨_, hd _ t.2⟩) := by
        apply SetLike.prod_mem_graded
        rintro ⟨t, ht⟩ -
        apply SetLike.pow_mem_graded
        exact T'.s'_deg ⟨_, hd _ ht⟩
      have := SetLike.mul_mem_graded ha (SetLike.mul_mem_graded mem2 mem1)
      convert this using 2
      rw [show ∑ t ∈ d.support.attach, d t • (T'.n ⟨_, hd _ t.2⟩ - 1 : ℕ) • degt _ t.2 =
        ∑ t ∈ d.support.attach, d t  • (T'.n ⟨_, hd _ t.2⟩: ℕ) • degt _ t.2 -
        ∑ t ∈ d.support.attach, d t • degt _ t.2 by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        rintro ⟨t, ht⟩ -
        rw [← smul_assoc, ← smul_assoc]
        simp only [smul_eq_mul, Nat.mul_sub, mul_one]
        rw [sub_nsmul, ← sub_eq_add_neg]
        have : 0 < (T'.n ⟨_, hd _ ht⟩: ℕ) := T'.n ⟨_, hd _ ht⟩ |>.2
        apply Nat.le_mul_of_pos_right
        exact this]
      rw [i_eq]
      simp only [add_assoc, add_right_inj]
      rw [show ∀ (a b c d : ι), a + (b + (c - d)) = (b + c + (a - d)) by intros; abel]
      simp only [sub_self, add_zero]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      rintro ⟨t, ht⟩ -
      rw [← smul_add]
      have mem1 := SetLike.pow_mem_graded (d t) (T'.t_deg ⟨_, hd _ ht⟩)
      simp only [← pow_mul] at mem1
      have ne_zero1 :  t ^ (T'.n ⟨t, hd _ ht⟩ * d t: ℕ) ≠ 0 := by
        contrapose! zero_mem
        rw [← zero_mem]
        apply pow_mem
        refine T'.subset <| hd _ ht
      have mem3 : t ^ (T'.n ⟨t, hd _ ht⟩ * d t : ℕ) ∈
        𝒜 ((T'.n ⟨t, hd _ ht⟩ * d t : ℕ) • degt _ ht) := by
        apply SetLike.pow_mem_graded
        exact hdegt t ht
      have eq' := DirectSum.degree_eq_of_mem_mem (ℳ := 𝒜) mem1 mem3 ne_zero1
      simp only [smul_sub, sub_eq_iff_eq_add, smul_add] at eq' ⊢
      rw [eq']
      rw [mul_smul, add_comm, smul_comm]⟩,
    ⟨𝔰 * ∏ t ∈ d.support.attach, T'.s ⟨_, hd _ t.2⟩ ^ (d t), SetLike.mul_mem_graded 𝔰_deg <| by
      apply SetLike.prod_mem_graded
      rintro ⟨t, ht⟩ -
      simp only
      apply SetLike.pow_mem_graded
      exact T'.s_deg ⟨_, hd _ ht⟩⟩, mul_mem (S.le_bar ‹_›) <| prod_mem <| by
      rintro ⟨t, ht⟩ -
      apply pow_mem
      exact T'.s_mem_bar ⟨_, hd _ ht⟩⟩
  let den : T'.toSubmonoid :=
    ⟨S.equivBarPotion.symm (∏ t ∈ d.support.attach, .mk ⟨T'.i ⟨_, hd _ t.2⟩,
      ⟨t ^ (T'.n ⟨_, hd _ t.2⟩ : ℕ) * T'.s' ⟨_, hd _ t.2⟩,
        by simpa using SetLike.mul_mem_graded (T'.t_deg ⟨_, hd _ t.2⟩) (T'.s'_deg ⟨_, hd _ t.2⟩)⟩,
      ⟨T'.s ⟨_, hd _ t.2⟩, T'.s_deg _⟩,
      T'.s_mem_bar _⟩ ^ (d t)), ?_⟩
  swap
  · simp only [map_prod, map_pow]
    apply prod_mem
    rintro ⟨t, ht⟩ -
    have := T'.s_mem_bar ⟨_, hd _ ht⟩
    simp only [mem_bar] at this
    obtain ⟨hom, y, hy, dvd⟩ := this
    obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 hom (S.2 hy) dvd
    rw [equivBarPotion_symm_apply (z_mem := hj) (hz := hy)]
    simp only
    apply pow_mem
    refine Submonoid.subset_closure ?_
    simp only [Subtype.exists, Set.mem_setOf_eq]
    refine ⟨t, hd _ ht, ?_⟩
    apply_fun S.equivBarPotion
    simp only [equivBarPotion_apply, toBarPotion_mk, eq_mp_eq_cast, RingEquiv.apply_symm_apply]
    apply Quotient.sound'
    simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists, mem_toSubmonoid_iff,
      mem_bar, exists_prop]
    refine ⟨1, ⟨SetLike.homogeneous_one _, 1, one_mem _, by rfl⟩, by ring⟩
  let X : Localization T'.toSubmonoid := .mk num den
  use X
  simp only [localizationToPotion, Localization.mk_eq_mk', IsLocalization.lift_mk',
    RingHom.toMonoidHom_eq_coe, X]
  rw [Units.mul_inv_eq_iff_eq_mul]
  rw [IsUnit.coe_liftRight]
  simp only [smul_eq_mul, toMul_equivBarPotion_symm, id_eq, eq_mpr_eq_cast, ne_eq, Int.reduceNeg,
    eq_mp_eq_cast, map_prod, map_pow, MonoidHom.restrict_apply, MonoidHom.coe_coe, num, den, X]
  apply_fun (S * T).equivBarPotion
  simp only [RingEquiv.apply_symm_apply, map_mul, equivBarPotion_apply, toBarPotion_mk, map_prod,
    map_pow, ← HomogeneousLocalization.mk_pow, HomogeneousLocalization.prod_mk, num, den, X]
  apply Quotient.sound'
  rw [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
    HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  simp only [eq_mp_eq_cast, HomogeneousLocalization.NumDenSameDeg.deg_mul,
    HomogeneousLocalization.NumDenSameDeg.den_mul, HomogeneousLocalization.NumDenSameDeg.den_prod,
    HomogeneousLocalization.NumDenSameDeg.deg_pow, HomogeneousLocalization.NumDenSameDeg.den_pow,
    HomogeneousLocalization.NumDenSameDeg.num_mul, HomogeneousLocalization.NumDenSameDeg.num_prod,
    HomogeneousLocalization.NumDenSameDeg.num_pow, Subtype.exists, mem_toSubmonoid_iff, mem_bar,
    exists_prop, num, den, X]
  refine ⟨1, ⟨SetLike.homogeneous_one _, 1, one_mem _, by rfl⟩, ?_⟩
  simp only [Finsupp.prod,
    show (∏ x ∈ d.support, x ^ d x) = ∏ x ∈ d.support.attach, x.1 ^ d x by
      conv_lhs => rw [← Finset.prod_attach],
    one_mul, num, den, X]
  conv_lhs => rw [show ∀ (a b c d e : A), ((a * b) * c) * (d * e) = (a * d) * (b * c * e) by intros; ring]
  conv_rhs => rw [show ∀ (a b c d : A), (a * b) * (c * d) = (a * c) * (b * d) by intros; ring]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  rintro ⟨t, ht⟩ -
  simp only [num, den, X]
  conv_rhs => rw [show (T'.n ⟨t, hd _ ht⟩ : ℕ) = (T'.n ⟨t, hd _ ht⟩ - 1 + 1 : ℕ) from
    Nat.succ_pred_eq_of_pos (T'.n ⟨t, hd _ ht⟩).2 |>.symm]
  ring

variable {S T} in
def localizationRingEquivPotion (T' : potionGen S T) :
    Localization T'.toSubmonoid ≃+* (S * T).Potion :=
  RingEquiv.ofBijective (localizationToPotion T')
    ⟨localizationToPotion_injective T', localizationToPotion_surjective T'⟩

variable {S T} in
def localizationAlgEquivPotion (T' : potionGen S T) :
    Localization T'.toSubmonoid ≃ₐ[S.Potion] (S * T).Potion :=
  AlgEquiv.ofRingEquiv (f := localizationRingEquivPotion T') fun x ↦ by
    simp only [localizationRingEquivPotion, ← Localization.mk_one_eq_algebraMap,
      RingEquiv.coe_ofBijective, mul_potion_algebraMap_eq]
    induction x using Quotient.inductionOn' with | h x =>
    simp [localizationToPotion, Localization.mk_eq_mk', IsLocalization.lift_mk']

instance (T' : potionGen S T) : IsLocalization (T'.toSubmonoid) (S * T).Potion :=
  IsLocalization.isLocalization_of_algEquiv (T'.toSubmonoid) (localizationAlgEquivPotion T')

end HomogeneousSubmonoid
