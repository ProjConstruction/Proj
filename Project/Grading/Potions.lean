import Project.Grading.HomogeneousSubmonoid
import Project.Grading.IsoBar

import Project.ForMathlib.HomogeneousLocalization

import Project.ForMathlib.LocalizationAway

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks

suppress_compilation

namespace HomogeneousSubmonoid

variable {ι R A : Type*}
variable [AddCommGroup ι] [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]
variable (S T : HomogeneousSubmonoid 𝒜)

abbrev Potion := HomogeneousLocalization 𝒜 S.toSubmonoid

def potionEquiv {S T : HomogeneousSubmonoid 𝒜} (eq : S = T) : S.Potion ≃+* T.Potion :=
  RingEquiv.ofHomInv
    (HomogeneousLocalization.map _ _ (RingHom.id _)
      (by subst eq; erw [Submonoid.comap_id])
      (by simp) : S.Potion →+* T.Potion)
    (HomogeneousLocalization.map _ _ (RingHom.id _)
      (by subst eq; erw [Submonoid.comap_id])
      (by simp) : T.Potion →+* S.Potion)
    (by
      ext x
      induction x using Quotient.inductionOn' with | h x =>
      simp [← show HomogeneousLocalization.mk x = Quotient.mk'' x by rfl,
        HomogeneousLocalization.map_mk])
    (by
      ext x
      induction x using Quotient.inductionOn' with | h x =>
      simp [← show HomogeneousLocalization.mk x = Quotient.mk'' x by rfl,
        HomogeneousLocalization.map_mk])

@[simp]
lemma potionEquiv_refl : S.potionEquiv rfl = RingEquiv.refl S.Potion := by
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  simp [← show HomogeneousLocalization.mk x = Quotient.mk'' x by rfl,
    HomogeneousLocalization.map_mk, potionEquiv]

@[simp high]
lemma potionEquiv_refl_apply (x) : S.potionEquiv rfl x = x := by
  simp

@[simp]
lemma potionEquiv_trans {R S T : HomogeneousSubmonoid 𝒜} (eq1 : R = S) (eq2 : S = T) :
    (R.potionEquiv eq1).trans (S.potionEquiv eq2) = R.potionEquiv (eq1.trans eq2) := by
  subst eq1 eq2
  simp only [potionEquiv_refl]
  rfl

@[simp]
lemma potionEquiv_trans_apply {R S T : HomogeneousSubmonoid 𝒜} (eq1 : R = S) (eq2 : S = T) (x) :
    S.potionEquiv eq2 (R.potionEquiv eq1 x) =
    R.potionEquiv (eq1.trans eq2) x :=
  congr($(potionEquiv_trans eq1 eq2) x)

def potionToMul : S.Potion →+* (S * T).Potion :=
  HomogeneousLocalization.map _ _ (RingHom.id _) (by
    erw [Submonoid.comap_id, ← le_iff]
    exact left_le_mul ..) fun i a hi ↦ hi

def potionToMulSelf : S.Potion ≃+* (S * S).Potion :=
  potionEquiv (by simp)

@[simp]
lemma toMul_mk (x) : S.potionToMul T (.mk x) = .mk ⟨x.deg, x.num, x.den, left_le_mul _ _ x.den_mem⟩ := rfl

instance : Algebra S.Potion (S * T).Potion := RingHom.toAlgebra (potionToMul S T)

@[simp]
lemma mul_potion_algebraMap_eq : (algebraMap S.Potion (S * T).Potion) = S.potionToMul T := rfl

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
    S.potionToMul T (S.equivBarPotion.symm <| .mk x) =
    (S * T).equivBarPotion.symm (.mk
      { deg := x.deg
        num := x.num
        den := x.den
        den_mem := bar_mono _ _ (left_le_mul S T) x.den_mem }) := by
  rcases x with ⟨i, ⟨m, hm⟩, ⟨n, hn⟩, hn'⟩
  simp only [mem_toSubmonoid_iff, mem_bar] at hn'
  obtain ⟨hn', y, hy, dvd⟩ := hn'
  obtain ⟨z, rfl, ⟨j, hz⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 hn'
    (S.homogeneous hy) dvd
  rw [equivBarPotion_symm_apply (z_mem := hz) (hz := hy), toMul_mk]
  simp only
  rw [equivBarPotion_symm_apply (z_mem := hz) (hz := left_le_mul S T hy)]

instance : Algebra S.Potion S.bar.Potion :=
  RingHom.toAlgebra S.equivBarPotion

@[simp]
lemma bar_potion_algebraMap_eq : (algebraMap S.Potion S.bar.Potion) = S.equivBarPotion := rfl

structure PotionGen where
  (index : Type*)
  (elem : index → A)
  (elem_mem : ∀ t, elem t ∈ T)
  (gen : Submonoid.closure (Set.range elem) = T.toSubmonoid)
  (n : index → ℕ+)
  (s s' : index → A)
  (s_mem_bar : ∀ t, s t ∈ S.bar)
  (s'_mem_bar : ∀ t, s' t ∈ S.bar)
  (i i' : index → ι)
  (t_deg : ∀ t : index, (elem t : A)^(n t : ℕ) ∈ 𝒜 (i t - i' t))
  (s_deg : ∀ t, s t ∈ 𝒜 (i t))
  (s'_deg : ∀ t, s' t ∈ 𝒜 (i' t))

-- instance : CoeSort (PotionGen S T) (Type _) := ⟨fun T => T.carrier⟩

variable {S T} in
def PotionGen.genSubmonoid (T' : PotionGen S T) : Submonoid S.Potion :=
  Submonoid.closure
    {x | ∃ (t : T'.index), x =
      S.equivBarPotion.symm (HomogeneousLocalization.mk
        { deg := T'.i t,
          num := ⟨(T'.elem t) ^ (T'.n t : ℕ) * T'.s' t,
            by simpa using SetLike.mul_mem_graded (T'.t_deg t) (T'.s'_deg t)⟩,
          den := ⟨T'.s t, T'.s_deg t⟩,
          den_mem := T'.s_mem_bar t }) }

variable {S T} in
def localizationToPotion (T' : PotionGen S T) :
    Localization T'.genSubmonoid →+*
    (S * T).Potion :=
  @IsLocalization.lift
    (R := S.Potion)
    (M :=  _)
    (S :=  _)
    (P := (S * T).Potion)
    (g := S.potionToMul T) _ _ _ _
    (Localization.isLocalization (R := S.Potion) (M := T'.genSubmonoid)) <| by
    rintro ⟨y, hy⟩
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    refine Submonoid.closure_induction (hx := hy) ?_ ?_ ?_
    · rintro x hx
      simp only [Subtype.exists, Set.mem_setOf_eq] at hx
      obtain ⟨t, rfl⟩ := hx
      let i := T'.i t
      let i' := T'.i' t
      let n := T'.n t
      let s := T'.s t
      let s' := T'.s' t
      have s_mem_bar' : s ∈ S.bar := T'.s_mem_bar t
      have s_mem_bar : s ∈ S.bar := T'.s_mem_bar t
      have s'_mem_bar' : s' ∈ S.bar := T'.s'_mem_bar t
      have s'_mem_bar : s' ∈ S.bar := T'.s'_mem_bar t
      simp only [mem_bar] at s_mem_bar' s'_mem_bar'
      obtain ⟨s_hom, y, hy, dvd⟩ := s_mem_bar'
      obtain ⟨s'_hom, y', hy', dvd'⟩ := s'_mem_bar'
      obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 s_hom (S.2 hy) dvd
      obtain ⟨z', rfl, ⟨j', hj'⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 s'_hom (S.2 hy') dvd'
      have t_deg : (T'.elem t : A)^(n : ℕ) ∈ 𝒜 (i - i') := T'.t_deg t
      have s_deg : s ∈ 𝒜 i := T'.s_deg t
      have s'_deg : s' ∈ 𝒜 i' := T'.s'_deg t
      change IsUnit <| S.potionToMul T <| S.equivBarPotion.symm <| .mk ⟨i, ⟨T'.elem t^(n : ℕ) * s', _⟩, ⟨s, _⟩, _⟩
      rw [equivBarPotion_symm_apply (z_mem := hj) (hz := hy), toMul_mk]
      simp only [eq_mp_eq_cast]
      refine isUnit_of_mul_eq_one _ (.mk ⟨i + j', ⟨s * z', SetLike.mul_mem_graded s_deg hj'⟩,
        ⟨T'.elem t ^ (n : ℕ) * s' * z',
          SetLike.mul_mem_graded (by simpa using SetLike.mul_mem_graded t_deg s'_deg) hj'⟩,
        ⟨s' * z', hy', T'.elem t^(n : ℕ), pow_mem (T'.gen ▸ Submonoid.subset_closure
          (Set.mem_range_self _)) _, by ring⟩⟩) ?_
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
lemma localizationToPotion_injective (T' : PotionGen S T) :
    Function.Injective (localizationToPotion T') := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro x hx
  induction x using Localization.induction_on with | H x =>
  rcases x with ⟨a, b, hb⟩
  have hb' := hb
  rw [PotionGen.genSubmonoid, Submonoid.mem_closure_iff] at hb'
  obtain ⟨y, hy, rfl⟩ := hb'
  have hy' := hy
  simp only [Subtype.exists, Set.mem_setOf_eq] at hy'
  choose t ht1 using hy'
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
  choose i hi using hd
  obtain ⟨i𝔰, 𝔰_deg⟩ := S.2 h𝔰
  refine ⟨∏ t ∈ d.support.attach, S.equivBarPotion.symm (.mk ⟨i𝔰 + T'.i (i _ t.2),
    ⟨𝔰 * (t ^ (T'.n (i _ t.2) : ℕ) * T'.s' (i _ t.2)), SetLike.mul_mem_graded 𝔰_deg <| by
      have := SetLike.mul_mem_graded (T'.t_deg (i _ t.2)) (T'.s'_deg (i _ t.2))
      simp only [sub_add_cancel, hi] at this
      exact this⟩,
    ⟨𝔰 * T'.s (i _ t.2), SetLike.mul_mem_graded 𝔰_deg <| T'.s_deg (i _ t.2)⟩,
    mul_mem (S.le_bar h𝔰) <| T'.s_mem_bar _⟩) ^ (d t.1), prod_mem fun t ht ↦ by
      refine pow_mem (Submonoid.subset_closure ?_) _
      simp only [Subtype.exists, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq]
      refine ⟨i _ t.2, Quotient.sound' <| by
        simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
          Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists, mem_toSubmonoid_iff,
          mem_bar, exists_prop]
        refine ⟨1, ⟨SetLike.homogeneous_one _, 1, one_mem _, by rfl⟩, ?_⟩
        simp only [one_mul, hi]
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
  rw [show ∏ x ∈ d.support.attach, x.1 ^ (T'.n (i _ x.2) * d x) =
    ∏ x ∈ d.support.attach, (x.1 ^ d x * x.1 ^ ((T'.n (i _ x.2) - 1 : ℕ) * d x)) by
    refine Finset.prod_congr rfl ?_;
    intro x hx
    have : 0 < (T'.n (i _ x.2) : ℕ) := (T'.n (i _ x.2)).2
    conv_lhs => rw [show (T'.n (i _ x.2) : ℕ) = (T'.n (i _ x.2) - 1 : ℕ) + 1 from
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
lemma localizationToPotion_surjective (T' : PotionGen S T) :
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
  choose x hx using hd
  have H : ∀ i ∈ d.support, SetLike.Homogeneous 𝒜 i := fun i hi ↦ T.2 <| by
    simpa [hx] using T'.elem_mem <| (x _ hi)
  choose degt hdegt using H
  have h𝔰𝔱' : (𝔰 * d.prod fun y i ↦ y ^ i) ∈ 𝒜 (i𝔰 + ∑ t ∈ d.support.attach, d t • degt _ t.2) := by
    refine SetLike.mul_mem_graded 𝔰_deg ?_
    rw [Finsupp.prod, ← Finset.prod_attach]
    apply SetLike.prod_mem_graded
    rintro ⟨t, ht⟩ -
    apply SetLike.pow_mem_graded
    exact hdegt t ht
  have i_eq := DirectSum.degree_eq_of_mem_mem (ℳ := 𝒜) h𝔰𝔱 h𝔰𝔱' trivial_case

  let num : S.Potion := S.equivBarPotion.symm <| .mk ⟨i𝔰 + ∑ t ∈ d.support.attach, d t • T'.i (x _ t.2),
    ⟨a * ∏ t ∈ d.support.attach,
      (T'.s' (x _ t.2) ^ d t) * (t.1 ^ (d t • (T'.n (x _ t.2) - 1 : ℕ))), by
      rw [Finset.prod_mul_distrib]
      by_cases triv : ∏ t ∈ d.support.attach, t.1 ^ (d t • (T'.n (x _ t.2) - 1 : ℕ)) = 0
      · rw [triv]
        simp
      have non_triv (t : d.support) :  t.1 ^ (d t • (T'.n (x _ t.2) - 1 : ℕ)) ≠ 0 := by
        contrapose! triv
        fapply Finset.prod_eq_zero (i := t) (by aesop) triv
      have mem1 : ∏ t ∈ d.support.attach, t.1 ^ (d t • (T'.n (x _ t.2) - 1 : ℕ)) ∈
        𝒜 (∑ t ∈ d.support.attach, d t • (T'.n (x _ t.2) - 1 : ℕ) • degt _ t.2) := by
        apply SetLike.prod_mem_graded
        rintro ⟨t, ht⟩ -
        rw [← smul_assoc]
        exact SetLike.pow_mem_graded (d t • (T'.n (x _ ht) - 1 : ℕ)) (hdegt t ht)


      have mem2 : ∏ t ∈ d.support.attach, (T'.s' (x _ t.2) ^ d t) ∈ 𝒜 (∑ t ∈ d.support.attach,
        d t • T'.i' (x _ t.2)) := by
        apply SetLike.prod_mem_graded
        rintro ⟨t, ht⟩ -
        apply SetLike.pow_mem_graded
        exact T'.s'_deg (x _ ht)
      have := SetLike.mul_mem_graded ha (SetLike.mul_mem_graded mem2 mem1)
      convert this using 2
      rw [show ∑ t ∈ d.support.attach, d t • (T'.n (x _ t.2) - 1 : ℕ) • degt _ t.2 =
        ∑ t ∈ d.support.attach, d t  • (T'.n (x _ t.2) : ℕ) • degt _ t.2 -
        ∑ t ∈ d.support.attach, d t • degt _ t.2 by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        rintro ⟨t, ht⟩ -
        rw [← smul_assoc, ← smul_assoc]
        simp only [smul_eq_mul, Nat.mul_sub, mul_one]
        rw [sub_nsmul, ← sub_eq_add_neg]
        have : 0 < (T'.n (x _ ht): ℕ) := T'.n (x _ ht) |>.2
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
      have mem1 := SetLike.pow_mem_graded (d t) (T'.t_deg (x _ ht))
      simp only [← pow_mul] at mem1
      have ne_zero1 :  t ^ (T'.n (x _ ht) * d t: ℕ) ≠ 0 := by
        contrapose! zero_mem
        rw [← zero_mem]
        apply pow_mem
        simpa [hx] using T'.elem_mem (x _ ht)
      have mem3 : t ^ (T'.n (x _ ht) * d t : ℕ) ∈
        𝒜 ((T'.n (x _ ht) * d t : ℕ) • degt _ ht) := by
        apply SetLike.pow_mem_graded
        exact hdegt t ht
      simp only [hx] at mem1
      have eq' := DirectSum.degree_eq_of_mem_mem (ℳ := 𝒜) mem1 mem3 ne_zero1
      simp only [smul_sub, sub_eq_iff_eq_add, smul_add] at eq' ⊢
      rw [eq']
      rw [mul_smul, add_comm, smul_comm]⟩,
    ⟨𝔰 * ∏ t ∈ d.support.attach, T'.s (x _ t.2) ^ (d t), SetLike.mul_mem_graded 𝔰_deg <| by
      apply SetLike.prod_mem_graded
      rintro ⟨t, ht⟩ -
      simp only
      apply SetLike.pow_mem_graded
      exact T'.s_deg (x _ ht)⟩, mul_mem (S.le_bar ‹_›) <| prod_mem <| by
      rintro ⟨t, ht⟩ -
      apply pow_mem
      exact T'.s_mem_bar (x _ ht)⟩
  let den : T'.genSubmonoid :=
    ⟨S.equivBarPotion.symm (∏ t ∈ d.support.attach, .mk ⟨T'.i (x _ t.2),
      ⟨t ^ (T'.n (x _ t.2) : ℕ) * T'.s' (x _ t.2),
        by simpa [hx] using SetLike.mul_mem_graded (T'.t_deg (x _ t.2)) (T'.s'_deg (x _ t.2))⟩,
      ⟨T'.s (x _ t.2), T'.s_deg _⟩,
      T'.s_mem_bar _⟩ ^ (d t)), ?_⟩
  swap
  · simp only [map_prod, map_pow]
    apply prod_mem
    rintro ⟨t, ht⟩ -
    have := T'.s_mem_bar (x _ ht)
    simp only [mem_bar] at this
    obtain ⟨hom, y, hy, dvd⟩ := this
    obtain ⟨z, rfl, ⟨j, hj⟩⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜 hom (S.2 hy) dvd
    rw [equivBarPotion_symm_apply (z_mem := hj) (hz := hy)]
    simp only
    apply pow_mem
    refine Submonoid.subset_closure ?_
    simp only [Subtype.exists, Set.mem_setOf_eq]
    refine ⟨x _ ht, ?_⟩
    apply_fun S.equivBarPotion
    simp only [equivBarPotion_apply, toBarPotion_mk, eq_mp_eq_cast, RingEquiv.apply_symm_apply]
    apply Quotient.sound'
    simp only [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists, mem_toSubmonoid_iff,
      mem_bar, exists_prop]
    refine ⟨1, ⟨SetLike.homogeneous_one _, 1, one_mem _, by rfl⟩, by
      simp only [one_mul, hx]; ring⟩
  let X : Localization T'.genSubmonoid := .mk num den
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
  conv_rhs => rw [show (T'.n (x _ ht) : ℕ) = (T'.n (x _ ht) - 1 + 1 : ℕ) from
    Nat.succ_pred_eq_of_pos (T'.n (x _ ht)).2 |>.symm]
  ring

variable {S T} in
def localizationRingEquivPotion (T' : PotionGen S T) :
    Localization T'.genSubmonoid ≃+* (S * T).Potion :=
  RingEquiv.ofBijective (localizationToPotion T')
    ⟨localizationToPotion_injective T', localizationToPotion_surjective T'⟩

variable {S T} in
@[simp]
lemma localizationRingEquivPotion_apply (T' : PotionGen S T) (x) :
    localizationRingEquivPotion T' x = localizationToPotion T' x := rfl

variable {S T} in
def localizationAlgEquivPotion (T' : PotionGen S T) :
    Localization T'.genSubmonoid ≃ₐ[S.Potion] (S * T).Potion :=
  AlgEquiv.ofRingEquiv (f := localizationRingEquivPotion T') fun x ↦ by
    simp only [localizationRingEquivPotion, ← Localization.mk_one_eq_algebraMap,
      RingEquiv.coe_ofBijective, mul_potion_algebraMap_eq]
    induction x using Quotient.inductionOn' with | h x =>
    simp [localizationToPotion, Localization.mk_eq_mk', IsLocalization.lift_mk']

instance (T' : PotionGen S T) : IsLocalization (T'.genSubmonoid) (S * T).Potion :=
  IsLocalization.isLocalization_of_algEquiv (T'.genSubmonoid) (localizationAlgEquivPotion T')

variable {S} in
lemma finite_potionGen_exists_aux₁ (S_rel : IsRelevant S) (t : A) (m : ι) (ht : t ∈ 𝒜 m) : ∃ (n : ℕ+) (s s' : A) (i i' : ι),
    t^(n : ℕ) ∈ 𝒜 (i - i') ∧ s ∈ 𝒜 i ∧ s' ∈ 𝒜 i' ∧ s ∈ S.bar ∧ s' ∈ S.bar := by
  obtain ⟨n, n_pos, hm⟩ := S_rel m
  delta agrDeg at hm
  rw [← SetLike.mem_coe] at hm
  rw [AddSubgroup.closure_addSubmonoid (N := S.bar.deg)] at hm
  obtain ⟨⟨i, ⟨s, hs₁, hs₂⟩⟩, ⟨i', ⟨s', hs'₁, hs'₂⟩⟩, (hii' : _ = i + -i')⟩ := hm
  refine ⟨⟨n, n_pos⟩, s, s', i, i', ?_, hs₂, hs'₂, hs₁, hs'₁⟩
  have ht' : t ^ n ∈ 𝒜 (n • m) := SetLike.pow_mem_graded _ ‹_›
  rw [hii'] at ht'
  rw [← sub_eq_add_neg] at ht'
  simpa

variable {S} in
lemma finite_potionGen_exists_aux₂ (S_rel : IsRelevant S) (t : A) (ht : SetLike.Homogeneous 𝒜 t) :
  ∃ (n : ℕ+) (s s' : A) (i i' : ι),
    t^(n : ℕ) ∈ 𝒜 (i - i') ∧ s ∈ 𝒜 i ∧ s' ∈ 𝒜 i' ∧ s ∈ S.bar ∧ s' ∈ S.bar :=
  finite_potionGen_exists_aux₁ S_rel t ht.choose ht.choose_spec

variable {S T} in
def finitePotionGen (S_rel : IsRelevant S) (T_fg : T.FG) : PotionGen S T :=
  let carrier := T_fg.choose
  let subset : (carrier : Set _) ⊆ T.carrier := by
      intro x hx
      have := T_fg.choose_spec ▸ Submonoid.subset_closure hx
      exact this
  let gen : Submonoid.closure carrier = T.toSubmonoid := T_fg.choose_spec
  let n : carrier → ℕ+ := fun t ↦ (finite_potionGen_exists_aux₂ S_rel t <| T.2 <| subset t.2).choose
  let s : carrier → A :=
    fun t ↦ (finite_potionGen_exists_aux₂ S_rel t <| T.2 <| subset t.2).choose_spec.choose
  let s' : carrier → A := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <| subset t.2).choose_spec.choose_spec.choose
  let i : carrier → ι := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose
  let i' : carrier → ι := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose
  let t_deg : ∀ (x : carrier), x.1 ^ (n x : ℕ) ∈ 𝒜 (i x - i' x) := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  let s_deg : ∀ (x : carrier), s x ∈ 𝒜 (i x) := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let s'_deg : ∀ (x : carrier), s' x ∈ 𝒜 (i' x) := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
  let s_mem_bar : ∀ (x : carrier), s x ∈ S.bar := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
  let s'_mem_bar : ∀ (x : carrier), s' x ∈ S.bar := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.2 <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2
  {
    index := carrier
    elem := Subtype.val
    elem_mem := by simpa
    gen := by simpa
    n := n
    s := s
    s' := s'
    s_mem_bar := s_mem_bar
    s'_mem_bar := s'_mem_bar
    i := i
    i' := i'
    t_deg := t_deg
    s_deg := s_deg
    s'_deg := s'_deg
  }

variable {S T} in
lemma finitePotionGen_finite (S_rel : IsRelevant S) (T_fg : T.FG)  :
  Finite (finitePotionGen S_rel T_fg).index := T_fg.choose.finite_toSet

def PotionGen.disjUnion {R S T : HomogeneousSubmonoid 𝒜} (R' : PotionGen S R) (T' : PotionGen S T) :
    PotionGen S (R * T) where
  index := R'.index ⊕ T'.index
  elem := Sum.rec R'.elem T'.elem
  elem_mem := by
    rintro (x|x)
    · simp only [SetLike.mem_coe]
      exact left_le_mul _ _ <| R'.elem_mem x
    · simp only
      exact right_le_mul _ _ <| T'.elem_mem x

  gen := by
    rw [mul_toSubmonoid, ← R'.gen, ← T'.gen, ← Submonoid.closure_union_eq_mul]
    refine le_antisymm ?_ ?_ <;> rw [Submonoid.closure_le]

    · rintro _ ⟨(x|x), rfl⟩
      · exact Submonoid.subset_closure <| Or.inl <| (by simp)
      · exact Submonoid.subset_closure <| Or.inr <| (by simp)
    · rintro _ (⟨x, rfl⟩|⟨x, rfl⟩)
      · exact Submonoid.subset_closure (by simp)
      · exact Submonoid.subset_closure (by simp)
  n := Sum.rec R'.n T'.n
  s := Sum.rec R'.s T'.s
  s' := Sum.rec R'.s' T'.s'
  s_mem_bar := Sum.rec R'.s_mem_bar T'.s_mem_bar
  s'_mem_bar := Sum.rec R'.s'_mem_bar T'.s'_mem_bar
  i := Sum.rec R'.i T'.i
  i' := Sum.rec R'.i' T'.i'
  t_deg := Sum.rec R'.t_deg T'.t_deg
  s_deg := Sum.rec R'.s_deg T'.s_deg
  s'_deg := Sum.rec R'.s'_deg T'.s'_deg

lemma PotionGen.disjUnion_genSubmonoid {R S T : HomogeneousSubmonoid 𝒜}
      (R' : PotionGen S R) (T' : PotionGen S T) :
    (R'.disjUnion T').genSubmonoid = R'.genSubmonoid * T'.genSubmonoid := by
  simp only [genSubmonoid]
  rw [← Submonoid.closure_union_eq_mul]
  refine le_antisymm ?_ ?_
  · rw [Submonoid.closure_le]
    rintro _ ⟨(t|t), rfl⟩
    · exact Submonoid.subset_closure <| Or.inl ⟨t, rfl⟩
    · exact Submonoid.subset_closure <| Or.inr ⟨t, rfl⟩
  · rw [Submonoid.closure_le]
    rintro _ (⟨t, rfl⟩|⟨t, rfl⟩)
    · exact Submonoid.subset_closure ⟨Sum.inl t, rfl⟩
    · exact Submonoid.subset_closure ⟨Sum.inr t, rfl⟩

open AlgebraicGeometry
lemma IsOpenImmersion.of_isRelevant_FG (S_rel : IsRelevant S) (T_fg : T.FG) :
    IsOpenImmersion <| Spec.map <| CommRingCat.ofHom (S.potionToMul T) := by
  classical
  let T' : PotionGen S T := finitePotionGen S_rel T_fg
  have eq : S.potionToMul T =
    RingHom.comp (localizationRingEquivPotion T')
      (algebraMap S.Potion (Localization T'.genSubmonoid)) := by
    ext x
    induction x using Quotient.inductionOn' with | h x =>
    simp [← Localization.mk_one_eq_algebraMap, localizationToPotion, Localization.mk_eq_mk',
      IsLocalization.lift_mk']
  rw [eq]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp]
  apply (config := {allowSynthFailures := true}) IsOpenImmersion.comp
  · rw [show (CommRingCat.ofHom (localizationRingEquivPotion T') :
      CommRingCat.of (Localization T'.genSubmonoid) ⟶ CommRingCat.of (S * T).Potion) =
      (localizationRingEquivPotion T').toCommRingCatIso.hom by rfl]
    apply IsOpenImmersion.of_isIso
  apply AlgebraicGeometry.IsOpenImmersion.of_map_localization_finite_closure
  set lhs := _
  change Set.Finite lhs
  suffices Fintype lhs by exact Set.toFinite lhs
  let f : lhs → T'.index := fun x ↦ x.2.choose
  have hf (i : lhs) : i.1 = S.equivBarPotion.symm
    (.mk ⟨T'.i (f i), ⟨T'.elem (f i) ^ (T'.n (f i) : ℕ) * T'.s' (f i), _⟩, ⟨T'.s (f i), _⟩,
      _⟩) := i.2.choose_spec
  haveI : Finite T'.index := finitePotionGen_finite S_rel T_fg
  letI : Fintype T'.index := Fintype.ofFinite T'.index
  apply Fintype.ofInjective f
  rintro ⟨x, hx⟩ ⟨y, hy⟩ eq
  ext : 1
  rw [hf ⟨x, hx⟩, hf ⟨y, hy⟩]
  simp_rw [eq]

  simp only [EmbeddingLike.apply_eq_iff_eq]
  apply Quotient.sound'
  rw [Setoid.ker_def, HomogeneousLocalization.NumDenSameDeg.embedding,
    HomogeneousLocalization.NumDenSameDeg.embedding,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

end HomogeneousSubmonoid

section

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

def t'Aux₀ (R S T : GoodPotionIngredient 𝒜) :
    (S * T).Potion ⊗[S.Potion] (S * R).Potion ≃+* (R * S * T).Potion :=
  mixing (finitePotionGen S.relevant R.fg) (finitePotionGen S.relevant T.fg)

def t'Aux₁ (R S T : GoodPotionIngredient 𝒜) :
    (R * S).Potion ⊗[R.Potion] (R * T).Potion ≃+* (R * S * T).Potion :=
  (mixing (finitePotionGen R.relevant T.fg) (finitePotionGen R.relevant S.fg)).toRingEquiv.trans <|
    potionEquiv (by rw [mul_comm T, mul_assoc, mul_comm T, ← mul_assoc])

def t' (R S T : GoodPotionIngredient 𝒜) :
    ((S * T).Potion ⊗[S.Potion] (S * R).Potion) ≃+*
    ((R * S).Potion ⊗[R.Potion] (R * T).Potion) :=
  (t'Aux₀ R S T).trans (t'Aux₁ R S T).symm

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

open Limits in
def glueData (ℱ : Set (GoodPotionIngredient 𝒜)) : Scheme.GlueData where
  J := ℱ
  U S := Spec <| CommRingCat.of S.1.Potion
  V pair := Spec <| CommRingCat.of (pair.1.1 * pair.2.1).Potion
  f S T := Spec.map <| CommRingCat.ofHom <| S.1.1.potionToMul T.1.1
  f_id S := by
    dsimp only
    rw [show CommRingCat.ofHom (S.1.1.potionToMul S.1.1) =
      S.1.potionToMulSelf.toCommRingCatIso.hom by rfl]
    infer_instance
  f_open := by
    rintro (S T : ℱ)
    exact isOpenImmersion S.1 T.1
  t S T := Spec.map <| CommRingCat.ofHom <| (HomogeneousSubmonoid.potionEquiv <| by rw [mul_comm]).toRingHom
  t_id S := by
    erw [← Scheme.Spec.map_id]
    simp
  t' R S T :=
    (AlgebraicGeometry.pullbackSpecIso _ _ _).hom ≫
    Spec.map (CommRingCat.ofHom <| t' R.1 S.1 T.1) ≫
    (AlgebraicGeometry.pullbackSpecIso _ _ _).inv
  t_fac R S T := by
    sorry
  cocycle R S T := by
    dsimp only
    simp only [mul_toHomogeneousSubmonoid, mul_toSubmonoid, mul_potion_algebraMap_eq,
      RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    rw [← Category.assoc, Iso.comp_inv_eq_id]
    convert Category.comp_id _ using 2
    convert Spec.map_id (CommRingCat.of <| (R.1 * S.1).Potion ⊗[R.1.Potion] (R.1 * T.1).Potion) using 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    convert CommRingCat.ofHom_id using 2
    ext x
    simpa using congr($(t'_cocycle R.1 S.1 T.1) x)

end GoodPotionIngredient

end
