import Project.HomogeneousSubmonoid.IsoBar
import Project.HomogeneousSubmonoid.Relevant
import Project.ForMathlib.HomogeneousLocalization
import Project.ForMathlib.LocalizationAway

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks

suppress_compilation

namespace HomogeneousSubmonoid

variable {ι R A B : Type*}
variable [AddCommGroup ι] [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]
variable [CommRing B] [Algebra R B] {ℬ : ι → Submodule R B}
variable [GradedAlgebra ℬ]
variable (S T : HomogeneousSubmonoid 𝒜)

abbrev Potion := HomogeneousLocalization 𝒜 S.toSubmonoid

lemma potion_nonzero_divisor (a : A) (deg_zero : a ∈ 𝒜 0) (mem : a ∈ S) :
    algebraMap (𝒜 0) S.Potion ⟨a, deg_zero⟩ ∈ nonZeroDivisors S.Potion := by
  intro x hx
  induction x using Quotient.inductionOn' with | h x =>
  change Quotient.mk'' _ = Quotient.mk'' 0 at hx
  rw [HomogeneousLocalization.ext_iff_val] at hx
  -- rw [Quotient.eq'', Setoid.ker_iff_mem_preimage] at hx
  simp only [HomogeneousLocalization.mk_mul, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mk, SetLike.GradeZero.coe_one, Localization.mk_mul,
    Submonoid.mk_mul_mk, mul_one, HomogeneousLocalization.mk_zero,
    HomogeneousLocalization.val_zero] at hx
  rw [← Localization.mk_zero 1, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hx
  obtain ⟨c, hc⟩ := hx
  simp only [OneMemClass.coe_one, one_mul, mul_zero] at hc
  ext
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero]
  rw [← Localization.mk_zero 1, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨c * ⟨a, mem⟩, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, mul_zero]
  rw [← hc]
  ring

open scoped Graded in
def potionToMap (Φ : 𝒜 →+* ℬ) : S.Potion →+* (S.map Φ).Potion :=
  HomogeneousLocalization.map _ _ Φ (by simp [map_toSubmonoid]; apply Submonoid.le_comap_map)
    fun i hi ↦ Φ.map_mem

open scoped Graded in
@[simp]
lemma potionToMap_mk (Φ : 𝒜 →+* ℬ) (x) :
    S.potionToMap Φ (.mk x) =
      .mk ⟨x.deg, ⟨Φ x.num.1, Φ.map_mem x.num.2⟩, ⟨Φ x.den.1, Φ.map_mem x.den.2⟩,
        by simp only [mem_toSubmonoid_iff]; apply Submonoid.mem_map_of_mem; exact x.den_mem⟩ := rfl

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
lemma potionEquiv_mk {S T : HomogeneousSubmonoid 𝒜} (eq : S = T) (x) :
    S.potionEquiv eq (.mk x) = .mk ⟨x.deg, ⟨x.num, eq ▸ x.num.2⟩, ⟨x.den, eq ▸ x.den.2⟩,
      by subst eq; exact x.den_mem⟩ := rfl

@[simp]
lemma potionEquiv_mk' {S T : HomogeneousSubmonoid 𝒜} (eq : S = T) (x) :
    S.potionEquiv eq (Quotient.mk'' x) = .mk ⟨x.deg, ⟨x.num, eq ▸ x.num.2⟩, ⟨x.den, eq ▸ x.den.2⟩,
      by subst eq; exact x.den_mem⟩ := rfl

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
lemma potionEquiv_symm {R S : HomogeneousSubmonoid 𝒜} (eq : R = S) :
    (R.potionEquiv eq).symm = S.potionEquiv eq.symm := by
  subst eq
  simp only [potionEquiv_refl]
  rfl

@[simp]
lemma potionEquiv_symm_apply {R S : HomogeneousSubmonoid 𝒜} (eq : R = S) (x) :
    (R.potionEquiv eq).symm x = S.potionEquiv eq.symm x :=
  congr($(potionEquiv_symm eq) x)

@[simp]
lemma potionEquiv_trans {R S T : HomogeneousSubmonoid 𝒜} (eq1 : R = S) (eq2 : S = T) :
    (R.potionEquiv eq1).trans (S.potionEquiv eq2) = R.potionEquiv (eq1.trans eq2) := by
  subst eq1 eq2
  simp only [potionEquiv_refl]
  rfl

@[simp]
lemma potionEquiv_comp {R S T : HomogeneousSubmonoid 𝒜} (eq1 : R = S) (eq2 : S = T) :
    (S.potionEquiv eq2).toRingHom.comp (R.potionEquiv eq1).toRingHom =
    (R.potionEquiv (eq1.trans eq2)).toRingHom := by
  subst eq1 eq2
  simp only [potionEquiv_refl]
  rfl

@[simp]
lemma potionEquiv_trans_apply {R S T : HomogeneousSubmonoid 𝒜} (eq1 : R = S) (eq2 : S = T) (x) :
    S.potionEquiv eq2 (R.potionEquiv eq1 x) =
    R.potionEquiv (eq1.trans eq2) x :=
  congr($(potionEquiv_trans eq1 eq2) x)

open scoped Graded in
lemma potionToMap_comp_potionEquiv (Φ : 𝒜 →+* ℬ) (eq : S = T) :
    (S.potionToMap Φ).comp (potionEquiv eq.symm).toRingHom =
    RingHom.comp (potionEquiv (by rw [eq])).toRingHom (T.potionToMap Φ) := by
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  rfl

def potionToMul : S.Potion →+* (S * T).Potion :=
  HomogeneousLocalization.map _ _ (RingHom.id _) (by
    erw [Submonoid.comap_id, ← le_iff]
    exact left_le_mul ..) fun i a hi ↦ hi

def potionToMulSelf : S.Potion ≃+* (S * S).Potion :=
  potionEquiv (by simp)

@[simp]
lemma potionToMul_mk (x) : S.potionToMul T (.mk x) = .mk ⟨x.deg, x.num, x.den, left_le_mul _ _ x.den_mem⟩ := rfl

@[simp]
lemma potionToMul_mk' (x) : S.potionToMul T (Quotient.mk'' x) = .mk ⟨x.deg, x.num, x.den, left_le_mul _ _ x.den_mem⟩ := rfl

/-
A_(S) -> A_(ST) -> B_(φ(ST))
  |                 |
B_(φS) ->         B_(φ(S)φ(T))

-/
open scoped Graded in
lemma potionToMul_comp_potionToMap (Φ : 𝒜 →+* ℬ) :
    ((S.map Φ).potionToMul (T.map Φ)).comp (S.potionToMap Φ) =
    (RingHom.comp (potionEquiv (HomogeneousSubmonoid.map_mul ..)).toRingHom
      ((S * T).potionToMap Φ)).comp (S.potionToMul T) := by
  ext x
  induction x using Quotient.inductionOn' with | h x =>
  simp only [mul_toSubmonoid, RingHom.coe_comp, Function.comp_apply, potionToMap_mk, potionToMul_mk,
    id_eq, eq_mpr_eq_cast, cast_eq, HomogeneousLocalization.val_mk, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [potionToMap_mk, potionEquiv_mk]
  simp

@[simp]
lemma potionEquiv_potionToMul_assoc {R S T : HomogeneousSubmonoid 𝒜} (x : R.Potion):
  ((R*S).potionToMul T (R.potionToMul S x)) =
  potionEquiv (by rw [mul_assoc]) (R.potionToMul (S * T) x) := by
  induction x using Quotient.inductionOn' with | h x =>
  rw [potionToMul_mk, potionToMul_mk, potionToMul_mk, potionEquiv_mk]

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
  rw [equivBarPotion_symm_apply (z_mem := hz) (hz := hy), potionToMul_mk]
  simp only
  rw [equivBarPotion_symm_apply (z_mem := hz) (hz := left_le_mul S T hy)]

instance : Algebra S.Potion S.bar.Potion :=
  RingHom.toAlgebra S.equivBarPotion

@[simp]
lemma bar_potion_algebraMap_eq : (algebraMap S.Potion S.bar.Potion) = S.equivBarPotion := rfl

section PotionGen

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

variable {S T} in
def PotionGen.genSubmonoid (T' : PotionGen S T) : Submonoid S.Potion :=
  Submonoid.closure
    {x | ∃ (t : T'.index), x =
      S.equivBarPotion.symm (.mk
        { deg := T'.i t,
          num := ⟨(T'.elem t) ^ (T'.n t : ℕ) * T'.s' t,
            by simpa using SetLike.mul_mem_graded (T'.t_deg t) (T'.s'_deg t)⟩,
          den := ⟨T'.s t, T'.s_deg t⟩,
          den_mem := T'.s_mem_bar t }) }

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
  let n : carrier → ℕ+ := fun t ↦ (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <| subset t.2).choose
  let s : carrier → A :=
    fun t ↦ (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <| subset t.2).choose_spec.choose
  let s' : carrier → A := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <| subset t.2).choose_spec.choose_spec.choose
  let i : carrier → ι := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose
  let i' : carrier → ι := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose
  let t_deg : ∀ (x : carrier), x.1 ^ (n x : ℕ) ∈ 𝒜 (i x - i' x) := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  let s_deg : ∀ (x : carrier), s x ∈ 𝒜 (i x) := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let s'_deg : ∀ (x : carrier), s' x ∈ 𝒜 (i' x) := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
  let s_mem_bar : ∀ (x : carrier), s x ∈ S.bar := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
      subset t.2).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
  let s'_mem_bar : ∀ (x : carrier), s' x ∈ S.bar := fun t ↦
    (finite_potionGen_exists_aux₂ S_rel t <| T.homogeneous <|
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

end PotionGen

end HomogeneousSubmonoid
