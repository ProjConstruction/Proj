import Project.Grading.Localization
import Project.Grading.GradedRingHom

suppress_compilation

open scoped Graded

variable {ι A σ : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A] {𝒜 : ι → σ}
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]

namespace HomogeneousSubmonoid

variable (S : HomogeneousSubmonoid 𝒜)

def localizationToLocalizationBar : Localization S.toSubmonoid →+* Localization S.bar.toSubmonoid :=
IsLocalization.lift
  (M := S.toSubmonoid) (R := A) (S := Localization S.toSubmonoid) (g := algebraMap _ _) <| by
  intro s
  refine ⟨⟨_, .mk 1 ⟨s, S.le_bar s.2⟩, ?_, ?_⟩, rfl⟩ <;>
  · simp only [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]
    exact Localization.mk_self (⟨s, S.le_bar s.2⟩ : S.bar.toSubmonoid)

@[simp]
lemma localizationToLocalizationBar_mk (a : A) (s : S.toSubmonoid) :
    S.localizationToLocalizationBar (Localization.mk a s) = Localization.mk a ⟨s, S.le_bar s.2⟩ := by
  delta localizationToLocalizationBar
  rw [Localization.mk_eq_mk', IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul,
    IsUnit.coe_liftRight]
  simp only [← Localization.mk_one_eq_algebraMap, RingHom.toMonoidHom_eq_coe,
    MonoidHom.restrict_apply, MonoidHom.coe_coe, Localization.mk_mul, mul_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, mul_comm, mul_one]

def localizationBarToLocalization : Localization S.bar.toSubmonoid →+* Localization S.toSubmonoid :=
IsLocalization.lift
  (M := S.bar.toSubmonoid) (R := A) (S := Localization S.bar.toSubmonoid) (g := algebraMap _ _) <| by
  rintro ⟨s, hs⟩
  simp only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hs
  obtain ⟨-, y, hy, hdvd⟩ := hs
  obtain ⟨z, rfl, hz⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜
    (S.bar.homogeneous hs) (S.homogeneous hy) hdvd
  refine ⟨⟨_, .mk z ⟨_, hy⟩, ?_, ?_⟩, rfl⟩
  · simp only [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]
    exact Localization.mk_self (⟨_, hy⟩ : S.toSubmonoid)
  · simp only [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]
    rw [mul_comm]
    exact Localization.mk_self (⟨_, hy⟩ : S.toSubmonoid)

lemma localizationBarToLocalization_mk (a z : A)
      (s : S.bar.toSubmonoid) (hz : s * z ∈ S.toSubmonoid) :
    S.localizationBarToLocalization (Localization.mk a s) =
    Localization.mk (a * z) ⟨s * z, hz⟩ := by
  delta localizationBarToLocalization
  rw [Localization.mk_eq_mk', IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul,
    IsUnit.coe_liftRight]
  simp only [← Localization.mk_one_eq_algebraMap, RingHom.toMonoidHom_eq_coe,
    MonoidHom.restrict_apply, MonoidHom.coe_coe, Localization.mk_mul, mul_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  ring

@[simp]
lemma localizationBarToLocalization_mk' (a : A) (s : S.toSubmonoid) :
    S.localizationBarToLocalization (Localization.mk a ⟨s, S.le_bar s.2⟩) =
    Localization.mk a s := by
  delta localizationBarToLocalization
  rw [Localization.mk_eq_mk', IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul,
    IsUnit.coe_liftRight]
  simp only [← Localization.mk_one_eq_algebraMap, RingHom.toMonoidHom_eq_coe,
    MonoidHom.restrict_apply, MonoidHom.coe_coe, Localization.mk_mul, mul_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  ring

def localizationEquivLocalizationBar : S.LocalizationGrading ≃+* S.bar.LocalizationGrading where
  __ := S.localizationToLocalizationBar
  invFun := S.localizationBarToLocalization
  left_inv := by
    intro x
    induction x using Localization.induction_on with | H x => simp
  right_inv := by
    intro x
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨a, s, hs⟩
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    simp only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hs
    obtain ⟨hs', y, hy1, hy2⟩ := hs
    obtain ⟨z, rfl, hz⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜
      (S.bar.homogeneous hs) (S.homogeneous hy1) hy2
    rw [localizationBarToLocalization_mk (hz := hy1)]
    simp only [localizationToLocalizationBar_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    ring
  map_mem' := by
    rintro i x hx
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [mem_localizationGrading_iff] at hx
    obtain ⟨m, n, hmn, a, b, hb, rfl⟩ := hx
    simp only [localizationToLocalizationBar_mk]
    rw [mem_localizationGrading_iff]
    exact ⟨m, n, hmn, a, b, S.le_bar hb, rfl⟩
  inv_mem' := by
    intro i x hx
    simp only
    rw [mem_localizationGrading_iff] at hx
    obtain ⟨m, n, hmn, ⟨a, a_mem⟩, ⟨b, b_mem⟩, hb, rfl⟩ := hx
    simp only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hb
    obtain ⟨-, y, hy1, hdvd⟩ := hb
    obtain ⟨z, rfl, hz⟩ := SetLike.Homogeneous.exists_homogeneous_of_dvd 𝒜
      (S.bar.homogeneous hb) (S.homogeneous hy1) hdvd
    rw [localizationBarToLocalization_mk (hz := hy1)]
    simp only
    obtain ⟨k, hk⟩ := hz
    rw [mem_localizationGrading_iff]
    exact ⟨m + k, n + k, by rw [← hmn]; abel, ⟨a * z, SetLike.mul_mem_graded a_mem hk⟩,
      ⟨b * z, SetLike.mul_mem_graded b_mem hk⟩, hy1, rfl⟩

@[simp]
lemma localizationEquivLocalizationBar_apply (x) :
    S.localizationEquivLocalizationBar x = S.localizationToLocalizationBar x := rfl

@[simp]
lemma localizationEquivLocalizationBar_symm_apply (x) :
    S.localizationEquivLocalizationBar.symm x = S.localizationBarToLocalization x := rfl

end HomogeneousSubmonoid
