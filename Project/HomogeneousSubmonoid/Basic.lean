import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.Algebra.Group.Submonoid.Pointwise

import Project.ForMathlib.SubgroupBasic
import Project.ForMathlib.Submonoid
import Project.ForMathlib.SetLikeHomogeneous
import Project.GR.Basic
import Project.Grading.GradedRingHom

open DirectSum TensorProduct
open scoped NNReal

variable {ι A B σ σ' : Type*}
variable [AddCommGroup ι] [CommRing A] [SetLike σ A]  (𝒜 : ι → σ)
variable [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜]
variable [CommRing B] [SetLike σ' B]  (ℬ : ι → σ')
variable [AddSubgroupClass σ' B] [GradedRing ℬ]

@[ext]
structure HomogeneousSubmonoid extends Submonoid A where
  homogeneous_gen : ∃ (s : Set A),
    toSubmonoid = Submonoid.closure s ∧ ∀ x ∈ s, SetLike.Homogeneous 𝒜 x

open scoped GR

namespace HomogeneousSubmonoid

variable {𝒜 ℬ} (S : HomogeneousSubmonoid 𝒜)

omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] in
variable (𝒜) in
lemma toSubmonoid_injective :
    Function.Injective (toSubmonoid : HomogeneousSubmonoid 𝒜 → Submonoid A) := by
  rintro ⟨S, hS⟩ ⟨T, hT⟩ h
  simp only at h
  subst h
  rfl

instance : SetLike (HomogeneousSubmonoid 𝒜) A where
  coe S := S.toSubmonoid
  coe_injective' := by
    rintro ⟨S, hS⟩ ⟨T, hT⟩ h
    simpa using h

omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] in
lemma mem_iff (x : A) : x ∈ S ↔ x ∈ S.toSubmonoid := Iff.rfl

omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp]
lemma mem_toSubmonoid_iff (x : A) : x ∈ S.toSubmonoid ↔ x ∈ S := Iff.rfl

instance : SubmonoidClass (HomogeneousSubmonoid 𝒜) A where
  mul_mem ha hb := mul_mem (S := Submonoid A) ha hb
  one_mem S := one_mem S.toSubmonoid


lemma homogeneous {x : A} : x ∈ S → SetLike.Homogeneous 𝒜 x := by
  rintro hx
  obtain ⟨s, hs, h⟩ := S.homogeneous_gen
  rw [← mem_toSubmonoid_iff, hs] at hx
  obtain ⟨n, hn, rfl⟩ := Submonoid.mem_closure_iff _ _ _ |>.1 hx
  apply SetLike.Homogeneous.prod'' 𝒜
  intro i hi
  apply SetLike.Homogeneous.pow
  apply h _ (hn _ hi)

open scoped Graded in
def map (Φ : 𝒜 →+* ℬ) (S : HomogeneousSubmonoid 𝒜) : HomogeneousSubmonoid ℬ where
  toSubmonoid := S.toSubmonoid.map Φ
  homogeneous_gen := by
    obtain ⟨s, hs, h⟩ := S.homogeneous_gen
    refine ⟨Φ '' s, le_antisymm ?_ ?_, ?_⟩
    · rw [Submonoid.map_le_iff_le_comap, hs, Submonoid.closure_le]
      rintro x hx
      simp only [Submonoid.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      apply Submonoid.subset_closure
      use x
    · rw [Submonoid.closure_le]
      rintro - ⟨x, hx, rfl⟩
      simp only [Submonoid.coe_map, Set.mem_image, SetLike.mem_coe, mem_toSubmonoid_iff]
      refine ⟨x, ?_, rfl⟩
      rw [← mem_toSubmonoid_iff, hs]
      apply Submonoid.subset_closure
      exact hx
    · rintro - ⟨x, hx, rfl⟩
      exact Φ.map_homogeneous (h x hx)

open scoped Graded in
omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass σ' B] [GradedRing ℬ] in
lemma map_toSubmonoid (Φ : 𝒜 →+* ℬ) (S : HomogeneousSubmonoid 𝒜) :
    (S.map Φ).toSubmonoid = S.toSubmonoid.map Φ := rfl

omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] [AddSubgroupClass σ' B] [GradedRing ℬ] in
open scoped Graded in
lemma mem_map_of_mem (Φ : 𝒜 →+* ℬ) {S : HomogeneousSubmonoid 𝒜} {x : A} :
    x ∈ S → Φ x ∈ S.map Φ := by
  intro hx
  rw [mem_iff, map_toSubmonoid]
  exact Submonoid.mem_map_of_mem _ hx

def closure (s : Set A) (hs : ∀ x ∈ s, SetLike.Homogeneous 𝒜 x) : HomogeneousSubmonoid 𝒜 where
  __ := Submonoid.closure s
  homogeneous_gen := by
    use Submonoid.closure s
    simp only [Submonoid.closure_eq, SetLike.mem_coe, true_and]
    intro x hx
    exact Submonoid.closure_induction hs
      (SetLike.homogeneous_one 𝒜)
      (fun _ _ _ _ hx hy => SetLike.homogeneous_mul hx hy) hx

lemma mem_closure_singleton (a : A) (ha : SetLike.Homogeneous 𝒜 a) (x) :
    x ∈ (closure {a} (by simpa)) ↔
    ∃ (n : ℕ), x = a ^ n := by
  simp [closure, Submonoid.mem_closure_singleton, eq_comm, mem_iff]

@[simps]
protected def bot : HomogeneousSubmonoid 𝒜 where
  carrier := {1}
  mul_mem' := by simp
  one_mem' := by simp
  homogeneous_gen := by
    use {1}
    fconstructor
    · ext x
      simp [Submonoid.mem_closure_singleton, eq_comm]
    simp only [Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_singleton_iff, forall_eq]
    exact ⟨0, SetLike.GradedOne.one_mem⟩

@[simp]
lemma mem_bot (x : A) : x ∈ HomogeneousSubmonoid.bot (𝒜 := 𝒜) ↔ x = 1 := by rfl

instance : One (HomogeneousSubmonoid 𝒜) where
  one := HomogeneousSubmonoid.bot

@[simp]
lemma mem_one (x : A) : x ∈ (1 : HomogeneousSubmonoid 𝒜) ↔ x = 1 := by rfl

open Pointwise in
instance : Mul (HomogeneousSubmonoid 𝒜) where
  mul S T :=
  { toSubmonoid := S.toSubmonoid * T.toSubmonoid
    homogeneous_gen := by
      use S ∪ T
      simp only [Submonoid.closure_union_eq_mul, Set.mem_union, SetLike.mem_coe]
      constructor
      · erw [Submonoid.closure_eq, Submonoid.closure_eq]
      rintro a (ha|hb)
      · exact S.homogeneous ha

      · exact T.homogeneous hb }

@[simp]
lemma mul_toSubmonoid (S T : HomogeneousSubmonoid 𝒜) : (S * T).toSubmonoid = S.toSubmonoid * T.toSubmonoid := rfl

lemma mem_mul_iff {S T : HomogeneousSubmonoid 𝒜} (x : A) :
    x ∈ (S * T) ↔
    ∃ s ∈ S, ∃ t ∈ T, x = s * t := by
  fconstructor <;>
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨s, hs, t, ht, rfl⟩

@[simp]
lemma mul_self (S : HomogeneousSubmonoid 𝒜) : S * S = S := by
  ext x
  simp

instance : CommMonoid (HomogeneousSubmonoid 𝒜) where
  mul_assoc R S T:= toSubmonoid_injective _ <| mul_assoc _ _ _
  mul_comm S T :=  toSubmonoid_injective _ <| mul_comm _ _
  one_mul _ := toSubmonoid_injective _ <| one_mul _
  mul_one _ := toSubmonoid_injective _ <| mul_one _

lemma closure_union_eq_mul (s t : Set A) (hs : ∀ x ∈ s, SetLike.Homogeneous 𝒜 x)
    (ht : ∀ x ∈ t, SetLike.Homogeneous 𝒜 x) :
    closure (s ∪ t) (by aesop) = closure s hs * closure t ht := by
  apply toSubmonoid_injective
  exact Submonoid.closure_union_eq_mul ..

open scoped Graded in
protected lemma map_mul (Φ : 𝒜 →+* ℬ) (S T : HomogeneousSubmonoid 𝒜)  : (S * T).map Φ = S.map Φ * T.map Φ :=
  toSubmonoid_injective ℬ <| Submonoid.map_mul ..

def bar : HomogeneousSubmonoid 𝒜 where
  carrier := {x | SetLike.Homogeneous 𝒜 x ∧ ∃ y ∈ S, x ∣ y}
  mul_mem' := by
    rintro x y ⟨hom_x, ⟨ax, ⟨hax, hax'⟩⟩⟩ ⟨hom_y, ⟨ay, ⟨hay, hay'⟩⟩⟩
    exact ⟨SetLike.homogeneous_mul hom_x hom_y, ⟨ax * ay, ⟨mul_mem hax hay,
      mul_dvd_mul hax' hay'⟩⟩⟩
  one_mem' := ⟨SetLike.homogeneous_one 𝒜, ⟨1, ⟨one_mem _, by rfl⟩⟩⟩
  homogeneous_gen := by
    use {x | SetLike.Homogeneous 𝒜 x ∧ ∃ y ∈ S, x ∣ y}
    constructor
    · refine le_antisymm Submonoid.subset_closure ?_
      rw [Submonoid.closure_le]
      rfl
    rintro x ⟨hom_x, ⟨y, ⟨hy, hy'⟩⟩⟩; exact hom_x

@[simp]
lemma mem_bar (x : A) :
    x ∈ S.bar ↔
    SetLike.Homogeneous 𝒜 x ∧ ∃ (y : A), y ∈ S ∧ x ∣ y := by rfl

instance : PartialOrder (HomogeneousSubmonoid 𝒜) :=
  PartialOrder.lift (fun S ↦ S.toSubmonoid)
    (injective_of_le_imp_le _ <| by aesop)

lemma bar_mono (S T : HomogeneousSubmonoid 𝒜) : S ≤ T → S.bar ≤ T.bar := by
  rintro h x ⟨hom_x, ⟨y, ⟨hy, hy'⟩⟩⟩
  exact ⟨hom_x, ⟨y, ⟨h hy, hy'⟩⟩⟩

omit [AddCommGroup ι] [DecidableEq ι] [AddSubgroupClass σ A] [GradedRing 𝒜] in
lemma le_iff (S T : HomogeneousSubmonoid 𝒜) : S ≤ T ↔ S.toSubmonoid ≤ T.toSubmonoid :=
  Iff.rfl

lemma left_le_mul (S T : HomogeneousSubmonoid 𝒜) : S ≤ S * T := Submonoid.left_le_mul

lemma right_le_mul (S T : HomogeneousSubmonoid 𝒜) : T ≤ S * T := Submonoid.right_le_mul

instance : CommMonoid (HomogeneousSubmonoid 𝒜) where
  mul_one S := by
    ext x
    simp [mem_mul_iff]
  one_mul S := by
    ext x
    simp [mem_mul_iff]
  mul_comm S T := by
    ext x
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, mem_toSubmonoid_iff,
      mem_mul_iff]
    fconstructor <;>
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨t, ht, s, hs, mul_comm _ _⟩
  mul_assoc R S T := by
    ext x
    fconstructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
      simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, mem_toSubmonoid_iff]
      exact ⟨a, ha, ⟨b * c, ⟨b, hb, c, hc, rfl⟩, mul_assoc _ _ _ |>.symm⟩⟩
    · rintro ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
      simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, mem_toSubmonoid_iff]
      rw [← mul_assoc]
      exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩

lemma le_bar : S ≤ S.bar := by
  rintro x hx
  exact ⟨S.homogeneous hx, x, hx, by rfl⟩

lemma mem_bot_bar (x : A) :
    x ∈ HomogeneousSubmonoid.bot.bar (𝒜 := 𝒜) ↔
    SetLike.Homogeneous 𝒜 x ∧ ∃ (y : A), x * y = 1 := by
  simp only [bar, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  fconstructor
  · rintro ⟨hx, y, rfl, ⟨z, hz⟩⟩
    use hx, z
    exact hz.symm
  · rintro ⟨hx, y, hy⟩
    use hx
    simp only [mem_bot, exists_eq_left]
    use y
    exact hy.symm

@[simps]
def deg : AddSubmonoid ι where
  carrier := {i | ∃ x ∈ S, x ∈ 𝒜 i}
  add_mem' := by
    rintro i j ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    exact ⟨x * y, mul_mem hx hy, SetLike.GradedMul.mul_mem hx' hy'⟩
  zero_mem' := ⟨1, one_mem _, SetLike.GradedOne.one_mem⟩

@[simp]
lemma mem_deg_iff (i : ι) : i ∈ S.deg ↔ ∃ x ∈ S, x ∈ 𝒜 i := Iff.rfl

lemma deg_mono (S T : HomogeneousSubmonoid 𝒜) : S ≤ T → S.deg ≤ T.deg := by
  rintro h i ⟨x, hx, hx'⟩
  exact ⟨x, h hx, hx'⟩

@[simp]
lemma closure_one :
    (closure (𝒜 := 𝒜) {(1 : A)}
      (by simpa using ⟨0,SetLike.GradedOne.one_mem (A := 𝒜)⟩)) = HomogeneousSubmonoid.bot := by
  ext x
  simp [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, bot_carrier,
    Set.mem_singleton_iff, closure, Submonoid.mem_closure_singleton, eq_comm,
    HomogeneousSubmonoid.bot]

lemma mem_deg_singleton (a : A) (ha : SetLike.Homogeneous 𝒜 a) (x) :
    x ∈ (closure {a} (by simpa)).deg ↔
    (∃ n : ℕ, a ^ n ∈ 𝒜 x) := by
  simp only [mem_deg_iff]
  fconstructor
  · rintro ⟨y, hy, h⟩
    rw [mem_closure_singleton (ha := ha)] at hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨n, ‹_›⟩
  · rintro ⟨n, hn⟩
    refine ⟨a^n, ?_, hn⟩
    rw [mem_closure_singleton (ha := ha)]
    aesop

lemma mem_deg {i} : i ∈ S.deg ↔ ∃ x ∈ S, x ∈ 𝒜 i := Iff.rfl

lemma zero_mem_deg [Nontrivial A] : 0 ∈ S.deg :=
  ⟨1, one_mem _, SetLike.GradedOne.one_mem⟩

def agrDeg : AddSubgroup ι := AddSubgroup.closure S.deg

scoped notation:max ι"["S"]" => agrDeg (ι := ι) S

lemma agrDeg_mono {S T : HomogeneousSubmonoid 𝒜} (le : S ≤ T) : S.agrDeg ≤ T.agrDeg :=
  AddSubgroup.closure_mono (deg_mono S T le)

noncomputable def agrDegEquiv : S.degᵃᵍʳ ≃+ ι[S] := (AddGR.equivAsAddSubgroup ..).trans
  { __ := AddSubgroup.inclusion (by
      rw [AddSubgroup.closure_le]
      change S.deg ≤ S.agrDeg.toAddSubmonoid
      exact AddSubgroup.subset_closure)
    invFun := AddSubgroup.inclusion (by
      erw [AddSubgroup.closure_le]
      exact AddSubgroup.subset_closure)
    left_inv x := rfl
    right_inv x := rfl }

end HomogeneousSubmonoid
