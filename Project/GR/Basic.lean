import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.ApplyFun

universe u v

namespace GRConstruction

variable (M : Type u) [CommMonoid M]

@[to_additive AddGRConstruction.rel]
def rel : (M × M) → (M × M) → Prop
| (x, y), (x', y') => ∃ z, x * y' * z = x' * y * z

@[to_additive AddGRConstruction.rel_refl]
lemma rel_refl : ∀ x : M × M, rel M x x :=
  fun ⟨x, y⟩ => ⟨1, by simp⟩

@[to_additive AddGRConstruction.rel_symm]
lemma rel_symm : ∀ {x y : M × M}, rel M x y → rel M y x :=
  fun ⟨z, h⟩ => ⟨z, h.symm⟩

@[to_additive AddGRConstruction.rel_trans]
lemma rel_trans : ∀ {x y z : M × M}, rel M x y → rel M y z → rel M x z := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨x'', y''⟩ ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨y' * a * b, by
    rw [show x * y'' * (y' * a * b) = (x * y' * a) * (y'' * b) by
      simp only [mul_assoc, mul_comm y'']]
    rw [ha]
    rw [show x' * y * a * (y'' * b) = (x' * y'' * b) * (y * a) by
      simp only [mul_assoc, mul_comm y]
      congr 1
      simp only [mul_comm b, mul_comm y'', ← mul_assoc]]
    rw [hb]
    simp only [mul_assoc, mul_comm y']
    congr 1
    simp only [mul_comm a, ← mul_assoc, mul_comm b]
    simp [mul_assoc, mul_comm a b]⟩

@[to_additive (attr := simps) AddGRConstruction.addCon]
def con : Con (M × M) where
  r := rel M
  mul' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, d⟩ ⟨c', d'⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Prod.mk_mul_mk]
    refine ⟨x * y, ?_⟩
    calc a * c * (b' * d') * (x * y)
      _ = (a * b' * x) * (c * d' * y) := by
        simp only [mul_assoc]
        congr 1
        simp only [mul_comm c, mul_assoc]
        congr 1
        simp only [mul_comm d', mul_assoc]
      _ = (a' * b * x) * (c' * d * y) := by rw [hx, hy]
      _ = _ := by
        simp only [mul_assoc]
        congr 1
        simp only [mul_comm c', mul_assoc]
        congr 1
        simp only [mul_comm d, mul_assoc]
  iseqv :=
  { refl := rel_refl M
    symm := rel_symm M
    trans := rel_trans M }

@[to_additive AddGRConstruction.con_def]
lemma con_def (x y : M × M) : con M x y = ∃ z, x.1 * y.2 * z = y.1 * x.2 * z := rfl

end GRConstruction

@[to_additive AddGR]
abbrev GR (M : Type*) [CommMonoid M] := (GRConstruction.con M).Quotient

scoped [GR] postfix:max "ᵍʳ" => GR

scoped [GR] postfix:max "ᵃᵍʳ" => AddGR

namespace GR

section monoid

variable (M : Type u) [CommMonoid M]

@[to_additive]
def emb : M →* Mᵍʳ where
  toFun x := ↑((x, 1) : M × M)
  map_one' := rfl
  map_mul' x y := by
    simp only [Con.coe_mk']
    change Con.mk' _ _ = Con.mk' _ _
    simp only [Con.coe_mk', Prod.mk_mul_mk, mul_one]

@[to_additive]
lemma emb_injective [IsCancelMul M] : Function.Injective (emb M) := by
  intro x y h
  simpa [emb, GRConstruction.con_def] using h

variable {M}

@[to_additive (attr := elab_as_elim)]
lemma recOn {motive : Mᵍʳ → Prop} (x : Mᵍʳ)
    (base : ∀ x : M, motive ↑((x, 1) : M × M))
    (inv : ∀ x : M, motive ↑((1, x) : M × M))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) :
    motive x := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Con.mk'_surjective x
  rw [show (x, y) = (x, 1) * (1, y) by simp, map_mul]
  aesop

@[to_additive]
instance : Inv Mᵍʳ where
  inv := Con.lift _ (MonoidHom.comp (Con.mk' _)
    { toFun := .swap
      map_one' := by simp
      map_mul' := by simp }) <| by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨z, h⟩
    simp only [Con.ker_rel, MonoidHom.coe_comp, Con.coe_mk', MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply, Prod.swap_prod_mk, Con.eq]
    refine ⟨z, ?_⟩
    convert h.symm using 1 <;>
    · simp only [mul_comm _ z]
      congr 1
      rw [mul_comm]

@[to_additive (attr := simp)]
lemma inv_coe (x y : M) : (↑(x, y) : Mᵍʳ)⁻¹ = ↑(y, x) := rfl

@[to_additive (attr := simp)]
lemma coe_same (x : M) : (↑(x, x) : Mᵍʳ) = 1 := by
  rw [show (1 : Mᵍʳ) = ↑((1, 1) : M × M) by simp, Con.eq]
  use 1
  simp

@[to_additive]
instance : Group Mᵍʳ where
  one_mul a := recOn a (by simp) (by simp) (by simp)
  mul_one a := recOn a (by simp) (by simp) (by simp)
  inv_mul_cancel a := by
    obtain ⟨⟨a, b⟩, rfl⟩ := Con.mk'_surjective a
    simp [← Con.coe_mul, mul_comm a]

@[to_additive]
def lift {G : Type v} [Group G] (f : M →* G) : Mᵍʳ →* G :=
  Con.lift _
    { toFun p := (f p.1) * (f p.2)⁻¹
      map_one' := by
        simp only [Prod.fst_one, map_one, Prod.snd_one, inv_one, mul_one]
      map_mul' := by
        rintro ⟨a, b⟩ ⟨c, d⟩
        simp only [Prod.mk_mul_mk, map_mul, mul_inv_rev, ← mul_assoc, mul_inv_eq_iff_eq_mul]
        simp only [mul_assoc, mul_right_inj]
        symm
        simp only [← map_mul, mul_comm b, inv_mul_eq_iff_eq_mul]
        simp [map_mul]  } <| by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨z, h⟩
    have eq₀ := congr(f $h)
    simp only [map_mul, mul_left_inj, Con.ker_rel, MonoidHom.coe_mk, OneHom.coe_mk] at eq₀ ⊢
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, show (f y')⁻¹ * f y = f y * (f y')⁻¹ by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← map_mul, mul_comm y', eq_comm,
        mul_inv_eq_iff_eq_mul, map_mul], ← mul_assoc, eq_comm, mul_inv_eq_iff_eq_mul]
    exact eq₀.symm

@[to_additive (attr := simp)]
lemma lift_comp_emb {G : Type v} [Group G] (f : M →* G) : (lift f).comp (emb M) = f := by
  ext x
  simp [lift, emb]

@[to_additive (attr := simp)]
lemma lift_emb_apply {G : Type v} [Group G] (f : M →* G) (x) : (lift f) (emb M x) = f x := by
  simp [lift, emb]

@[to_additive (attr := simp)]
lemma lift_uniq {G : Type v} [Group G] (f : M →* G) (f' : Mᵍʳ →* G) (h : f'.comp (emb M) = f) :
    f' = lift f := by
  ext x
  obtain ⟨⟨a, b⟩, rfl⟩ := Con.mk'_surjective x
  simp only [Con.coe_mk', lift, Con.lift_coe, MonoidHom.coe_mk, OneHom.coe_mk]
  have eq (x : M) := congr($h x)
  simp only [emb, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply] at eq
  rw [show ((a, b) : M × M) = (a, 1) * (1, b) by simp, Con.coe_mul, map_mul, eq,
    show (↑((1, b) : M × M) : Mᵍʳ) = ↑(((b, 1) : M × M) : Mᵍʳ)⁻¹ by simp, map_inv, eq]

@[to_additive (attr := simp)]
lemma lift_apply_coe {G : Type v} [Group G] (f : M →* G) (a b : M) :
    lift f (↑(a, b)) = f a * (f b)⁻¹ := rfl


end monoid

section subgroup

variable {M : Type u} [CommGroup M] (N : Submonoid M)

instance : IsCancelMul N where
  mul_left_cancel := by aesop
  mul_right_cancel := by aesop

@[simps! apply]
noncomputable def equivAsSubgroup : Nᵍʳ ≃* Subgroup.closure (N : Set M) :=
  MulEquiv.ofBijective (lift (Submonoid.inclusion Subgroup.subset_closure)) <| by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x h
      obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := Con.mk'_surjective x
      simp only [lift_comp_emb, Con.coe_mk', MonoidHom.mem_ker, lift_apply_coe, Subtype.ext_iff,
        Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one] at h
      change a * b⁻¹ = 1 at h
      rw [mul_inv_eq_one] at h
      subst h
      simp only [Con.coe_mk', coe_same, Subgroup.mem_bot]
    · rintro ⟨x, hx⟩
      apply Subgroup.closure_induction (p := _) (x := x) (hx := hx)
      · intro x hx
        refine ⟨emb _ ⟨x, hx⟩, ?_⟩
        simp only [lift_comp_emb, lift_emb_apply]
        rfl
      · use 1
        simp only [lift_comp_emb, map_one]
        rfl
      · rintro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        rw [map_mul, ha, hb]
        rfl
      · rintro x hx ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        simp only [lift_comp_emb, map_inv, ha]
        rfl

end subgroup

end GR
