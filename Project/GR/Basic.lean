import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.Tactic.Group

universe u

variable (M : Type u) [CommMonoid M]

namespace GRConstruction

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

@[to_additive AddGRConstruction.addCon]
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

end GRConstruction

@[to_additive AddGR]
abbrev GR : Type u := Con.Quotient (GRConstruction.con M)

scoped [GR] postfix:max "ᵍʳ" => GR

scoped [GR] postfix:max "ᵃᵍʳ" => AddGR

namespace GR

@[to_additive]
def emb : M →* Mᵍʳ where
  toFun x := ↑((x, 1) : M × M)
  map_one' := rfl
  map_mul' x y := by
    simp only [Con.coe_mk']
    change Con.mk' _ _ = Con.mk' _ _
    simp only [Con.coe_mk', Prod.mk_mul_mk, mul_one]

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
instance : MulOneClass Mᵍʳ where
  one_mul a := recOn a (by simp) (by simp) (by simp)
  mul_one a := recOn a (by simp) (by simp) (by simp)


@[to_additive]
instance : Group Mᵍʳ where
  inv_mul_cancel a := by
    obtain ⟨⟨a, b⟩, rfl⟩ := Con.mk'_surjective a
    simp [← Con.coe_mul, mul_comm a]

end GR
