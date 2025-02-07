import Mathlib

#eval List.range 2025 |>.filter (fun x => (x ∣ 2025) ∧ (x % 10) = 1)

set_option maxRecDepth 2400 in
/- We are tasked to compute the number of positive divisors of 2121 which have a units digit of 1. -/
theorem number_theory_43033 (s : Finset ℕ) (h : ∀ x, x ∈ s ↔ x ∣ 2121 ∧ (x % 10) = 1) :
    s.card = 4 := by
  let res : List ℕ := List.range 2122 |>.filter (fun x => (x ∣ 2121) ∧ (x % 10) = 1)
  have : res.length = 4 := rfl
  rw [← show res.toFinset = s by
    ext x
    simp only [Bool.decide_and, List.toFinset_filter, Bool.and_eq_true, decide_eq_true_eq,
      Finset.mem_filter, List.mem_toFinset, List.mem_range, h, and_iff_right_iff_imp, and_imp, res]
    intro hx1 hx2
    rw [Nat.lt_succ]
    apply Nat.le_of_dvd <;> aesop]
  rwa [List.toFinset_card_of_nodup]
  decide
