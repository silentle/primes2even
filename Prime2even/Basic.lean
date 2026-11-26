module
import Mathlib

theorem any_two_primes_gt_two_sum_even :
    ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → 2 < q → Even (p + q) := by
  intro p q hp hq hp2 hq2
  have hp_mod : p % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd hp).resolve_left (by omega)
  have hq_mod : q % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd hq).resolve_left (by omega)
  have hp_odd : Odd p := Nat.odd_iff.mpr hp_mod
  have hq_odd : Odd q := Nat.odd_iff.mpr hq_mod
  exact hp_odd.add_odd hq_odd
