/-
Copyright (c) 2025 silentle. All rights reserved.
SPDX-License-Identifier: MIT
Authors: silentle
-/
/-!
# Prime2even.Minimal

A self-contained, minimal-axiom proof that the sum of two primes greater
than `2` is even.  Nothing from Mathlib is used: the ingredients are just
`Nat` recursion, `rfl`, one induction, `decide`, and rewriting with core
`Nat` lemmas.  `#print axioms` at the end of this file confirms the proof
depends on **no axioms at all** (not even `propext`, `Classical.choice`
or `Quot.sound`).
-/

namespace Prime2even.Minimal

/-- Evenness, from first principles. -/
def isEven (n : Nat) : Prop := ∃ k, n = k + k

/-- Divisibility, from first principles. -/
def Div (d n : Nat) : Prop := ∃ k, n = d * k

/-- Primality, from first principles: no non-trivial proper divisors. -/
def isPrime (n : Nat) : Prop :=
  1 < n ∧ ∀ d, 1 < d → d < n → ¬ Div d n

private theorem succ_add' (x y : Nat) : x + 1 + y = Nat.succ (x + y) :=
  Nat.succ_add x y

private theorem add_succ' (x y : Nat) : x + (y + 1) = Nat.succ (x + y) := rfl

private theorem sum (a b : Nat) : a + a + (b + b) = a + b + (a + b) := by
  rw [← Nat.add_assoc (a + a) b b, Nat.add_right_comm a a b, Nat.add_assoc (a + b) a b]

/-- Every natural number is either even or odd, by direct induction. -/
theorem parity (n : Nat) : (∃ k, n = k + k) ∨ (∃ k, n = k + k + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      exact Or.inr ⟨k, rfl⟩
    · subst hk
      refine Or.inl ⟨k + 1, ?_⟩
      show Nat.succ (Nat.succ (k + k)) = Nat.succ k + Nat.succ k
      rw [Nat.add_succ, Nat.succ_add]

/-- A prime greater than `2` is odd: if it were even, `2` would be a
non-trivial proper divisor. -/
private theorem prime_gt_two_odd {p : Nat} (hp : isPrime p) (hp2 : 2 < p) :
    ∃ k, p = k + k + 1 := by
  rcases parity p with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd ⟨k, hk.trans ((Nat.mul_two k).symm.trans (Nat.mul_comm k 2))⟩
      (hp.2 2 (by decide) hp2)
  · exact ⟨k, hk⟩

/-- The minimal-axiom main theorem: the sum of any two primes greater
than `2` is even. -/
theorem primes_sum_even (p q : Nat)
    (hp : isPrime p) (hp2 : 2 < p)
    (hq : isPrime q) (hq2 : 2 < q) :
    isEven (p + q) := by
  rcases prime_gt_two_odd hp hp2 with ⟨a, ha⟩
  rcases prime_gt_two_odd hq hq2 with ⟨b, hb⟩
  refine ⟨a + b + 1, ?_⟩
  rw [ha, hb]
  rw [add_succ' (a + a + 1) (b + b), succ_add' (a + a) (b + b),
      add_succ' (a + b + 1) (a + b), succ_add' (a + b) (a + b), sum a b]

end Prime2even.Minimal

#print axioms Prime2even.Minimal.primes_sum_even
