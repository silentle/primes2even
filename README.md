# Prime2Even

[![CI](https://github.com/silentle/primes2even/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/silentle/primes2even/actions/workflows/lean_action_ci.yml)

A small Lean 4 / Mathlib formalization proving that the sum of any two primes greater than `2` is even.

## Theorem

```lean
theorem any_two_primes_gt_two_sum_even :
    ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → 2 < q → Even (p + q)
```

A prime greater than `2` is odd (`Nat.Prime.eq_two_or_odd`), and the sum of two odd numbers is even (`Odd.add_odd`). See `Prime2even/Basic.lean`.

## Zero-axiom variant

`Prime2even/Minimal.lean` proves the same statement from first principles, without Mathlib — `#print axioms` reports it depends on no axioms at all.

## Build

```bash
lake exe cache get   # download precompiled Mathlib oleans
lake build
```

Toolchain and dependencies are pinned in `lean-toolchain` and `lake-manifest.json`.
