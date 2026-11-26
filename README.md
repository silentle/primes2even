# Prime2Even

A small Lean 4 / Mathlib formalization proving that the sum of any two primes greater than `2` is even.

## Theorem

For natural numbers `p q`, if both are prime and both are greater than `2`, then `p + q` is even:

```lean
theorem sum_of_primes_gt_two_even {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : 2 < p) (hq2 : 2 < q) :
    Even (p + q)
```

Equivalently, in fully quantified form:

```lean
theorem any_two_primes_gt_two_sum_even :
    ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 2 < p → 2 < q → Even (p + q)
```

## Proof idea

The argument is short and entirely constructive:

1. A prime is either `2` or odd (`Nat.Prime.eq_two_or_odd`).
2. Since `p > 2`, `p` cannot be `2`, hence `p` is odd. Likewise `q` is odd.
3. The sum of two odd numbers is even (`Odd.add_odd`).

```lean
have hp_odd : Odd p :=
  (Nat.Prime.eq_two_or_odd hp).resolve_left (by omega)
have hq_odd : Odd q :=
  (Nat.Prime.eq_two_or_odd hq).resolve_left (by omega)
exact hp_odd.add_odd hq_odd
```

## Requirements

- [Lean 4](https://lean-lang.org/) via [elan](https://github.com/leanprover/elan)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

The exact toolchain is pinned in `lean-toolchain` and dependencies are pinned in `lake-manifest.json`.

## Build

Fetch dependencies (first run may take a while, as Mathlib is large):

```bash
lake exe cache get   # download precompiled Mathlib oleans
lake build
```

To check a single file without building everything:

```bash
lake env lean Prime2even.lean
```

## Project layout

```text
.
├── Prime2even.lean        # main theorem and proof
├── Prime2even/            # supporting modules (if any)
├── lakefile.toml          # Lake build configuration
├── lean-toolchain         # pinned Lean toolchain
├── lake-manifest.json     # pinned dependency revisions
└── README.md
```

## Checking the proof

- In VS Code with the Lean 4 extension, a successful proof shows a **blue double checkmark** in the gutter.
- `lake build` performs a full kernel type-check of the project.
- To confirm no `sorry` or unexpected axioms are used, run:

```lean
#print axioms sum_of_primes_gt_two_even
```
