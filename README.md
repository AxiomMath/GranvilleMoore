[![](logo.svg)](https://axiommath.ai/)

# The p-divisibility of the integer Moore determinant and iterated Fermat quotients

This is a Lean formalization of Granville's results on the p-divisibility of the integer Moore determinant and on iterated Fermat quotients.

## Main Results

* The iterated Fermat quotients `F⁽ʲ⁾ₖ(x)` are integers, for every `j ≤ p - 1`.
* `j! F⁽ʲ⁾ₖ(x) ≡ x qₚ(x)ʲ (mod p)`, for every `j ≤ p - 2`.
* `(p-1)! F⁽ᵖ⁻¹⁾₀(x) ≡ x qₚ(x)^(p-1) - x qₚ(x) (mod p)`, the exceptional case `j = p - 1`.
* The p-adic valuation of the Moore determinant `det Mₚ(x₁, …, x_d)` is at least `C(d+1, 3)`.
* That valuation equals `C(d+1, 3)` exactly when `qₚ(x₁), …, qₚ(x_d)` are pairwise distinct modulo `p`.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependency above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
