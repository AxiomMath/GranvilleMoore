/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

namespace GranvilleMoore

/-- The unit attached to an integer `x` at `p`: the power `t_x = x ^ (p - 1)`. -/
abbrev fermatUnit (p : ℕ) (x : ℤ) : ℤ := x ^ (p - 1)

/-- The Fermat quotient of an integer `x` at `p`: `q_p(x) = (x ^ (p - 1) - 1) / p`, the
quotient being taken in `ℚ`. -/
def fermatQuotient (p : ℕ) (x : ℤ) : ℚ := ((fermatUnit p x - 1 : ℤ) : ℚ) / (p : ℚ)

/-- The iterated Fermat quotient `F^{(j)}_k(x)`: `F^{(0)}_k(x)` is `x ^ p ^ k`, and
`F^{(j+1)}_k(x)` is the divided difference
`(F^{(j)}_{k+1}(x) - F^{(j)}_k(x)) / p ^ (k + 1)`. -/
def iteratedFermatQuot (p : ℕ) : ℕ → ℕ → ℤ → ℚ
  | 0, k, x => (x : ℚ) ^ p ^ k
  | j + 1, k, x =>
      (iteratedFermatQuot p j (k + 1) x - iteratedFermatQuot p j k x) / (p : ℚ) ^ (k + 1)

/-- The Moore matrix of `x = (x 1, …, x d)` at `p`: the `d × d` matrix whose `(i, j)`
entry is `x j ^ p ^ i`. -/
def mooreMatrix {R : Type*} {d : ℕ} [Monoid R] (p : ℕ) (x : Fin d → R) :
    Matrix (Fin d) (Fin d) R :=
  Matrix.of fun i j => x j ^ p ^ (i : ℕ)

namespace Challenge

/-- **`thm_fermat_integral` — integrality of the iterated Fermat quotients.** For an odd
prime `p`, an integer `x` prime to `p`, and `j ≤ p - 1`, the rational number
`F^{(j)}_k(x)` is an integer. -/
theorem thm_fermat_integral {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 1) (k : ℕ) :
    ∃ z : ℤ, iteratedFermatQuot p j k x = (z : ℚ) :=
  sorry

/-- **`thm_fermat_congruence` — the iterated Fermat quotients modulo `p`.** For an odd
prime `p`, an integer `x` prime to `p`, and `j ≤ p - 2`, the integer `j! F^{(j)}_k(x)` is
congruent to `x q_p(x) ^ j` modulo `p`. -/
theorem thm_fermat_congruence {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 2) (k : ℕ) {z q : ℤ}
    (hz : iteratedFermatQuot p j k x = (z : ℚ)) (hq : fermatQuotient p x = (q : ℚ)) :
    (j.factorial : ℤ) * z ≡ x * q ^ j [ZMOD (p : ℤ)] :=
  sorry

/-- **`thm_fermat_congruence_exceptional` — the exceptional congruence.** At `j = p - 1`
the pattern of `thm_fermat_congruence` breaks: `(p-1)! F^{(p-1)}_0(x)` is congruent to
`x q_p(x) ^ (p-1) - x q_p(x)` modulo `p`. -/
theorem thm_fermat_congruence_exceptional {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {z q : ℤ}
    (hz : iteratedFermatQuot p (p - 1) 0 x = (z : ℚ)) (hq : fermatQuotient p x = (q : ℚ)) :
    ((p - 1).factorial : ℤ) * z ≡ x * q ^ (p - 1) - x * q [ZMOD (p : ℤ)] :=
  sorry

/-- **`thm_lower_bound` — the lower bound.** For an odd prime `p`, `1 ≤ d ≤ p` and
integers `x_1, …, x_d` prime to `p` with nonzero Moore determinant, the `p`-adic valuation
of that determinant is at least `C(d+1, 3)`. -/
theorem thm_lower_bound {p d : ℕ} (hp : p.Prime) (hodd : Odd p) (hd : 1 ≤ d) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) (hdet : (mooreMatrix p x).det ≠ 0) :
    Nat.choose (d + 1) 3 ≤ padicValInt p (mooreMatrix p x).det :=
  sorry

/-- **`thm_main` — equality in the Moore determinant bound.** Under the hypotheses of
`thm_lower_bound`, the valuation equals `C(d+1, 3)` exactly when the Fermat quotients
`q_p(x_1), …, q_p(x_d)` are pairwise distinct modulo `p`. -/
theorem thm_main {p d : ℕ} (hp : p.Prime) (hodd : Odd p) (hd : 1 ≤ d) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) (hdet : (mooreMatrix p x).det ≠ 0) :
    padicValInt p (mooreMatrix p x).det = Nat.choose (d + 1) 3
      ↔ Function.Injective fun j => ((q j : ZMod p)) :=
  sorry

end Challenge

end GranvilleMoore
