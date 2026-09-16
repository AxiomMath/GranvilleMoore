/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import GranvilleMoore

/-! # The solution file

The statements of `Challenge/Basic.lean`, proved from this repository's library.

-/

@[expose] public section

namespace GranvilleMoore.Challenge

/-- **`thm_fermat_integral` — integrality of the iterated Fermat quotients.** For an odd
prime `p`, an integer `x` prime to `p`, and `j ≤ p - 1`, the rational number
`F^{(j)}_k(x)` is an integer. -/
theorem thm_fermat_integral {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 1) (k : ℕ) :
    ∃ z : ℤ, iteratedFermatQuot p j k x = (z : ℚ) :=
  exists_intCast_iteratedFermatQuot hp hodd hx hj k

/-- **`thm_fermat_congruence` — the iterated Fermat quotients modulo `p`.** For an odd
prime `p`, an integer `x` prime to `p`, and `j ≤ p - 2`, the integer `j! F^{(j)}_k(x)` is
congruent to `x q_p(x) ^ j` modulo `p`. -/
theorem thm_fermat_congruence {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {j : ℕ} (hj : j ≤ p - 2) (k : ℕ) {z q : ℤ}
    (hz : iteratedFermatQuot p j k x = (z : ℚ)) (hq : fermatQuotient p x = (q : ℚ)) :
    (j.factorial : ℤ) * z ≡ x * q ^ j [ZMOD (p : ℤ)] :=
  Int.ModEq.symm (Int.modEq_iff_dvd.mpr
    (dvd_factorial_mul_sub_mul_pow hp hodd hx hj k hz hq))

/-- **`thm_fermat_congruence_exceptional` — the exceptional congruence.** At `j = p - 1`
the pattern of `thm_fermat_congruence` breaks: `(p-1)! F^{(p-1)}_0(x)` is congruent to
`x q_p(x) ^ (p-1) - x q_p(x)` modulo `p`. -/
theorem thm_fermat_congruence_exceptional {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) {z q : ℤ}
    (hz : iteratedFermatQuot p (p - 1) 0 x = (z : ℚ)) (hq : fermatQuotient p x = (q : ℚ)) :
    ((p - 1).factorial : ℤ) * z ≡ x * q ^ (p - 1) - x * q [ZMOD (p : ℤ)] :=
  Int.ModEq.symm (Int.modEq_iff_dvd.mpr
    (dvd_factorial_mul_sub_exceptional hp hodd hx hz hq))

/-- **`thm_lower_bound` — the lower bound.** For an odd prime `p`, `1 ≤ d ≤ p` and
integers `x_1, …, x_d` prime to `p` with nonzero Moore determinant, the `p`-adic valuation
of that determinant is at least `C(d+1, 3)`. -/
theorem thm_lower_bound {p d : ℕ} (hp : p.Prime) (hodd : Odd p) (hd : 1 ≤ d) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) (hdet : (mooreMatrix p x).det ≠ 0) :
    Nat.choose (d + 1) 3 ≤ padicValInt p (mooreMatrix p x).det := by
  have hfact : Fact p.Prime := ⟨hp⟩
  rcases (padicValInt_dvd_iff _ _).mp (pow_dvd_det_mooreMatrix hp hodd hd hdp hx hdet) with h | h
  · exact absurd h hdet
  · exact h

/-- **`thm_main` — equality in the Moore determinant bound.** Under the hypotheses of
`thm_lower_bound`, the valuation equals `C(d+1, 3)` exactly when the Fermat quotients
`q_p(x_1), …, q_p(x_d)` are pairwise distinct modulo `p`. -/
theorem thm_main {p d : ℕ} (hp : p.Prime) (hodd : Odd p) (hd : 1 ≤ d) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) (hdet : (mooreMatrix p x).det ≠ 0) :
    padicValInt p (mooreMatrix p x).det = Nat.choose (d + 1) 3
      ↔ Function.Injective fun j => ((q j : ZMod p)) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hlow : (p : ℤ) ^ Nat.choose (d + 1) 3 ∣ (mooreMatrix p x).det :=
    pow_dvd_det_mooreMatrix hp hodd hd hdp hx hdet
  have hiff := not_pow_succ_dvd_det_mooreMatrix_iff hp hodd hd hdp hx hq hdet
  have hle : Nat.choose (d + 1) 3 ≤ padicValInt p (mooreMatrix p x).det := by
    rcases (padicValInt_dvd_iff _ _).mp hlow with h | h
    · exact absurd h hdet
    · exact h
  rw [← hiff]
  constructor
  · intro h hcon
    rcases (padicValInt_dvd_iff _ _).mp hcon with h' | h'
    · exact hdet h'
    · omega
  · intro h
    by_contra hne
    exact h ((padicValInt_dvd_iff _ _).mpr (Or.inr (by omega)))

end GranvilleMoore.Challenge
