import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

/- We'll be proving the irrationality of √2.
  This file was adapted from the book `Mathematics in Lean`. -/

/- Let's first get acquainted with the basic ingredients: gcds, coprimality and prime numbers. -/

--Two numbers are coprime iff their gcd is 1
#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h -- Note: this rewrite is not strictly necessary
  exact h

/- There are multiple equivalent definitions of prime numbers -/
#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

/- In the exercises below, the following might be useful lemmas-/
#check Nat.Prime.dvd_mul -- {p m n : ℕ} (pp : Nat.Prime p) :  p ∣ m * n ↔ p ∣ m ∨ p ∣ n
-- The above lemma applied to the fact that 2 is prime
#check Nat.Prime.dvd_mul Nat.prime_two -- 2 ∣ a * b ↔ 2 ∣ a ∨ 2 ∣ b
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

/- √2 can not be written as a quotient of two natural numbers -/
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    sorry
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
    sorry
  have : 2 ∣ n := by
    sorry
  have : 2 ∣ m.gcd n := by
    sorry
  have : 2 ∣ 1 := by
    sorry
  norm_num at this

-- As a challenge, you can try to generalize the above proof for an arbitrary prime `p`
example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  sorry
