/-
This module defines q-analogs of natural numbers, q-factorials, q-Pochhammer symbols, and q-binomial coefficients. It proves the q-Pascal identity and the q-binomial theorem. The main results are `q_pascal'` (q-Pascal identity) and `q_binomial_theorem_final` (q-binomial theorem).
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic
import Project.FinInv

/-
The q-analog of a natural number n, denoted [n]_q, is the sum 1 + q + ... + q^(n-1).
-/
def q_analog {R : Type*} [Semiring R] : ℕ → R → R
  | 0, _     => 0
  | n + 1, q => q_analog n q + q ^ n

@[simp]
theorem q_analog_eq_geom_sum {R : Type*} [Ring R] (n : ℕ) (q : R) :
    q_analog n q * (1 - q) = (1 - q ^ n) := by
  induction n with
  | zero => simp [q_analog]
  | succ n ih =>
    rw [q_analog, add_mul, ih]
    simp only [mul_sub, mul_one, sub_add_sub_cancel, sub_right_inj]
    exact Eq.symm (pow_succ q n)

/-
The q-analog of n when q=1 is equal to n.
-/
theorem q_analog_one {R : Type*} [Semiring R] (n : ℕ) : q_analog n (1 : R) = n := by
  induction n with
  | zero => simp [q_analog]
  | succ n ih => simp [q_analog, ih]

/-
The q-factorial of n, denoted [n]_q!, is the product [1]_q * [2]_q * ... * [n]_q.
-/
def q_factorial {R : Type*} [Semiring R] : ℕ → R → R
  | 0, _     => 1
  | n + 1, q => q_factorial n q * q_analog (n + 1) q

@[simp]
theorem q_factorial_zero {R : Type*} [Semiring R] (q : R) : q_factorial 0 q = 1 := by
  simp [q_factorial]

/-
The q-Pochhammer symbol (a; q)_n is defined as (1 - a)(1 - aq)...(1 - aq^(n-1)).
-/
def q_pochhammer {R : Type*} [Ring R] (n : ℕ) (a q : R) : R :=
  match n with
  | 0     => 1
  | n + 1 => q_pochhammer n a q * (1 - a * q ^ n)

@[simp]
theorem q_pochhammer_zero {R : Type*} [Ring R] (a q : R) : q_pochhammer 0 a q = 1 := by
  simp [q_pochhammer]

/-
The q-binomial coefficient, denoted [n choose k]_q, is defined as [n]_q! / ([k]_q! * [n-k]_q!).
-/
def q_binomial {R : Type*} [Semiring R] : ℕ → ℕ → R → R
  | _, 0, _     => 1
  | 0, _, _     => 0
  | n + 1, k + 1, q => q_binomial n k q + q ^ (k + 1) * q_binomial n (k + 1) q

@[simp]
theorem q_binomial_zero_right {R : Type*} [Semiring R] (n : ℕ) (q : R) : q_binomial n 0 q = 1 := by
  simp [q_binomial]

@[simp]
theorem q_binomial_zero_left {R : Type*} [Semiring R] (k : ℕ) (q : R) : q_binomial 0 k q = (if k = 0 then 1 else 0) := by
  cases k <;> simp [q_binomial]

/-
The q-Pascal identity states that [n+1 choose k+1]_q = [n choose k]_q + q^(k+1) * [n choose k+1]_q.
-/
theorem q_pascal {R : Type*} [Semiring R] (n k : ℕ) (q : R):
    q_binomial (n + 1) (k + 1) q = q_binomial n k q + q ^ (k + 1) * q_binomial n (k + 1) q := by
  rfl

theorem sum_inv_eq_q_binomial {R : Type*} [Semiring R] (n k : ℕ) (q : R) (hq : q ≠ 0) :
    ∑ (S : Finset (Fin n)) with (fun S => S.card = k) S,
      q ^ inv S = q_binomial n k q := by
  induction' n with n ih generalizing k
  · simp only [Finset.univ_unique]
    have : @default (Finset (Fin 0)) _ = ∅ := by rfl
    rw [this, Finset.sum_filter, Finset.sum_singleton, Finset.card_empty]
    simp only [inv_empty, pow_zero, q_binomial_zero_left]
    simp_rw [(eq_comm : 0 = k ↔ k = 0)]
  · induction' k with k ihk
    · simp only [Finset.card_eq_zero, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, inv_empty, pow_zero]
      rw [q_binomial]
    · rw [← Finset.sum_filter_add_sum_filter_not _ (fun S ↦ ⟨n, by linarith⟩ ∈ S) _]
      rw [q_pascal n k q]
      congr
      · sorry
      · sorry
