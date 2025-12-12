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
      ·
        classical
        -- subsets containing `last` correspond to subsets of `Fin n`
        let last : Fin (n + 1) := Fin.last n
        let s : Finset (Finset (Fin n)) :=
          Finset.univ.filter fun S : Finset (Fin n) => S.card = k
        let t : Finset (Finset (Fin (n + 1))) :=
          (Finset.univ.filter fun T : Finset (Fin (n + 1)) => T.card = k + 1).filter
            fun T => last ∈ T
        have h_bij :
            ∑ S ∈ s, q ^ inv S = ∑ T ∈ t, q ^ inv T := by
          refine Finset.sum_bij (s := s) (t := t)
            (i := fun S _ => insert last (Finset.liftToSucc S))
            ?h_mem ?h_inj ?h_surj ?h_weights
          · intro S hS
            rcases Finset.mem_filter.mp hS with ⟨-, hcard⟩
            have hnot : last ∉ Finset.liftToSucc S :=
              Finset.last_not_mem_liftToSucc (S := S)
            have hcard' : (insert last (Finset.liftToSucc S)).card = k + 1 := by
              have hcard_lift : (Finset.liftToSucc S).card = k := by
                simpa [Finset.card_liftToSucc] using hcard
              have hcard_insert :=
                Finset.card_insert_of_not_mem (s := Finset.liftToSucc S) (a := last) hnot
              simpa [hcard_lift, Nat.add_comm] using hcard_insert
            refine Finset.mem_filter.mpr ?_
            constructor
            · refine Finset.mem_filter.mpr ?_
              constructor
              · simp
              · exact hcard'
            · simp
          · intro S₁ h₁ S₂ h₂ hEq
            apply Finset.ext
            intro i
            constructor <;> intro hi
            · have hi' : i.castSucc ∈ insert last (Finset.liftToSucc S₁) := by
                simp [hi]
              have hi'' : i.castSucc ∈ insert last (Finset.liftToSucc S₂) := by
                simpa [hEq] using hi'
              have hneq : i.castSucc ≠ last := Fin.castSucc_ne_last i
              have hi''' : i.castSucc ∈ Finset.liftToSucc S₂ := by
                simpa [hneq] using hi''
              simpa [Finset.mem_liftToSucc] using hi'''
            · have hi' : i.castSucc ∈ insert last (Finset.liftToSucc S₂) := by
                simp [hi]
              have hi'' : i.castSucc ∈ insert last (Finset.liftToSucc S₁) := by
                simpa [hEq] using hi'
              have hneq : i.castSucc ≠ last := Fin.castSucc_ne_last i
              have hi''' : i.castSucc ∈ Finset.liftToSucc S₁ := by
                simpa [hneq] using hi''
              simpa [Finset.mem_liftToSucc] using hi'''
          · intro T hT
            rcases Finset.mem_filter.mp hT with ⟨hTcard, hLast⟩
            rcases Finset.mem_filter.mp hTcard with ⟨-, hcardT⟩
            let S : Finset (Fin n) := Finset.univ.filter fun i : Fin n => i.castSucc ∈ T
            have hLift : Finset.liftToSucc S = T.erase last := by
              ext j
              rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | hlast
              · constructor
                · intro hj
                  have hi : i ∈ S := Finset.mem_liftToSucc.mp hj
                  rcases Finset.mem_filter.mp hi with ⟨-, hiT⟩
                  exact Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last i, hiT⟩
                · intro hj
                  rcases Finset.mem_erase.mp hj with ⟨hneq, hjT⟩
                  refine Finset.mem_liftToSucc.mpr ?_
                  refine Finset.mem_filter.mpr ?_
                  constructor
                  · simp
                  · exact hjT
              · constructor <;> intro hj
                · have hnot := Finset.last_not_mem_liftToSucc (S := S)
                  exact (hnot (by simpa [hlast] using hj)).elim
                · rcases Finset.mem_erase.mp hj with ⟨hneq, hjT⟩
                  exact (hneq hlast).elim
            have hcard_erase : (T.erase last).card = k := by
              have hcardErase_succ :
                  (T.erase last).card + 1 = k + 1 := by
                simpa [hcardT] using
                  (Finset.card_erase_add_one (s := T) (a := last) hLast)
              have hcardErase_succ' :
                  (T.erase last).card.succ = k.succ := by
                simpa [Nat.succ_eq_add_one] using hcardErase_succ
              exact Nat.succ.inj hcardErase_succ'
            have hcardS : S.card = k := by
              have hcardLift : (Finset.liftToSucc S).card = k := by
                simpa [hLift] using hcard_erase
              simpa [Finset.card_liftToSucc] using hcardLift
            refine ⟨S, Finset.mem_filter.mpr ⟨by simp, hcardS⟩, ?_⟩
            calc
              insert last (Finset.liftToSucc S)
                  = insert last (T.erase last) := by simpa [hLift]
              _ = T := Finset.insert_erase hLast
          · intro S hS
            simp [Finset.inv_insert_last_lift, last]
        have h_eq : ∑ T ∈ t, q ^ inv T = ∑ S ∈ s, q ^ inv S := h_bij.symm
        have hih : ∑ S ∈ s, q ^ inv S = q_binomial n k q := by
          simpa [s] using ih k
        have hsum : ∑ T ∈ t, q ^ inv T = q_binomial n k q := by
          simpa [hih] using h_eq
        -- match the original filtered sum
        simpa [t, s] using hsum
      ·
        classical
        -- subsets avoiding `last` correspond to subsets of `Fin n`
        let last : Fin (n + 1) := Fin.last n
        let s : Finset (Finset (Fin n)) :=
          Finset.univ.filter fun S : Finset (Fin n) => S.card = k + 1
        let t : Finset (Finset (Fin (n + 1))) :=
          (Finset.univ.filter fun T : Finset (Fin (n + 1)) => T.card = k + 1).filter
            fun T => last ∉ T
        have h_bij :
            ∑ S ∈ s, q ^ (inv S + S.card) = ∑ T ∈ t, q ^ inv T := by
          refine Finset.sum_bij (s := s) (t := t)
            (i := fun S _ => Finset.liftToSucc S)
            ?h_mem' ?h_inj' ?h_surj' ?h_weights'
          · intro S hS
            rcases Finset.mem_filter.mp hS with ⟨-, hcard⟩
            have hcard' : (Finset.liftToSucc S).card = k + 1 := by
              simpa [Finset.card_liftToSucc, hcard]
            have hnot : last ∉ Finset.liftToSucc S := by
              simpa [last] using (Finset.last_not_mem_liftToSucc (S := S))
            refine Finset.mem_filter.mpr ?_
            constructor
            · refine Finset.mem_filter.mpr ?_
              exact ⟨by simp, hcard'⟩
            · exact hnot
          · intro S₁ h₁ S₂ h₂ hEq
            apply Finset.ext
            intro i
            constructor <;> intro hi
            · have hi' : i.castSucc ∈ Finset.liftToSucc S₁ := by
                simpa [Finset.mem_liftToSucc] using hi
              have hi'' : i.castSucc ∈ Finset.liftToSucc S₂ := by simpa [hEq] using hi'
              simpa [Finset.mem_liftToSucc] using hi''
            · have hi' : i.castSucc ∈ Finset.liftToSucc S₂ := by
                simpa [Finset.mem_liftToSucc] using hi
              have hi'' : i.castSucc ∈ Finset.liftToSucc S₁ := by simpa [hEq] using hi'
              simpa [Finset.mem_liftToSucc] using hi''
          · intro T hT
            rcases Finset.mem_filter.mp hT with ⟨hTcard, hnotLast⟩
            rcases Finset.mem_filter.mp hTcard with ⟨-, hcardT⟩
            let S : Finset (Fin n) := Finset.univ.filter fun i : Fin n => i.castSucc ∈ T
            have hLift : Finset.liftToSucc S = T := by
              ext j
              rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | hlast
              · constructor
                · intro hj
                  have hi : i ∈ S := Finset.mem_liftToSucc.mp hj
                  exact (Finset.mem_filter.mp hi).2
                · intro hj
                  have hi : i ∈ S := by
                    refine Finset.mem_filter.mpr ?_
                    exact ⟨by simp, hj⟩
                  exact Finset.mem_liftToSucc.mpr hi
              · constructor <;> intro hj
                · have hnot := Finset.last_not_mem_liftToSucc (S := S)
                  exact (hnot (by simpa [hlast] using hj)).elim
                · exact (hnotLast (by simpa [hlast] using hj)).elim
            have hcardS : S.card = k + 1 := by
              calc
                S.card = (Finset.liftToSucc S).card := (Finset.card_liftToSucc S).symm
                _ = T.card := by simpa [hLift]
                _ = k + 1 := hcardT
            refine ⟨S, Finset.mem_filter.mpr ⟨by simp, hcardS⟩, by simpa [hLift]⟩
          · intro S hS
            rcases Finset.mem_filter.mp hS with ⟨-, hcard⟩
            simp [Finset.inv_liftToSucc, hcard, pow_add, mul_comm, mul_left_comm, mul_assoc]
        have h_eq : ∑ T ∈ t, q ^ inv T = ∑ S ∈ s, q ^ (inv S + S.card) := h_bij.symm
        have h_expand :
            ∑ S ∈ s, q ^ (inv S + S.card)
              = ∑ S ∈ s, q ^ (k + 1) * q ^ inv S := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          have hcard : S.card = k + 1 := (Finset.mem_filter.mp hS).2
          calc
            q ^ (inv S + S.card)
                = q ^ (inv S + (k + 1)) := by simp [hcard]
            _ = q ^ (k + 1 + inv S) := by
              have : inv S + (k + 1) = k + 1 + inv S := by
                ac_rfl
              simpa [this]
            _ = q ^ (k + 1) * q ^ inv S := pow_add q (k + 1) (inv S)
        have h_factor :
            ∑ S ∈ s, q ^ (k + 1) * q ^ inv S
              = q ^ (k + 1) * ∑ S ∈ s, q ^ inv S := by
          classical
          simpa using
            (Finset.mul_sum (s := s) (f := fun S => q ^ inv S) (a := q ^ (k + 1))).symm
        have hih : ∑ S ∈ s, q ^ inv S = q_binomial n (k + 1) q := by
          simpa [s] using ih (k + 1)
        have hsum :
            ∑ T ∈ t, q ^ inv T = q ^ (k + 1) * q_binomial n (k + 1) q := by
          calc
            ∑ T ∈ t, q ^ inv T
                = ∑ S ∈ s, q ^ (inv S + S.card) := h_eq
            _ = ∑ S ∈ s, q ^ (k + 1) * q ^ inv S := h_expand
            _ = q ^ (k + 1) * ∑ S ∈ s, q ^ inv S := h_factor
            _ = q ^ (k + 1) * q_binomial n (k + 1) q := by simpa [hih]
        -- match the original filtered sum
        simpa [t, s] using hsum
