/- Utilities about inversion counts on subsets of `Fin n`. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Finset

/-- Inversion statistic on a subset of `Fin n`: counts pairs `(i,j)` with `i ∈ S`, `j > i`,
and `j ∉ S`. Implemented via a filter on `Finset.univ` to avoid extra finiteness instances. -/
def finInv {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  ∑ i ∈ S, (Finset.univ.filter (fun j : Fin n => j > i ∧ j ∉ S)).card

@[simp]
lemma finInv_empty {n : ℕ} : finInv (∅ : Finset (Fin n)) = 0 := by
  simp [finInv]

end Finset

/-- Convenient alias for `Finset.finInv`. -/
def inv {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  Finset.finInv S

@[simp] lemma inv_empty {n : ℕ} : inv (∅ : Finset (Fin n)) = 0 := by
  simp [inv, Finset.finInv_empty]

namespace Finset

variable {n : ℕ}

/-- Embed a subset of `Fin n` into `Fin (n + 1)` by skipping the last element. -/
def liftToSucc (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map Fin.castSuccEmb

@[simp] lemma card_liftToSucc (S : Finset (Fin n)) : (liftToSucc S).card = S.card := by
  classical
  simpa [liftToSucc] using card_map (Fin.castSuccEmb) S

@[simp] lemma mem_liftToSucc {S : Finset (Fin n)} {x : Fin n} :
    x.castSucc ∈ liftToSucc S ↔ x ∈ S := by
  classical
  simpa [liftToSucc] using (Finset.mem_map' (f := Fin.castSuccEmb) (s := S) (a := x))

@[simp] lemma last_not_mem_liftToSucc (S : Finset (Fin n)) :
    Fin.last n ∉ liftToSucc S := by
  classical
  intro h
  have h' : Fin.last n ∈ S.map Fin.castSuccEmb := by
    simpa [liftToSucc] using h
  rcases mem_map.mp h' with ⟨x, _, hx⟩
  have hxval : (x : ℕ) = n := by
    have := congrArg Fin.val hx
    simpa [Fin.castSuccEmb] using this
  exact (Nat.ne_of_lt x.is_lt) hxval

/-- Inserting a dummy top element contributes exactly one extra inversion for every element of `S`. -/
@[simp] lemma inv_liftToSucc (S : Finset (Fin n)) :
    inv (liftToSucc S) = inv S + S.card := by
  classical
  have h_image : liftToSucc S = S.image Fin.castSucc := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, hkx⟩
      exact Finset.mem_map.mpr ⟨k, hk, by simpa [Fin.castSuccEmb] using hkx⟩
  unfold inv Finset.finInv
  -- rewrite the outer sum over `liftToSucc S` as a sum over `S`
  have h_sum :
      ∑ i ∈ S.image Fin.castSucc,
        (Finset.univ.filter
          (fun j : Fin (n + 1) => j > i ∧ j ∉ liftToSucc S)).card
        =
      ∑ i ∈ S,
        (Finset.univ.filter
          (fun j : Fin (n + 1) => j > i.castSucc ∧ j ∉ liftToSucc S)).card := by
    refine Finset.sum_image ?_
    intro a ha b hb h
    simpa using h
  -- simplify the inner counts: `Fin.last n` is always counted
  have h_inner (i : Fin n) :
      (Finset.univ.filter
          (fun j : Fin (n + 1) => j > i.castSucc ∧ j ∉ liftToSucc S)).card
        =
      (Finset.univ.filter (fun j : Fin n => j > i ∧ j ∉ S)).card + 1 := by
    let p : Fin (n + 1) → Prop :=
      fun j => j > i.castSucc ∧ j ∉ liftToSucc S
    let q : Fin n → Prop :=
      fun j => j > i ∧ j ∉ S
    have hlast : Fin.last n ∈ Finset.univ.filter p := by
      simp [p, last_not_mem_liftToSucc]
    have h_erase :
        (Finset.univ.filter p).erase (Fin.last n)
          =
        (Finset.univ.filter q).map Fin.castSuccEmb := by
      ext j
      constructor
      · intro hj
        rcases Finset.mem_erase.mp hj with ⟨hneq, hj⟩
        rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
        · refine Finset.mem_map.mpr ?_
          refine ⟨k, ?_, rfl⟩
          refine Finset.mem_filter.mpr ?_
          constructor
          · simp
          ·
            have hjp : p (Fin.castSucc k) := (Finset.mem_filter.mp hj).2
            simpa [p, q, mem_liftToSucc] using hjp
        · exact (hneq rfl).elim
      · intro hj
        rcases Finset.mem_map.mp hj with ⟨k, hk, rfl⟩
        have hkq : q k := (Finset.mem_filter.mp hk).2
        have hmem : (Fin.castSucc k) ∈ Finset.univ.filter p := by
          refine Finset.mem_filter.mpr ?_
          constructor
          · simp
          · simpa [p, q, mem_liftToSucc] using hkq
        have hneq : Fin.castSucc k ≠ Fin.last n := Fin.castSucc_ne_last k
        exact Finset.mem_erase.mpr ⟨hneq, hmem⟩
    calc
      (Finset.univ.filter
          (fun j : Fin (n + 1) => j > i.castSucc ∧ j ∉ liftToSucc S)).card
          = ((Finset.univ.filter p).erase (Fin.last n)).card + 1 := by
            simpa using
              (Finset.card_erase_add_one (s := Finset.univ.filter p) (a := Fin.last n) hlast).symm
      _ = ((Finset.univ.filter q).map Fin.castSuccEmb).card + 1 := by
        simpa [p, q, h_erase]
      _ = (Finset.univ.filter (fun j : Fin n => j > i ∧ j ∉ S)).card + 1 := by
        simpa [q] using (Finset.card_map (Fin.castSuccEmb) (Finset.univ.filter q))
  -- assemble the final sum
  calc
    ∑ i ∈ liftToSucc S,
        (Finset.univ.filter
          (fun j : Fin (n + 1) => j > i ∧ j ∉ liftToSucc S)).card
        =
        ∑ i ∈ S.image Fin.castSucc,
          (Finset.univ.filter
            (fun j : Fin (n + 1) => j > i ∧ j ∉ liftToSucc S)).card := by
      simpa [h_image]
    _ = ∑ i ∈ S,
          (Finset.univ.filter
          (fun j : Fin (n + 1) => j > i.castSucc ∧ j ∉ liftToSucc S)).card := h_sum
    _ = ∑ i ∈ S,
          ((Finset.univ.filter (fun j : Fin n => j > i ∧ j ∉ S)).card + 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa using h_inner i
    _ = ∑ i ∈ S, (Finset.univ.filter (fun j : Fin n => j > i ∧ j ∉ S)).card
          + ∑ _i ∈ S, (1 : ℕ) := by
      simp [Finset.sum_add_distrib]
    _ = ∑ i ∈ S, (Finset.univ.filter (fun j : Fin n => j > i ∧ j ∉ S)).card
          + S.card := by
      have hconst : ∀ i ∈ S, (1 : ℕ) = 1 := by intros; rfl
      simpa using (Finset.sum_const_nat (s := S) (f := fun _ => (1 : ℕ)) (m := 1) hconst)
    _ = inv S + S.card := by
      simp [inv, Finset.finInv]

end Finset
