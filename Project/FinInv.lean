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
