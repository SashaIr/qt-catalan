import Mathlib.Combinatorics.Enumerative.DyckWord

namespace DyckWord

open DyckStep
open scoped BigOperators

/-- Helper recursion for computing the area word associated to a Dyck word.  The
second argument tracks the height (the number of `U` steps minus the number of
`D` steps) immediately before the current step. -/
def areaAux : List DyckStep → ℕ → List ℕ
  | [], _ => []
  | U :: xs, h => h :: areaAux xs (h + 1)
  | D :: xs, h => areaAux xs (h - 1)
termination_by xs _ => xs.length
decreasing_by
  all_goals
    simp_wf

/-- The area word of a Dyck word.  This records, for each `U` in the Dyck word,
the difference between the number of `U` and `D` steps seen so far (including
the current `U`).  Equivalently, this is the height of the Dyck path just after
each `U`. -/
def areaWord (p : DyckWord) : List ℕ :=
  areaAux p.toList 0

@[simp] lemma areaWord_nil : areaWord (0 : DyckWord) = [] := by
  change areaAux ([] : List DyckStep) 0 = []
  simp [areaAux]

/-- The area of a Dyck word, i.e. the sum of its area word. -/
def area (p : DyckWord) : ℕ :=
  (areaWord p).sum

@[simp] lemma area_zero : (0 : DyckWord).area = 0 := by
  simp [area]

/-- Counts diagonal inversions of a list, i.e. pairs `i < j` satisfying
`aᵢ = aⱼ` or `aᵢ = aⱼ + 1`. -/
def dinvList : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if x = y ∨ x = y + 1 then 1 else 0) 0
        + dinvList xs

/-- The diagonal inversion statistic of a Dyck word. -/
def dinv (p : DyckWord) : ℕ :=
  dinvList (areaWord p)

@[simp] lemma dinv_zero : (0 : DyckWord).dinv = 0 := by
  simp [dinv, dinvList]

/-- Modify the `n`-th entry of a list. -/
private def modifyNth {α : Type*} : List α → ℕ → (α → α) → List α
  | [], _, _ => []
  | x :: xs, 0, f => f x :: xs
  | x :: xs, n + 1, f => x :: modifyNth xs n f

/-- Retrieve the `n`-th entry of a list, if it exists. -/
private def getNth? {α : Type*} : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getNth? xs n

/-- Find the first entry in `xs` greater than or equal to `y`. -/
private def findGe : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | x :: xs, y => if y ≤ x then some x else findGe xs y

/-- For each column `x`, list the heights `y` at which an east step of the Dyck path begins. -/
private def columnStarts (p : DyckWord) : List (List ℕ) :=
  let n := p.semilength
  let init := List.replicate n []
  let (_, _, cols) :=
    p.toList.foldl
      (fun (state : ℕ × ℕ × List (List ℕ)) step =>
        let (u, d, cols) := state
        match step with
        | U => (u + 1, d, cols)
        | D =>
          let cols' := modifyNth cols d (fun ys => u :: ys)
          (u, d + 1, cols'))
      (0, 0, init)
  cols.map List.reverse

/-- Auxiliary recursion carrying a `fuel` parameter to ensure termination. -/
private def bounceAux (cols : List (List ℕ)) (n : ℕ) :
    ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, curr, acc =>
      if curr = n then acc
      else
        match getNth? cols curr with
        | none => acc
        | some column =>
          match findGe column curr with
          | none => acc
          | some nextY =>
              let acc' := if nextY = n then acc else acc + (n - nextY)
              bounceAux cols n fuel nextY acc'

/-- The bounce statistic of a Dyck word. -/
def bounce (p : DyckWord) : ℕ :=
  let n := p.semilength
  let cols := columnStarts p
  bounceAux cols n n 0 0

@[simp] lemma bounce_zero : (0 : DyckWord).bounce = 0 := by
  simp [bounce, columnStarts, bounceAux]

/-- The `q,t`-Catalan polynomial: sum over all Dyck words of semilength `n` of
`q ^ dinv * t ^ area`. -/
def qtCatalan (n : ℕ) (R : Type*) [Semiring R] (q t : R) : R :=
  ∑ w : {p : DyckWord // p.semilength = n}, q ^ w.1.dinv * t ^ w.1.area

/-- Alternate form of the `q,t`-Catalan polynomial, summing `q^area * t^bounce`. -/
def qtCatalanAlt (n : ℕ) (R : Type*) [Semiring R] (q t : R) : R :=
  ∑ w : {p : DyckWord // p.semilength = n}, q ^ w.1.area * t ^ w.1.bounce

/-- Placeholder theorem asserting the equality of the two `q,t`-Catalan formulations. -/
theorem qtCatalan_eq_qtCatalanAlt (n : ℕ) (R : Type*) [Semiring R] (q t : R) :
    qtCatalan n R q t = qtCatalanAlt n R q t := by
  sorry

end DyckWord
