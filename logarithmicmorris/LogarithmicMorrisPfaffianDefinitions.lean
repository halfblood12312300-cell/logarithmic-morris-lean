import Mathlib

/-!
# The augmented sawtooth alternating sum
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

def pairLeft (m : ℕ) (r : Fin m) : Fin (2 * m + 1) :=
  ⟨2 * r.1, by omega⟩

def pairRight (m : ℕ) (r : Fin m) : Fin (2 * m + 1) :=
  ⟨2 * r.1 + 1, by omega⟩

/-- Alternation of a product on the standard near-perfect matching. -/
def pairedAlternatingSum (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ∏ r : Fin m, A (σ (pairLeft m r)) (σ (pairRight m r))

/-- The skew matrix whose upper-triangular entries are `y_j-y_i+c`. -/
def sawMatrix (m : ℕ) (c : ℂ) (y : Fin (2 * m + 1) → ℂ)
    (i j : Fin (2 * m + 1)) : ℂ :=
  if i < j then y j - y i + c
  else if j < i then -(y i - y j + c)
  else 0

@[simp] theorem sawMatrix_self (m : ℕ) (c : ℂ)
    (y : Fin (2 * m + 1) → ℂ) (i : Fin (2 * m + 1)) :
    sawMatrix m c y i i = 0 := by
  simp [sawMatrix]

theorem sawMatrix_skew (m : ℕ) (c : ℂ)
    (y : Fin (2 * m + 1) → ℂ) (i j : Fin (2 * m + 1)) :
    sawMatrix m c y j i = -sawMatrix m c y i j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [sawMatrix, hij, not_lt_of_ge hij.le]
  · subst j
    simp
  · simp [sawMatrix, hij, not_lt_of_ge hij.le]

end LogarithmicMorrisFull
