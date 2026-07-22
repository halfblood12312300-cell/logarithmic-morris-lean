import logarithmicmorris.ScratchSkew

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- Alternating a product over disjoint ordered pairs only sees the
skew-symmetric part, with one factor of two per pair. -/
theorem pairedAlternatingSum_skewPart (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (fun i j => A i j - A j i) =
      (2 : ℂ) ^ m * pairedAlternatingSum m A := by
  exact pairedAlternatingSum_skewPart_full m A

end LogarithmicMorrisFull
