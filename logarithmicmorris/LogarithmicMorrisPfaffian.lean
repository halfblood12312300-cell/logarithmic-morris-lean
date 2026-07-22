import logarithmicmorris.ScratchOrderSignInvolution

/-!
# The augmented sawtooth Pfaffian

This is the finite algebraic identity behind the direct, unconditional proof of
the logarithmic Morris formula.  We use the alternating-permutation definition,
so no Pfaffian library or external axiom is needed.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- The augmented Pfaffian evaluation, expressed without introducing a
Pfaffian primitive. -/
theorem pairedAlternatingSum_sawMatrix (m : ℕ) (c : ℂ)
    (y : Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (sawMatrix m c y) =
      ((2 : ℂ) ^ m * (m.factorial : ℂ)) * c ^ m := by
  exact pairedAlternatingSum_sawMatrix_complete m c y

end LogarithmicMorrisFull
