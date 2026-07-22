import logarithmicmorris.ScratchLogCTBridge

/-!
# The formal logarithmic coefficient as a torus integral
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory

/-- Fourier coefficients of the principal logarithm realize exactly the
finite coefficient functional `standardLogCT`. -/
theorem standardLogCT_eq_torusIntegral (S : Setup) (F : Laurent ℚ S.n) :
    ((standardLogCT S F : ℚ) : ℂ) =
      ∫ t : UnitAddTorus (Fin S.n), torusEval F t * standardPairedLog S t := by
  exact standardLogCT_eq_torusIntegral_proved S F

end LogarithmicMorrisFull
