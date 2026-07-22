import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import logarithmicmorris.LogarithmicMorrisFullArithmetic
import logarithmicmorris.LogarithmicMorrisEvaluation

/-!
# Definitions for the circular Morris integral

This module deliberately contains only concrete definitions.  Separating it
from the evaluation theorem keeps intermediate reductions independent of any
unfinished Selberg/Dyson proof.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory

/-- The symmetric circular-Morris density at exponent `K/2`. -/
def circularMorrisIntegrand (S : Setup) (t : UnitAddTorus (Fin S.n)) : ℂ :=
  (∏ i : Fin S.n,
      (1 - fourier 1 (t i)) ^ S.a *
        (1 - (fourier 1 (t i))⁻¹) ^ S.b) *
    ∏ p ∈ increasingPairs S.n,
      (‖fourier 1 (t p.1) - fourier 1 (t p.2)‖ : ℂ) ^ S.K

/-- The normalized circular Morris integral. -/
def circularMorrisIntegral (S : Setup) : ℂ :=
  ∫ t : UnitAddTorus (Fin S.n), circularMorrisIntegrand S t

end LogarithmicMorrisFull
