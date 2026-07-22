import Mathlib
import Mathlib.Analysis.Fourier.AddCircleMulti
import logarithmicmorris.LogarithmicMorrisEvaluation

/-!
# Boundary logarithms on the unit torus
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- Principal-branch boundary value of the formal series `log(1-z)`. -/
def circleLog (t : UnitAddCircle) : ℂ :=
  Complex.log (1 - fourier 1 t)

/-- Product of the standard disjoint logarithmic pairs. -/
def standardPairedLog (S : Setup) (t : UnitAddTorus (Fin S.n)) : ℂ :=
  ∏ r : Fin S.m, circleLog (t (S.rightVertex r) - t (S.leftVertex r))

end LogarithmicMorrisFull
