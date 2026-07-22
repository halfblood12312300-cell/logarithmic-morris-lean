import logarithmicmorris.AristotleEvenDysonFresh
import logarithmicmorris.AristotleBetaMomentFresh
import logarithmicmorris.AristotleGammaMultiplicationFresh
import logarithmicmorris.AristotleMomentUniquenessFresh
import logarithmicmorris.LogarithmicMorrisDysonArithmetic
import logarithmicmorris.ScratchKernelEval
import Mathlib.MeasureTheory.Integral.Pi

/-! # Definitions for the compact-moment proof of the circular Dyson integral -/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace LogarithmicMorrisFull

open MeasureTheory

/-- Squared absolute Vandermonde on the normalized unit torus. -/
def circularDiscriminantSq (n : ℕ) (t : UnitAddTorus (Fin n)) : ℝ :=
  ∏ p ∈ increasingPairs n,
    ‖fourier 1 (t p.1) - fourier 1 (t p.2)‖ ^ 2

/-- A globally bounded version of the identity map, equal to it on `[0,1]`. -/
def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The `i`th beta factor in the Mellin factorization of the Dyson moments. -/
def dysonBetaMeasure (n : ℕ) (i : Fin (n - 1)) : Measure ℝ :=
  ProbabilityTheory.betaMeasure
    (((i : ℕ) + 1 : ℝ) / n)
    (1 - (((i : ℕ) + 1 : ℝ) / n))

/-- Product of the beta coordinates, with the Gauss-multiplication scale. -/
def dysonBetaProduct (n : ℕ) (x : Fin (n - 1) → ℝ) : ℝ :=
  (n : ℝ) ^ n * ∏ i, clampUnit (x i)

end LogarithmicMorrisFull
