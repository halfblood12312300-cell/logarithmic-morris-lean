import logarithmicmorris.ScratchPointwise
import logarithmicmorris.LogarithmicMorrisDysonArithmetic

/-!
# Reduction of the beta-one Dyson base to a finite logarithmic coefficient

The remaining beta-one task is the finite statement that the centered
Vandermonde has standard logarithmic coefficient one.  This module proves that
this statement already gives the required normalized circular integral.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

theorem circularMorrisIntegral_dyson_zero_of_lhs_one (S : Setup)
    (hLHS : logarithmicMorrisLHS (dysonSetup S 0) = 1) :
    circularMorrisIntegral (dysonSetup S 0) =
      gammaPochhammerPart (dysonSetup S 0) (dysonSetup S 0).K := by
  let D := dysonSetup S 0
  have hbase := morrisKernel_standardPairedLog_integrable D
  have hbridge := standardLogCT_eq_torusIntegral D (morrisKernel D)
  have hcircle := torusLogIntegral_eq_circular D hbase
  have hone : (1 : ℂ) =
      (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral D := by
    calc
      (1 : ℂ) = ((logarithmicMorrisLHS D : ℚ) : ℂ) := by
        rw [hLHS]
        norm_num
      _ = ∫ t : UnitAddTorus (Fin D.n),
          torusEval (morrisKernel D) t * standardPairedLog D t := hbridge
      _ = (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral D := by
        simpa [D] using hcircle
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hcoeff :
      ((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ) ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero S.m)
        (pow_ne_zero _ hpi))
      (by exact_mod_cast Nat.factorial_ne_zero S.n)
  apply (mul_left_cancel₀ hcoeff)
  calc
    (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral D = 1 := hone.symm
    _ = (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) *
        gammaPochhammerPart D D.K := by
      rw [gammaPochhammerPart_dyson]
      norm_num [doubleFactorial_one]
      have hfac := congrArg (fun q : ℕ => (q : ℂ)) (factorial_rank_eq S)
      push_cast at hfac
      rw [hfac]
      have hmf : (S.m.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero S.m
      have hdf : (doubleFactorial S.n : ℂ) ≠ 0 := by
        exact_mod_cast doubleFactorial_ne_zero S.n
      field_simp [hpi, hmf, hdf]
      simp [← mul_pow, hpi]
      congr 1
      field_simp [hpi]

end LogarithmicMorrisFull
