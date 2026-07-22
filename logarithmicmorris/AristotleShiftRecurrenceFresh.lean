import logarithmicmorris.ScratchShiftLogZero

/-!
# The Adamović--Milas endpoint-parameter recurrence

This file isolates the sole remaining parameter-shift identity.  It is a
finite Laurent-polynomial statement about the already concrete functional
`standardLogCT`; no circular integral evaluation is available or allowed here.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- Adamović--Milas recurrence, obtained by summing the coefficientwise
Laurent Euler-derivative identity. -/
theorem shift_recurrence_fresh (S : Setup) (a b r : ℕ) (hr : r < S.n) :
    ((S.n - r : ℕ) : ℚ) * (2 * b + r * S.K : ℕ) * shiftFamily S a b r =
      ((r + 1 : ℕ) : ℚ) *
        (2 * a + 2 + (S.n - r - 1) * S.K : ℕ) *
        shiftFamily S a b (r + 1) := by
  have hpoly := two_localShiftDerivativeSum S a b r hr
  have hct := congrArg (standardLogCT (S.withAB a b)) hpoly
  have hzero := standardLogCT_localShiftDerivativeSum_eq_zero S a b r
  rw [standardLogCT_smul_clean, hzero,
    standardLogCT_add_clean,
    standardLogCT_smul_clean, standardLogCT_smul_clean] at hct
  change
    (2 : ℚ) * 0 =
      -(((S.n - r : ℕ) : ℚ) * (2 * b + r * S.K : ℕ)) *
          shiftFamily S a b r +
        (((r + 1 : ℕ) : ℚ) *
          (2 * a + 2 + (S.n - r - 1) * S.K : ℕ)) *
          shiftFamily S a b (r + 1) at hct
  linear_combination hct

end LogarithmicMorrisFull
