import logarithmicmorris.LogarithmicMorrisDysonMomentEvaluation
import logarithmicmorris.LogarithmicMorrisParameterReduction

/-!
# Unconditional logarithmic Morris constant-term identity

The proof has two independent parts.  First, the odd Dyson specialization
`a = b = 0` is evaluated by compact moment determinacy, using the finite
integer Dyson constant-term identity to identify all moments.  Second, the
Adamović--Milas endpoint recurrence reduces arbitrary nonnegative `a,b` to
that specialization.
-/

noncomputable section

namespace LogarithmicMorrisFull

lemma withAB_zero_zero_eq_dysonSetup (S : Setup) :
    S.withAB 0 0 = dysonSetup S S.k := by
  rfl

/-- The displayed logarithmic Morris constant-term identity from Theorem 1.3. -/
theorem logarithmicMorris_full (S : Setup) :
    LogarithmicMorrisStatement S := by
  apply logarithmicMorris_parameter_reduction S
  rw [withAB_zero_zero_eq_dysonSetup]
  exact logarithmicMorris_dyson_proved S S.k

end LogarithmicMorrisFull
