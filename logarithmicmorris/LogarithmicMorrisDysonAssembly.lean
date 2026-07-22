import logarithmicmorris.ScratchPointwise
import logarithmicmorris.LogarithmicMorrisDysonArithmetic

/-!
# Assembly of the logarithmic identity at `a=b=0`
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

theorem logarithmicMorris_dyson_of_circular (S : Setup) (k : ℕ)
    (hcircular : circularMorrisIntegral (dysonSetup S k) =
      gammaPochhammerPart (dysonSetup S k) (dysonSetup S k).K) :
    LogarithmicMorrisStatement (dysonSetup S k) := by
  let D := dysonSetup S k
  have hbase := morrisKernel_standardPairedLog_integrable D
  have hcast : ((logarithmicMorrisLHS D : ℚ) : ℂ) =
      ((logarithmicMorrisRHS D : ℚ) : ℂ) := by
    calc
      ((logarithmicMorrisLHS D : ℚ) : ℂ) =
          ∫ t : UnitAddTorus (Fin D.n),
            torusEval (morrisKernel D) t * standardPairedLog D t := by
        exact standardLogCT_eq_torusIntegral D (morrisKernel D)
      _ = (((D.m.factorial : ℂ) * (Real.pi : ℂ) ^ D.m) /
            (D.n.factorial : ℂ)) * circularMorrisIntegral D :=
        torusLogIntegral_eq_circular D hbase
      _ = (((D.m.factorial : ℂ) * (Real.pi : ℂ) ^ D.m) /
            (D.n.factorial : ℂ)) * gammaPochhammerPart D D.K := by
        rw [hcircular]
      _ = ((logarithmicMorrisRHS D : ℚ) : ℂ) := by
        rw [gammaPochhammerPart_at_K]
        have hpi : (Real.pi : ℂ) ≠ 0 := by
          exact_mod_cast Real.pi_ne_zero
        have hn : (D.n.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero D.n
        have hcollapse :
            (((D.m.factorial : ℂ) * (Real.pi : ℂ) ^ D.m) /
                (D.n.factorial : ℂ)) *
                ((2 / (Real.pi : ℂ)) ^ D.m *
                  ∏ i ∈ Finset.range D.n, (rhsFactor D i : ℂ)) =
              (((D.m.factorial : ℂ) * (2 : ℂ) ^ D.m) /
                (D.n.factorial : ℂ)) *
                  ∏ i ∈ Finset.range D.n, (rhsFactor D i : ℂ) := by
          rw [div_pow]
          field_simp [hpi, hn]
        rw [hcollapse]
        have hpref := congrArg (fun q : ℚ => (q : ℂ))
          (factorial_prefactor_eq D)
        push_cast at hpref
        rw [hpref]
        simp only [logarithmicMorrisRHS]
        push_cast
        rfl
  unfold LogarithmicMorrisStatement
  exact_mod_cast hcast

end LogarithmicMorrisFull
