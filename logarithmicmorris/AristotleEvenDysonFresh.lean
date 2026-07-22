import logarithmicmorris.ScratchGoodBoundary

/-!
# The integer Dyson constant-term identity

This is a focused scratch target for Aristotle.  The intended proof is Good's
finite induction: first prove the inhomogeneous identity with a vector of row
exponents, use the Lagrange partial-fraction recurrence when every exponent is
positive, and remove a zero row at the boundary.  Everything here is a finite
Laurent polynomial; no analytic continuation or unproved constant-term theorem
may be assumed.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- The ordinary (even-exponent) Dyson Laurent polynomial. -/
def evenDysonLaurent (n q : ℕ) : Laurent ℚ n :=
  ∏ p ∈ increasingPairs n,
    (1 - ratio p.1 p.2) ^ q * (1 - ratio p.2 p.1) ^ q

/-- Dyson's constant-term identity, in the equal-exponent specialization. -/
theorem constantTerm_evenDysonLaurent (n q : ℕ) :
    MultiLaurent.constantTerm (evenDysonLaurent n q) =
      (((n * q).factorial : ℚ) / (q.factorial : ℚ) ^ n) := by
  have hkernel :
      evenDysonLaurent n q = goodKernel n Finset.univ (fun _ => q) := by
    rw [goodKernel_univ_eq_ordered, prod_orderedPairs_generic]
    rfl
  rw [hkernel, constantTerm_goodKernel, goodFormula_univ_const]

end LogarithmicMorrisFull
