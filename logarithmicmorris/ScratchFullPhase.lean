import logarithmicmorris.ScratchChamber
import logarithmicmorris.ScratchKernelEval

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

theorem prod_midpoint_cexp (m : ℕ) (θ : Fin (2 * m + 1) → ℝ) :
    (∏ p ∈ increasingPairs (2 * m + 1),
        Complex.exp (((θ p.1 + θ p.2) / 2) * Complex.I)) =
      ∏ i : Fin (2 * m + 1),
        Complex.exp (θ i * Complex.I) ^ m := by
  simp_rw [← Complex.exp_nsmul]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  congr 1
  have hsum := sum_increasingPairs (2 * m + 1)
    (fun i : Fin (2 * m + 1) => (θ i : ℂ))
  simp only at hsum
  push_cast at hsum ⊢
  rw [← Finset.sum_mul]
  simp_rw [nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  linear_combination (Complex.I / 2) * hsum

theorem vandermonde_centered_on_ordered_chamber (m : ℕ)
    (θ : Fin (2 * m + 1) → ℝ)
    (horder : ∀ i j, i < j → θ i < θ j)
    (hwidth : ∀ i j, i < j → θ j - θ i < 2 * Real.pi) :
    (∏ p ∈ increasingPairs (2 * m + 1),
        (Complex.exp (θ p.1 * Complex.I) -
          Complex.exp (θ p.2 * Complex.I))) *
      (∏ i : Fin (2 * m + 1),
        (Complex.exp (θ i * Complex.I))⁻¹ ^ m) =
      (-Complex.I) ^ (m * (2 * m + 1)) *
        ∏ p ∈ increasingPairs (2 * m + 1),
          (‖Complex.exp (θ p.1 * Complex.I) -
            Complex.exp (θ p.2 * Complex.I)‖ : ℂ) := by
  have hpair (p : Fin (2 * m + 1) × Fin (2 * m + 1))
      (hp : p ∈ increasingPairs (2 * m + 1)) :
      Complex.exp (θ p.1 * Complex.I) - Complex.exp (θ p.2 * Complex.I) =
        (-Complex.I) * Complex.exp (((θ p.1 + θ p.2) / 2) * Complex.I) *
          (‖Complex.exp (θ p.1 * Complex.I) -
            Complex.exp (θ p.2 * Complex.I)‖ : ℂ) := by
    have hp' : p.1 < p.2 := by
      simpa [increasingPairs] using hp
    exact cexp_sub_cexp_ordered (horder p.1 p.2 hp') (hwidth p.1 p.2 hp')
  rw [Finset.prod_congr rfl hpair]
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const, card_increasingPairs_odd, prod_midpoint_cexp]
  rw [show
    ((-Complex.I) ^ (m * (2 * m + 1)) *
          ∏ i : Fin (2 * m + 1), Complex.exp (θ i * Complex.I) ^ m) *
        (∏ p ∈ increasingPairs (2 * m + 1),
          (‖Complex.exp (θ p.1 * Complex.I) -
            Complex.exp (θ p.2 * Complex.I)‖ : ℂ)) *
        (∏ i : Fin (2 * m + 1),
          (Complex.exp (θ i * Complex.I))⁻¹ ^ m) =
      (-Complex.I) ^ (m * (2 * m + 1)) *
        ((∏ i : Fin (2 * m + 1), Complex.exp (θ i * Complex.I) ^ m) *
          (∏ i : Fin (2 * m + 1),
            (Complex.exp (θ i * Complex.I))⁻¹ ^ m)) *
        (∏ p ∈ increasingPairs (2 * m + 1),
          (‖Complex.exp (θ p.1 * Complex.I) -
            Complex.exp (θ p.2 * Complex.I)‖ : ℂ)) by ring]
  rw [← Finset.prod_mul_distrib]
  simp

end LogarithmicMorrisFull
