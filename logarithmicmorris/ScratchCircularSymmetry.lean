import logarithmicmorris.ScratchPermutationIntegral
import logarithmicmorris.LogarithmicMorrisCircularDefinitions

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

theorem increasingNormProduct_permute {n K : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ℂ) :
    (∏ p ∈ increasingPairs n,
        (‖x (σ p.1) - x (σ p.2)‖ : ℂ) ^ K) =
      ∏ p ∈ increasingPairs n, (‖x p.1 - x p.2‖ : ℂ) ^ K := by
  rw [Finset.prod_pow, Finset.prod_pow]
  have h := congrArg (fun z : ℂ => (‖z‖ : ℂ) ^ K)
    (vandermondeProduct_permute σ x)
  rcases Int.units_eq_one_or σ.sign with hsign | hsign
  · simpa [hsign, norm_prod, norm_mul, norm_pow, Complex.ofReal_prod,
      Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] using h
  · simpa [hsign, norm_prod, norm_mul, norm_pow, Complex.ofReal_prod,
      Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] using h

theorem circularMorrisIntegrand_permute (S : Setup)
    (σ : Equiv.Perm (Fin S.n)) (t : UnitAddTorus (Fin S.n)) :
    circularMorrisIntegrand S (permuteTorus σ t) =
      circularMorrisIntegrand S t := by
  simp only [circularMorrisIntegrand, permuteTorus]
  rw [Equiv.prod_comp σ (fun i : Fin S.n =>
    (1 - fourier 1 (t i)) ^ S.a *
      (1 - (fourier 1 (t i))⁻¹) ^ S.b)]
  rw [increasingNormProduct_permute σ (fun i => fourier 1 (t i))]

end LogarithmicMorrisFull
