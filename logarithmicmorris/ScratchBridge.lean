import logarithmicmorris.ScratchFullPhase
import logarithmicmorris.LogarithmicMorrisCircularDefinitions

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

def angleTorus {n : ℕ} (θ : Fin n → ℝ) : UnitAddTorus (Fin n) :=
  fun i => ((θ i / (2 * Real.pi) : ℝ) : UnitAddCircle)

@[simp] theorem fourier_angleTorus {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) :
    fourier 1 (angleTorus θ i) = Complex.exp (θ i * Complex.I) := by
  rw [angleTorus, fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem torusEval_morrisKernel_ordered (S : Setup) (θ : Fin S.n → ℝ)
    (horder : ∀ i j, i < j → θ i < θ j)
    (hwidth : ∀ i j, i < j → θ j - θ i < 2 * Real.pi) :
    torusEval (morrisKernel S) (angleTorus θ) =
      (-Complex.I) ^ (S.m * S.n) *
        circularMorrisIntegrand S (angleTorus θ) := by
  rcases S with ⟨n, m, k, a, b, hn⟩
  subst n
  simp only at θ horder hwidth ⊢
  rw [torusEval_morrisKernel, orderedRatioProduct_eq_norm]
  simp only [circularMorrisIntegrand]
  simp_rw [fourier_angleTorus]
  have hphase := vandermonde_centered_on_ordered_chamber m θ horder hwidth
  let V : ℂ := ∏ p ∈ increasingPairs (2 * m + 1),
    (Complex.exp (θ p.1 * Complex.I) - Complex.exp (θ p.2 * Complex.I))
  let C : ℂ := ∏ i : Fin (2 * m + 1),
    (Complex.exp (θ i * Complex.I))⁻¹ ^ m
  let W : ℂ := ∏ i : Fin (2 * m + 1),
    (1 - Complex.exp (θ i * Complex.I)) ^ a *
      (1 - (Complex.exp (θ i * Complex.I))⁻¹) ^ b
  let D : ℂ := ∏ p ∈ increasingPairs (2 * m + 1),
    (‖Complex.exp (θ p.1 * Complex.I) -
      Complex.exp (θ p.2 * Complex.I)‖ : ℂ)
  let E : ℂ := ∏ p ∈ increasingPairs (2 * m + 1),
    (‖Complex.exp (θ p.1 * Complex.I) -
      Complex.exp (θ p.2 * Complex.I)‖ : ℂ) ^ (2 * k)
  have hCW :
      (∏ i : Fin (2 * m + 1),
        (Complex.exp (θ i * Complex.I))⁻¹ ^ m *
          (1 - Complex.exp (θ i * Complex.I)) ^ a *
          (1 - (Complex.exp (θ i * Complex.I))⁻¹) ^ b) = C * W := by
    dsimp [C, W]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hCW]
  change V * (C * W) * E =
    (-Complex.I) ^ (m * (2 * m + 1)) *
      (W * ∏ p ∈ increasingPairs (2 * m + 1),
        (‖Complex.exp (θ p.1 * Complex.I) -
          Complex.exp (θ p.2 * Complex.I)‖ : ℂ) ^ (2 * k + 1))
  change V * C = (-Complex.I) ^ (m * (2 * m + 1)) * D at hphase
  have hDE : D * E =
      ∏ p ∈ increasingPairs (2 * m + 1),
        (‖Complex.exp (θ p.1 * Complex.I) -
          Complex.exp (θ p.2 * Complex.I)‖ : ℂ) ^ (2 * k + 1) := by
    dsimp [D, E]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← pow_succ']
  rw [show V * (C * W) * E = (V * C) * (W * E) by ring, hphase]
  rw [show
    (-Complex.I) ^ (m * (2 * m + 1)) * D * (W * E) =
      (-Complex.I) ^ (m * (2 * m + 1)) * W * (D * E) by ring, hDE]
  ring

end LogarithmicMorrisFull
