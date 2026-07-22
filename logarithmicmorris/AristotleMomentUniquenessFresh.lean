import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Compact moment determinacy in the one form needed for circular Dyson

This is a focused Aristotle target.  The domain is already the compact interval,
so no support bookkeeping is needed.  The proof should use density of polynomial
functions (Weierstrass) and continuity of integration for finite measures.
-/

noncomputable section

open MeasureTheory Set
open scoped Polynomial

namespace LogarithmicMorrisFull

/-- Two probability measures on a compact interval with the same power moments
integrate every continuous real function equally. -/
theorem integral_continuous_eq_of_moments_on_Icc (C : ℝ)
    (μ ν : Measure (Set.Icc (0 : ℝ) C))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmom : ∀ q : ℕ,
      (∫ x, (x.1 : ℝ) ^ q ∂μ) = ∫ x, (x.1 : ℝ) ^ q ∂ν)
    (f : C(Set.Icc (0 : ℝ) C, ℝ)) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  have hintegrable (rho : Measure (Set.Icc (0 : ℝ) C))
      [IsProbabilityMeasure rho]
      (g : C(Set.Icc (0 : ℝ) C, ℝ)) : Integrable g rho := by
    have h := ContinuousOn.integrableOn_compact
      (μ := rho) isCompact_univ g.continuous.continuousOn
    change Integrable g (rho.restrict univ) at h
    simpa only [Measure.restrict_univ] using h
  have hpoly (p : ℝ[X]) :
      (∫ x, p.eval (x.1 : ℝ) ∂μ) =
        ∫ x, p.eval (x.1 : ℝ) ∂ν := by
    simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [integral_finset_sum, integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [integral_const_mul, integral_const_mul, hmom q]
    · intro q hq
      have hcont : Continuous
          (fun x : Set.Icc (0 : ℝ) C =>
            p.coeff q * (x.1 : ℝ) ^ q) := by fun_prop
      exact hintegrable ν ⟨_, hcont⟩
    · intro q hq
      have hcont : Continuous
          (fun x : Set.Icc (0 : ℝ) C =>
            p.coeff q * (x.1 : ℝ) ^ q) := by fun_prop
      exact hintegrable μ ⟨_, hcont⟩
  by_contra hne
  have hdiffpos : 0 < abs ((∫ x, f x ∂μ) - ∫ x, f x ∂ν) :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  let eps : ℝ := abs ((∫ x, f x ∂μ) - ∫ x, f x ∂ν) / 3
  have heps : 0 < eps := div_pos hdiffpos (by norm_num)
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap
    (0 : ℝ) C f eps heps
  let g : C(Set.Icc (0 : ℝ) C, ℝ) := p.toContinuousMapOn _
  have hfg : ‖g - f‖ < eps := by simpa [g] using hp
  have hclose (rho : Measure (Set.Icc (0 : ℝ) C))
      [IsProbabilityMeasure rho] :
      |(∫ x, g x ∂rho) - ∫ x, f x ∂rho| < eps := by
    have hgint := hintegrable rho g
    have hfint := hintegrable rho f
    rw [← integral_sub hgint hfint]
    have hnorm :
        ‖∫ x, g x - f x ∂rho‖ ≤ ‖g - f‖ := by
      calc
        ‖∫ x, g x - f x ∂rho‖ ≤
            ‖g - f‖ * rho.real univ :=
          norm_integral_le_of_norm_le_const (by
            filter_upwards with x
            exact ContinuousMap.norm_coe_le_norm (g - f) x)
        _ = ‖g - f‖ := by simp
    exact lt_of_le_of_lt hnorm hfg
  have hpoly' : (∫ x, g x ∂μ) = ∫ x, g x ∂ν := by
    simpa [g] using hpoly p
  have hmu := hclose μ
  have hnu := hclose ν
  have htri :
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| < 2 * eps := by
    calc
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| =
          |((∫ x, f x ∂μ) - ∫ x, g x ∂μ) +
            ((∫ x, g x ∂ν) - ∫ x, f x ∂ν)| := by
        rw [hpoly']
        congr 1
        ring
      _ ≤ |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| +
          |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| := abs_add_le _ _
      _ < eps + eps := by
        have hmu' : |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| < eps := by
          simpa [abs_sub_comm] using hmu
        exact add_lt_add hmu' hnu
      _ = 2 * eps := by ring
  dsimp [eps] at htri
  nlinarith

end LogarithmicMorrisFull
