import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Mellin moments of the beta distribution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

private lemma integral_beta_kernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1)) = beta a b := by
  rw [beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral,
    intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rcases hx with ⟨hx0, hx1⟩
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith
  convert Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]

/-- The nonnegative real Mellin moment of a beta random variable. -/
theorem integral_rpow_betaMeasure {alpha betaParam s : ℝ}
    (ha : 0 < alpha) (hb : 0 < betaParam) (hs : 0 ≤ s) :
    (∫ x : ℝ, x ^ s ∂(betaMeasure alpha betaParam)) =
      beta (alpha + s) betaParam / beta alpha betaParam := by
  convert (integral_withDensity_eq_integral_toReal_smul _ _ _) using 1
  · have h_betaPDF :
        ∫ x in Set.Ioo 0 1, (betaPDFReal alpha betaParam x) * x ^ s =
          beta (alpha + s) betaParam / beta alpha betaParam := by
      convert congr_arg (fun x : ℝ => x / beta alpha betaParam)
        (show ∫ x in Set.Ioo 0 1,
            x ^ (alpha + s - 1) * (1 - x) ^ (betaParam - 1) =
              beta (alpha + s) betaParam from
          integral_beta_kernel (add_pos_of_pos_of_nonneg ha hs) hb) using 1
      · rw [← MeasureTheory.integral_div]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        rw [betaPDFReal]
        ring
        rw [if_pos ⟨hx.1, hx.2⟩, Real.rpow_add hx.1]
        ring
        norm_num [Real.rpow_add hx.1, Real.rpow_neg_one]
        ring
    rw [← h_betaPDF, ← MeasureTheory.integral_indicator] <;>
      norm_num [Set.indicator]
    unfold betaPDF
    norm_num [betaPDFReal]
    congr
    ext
    split_ifs <;>
      simp_all +decide [MeasureTheory.Measure.restrict_apply]
    exact Or.inl (by
      rw [ENNReal.toReal_ofReal (mul_nonneg
        (mul_nonneg
          (inv_nonneg.2 (by rw [beta]; positivity))
          (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (by linarith) _))])
  · exact Measurable.ennreal_ofReal
      (Measurable.ite measurableSet_Ioo (by measurability) measurable_const)
  · refine MeasureTheory.ae_of_all _ ?_
    intro x
    by_cases hx : 0 < x ∧ x < 1 <;> simp_all +decide [betaPDF]

end ProbabilityTheory
