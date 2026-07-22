import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import logarithmicmorris.LogarithmicMorrisLogDefinitions

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace LogarithmicMorrisFull

private def liftedCircleZero (x : ℝ) : ℂ :=
  1 - Complex.exp (2 * Real.pi * Complex.I * x)

private theorem liftedCircleZero_meromorphic :
    MeromorphicOn liftedCircleZero (Set.uIcc 0 1) := by
  apply AnalyticOnNhd.meromorphicOn
  intro x hx
  unfold liftedCircleZero
  apply AnalyticAt.sub analyticAt_const
  exact analyticAt_cexp.restrictScalars.comp
    (analyticAt_const.mul (Complex.ofRealCLM.analyticAt x))

private theorem intervalIntegrable_liftedCircleLog :
    IntervalIntegrable (fun x : ℝ => Complex.log (liftedCircleZero x)) volume 0 1 := by
  have hre : IntervalIntegrable
      (fun x : ℝ => Real.log ‖liftedCircleZero x‖) volume 0 1 :=
    intervalIntegrable_log_norm_meromorphicOn liftedCircleZero_meromorphic
  have him : IntervalIntegrable
      (fun x : ℝ => Complex.arg (liftedCircleZero x)) volume 0 1 := by
    refine (intervalIntegrable_const (c := Real.pi)).mono_fun ?_ ?_
    · exact (Complex.measurable_arg.comp
        (by unfold liftedCircleZero; fun_prop : Measurable liftedCircleZero)).aestronglyMeasurable
    · filter_upwards [] with x
      simpa [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le] using
        Complex.abs_arg_le_pi (liftedCircleZero x)
  have hsum : IntervalIntegrable
      (fun x : ℝ => (Real.log ‖liftedCircleZero x‖ : ℂ) +
        (Complex.arg (liftedCircleZero x) : ℂ) * Complex.I) volume 0 1 :=
    ⟨hre.1.ofReal.add (him.1.ofReal.mul_const Complex.I),
      hre.2.ofReal.add (him.2.ofReal.mul_const Complex.I)⟩
  simpa [Complex.log] using hsum

theorem circleLog_integrable : Integrable circleLog := by
  have hmeas : AEStronglyMeasurable circleLog :=
    (Complex.measurable_log.comp
      ((measurable_const.sub (fourier 1).continuous.measurable))).aestronglyMeasurable
  rw [← (UnitAddCircle.measurePreserving_mk 0).integrable_comp hmeas]
  have h := intervalIntegrable_liftedCircleLog.1
  have heq : (circleLog ∘ (fun x : ℝ => (x : UnitAddCircle))) =
      (fun x : ℝ => Complex.log (liftedCircleZero x)) := by
    funext x
    simp only [Function.comp_apply, circleLog, fourier_coe_apply, liftedCircleZero]
    congr 3
    norm_num
  rw [heq]
  simpa only [IntegrableOn, zero_add] using h

end LogarithmicMorrisFull
