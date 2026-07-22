import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import logarithmicmorris.ScratchCircleLogIntegrable

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory Filter Topology

namespace LogarithmicMorrisFull

theorem unitVolume_eq_haar :
    (@volume UnitAddCircle (AddCircle.measureSpace 1)) =
      AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

theorem circleLog_integrable_haar :
    Integrable circleLog AddCircle.haarAddCircle := by
  rw [← unitVolume_eq_haar]
  exact circleLog_integrable

def radialCircleLog (r : ℝ) (t : UnitAddCircle) : ℂ :=
  Complex.log (1 - (r : ℂ) * fourier 1 t)

theorem radialCircleLog_hasSum (r : ℝ) (hr : |r| < 1)
    (t : UnitAddCircle) :
    HasSum (fun n : ℕ =>
      -(((r : ℂ) * fourier 1 t) ^ n / (n : ℂ)))
      (radialCircleLog r t) := by
  have hz : ‖(r : ℂ) * fourier 1 t‖ < 1 := by
    rw [norm_mul, Complex.norm_real, fourier_apply, Circle.norm_coe,
      mul_one, Real.norm_eq_abs]
    exact hr
  simpa [radialCircleLog] using
    (Complex.hasSum_taylorSeries_neg_log hz).neg

theorem radialCircleLog_eq_tsum (r : ℝ) (hr : |r| < 1)
    (t : UnitAddCircle) :
    radialCircleLog r t =
      ∑' n : ℕ, -(((r : ℂ) * fourier 1 t) ^ n / (n : ℂ)) := by
  exact (radialCircleLog_hasSum r hr t).tsum_eq.symm

theorem radialCircleLog_summable_norm (r : ℝ) (hr : |r| < 1) :
    Summable (fun n : ℕ => ‖((r : ℂ) ^ n / (n : ℂ))‖) := by
  have hz : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hr
  exact (Complex.hasSum_taylorSeries_neg_log hz).summable.norm

theorem fourier_one_pow (t : UnitAddCircle) (n : ℕ) :
    fourier 1 t ^ n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← fourier_add]
      congr 1

theorem norm_complex_log_le (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have hdecomp : Complex.log z =
      ((Complex.log z).re : ℂ) + ((Complex.log z).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hdecomp]
  calc
    _ ≤ ‖((Complex.log z).re : ℂ)‖ +
        ‖((Complex.log z).im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |(Complex.log z).re| + |(Complex.log z).im| := by
      simp [Real.norm_eq_abs]
    _ ≤ |Real.log ‖z‖| + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      gcongr
      exact Complex.abs_arg_le_pi z

theorem abs_log_le_of_comparable {d w : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hdw : d ≤ 2 * w) (hw2 : w ≤ 2) :
    |Real.log w| ≤ Real.log 2 + |Real.log d| := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hu : Real.log w ≤ Real.log 2 := Real.log_le_log hw hw2
  have hprod : 0 < 2 * w := mul_pos (by norm_num) hw
  have hl' : Real.log d ≤ Real.log (2 * w) := Real.log_le_log hd hdw
  rw [Real.log_mul (by norm_num) hw.ne'] at hl'
  rw [abs_le]
  constructor
  · calc
      -(Real.log 2 + |Real.log d|) ≤
          -(Real.log 2 + (-Real.log d)) := by
            gcongr
            exact neg_le_abs (Real.log d)
      _ ≤ Real.log w := by linarith
  · exact hu.trans (le_add_of_nonneg_right (abs_nonneg _))

theorem one_sub_mem_slitPlane_of_norm_one {z : ℂ}
    (hz : ‖z‖ = 1) (hne : z ≠ 1) : 1 - z ∈ Complex.slitPlane := by
  rw [Complex.slitPlane]
  by_cases him : z.im = 0
  · left
    have hsq : z.re ^ 2 = 1 := by
      have hnormsq := Complex.sq_norm z
      rw [hz] at hnormsq
      simp [Complex.normSq_apply, him] at hnormsq
      nlinarith [hnormsq]
    have hre : z.re ≠ 1 := by
      intro hre
      apply hne
      apply Complex.ext <;> simp [hre, him]
    change 0 < 1 - z.re
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show z.re ^ 2 = (1 : ℝ) ^ 2 by simpa using hsq) with h | h
    · exact (hre h).elim
    · nlinarith
  · right
    simp [him]

theorem fourier_one_ne_one_of_ne_zero (t : UnitAddCircle) (ht : t ≠ 0) :
    fourier 1 t ≠ 1 := by
  rw [fourier_one]
  intro h
  apply ht
  apply AddCircle.injective_toCircle one_ne_zero
  simpa using h

theorem boundaryDistance_pos (t : UnitAddCircle) (ht : t ≠ 0) :
    0 < ‖(1 : ℂ) - fourier 1 t‖ := by
  rw [norm_pos_iff]
  exact sub_ne_zero.mpr (fourier_one_ne_one_of_ne_zero t ht).symm

theorem radialDistance_pos (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (t : UnitAddCircle) :
    0 < ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ := by
  rw [norm_pos_iff]
  intro h
  have hnorm := congrArg norm (sub_eq_zero.mp h)
  simp [norm_mul, fourier_apply, Circle.norm_coe, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0] at hnorm
  linarith

theorem boundaryDistance_le_two_mul_radialDistance (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (t : UnitAddCircle) :
    ‖(1 : ℂ) - fourier 1 t‖ ≤
      2 * ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ := by
  let z : ℂ := fourier 1 t
  have hz : ‖z‖ = 1 := by simp [z, fourier_apply, Circle.norm_coe]
  have htri : ‖(1 : ℂ) - z‖ ≤
      ‖(1 : ℂ) - (r : ℂ) * z‖ + ‖((r : ℂ) - 1) * z‖ := by
    have hid : (1 : ℂ) - z =
        ((1 : ℂ) - (r : ℂ) * z) + ((r : ℂ) - 1) * z := by ring
    rw [hid]
    exact norm_add_le _ _
  have hrev : (1 - r) ≤ ‖(1 : ℂ) - (r : ℂ) * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z)
    simpa [norm_mul, hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0] using h
  have hsecond : ‖((r : ℂ) - 1) * z‖ = 1 - r := by
    rw [norm_mul, hz, mul_one]
    have hcast : (r : ℂ) - 1 = ((r - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  change ‖(1 : ℂ) - z‖ ≤ 2 * ‖(1 : ℂ) - (r : ℂ) * z‖
  rw [hsecond] at htri
  linarith

theorem radialDistance_le_two (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (t : UnitAddCircle) :
    ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖ ≤ 2 := by
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * fourier 1 t‖ := norm_sub_le _ _
    _ = 1 + r := by
      simp [norm_mul, fourier_apply, Circle.norm_coe, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr0]
    _ ≤ 2 := by linarith

theorem norm_radialCircleLog_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (t : UnitAddCircle) (ht : t ≠ 0) :
    ‖radialCircleLog r t‖ ≤
      Real.log 2 + ‖circleLog t‖ + Real.pi := by
  let d := ‖(1 : ℂ) - fourier 1 t‖
  let w := ‖(1 : ℂ) - (r : ℂ) * fourier 1 t‖
  have hd : 0 < d := boundaryDistance_pos t ht
  have hw : 0 < w := radialDistance_pos r hr0 hr1 t
  have hdw : d ≤ 2 * w :=
    boundaryDistance_le_two_mul_radialDistance r hr0 hr1.le t
  have hw2 : w ≤ 2 := radialDistance_le_two r hr0 hr1.le t
  have habs := abs_log_le_of_comparable hd hw hdw hw2
  have hre : |Real.log d| ≤ ‖circleLog t‖ := by
    have h := Complex.abs_re_le_norm (Complex.log ((1 : ℂ) - fourier 1 t))
    simpa only [circleLog, Complex.log_re] using h
  calc
    ‖radialCircleLog r t‖ ≤ |Real.log w| + Real.pi :=
      norm_complex_log_le _
    _ ≤ (Real.log 2 + |Real.log d|) + Real.pi := by gcongr
    _ ≤ Real.log 2 + ‖circleLog t‖ + Real.pi := by gcongr

def radialRadius (n : ℕ) : ℝ :=
  1 - 1 / (n + 1 : ℝ)

theorem radialRadius_nonneg (n : ℕ) : 0 ≤ radialRadius n := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hpos).mpr hden
  unfold radialRadius
  linarith

theorem radialRadius_lt_one (n : ℕ) : radialRadius n < 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold radialRadius
  have : 0 < 1 / ((n : ℝ) + 1) := div_pos zero_lt_one hpos
  linarith

theorem abs_radialRadius_lt_one (n : ℕ) : |radialRadius n| < 1 := by
  rw [abs_of_nonneg (radialRadius_nonneg n)]
  exact radialRadius_lt_one n

theorem tendsto_radialRadius :
    Tendsto radialRadius atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [radialRadius, sub_zero] using tendsto_const_nhds.sub h

theorem haar_measure_singleton_zero :
    AddCircle.haarAddCircle ({0} : Set UnitAddCircle) = 0 := by
  rw [← unitVolume_eq_haar, ← Metric.closedBall_zero,
    AddCircle.volume_closedBall]
  norm_num

theorem ae_ne_zero_circle : ∀ᵐ t : UnitAddCircle, t ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  rw [unitVolume_eq_haar]
  simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
    haar_measure_singleton_zero

theorem tendsto_radialCircleLog_ae :
    ∀ᵐ t : UnitAddCircle,
      Tendsto (fun n => radialCircleLog (radialRadius n) t)
        atTop (𝓝 (circleLog t)) := by
  filter_upwards [ae_ne_zero_circle] with t ht
  let z : ℂ := fourier 1 t
  have hz : ‖z‖ = 1 := by simp [z, fourier_apply, Circle.norm_coe]
  have hzne : z ≠ 1 := fourier_one_ne_one_of_ne_zero t ht
  have hslit : (1 : ℂ) - z ∈ Complex.slitPlane :=
    one_sub_mem_slitPlane_of_norm_one hz hzne
  have hrC : Tendsto (fun n => (radialRadius n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    (Complex.ofRealCLM.continuous.continuousAt.tendsto.comp tendsto_radialRadius)
  have harg : Tendsto (fun n => (1 : ℂ) - (radialRadius n : ℂ) * z)
      atTop (𝓝 ((1 : ℂ) - z)) := by
    simpa using tendsto_const_nhds.sub (hrC.mul_const z)
  change Tendsto (fun n => Complex.log ((1 : ℂ) - (radialRadius n : ℂ) * z))
    atTop (𝓝 (Complex.log ((1 : ℂ) - z)))
  exact (continuousAt_clog hslit).tendsto.comp harg

theorem tendsto_radialLog_fourier_integral (q : ℤ) :
    Tendsto
      (fun n => ∫ t : UnitAddCircle,
        fourier q t * radialCircleLog (radialRadius n) t)
      atTop
      (𝓝 (∫ t : UnitAddCircle, fourier q t * circleLog t)) := by
  let bound : UnitAddCircle → ℝ := fun t =>
    Real.log 2 + ‖circleLog t‖ + Real.pi
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun t : UnitAddCircle =>
        fourier q t * radialCircleLog (radialRadius n) t) := by
    apply AEStronglyMeasurable.mul
    · exact (fourier q).continuous.measurable.aestronglyMeasurable
    · exact (Complex.measurable_log.comp
        (measurable_const.sub
          (measurable_const.mul (fourier 1).continuous.measurable))).aestronglyMeasurable
  have hboundInt : Integrable bound := by
    simpa [bound, Pi.add_apply] using
      (((integrable_const (Real.log 2)).add circleLog_integrable.norm).add
        (integrable_const Real.pi))
  have hbound (n : ℕ) : ∀ᵐ t : UnitAddCircle,
      ‖fourier q t * radialCircleLog (radialRadius n) t‖ ≤ bound t := by
    filter_upwards [ae_ne_zero_circle] with t ht
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
    exact norm_radialCircleLog_le (radialRadius n)
      (radialRadius_nonneg n) (radialRadius_lt_one n) t ht
  have hlim : ∀ᵐ t : UnitAddCircle,
      Tendsto
        (fun n => fourier q t * radialCircleLog (radialRadius n) t)
        atTop (𝓝 (fourier q t * circleLog t)) := by
    filter_upwards [tendsto_radialCircleLog_ae] with t ht
    exact ht.const_mul (fourier q t)
  exact tendsto_integral_of_dominated_convergence bound hmeas hboundInt hbound hlim

theorem radialCircleLog_fourierCoeff (r : ℝ) (hr : |r| < 1) (p : ℤ) :
    fourierCoeff (radialCircleLog r) p =
      if hp : 0 < p then -((r : ℂ) ^ p.natAbs / (p.natAbs : ℂ)) else 0 := by
  let F : ℕ → UnitAddCircle → ℂ := fun n t =>
    -(((r : ℂ) * fourier 1 t) ^ n / (n : ℂ))
  have hF_int (n : ℕ) :
      Integrable (F n) AddCircle.haarAddCircle := by
    have hc : Continuous (F n) := by
      unfold F
      fun_prop
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ hc.continuousOn)
  have hF_norm : Summable (fun n : ℕ =>
      ∫ t : UnitAddCircle, ‖F n t‖ ∂AddCircle.haarAddCircle) := by
    have hs := radialCircleLog_summable_norm r hr
    apply hs.congr
    intro n
    simp [F, fourier_apply, Circle.norm_coe]
  have hsum : fourierCoeff (radialCircleLog r) p =
      ∑' n : ℕ, fourierCoeff (F n) p := by
    rw [fourierCoeff]
    have hInt (n : ℕ) : Integrable
        (fun t : UnitAddCircle => fourier (-p) t • F n t)
        AddCircle.haarAddCircle :=
      (hF_int n).fourier_smul (-p)
    have hNorm : Summable (fun n : ℕ =>
        ∫ t : UnitAddCircle, ‖fourier (-p) t • F n t‖
          ∂AddCircle.haarAddCircle) := by
      apply hF_norm.congr
      intro n
      apply integral_congr_ae
      filter_upwards [] with t
      simp [norm_smul, fourier_apply, Circle.norm_coe]
    have heq (t : UnitAddCircle) :
        fourier (-p) t • radialCircleLog r t =
          ∑' n : ℕ, fourier (-p) t • F n t := by
      exact ((radialCircleLog_hasSum r hr t).const_smul
        (fourier (-p) t)).tsum_eq.symm
    simp_rw [heq]
    change (∫ t : UnitAddCircle,
        ∑' n : ℕ, fourier (-p) t • F n t
          ∂AddCircle.haarAddCircle) = _
    rw [← integral_tsum_of_summable_integral_norm hInt hNorm]
    congr 1
  rw [hsum]
  have hcoeff (n : ℕ) : fourierCoeff (F n) p =
      -((r : ℂ) ^ n / (n : ℂ)) * if (p = (n : ℤ)) then 1 else 0 := by
    unfold F
    have hfun : (fun t : UnitAddCircle =>
        -(((r : ℂ) * fourier 1 t) ^ n / (n : ℂ))) =
        fun t => -((r : ℂ) ^ n / (n : ℂ)) * fourier (n : ℤ) t := by
      funext t
      rw [mul_pow]
      rw [fourier_one_pow]
      push_cast
      ring
    rw [hfun, fourierCoeff.const_mul]
    rw [show fourierCoeff (fourier (n : ℤ)) p =
        if p = (n : ℤ) then 1 else 0 by
      simpa [Pi.single_apply] using
        congrFun (fourierCoeff_fourier (T := (1 : ℝ)) (n : ℤ)) p]
  simp_rw [hcoeff]
  by_cases hp : 0 < p
  · simp only [hp, dite_true]
    have hpn : (p.natAbs : ℤ) = p := by omega
    rw [tsum_eq_single p.natAbs]
    · simp [hpn]
    · intro n hn
      have hne : p ≠ (n : ℤ) := by
        intro h
        apply hn
        apply Nat.cast_injective (R := ℤ)
        rw [← h, hpn]
      simp [hne]
  · simp only [hp, dite_false]
    have hzero : (fun n : ℕ =>
        -((r : ℂ) ^ n / (n : ℂ)) * if (p = (n : ℤ)) then 1 else 0) = 0 := by
      funext n
      cases n with
      | zero => simp
      | succ n =>
          have hne : p ≠ (n : ℤ) + 1 := by
            intro h
            apply hp
            rw [h]
            omega
          simp [hne]
    rw [hzero]
    exact (tsum_zero : (∑' _n : ℕ, (0 : ℂ)) = 0)

theorem radialCircleLog_fourierIntegral (r : ℝ) (hr : |r| < 1)
    (q : ℤ) :
    (∫ t : UnitAddCircle, fourier q t * radialCircleLog r t) =
      if hq : q < 0 then
        -((r : ℂ) ^ (-q).natAbs / ((-q).natAbs : ℂ)) else 0 := by
  rw [unitVolume_eq_haar]
  have h := radialCircleLog_fourierCoeff r hr (-q)
  rw [fourierCoeff] at h
  simpa only [neg_neg, smul_eq_mul, neg_pos] using h

theorem circleLog_fourierIntegral (q : ℤ) :
    (∫ t : UnitAddCircle, fourier q t * circleLog t) =
      if q < 0 then (1 : ℂ) / (q : ℂ) else 0 := by
  have hlim := tendsto_radialLog_fourier_integral q
  by_cases hq : q < 0
  · have hp : 0 < -q := by omega
    have hformula : (fun n : ℕ =>
        ∫ t : UnitAddCircle,
          fourier q t * radialCircleLog (radialRadius n) t) =
        fun n : ℕ =>
          -(((radialRadius n : ℂ) ^ (-q).natAbs) /
            ((-q).natAbs : ℂ)) := by
      funext n
      rw [radialCircleLog_fourierIntegral _ (abs_radialRadius_lt_one n) q]
      simp [hq]
    rw [hformula] at hlim
    have hrC : Tendsto (fun n : ℕ => (radialRadius n : ℂ)) atTop
        (𝓝 (1 : ℂ)) :=
      Complex.ofRealCLM.continuous.continuousAt.tendsto.comp
        tendsto_radialRadius
    have hpow : Tendsto
        (fun n : ℕ => (radialRadius n : ℂ) ^ (-q).natAbs)
        atTop (𝓝 ((1 : ℂ) ^ (-q).natAbs)) :=
      Tendsto.pow hrC _
    have hden : ((-q).natAbs : ℂ) ≠ 0 := by
      exact_mod_cast (Int.natAbs_ne_zero.mpr (by omega : -q ≠ 0))
    have hcalc :
        -(((1 : ℂ) ^ (-q).natAbs) / ((-q).natAbs : ℂ)) =
          (1 : ℂ) / (q : ℂ) := by
      have hcast : ((-q).natAbs : ℂ) = -(q : ℂ) := by
        calc
          ((-q).natAbs : ℂ) =
              (((( -q).natAbs : ℕ) : ℤ) : ℂ) := by norm_num
          _ = ((-q : ℤ) : ℂ) := congrArg (fun z : ℤ => (z : ℂ))
            (Int.natAbs_of_nonneg hp.le)
          _ = -(q : ℂ) := by push_cast; rfl
      rw [one_pow, hcast]
      field_simp
    have hlim' : Tendsto
        (fun n : ℕ =>
          -(((radialRadius n : ℂ) ^ (-q).natAbs) /
            ((-q).natAbs : ℂ)))
        atTop (𝓝 ((1 : ℂ) / (q : ℂ))) := by
      rw [← hcalc]
      exact (hpow.div_const ((-q).natAbs : ℂ)).neg
    rw [if_pos hq]
    exact tendsto_nhds_unique hlim hlim'
  · have hformula : (fun n : ℕ =>
        ∫ t : UnitAddCircle,
          fourier q t * radialCircleLog (radialRadius n) t) = 0 := by
      funext n
      rw [radialCircleLog_fourierIntegral _ (abs_radialRadius_lt_one n) q]
      simp [hq]
    rw [hformula] at hlim
    simp only [hq, if_false]
    exact tendsto_nhds_unique hlim tendsto_const_nhds

end LogarithmicMorrisFull
