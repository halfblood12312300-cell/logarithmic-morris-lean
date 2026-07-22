import Mathlib

noncomputable section

open scoped Real ComplexConjugate

namespace LogarithmicMorrisFull

theorem one_sub_cexp_polar {phi : ℝ} :
    (1 - Complex.exp (phi * Complex.I)) =
      (2 * Real.sin (phi / 2) : ℝ) *
        Complex.exp ((phi / 2 - Real.pi / 2) * Complex.I) := by
  have heq :
      (((phi : ℂ) / 2 - (Real.pi : ℂ) / 2) * Complex.I) =
        (((phi / 2 - Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [heq]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos phi, ← Complex.ofReal_sin phi,
    ← Complex.ofReal_cos (phi / 2 - Real.pi / 2),
    ← Complex.ofReal_sin (phi / 2 - Real.pi / 2)]
  rw [Real.cos_sub, Real.sin_sub, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp only [mul_zero, mul_one, add_zero, zero_mul, sub_zero]
  rw [show phi = 2 * (phi / 2) by ring, Real.cos_two_mul,
    Real.sin_two_mul]
  push_cast
  rw [← Complex.sin_sq_add_cos_sq ((phi : ℂ) / 2)]
  ring

theorem arg_one_sub_cexp {phi : ℝ} (hphi0 : 0 < phi)
    (hphi2pi : phi < 2 * Real.pi) :
    Complex.arg (1 - Complex.exp (phi * Complex.I)) =
      phi / 2 - Real.pi / 2 := by
  rw [one_sub_cexp_polar]
  have hs : 0 < 2 * Real.sin (phi / 2) := by
    exact mul_pos zero_lt_two
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  rw [Complex.arg_real_mul _ hs]
  have heq :
      (((phi : ℂ) / 2 - (Real.pi : ℂ) / 2) * Complex.I) =
        (((phi / 2 - Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [heq, Complex.arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).2]
  constructor <;> linarith [Real.pi_pos]

theorem log_one_sub_cexp_sub_reverse {phi : ℝ} (hphi0 : 0 < phi)
    (hphi2pi : phi < 2 * Real.pi) :
    Complex.log (1 - Complex.exp (phi * Complex.I)) -
        Complex.log (1 - Complex.exp (-phi * Complex.I)) =
      (phi - Real.pi) * Complex.I := by
  let z : ℂ := 1 - Complex.exp (phi * Complex.I)
  have hconj : conj z = 1 - Complex.exp (-phi * Complex.I) := by
    dsimp [z]
    rw [map_sub, map_one, ← Complex.exp_conj]
    congr 2
    simp
  have harg : Complex.arg z = phi / 2 - Real.pi / 2 := by
    exact arg_one_sub_cexp hphi0 hphi2pi
  have hargpi : Complex.arg z ≠ Real.pi := by
    rw [harg]
    linarith [Real.pi_pos]
  rw [← hconj]
  change Complex.log z - Complex.log (conj z) = _
  rw [Complex.log_conj z hargpi]
  apply Complex.ext
  · simp
  · simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      sub_zero, neg_neg, Complex.log_im, harg, Complex.sub_re,
      Complex.ofReal_re]
    push_cast
    ring

theorem neg_I_chamber_phase (m : ℕ) :
    (-Complex.I) ^ (m * (2 * m + 1)) * (-Complex.I) ^ m = 1 := by
  rw [← pow_add]
  obtain ⟨q, hq⟩ := Nat.even_mul_succ_self m
  have hexp : m * (2 * m + 1) + m = 4 * q := by
    nlinarith
  rw [hexp, pow_mul]
  have hfour : (-Complex.I) ^ 4 = 1 := by
    rw [show (-Complex.I) ^ 4 = Complex.I ^ 4 by ring]
    exact Complex.I_pow_four
  rw [hfour, one_pow]

theorem cexp_sub_cexp_ordered {x y : ℝ} (hxy : x < y)
    (hyx : y - x < 2 * Real.pi) :
    Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I) =
      (-Complex.I) * Complex.exp (((x + y) / 2) * Complex.I) *
        (‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ : ℂ) := by
  let delta : ℝ := y - x
  have hd0 : 0 < delta := by
    dsimp [delta]
    linarith
  have hd2 : delta < 2 * Real.pi := by simpa [delta] using hyx
  have hfactor :
      Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I) =
        Complex.exp (x * Complex.I) *
          (1 - Complex.exp (delta * Complex.I)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    dsimp [delta]
    push_cast
    ring
  have hsin : 0 < 2 * Real.sin (delta / 2) := by
    exact mul_pos zero_lt_two
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hnorm :
      ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ =
        2 * Real.sin (delta / 2) := by
    rw [hfactor, one_sub_cexp_polar, norm_mul, norm_mul,
      Complex.norm_exp, Complex.norm_exp]
    simp [Complex.norm_real, abs_of_pos hsin]
    have hsinCast : Complex.sin ((delta : ℂ) / 2) =
        (Real.sin (delta / 2) : ℝ) := by
      rw [show (delta : ℂ) / 2 = ((delta / 2 : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_sin]
    rw [hsinCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < Real.sin (delta / 2))]
  rw [hnorm, hfactor, one_sub_cexp_polar]
  have hnegI : (-Complex.I) =
      Complex.exp (((-Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos (-Real.pi / 2),
      ← Complex.ofReal_sin (-Real.pi / 2),
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  rw [hnegI, ← Complex.exp_add]
  rw [show
    Complex.exp (x * Complex.I) *
          ((2 * Real.sin (delta / 2) : ℝ) *
            Complex.exp ((delta / 2 - Real.pi / 2) * Complex.I)) =
        (Complex.exp (x * Complex.I) *
          Complex.exp ((delta / 2 - Real.pi / 2) * Complex.I)) *
          (2 * Real.sin (delta / 2) : ℝ) by ring,
    ← Complex.exp_add]
  congr 2
  dsimp [delta]
  push_cast
  ring

end LogarithmicMorrisFull
