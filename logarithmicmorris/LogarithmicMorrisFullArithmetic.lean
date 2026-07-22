import Mathlib
import logarithmicmorris.LogarithmicMorrisFullBasic

/-!
# Arithmetic and special-function layer for logarithmic Morris
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-! ## Double factorial and Pochhammer arithmetic -/

theorem doubleFactorial_pos (N : ℕ) : 0 < doubleFactorial N := by
  induction N using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more N hN _ =>
      rw [show N + 2 = N + 2 by rfl, doubleFactorial_succ_succ]
      exact Nat.mul_pos (by omega) hN

theorem doubleFactorial_ne_zero (N : ℕ) : doubleFactorial N ≠ 0 :=
  Nat.ne_of_gt (doubleFactorial_pos N)

theorem doubleFactorial_eq_natDoubleFactorial (N : ℕ) :
    doubleFactorial N = N.doubleFactorial := by
  induction N using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more N hN _ =>
      rw [doubleFactorial_succ_succ, Nat.doubleFactorial_add_two, hN]

theorem doubleFactorial_add_two_mul (N r : ℕ) :
    doubleFactorial (N + 2 * r) =
      (∏ j ∈ Finset.range r, (N + 2 * (j + 1))) * doubleFactorial N := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show N + 2 * (r + 1) = (N + 2 * r) + 2 by omega,
        doubleFactorial_succ_succ, ih, Finset.prod_range_succ]
      ring

theorem factorial_odd_eq (m : ℕ) :
    (2 * m + 1).factorial =
      2 ^ m * m.factorial * doubleFactorial (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        Nat.factorial_succ, Nat.factorial_succ, ih,
        doubleFactorial_succ_succ, pow_succ, Nat.factorial_succ]
      ring

theorem factorial_rank_eq (S : Setup) :
    S.n.factorial =
      2 ^ S.m * S.m.factorial * doubleFactorial S.n := by
  rw [S.odd_rank]
  exact factorial_odd_eq S.m

theorem factorial_prefactor_eq (S : Setup) :
    (S.m.factorial : ℚ) * (2 : ℚ) ^ S.m / S.n.factorial =
      1 / (doubleFactorial S.n : ℚ) := by
  rw [factorial_rank_eq]
  push_cast
  have hm : (S.m.factorial : ℚ) ≠ 0 := by positivity
  have htwo : (2 : ℚ) ^ S.m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdf : (doubleFactorial S.n : ℚ) ≠ 0 := by
    exact_mod_cast doubleFactorial_ne_zero S.n
  field_simp

/-- Rising factorial `(z)_r`. -/
def pochhammer (z : ℂ) (r : ℕ) : ℂ :=
  ∏ j ∈ Finset.range r, (z + j)

@[simp] theorem pochhammer_zero (z : ℂ) : pochhammer z 0 = 1 := by
  simp [pochhammer]

theorem pochhammer_succ (z : ℂ) (r : ℕ) :
    pochhammer z (r + 1) = pochhammer z r * (z + r) := by
  simp [pochhammer, Finset.prod_range_succ]

/-- Equation (5.7), first as a statement over `ℂ`. -/
theorem pochhammer_one_add_half_nat (N r : ℕ) :
    pochhammer (1 + (N : ℂ) / 2) r =
      (doubleFactorial (N + 2 * r) : ℂ) /
        ((2 : ℂ) ^ r * (doubleFactorial N : ℂ)) := by
  induction r with
  | zero => simp [doubleFactorial_ne_zero]
  | succ r ih =>
      rw [pochhammer_succ, ih,
        show N + 2 * (r + 1) = (N + 2 * r) + 2 by omega,
        doubleFactorial_succ_succ, pow_succ]
      have hdf : (doubleFactorial N : ℂ) ≠ 0 := by
        exact_mod_cast doubleFactorial_ne_zero N
      field_simp
      push_cast
      ring

/-! ## Gamma ratio at the odd exponent -/

/-- The Gamma quotient in equation (5.3), restricted to real arguments. -/
def realGammaRatio (S : Setup) (u : ℝ) : ℝ :=
  Real.Gamma (1 + (S.n : ℝ) * u / 2) /
    (Real.Gamma (1 + u / 2)) ^ S.n

private theorem gamma_ratio_algebra (m k : ℕ) (A B t p : ℝ)
    (hB0 : B ≠ 0) (ht0 : t ≠ 0) (hp0 : p ≠ 0) (ht : t ^ 2 = p) :
    (A * t / 2 ^ ((2 * m + 1) * k + m + 1)) /
        (B * t / 2 ^ (k + 1)) ^ (2 * m + 1) =
      (2 / p) ^ m * A / B ^ (2 * m + 1) := by
  simp only [div_pow, mul_pow]
  field_simp
  rw [show (t : ℝ) ^ (2 * m + 1) = t ^ (2 * m) * t by
    rw [pow_add, pow_one]]
  rw [show (t : ℝ) ^ (2 * m) = p ^ m by
    rw [pow_mul, ht]]
  have htwo : ((2 : ℝ) ^ (k + 1)) ^ (2 * m + 1) =
      2 ^ ((2 * m + 1) * k + m + 1) * 2 ^ m := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [htwo]
  ring

/-- The Gamma quotient in (5.3) at `K=2k+1`, proved from the
half-integer Gamma formula. -/
theorem realGammaRatio_at_K (S : Setup) :
    realGammaRatio S S.K =
      (2 / Real.pi) ^ S.m *
        (doubleFactorial (S.n * S.K) : ℝ) /
          (doubleFactorial S.K : ℝ) ^ S.n := by
  let qN := S.n * S.k + S.m
  have hN : 2 * qN + 1 = S.n * S.K := by
    dsimp [qN]
    rw [S.odd_rank]
    simp [Setup.K]
    ring
  have hK : 2 * S.k + 1 = S.K := by rfl
  have hnumArg :
      1 + (S.n : ℝ) * (S.K : ℝ) / 2 = (qN : ℝ) + 1 + 1 / 2 := by
    push_cast [qN, Setup.K]
    rw [S.odd_rank]
    push_cast
    ring
  have hdenArg :
      1 + (S.K : ℝ) / 2 = (S.k : ℝ) + 1 + 1 / 2 := by
    push_cast [Setup.K]
    ring
  rw [realGammaRatio, hnumArg, hdenArg,
    Real.Gamma_nat_add_one_add_half, Real.Gamma_nat_add_one_add_half]
  rw [← doubleFactorial_eq_natDoubleFactorial,
    ← doubleFactorial_eq_natDoubleFactorial, hN, hK]
  rw [S.odd_rank]
  rw [show qN + 1 = (2 * S.m + 1) * S.k + S.m + 1 by
    dsimp [qN]
    rw [S.odd_rank]]
  apply gamma_ratio_algebra
  · exact_mod_cast doubleFactorial_ne_zero S.K
  · exact ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  · exact ne_of_gt Real.pi_pos
  · exact Real.sq_sqrt (le_of_lt Real.pi_pos)

/-- Complex form of the Gamma quotient. -/
def complexGammaRatio (S : Setup) (u : ℂ) : ℂ :=
  Complex.Gamma (1 + (S.n : ℂ) * u / 2) /
    (Complex.Gamma (1 + u / 2)) ^ S.n

theorem complexGammaRatio_at_K (S : Setup) :
    complexGammaRatio S S.K =
      (2 / (Real.pi : ℂ)) ^ S.m *
        (doubleFactorial (S.n * S.K) : ℂ) /
          (doubleFactorial S.K : ℂ) ^ S.n := by
  have hnum : 1 + (S.n : ℂ) * (S.K : ℂ) / 2 =
      ((1 + (S.n : ℝ) * (S.K : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hden : 1 + (S.K : ℂ) / 2 =
      ((1 + (S.K : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [complexGammaRatio, hnum, hden, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  have h := congrArg Complex.ofReal (realGammaRatio_at_K S)
  simp only [realGammaRatio, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat] at h
  exact h

theorem pochhammer_index_K (S : Setup) (i r : ℕ) :
    pochhammer (1 + (i : ℂ) * (S.K : ℂ) / 2) r =
      (doubleFactorial (i * S.K + 2 * r) : ℂ) /
        ((2 : ℂ) ^ r * (doubleFactorial (i * S.K) : ℂ)) := by
  convert pochhammer_one_add_half_nat (i * S.K) r using 1 <;>
    push_cast <;> ring

private theorem quotient_algebra (A D₀ Da Db p q r : ℂ)
    (hD₀ : D₀ ≠ 0) (hDa : Da ≠ 0) (hDb : Db ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hpqr : p = q * r) :
    (A / (p * D₀)) / ((Da / (q * D₀)) * (Db / (r * D₀))) =
      A * D₀ / (Da * Db) := by
  field_simp
  rw [hpqr]
  ring

theorem pochhammer_ratio_index_K (S : Setup) (i : ℕ) :
    pochhammer (1 + (i : ℂ) * (S.K : ℂ) / 2) (S.a + S.b) /
        (pochhammer (1 + (i : ℂ) * (S.K : ℂ) / 2) S.a *
          pochhammer (1 + (i : ℂ) * (S.K : ℂ) / 2) S.b) =
      ((doubleFactorial (2 * S.a + 2 * S.b + i * S.K) : ℂ) *
          (doubleFactorial (i * S.K) : ℂ)) /
        ((doubleFactorial (2 * S.a + i * S.K) : ℂ) *
          (doubleFactorial (2 * S.b + i * S.K) : ℂ)) := by
  rw [pochhammer_index_K, pochhammer_index_K, pochhammer_index_K]
  have h₀ : (doubleFactorial (i * S.K) : ℂ) ≠ 0 := by
    exact_mod_cast doubleFactorial_ne_zero (i * S.K)
  have ha : (doubleFactorial (i * S.K + 2 * S.a) : ℂ) ≠ 0 := by
    exact_mod_cast doubleFactorial_ne_zero (i * S.K + 2 * S.a)
  have hb : (doubleFactorial (i * S.K + 2 * S.b) : ℂ) ≠ 0 := by
    exact_mod_cast doubleFactorial_ne_zero (i * S.K + 2 * S.b)
  have h := quotient_algebra
    (doubleFactorial (i * S.K + 2 * (S.a + S.b)) : ℂ)
    (doubleFactorial (i * S.K) : ℂ)
    (doubleFactorial (i * S.K + 2 * S.a) : ℂ)
    (doubleFactorial (i * S.K + 2 * S.b) : ℂ)
    ((2 : ℂ) ^ (S.a + S.b)) ((2 : ℂ) ^ S.a) ((2 : ℂ) ^ S.b)
    h₀ ha hb (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)) (by rw [pow_add])
  have hab : i * S.K + 2 * (S.a + S.b) =
      2 * S.a + 2 * S.b + i * S.K := by omega
  have haa : i * S.K + 2 * S.a = 2 * S.a + i * S.K := by omega
  have hbb : i * S.K + 2 * S.b = 2 * S.b + i * S.K := by omega
  simpa only [hab, haa, hbb] using h

/-! ## The conjectural closed form -/

/-- A polynomial with the two normalizations required in Conjecture 4.2. -/
structure MorrisPolynomial (S : Setup) where
  polynomial : Polynomial ℂ
  at_zero : polynomial.eval 0 =
    (1 : ℂ) / (doubleFactorial (S.n - 2) : ℂ)
  at_one : polynomial.eval 1 = 1

/-- The Gamma/Pochhammer factor `r_n(u)` from equation (5.3). -/
def gammaPochhammerPart (S : Setup) (u : ℂ) : ℂ :=
  (Complex.Gamma (1 + (S.n : ℂ) * u / 2) /
      (Complex.Gamma (1 + u / 2)) ^ S.n) *
    ∏ i ∈ Finset.range S.n,
      pochhammer (1 + (i : ℂ) * u / 2) (S.a + S.b) /
        (pochhammer (1 + (i : ℂ) * u / 2) S.a *
          pochhammer (1 + (i : ℂ) * u / 2) S.b)

private theorem prod_range_shift (D : ℕ → ℂ) (n : ℕ) (h0 : D 0 = 1) :
    (∏ i ∈ Finset.range n, D (i + 1)) =
      D n * ∏ i ∈ Finset.range n, D i := by
  calc
    _ = ∏ i ∈ Finset.range (n + 1), D i := by
      rw [Finset.prod_range_succ', h0, mul_one]
    _ = (∏ i ∈ Finset.range n, D i) * D n := Finset.prod_range_succ D n
    _ = _ := mul_comm _ _

private theorem product_quotient_shift (n : ℕ) (A Da Db D : ℕ → ℂ)
    (C : ℂ) (h0 : D 0 = 1) :
    (D n / C ^ n) *
        ∏ i ∈ Finset.range n, (A i * D i) / (Da i * Db i) =
      ∏ i ∈ Finset.range n,
        (A i * D (i + 1)) / (Da i * Db i * C) := by
  simp only [div_eq_mul_inv, mul_inv, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range]
  rw [prod_range_shift D n h0]
  ring

theorem gammaPochhammerPart_at_K (S : Setup) :
    gammaPochhammerPart S S.K =
      (2 / (Real.pi : ℂ)) ^ S.m *
        ∏ i ∈ Finset.range S.n, (rhsFactor S i : ℂ) := by
  rw [gammaPochhammerPart]
  change complexGammaRatio S S.K * _ = _
  rw [complexGammaRatio_at_K]
  simp_rw [pochhammer_ratio_index_K]
  rw [show
    (2 / (Real.pi : ℂ)) ^ S.m *
          (doubleFactorial (S.n * S.K) : ℂ) /
          (doubleFactorial S.K : ℂ) ^ S.n *
          (∏ i ∈ Finset.range S.n,
            ((doubleFactorial (2 * S.a + 2 * S.b + i * S.K) : ℂ) *
              (doubleFactorial (i * S.K) : ℂ)) /
            ((doubleFactorial (2 * S.a + i * S.K) : ℂ) *
              (doubleFactorial (2 * S.b + i * S.K) : ℂ))) =
      (2 / (Real.pi : ℂ)) ^ S.m *
        (((doubleFactorial (S.n * S.K) : ℂ) /
            (doubleFactorial S.K : ℂ) ^ S.n) *
          (∏ i ∈ Finset.range S.n,
            ((doubleFactorial (2 * S.a + 2 * S.b + i * S.K) : ℂ) *
              (doubleFactorial (i * S.K) : ℂ)) /
            ((doubleFactorial (2 * S.a + i * S.K) : ℂ) *
              (doubleFactorial (2 * S.b + i * S.K) : ℂ)))) by ring]
  apply congrArg ((2 / (Real.pi : ℂ)) ^ S.m * ·)
  let A : ℕ → ℂ := fun i =>
    (doubleFactorial (2 * S.a + 2 * S.b + i * S.K) : ℂ)
  let Da : ℕ → ℂ := fun i =>
    (doubleFactorial (2 * S.a + i * S.K) : ℂ)
  let Db : ℕ → ℂ := fun i =>
    (doubleFactorial (2 * S.b + i * S.K) : ℂ)
  let D : ℕ → ℂ := fun i => (doubleFactorial (i * S.K) : ℂ)
  have h := product_quotient_shift S.n A Da Db D
    (doubleFactorial S.K : ℂ) (by simp [D])
  dsimp [A, Da, Db, D] at h
  simpa only [rhsFactor, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    Nat.add_mul] using h

/-- `x(u)=cos(πu/2)`. -/
def cosineCoordinate (u : ℂ) : ℂ :=
  Complex.cos ((Real.pi : ℂ) * u / 2)

/-- `x(u)^m P_n(x(u)^2)`. -/
def cosinePolynomialPart (S : Setup) (P : MorrisPolynomial S) (u : ℂ) : ℂ :=
  cosineCoordinate u ^ S.m *
    P.polynomial.eval (cosineCoordinate u ^ 2)

/-- Right-hand side of the complex Morris identity (4.5). -/
def complexMorrisRHS (S : Setup) (P : MorrisPolynomial S) (u : ℂ) : ℂ :=
  cosinePolynomialPart S P u * gammaPochhammerPart S u

theorem cosineCoordinate_analyticAt (u : ℂ) :
    AnalyticAt ℂ cosineCoordinate u := by
  change AnalyticAt ℂ (fun z : ℂ =>
    Complex.cos ((Real.pi : ℂ) * z / 2)) u
  fun_prop

@[simp] theorem cosineCoordinate_at_K (S : Setup) :
    cosineCoordinate S.K = 0 := by
  have harg :
      (Real.pi : ℂ) * (S.K : ℂ) / 2 =
        ((Real.pi / 2 + S.k * Real.pi : ℝ) : ℂ) := by
    simp [Setup.K]
    ring
  rw [cosineCoordinate, harg, ← Complex.ofReal_cos,
    Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero, Complex.ofReal_zero]

theorem hasDerivAt_cosineCoordinate (u : ℂ) :
    HasDerivAt cosineCoordinate
      (-Complex.sin ((Real.pi : ℂ) * u / 2) * ((Real.pi : ℂ) / 2)) u := by
  change HasDerivAt (fun z : ℂ =>
    Complex.cos ((Real.pi : ℂ) * z / 2)) _ u
  simpa [Function.comp_def, div_eq_mul_inv, mul_assoc] using
    (Complex.hasDerivAt_cos ((Real.pi : ℂ) * u / 2)).comp u
      (((hasDerivAt_id u).const_mul (Real.pi : ℂ)).div_const 2)

theorem deriv_cosineCoordinate_at_K (S : Setup) :
    deriv cosineCoordinate S.K =
      (-1 : ℂ) ^ (S.k + 1) * ((Real.pi : ℂ) / 2) := by
  rw [(hasDerivAt_cosineCoordinate S.K).deriv]
  have harg :
      (Real.pi : ℂ) * (S.K : ℂ) / 2 =
        ((Real.pi / 2 + S.k * Real.pi : ℝ) : ℂ) := by
    simp [Setup.K]
    ring
  rw [harg, ← Complex.ofReal_sin, Real.sin_add_nat_mul_pi,
    Real.sin_pi_div_two]
  push_cast
  rw [pow_succ]
  ring

theorem gamma_analyticAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (Complex.differentiableAt_Gamma w (fun r hwr => by
      have hre := congrArg Complex.re hwr
      simp at hre
      have hwpos : 0 < w.re := hw
      rw [hre] at hwpos
      exact (not_lt_of_ge (neg_nonpos.mpr (by positivity))) hwpos)).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hz)

theorem pochhammer_comp_analyticAt (r : ℕ) (c u : ℂ) :
    AnalyticAt ℂ (fun z => pochhammer (1 + c * z / 2) r) u := by
  unfold pochhammer
  apply Finset.analyticAt_fun_prod
  intro j hj
  fun_prop

theorem pochhammer_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    pochhammer z r ≠ 0 := by
  unfold pochhammer
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  apply Complex.ne_zero_of_re_pos
  simp
  linarith

theorem gammaPochhammerPart_analyticAt_K (S : Setup) :
    AnalyticAt ℂ (gammaPochhammerPart S) S.K := by
  classical
  let numArg : ℂ → ℂ := fun u => 1 + (S.n : ℂ) * u / 2
  let denArg : ℂ → ℂ := fun u => 1 + u / 2
  have hnumPos : 0 < (numArg S.K).re := by
    dsimp [numArg]
    norm_num
    positivity
  have hdenPos : 0 < (denArg S.K).re := by
    dsimp [denArg]
    norm_num
    positivity
  have hnum : AnalyticAt ℂ (fun u => Complex.Gamma (numArg u)) S.K := by
    simpa [Function.comp_def] using
      (gamma_analyticAt_of_re_pos hnumPos).comp (by fun_prop :
        AnalyticAt ℂ numArg S.K)
  have hdenGamma : AnalyticAt ℂ (fun u => Complex.Gamma (denArg u)) S.K := by
    simpa [Function.comp_def] using
      (gamma_analyticAt_of_re_pos hdenPos).comp (by fun_prop :
        AnalyticAt ℂ denArg S.K)
  have hdenNe : Complex.Gamma (denArg S.K) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hdenPos
  have hgamma : AnalyticAt ℂ
      (fun u => Complex.Gamma (numArg u) /
        (Complex.Gamma (denArg u)) ^ S.n) S.K :=
    hnum.div (hdenGamma.pow S.n) (pow_ne_zero _ hdenNe)
  have hprod : AnalyticAt ℂ
      (fun u => ∏ i ∈ Finset.range S.n,
        pochhammer (1 + (i : ℂ) * u / 2) (S.a + S.b) /
          (pochhammer (1 + (i : ℂ) * u / 2) S.a *
            pochhammer (1 + (i : ℂ) * u / 2) S.b)) S.K := by
    apply Finset.analyticAt_fun_prod
    intro i hi
    have hbasePos : 0 < (1 + (i : ℂ) * (S.K : ℂ) / 2).re := by
      norm_num
      positivity
    apply (pochhammer_comp_analyticAt (S.a + S.b) i S.K).div
      ((pochhammer_comp_analyticAt S.a i S.K).mul
        (pochhammer_comp_analyticAt S.b i S.K))
    exact mul_ne_zero
      (pochhammer_ne_zero_of_re_pos hbasePos S.a)
      (pochhammer_ne_zero_of_re_pos hbasePos S.b)
  change AnalyticAt ℂ
    (fun u =>
      (Complex.Gamma (numArg u) / (Complex.Gamma (denArg u)) ^ S.n) *
        ∏ i ∈ Finset.range S.n,
          pochhammer (1 + (i : ℂ) * u / 2) (S.a + S.b) /
            (pochhammer (1 + (i : ℂ) * u / 2) S.a *
              pochhammer (1 + (i : ℂ) * u / 2) S.b)) S.K
  exact hgamma.mul hprod

end LogarithmicMorrisFull
