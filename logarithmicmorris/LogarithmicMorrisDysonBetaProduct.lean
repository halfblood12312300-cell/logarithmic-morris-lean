import logarithmicmorris.LogarithmicMorrisDysonMomentDefinitions
import Mathlib.MeasureTheory.Integral.Pi

/-! # Mellin transform of the beta product in the Dyson moment proof -/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace LogarithmicMorrisFull

open MeasureTheory Set ProbabilityTheory

lemma clampUnit_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clampUnit x = x := by
  simp [clampUnit, hx.1, hx.2]

lemma clampUnit_nonneg (x : ℝ) : 0 ≤ clampUnit x := by
  simp [clampUnit]

lemma clampUnit_le_one (x : ℝ) : clampUnit x ≤ 1 := by
  simp [clampUnit]

lemma measurable_clampUnit : Measurable clampUnit := by
  exact (continuous_const.max (continuous_const.min continuous_id)).measurable

lemma betaMeasure_ae_mem_Icc {alpha betaParam : ℝ} :
    ∀ᵐ x ∂(betaMeasure alpha betaParam), x ∈ Set.Icc (0 : ℝ) 1 := by
  have hpdf : Measurable (betaPDF alpha betaParam) := by
    unfold betaPDF
    exact (measurable_betaPDFReal alpha betaParam).ennreal_ofReal
  rw [betaMeasure, ae_withDensity_iff hpdf]
  filter_upwards with x
  intro hx
  constructor
  · by_contra hneg
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge hneg))
  · by_contra hgt
    exact hx (betaPDF_eq_zero_of_one_le (le_of_not_ge hgt))

lemma integral_clampUnit_rpow_betaMeasure {alpha betaParam s : ℝ}
    (ha : 0 < alpha) (hb : 0 < betaParam) (hs : 0 ≤ s) :
    (∫ x : ℝ, clampUnit x ^ s ∂(betaMeasure alpha betaParam)) =
      beta (alpha + s) betaParam / beta alpha betaParam := by
  calc
    _ = ∫ x : ℝ, x ^ s ∂(betaMeasure alpha betaParam) := by
      apply integral_congr_ae
      filter_upwards [betaMeasure_ae_mem_Icc
        (alpha := alpha) (betaParam := betaParam)] with x hx
      rw [clampUnit_eq_self hx]
    _ = _ := integral_rpow_betaMeasure ha hb hs

lemma dysonBeta_parameters_pos (n : ℕ) (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    0 < (((i : ℕ) + 1 : ℝ) / n) ∧
      0 < (1 - (((i : ℕ) + 1 : ℝ) / n)) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hi0 : (0 : ℝ) < ((i : ℕ) + 1 : ℕ) := by positivity
  have hiltn : (i : ℕ) + 1 < n := by
    have hi := i.isLt
    omega
  constructor
  · exact div_pos (by exact_mod_cast hi0) hn0
  · rw [sub_pos]
    exact (div_lt_one hn0).2 (by exact_mod_cast hiltn)

lemma dysonBetaMeasure_isProbability (n : ℕ) (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    IsProbabilityMeasure (dysonBetaMeasure n i) := by
  unfold dysonBetaMeasure
  exact isProbabilityMeasureBeta
    (dysonBeta_parameters_pos n hn i).1
    (dysonBeta_parameters_pos n hn i).2

lemma dysonBetaProduct_nonneg (n : ℕ) (x : Fin (n - 1) → ℝ) :
    0 ≤ dysonBetaProduct n x := by
  unfold dysonBetaProduct
  exact mul_nonneg (by positivity)
    (Finset.prod_nonneg fun i _ => clampUnit_nonneg (x i))

lemma dysonBetaProduct_le (n : ℕ) (x : Fin (n - 1) → ℝ) :
    dysonBetaProduct n x ≤ (n : ℝ) ^ n := by
  unfold dysonBetaProduct
  have hprod : ∏ i, clampUnit (x i) ≤ (1 : ℝ) := by
    simpa using Finset.prod_le_prod (fun i _ => clampUnit_nonneg (x i))
      (fun i _ => clampUnit_le_one (x i))
  nlinarith [show 0 ≤ (n : ℝ) ^ n by positivity]

lemma integral_dysonBetaProduct_rpow (n : ℕ) (hn : 2 ≤ n)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : Fin (n - 1) → ℝ, (dysonBetaProduct n x) ^ s
        ∂(Measure.pi (dysonBetaMeasure n))) =
      ProbabilityTheory.betaMellinProduct n s := by
  let μ : Fin (n - 1) → Measure ℝ := dysonBetaMeasure n
  letI (i : Fin (n - 1)) : IsProbabilityMeasure (μ i) :=
    dysonBetaMeasure_isProbability n hn i
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hscale :
      (((n : ℝ) ^ n) : ℝ) ^ s = (n : ℝ) ^ ((n : ℝ) * s) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul hn0 (n : ℝ) s).symm
  have hpoint (x : Fin (n - 1) → ℝ) :
      (dysonBetaProduct n x) ^ s =
        (n : ℝ) ^ ((n : ℝ) * s) * ∏ i, clampUnit (x i) ^ s := by
    unfold dysonBetaProduct
    rw [Real.mul_rpow (by positivity)
      (Finset.prod_nonneg fun i _ => clampUnit_nonneg (x i))]
    rw [hscale]
    congr 1
    exact (Real.finset_prod_rpow Finset.univ
      (fun i => clampUnit (x i))
      (fun i _ => clampUnit_nonneg (x i)) s).symm
  simp_rw [hpoint, integral_const_mul]
  change (n : ℝ) ^ ((n : ℝ) * s) *
      (∫ a : Fin (n - 1) → ℝ, ∏ i, clampUnit (a i) ^ s
        ∂(Measure.pi μ)) = _
  have hFubini := MeasureTheory.integral_fintype_prod_eq_prod
    (ι := Fin (n - 1)) (μ := μ)
    (fun _i (_x : ℝ) => clampUnit _x ^ s)
  rw [hFubini]
  unfold ProbabilityTheory.betaMellinProduct
  simp only [μ]
  congr 1
  calc
    (∏ i : Fin (n - 1),
        ∫ x, clampUnit x ^ s ∂dysonBetaMeasure n i) =
        ∏ i : Fin (n - 1),
          beta (s + (((i : ℕ) + 1 : ℝ) / n))
              (1 - (((i : ℕ) + 1 : ℝ) / n)) /
            beta ((((i : ℕ) + 1 : ℝ) / n))
              (1 - (((i : ℕ) + 1 : ℝ) / n)) := by
      apply Finset.prod_congr rfl
      intro i hi
      unfold dysonBetaMeasure
      rw [integral_clampUnit_rpow_betaMeasure
        (dysonBeta_parameters_pos n hn i).1
        (dysonBeta_parameters_pos n hn i).2 hs]
      congr 2
      ring
    _ = ∏ r ∈ Finset.Icc 1 (n - 1),
          beta (s + (r : ℝ) / n) (1 - (r : ℝ) / n) /
            beta ((r : ℝ) / n) (1 - (r : ℝ) / n) := by
      classical
      refine Finset.prod_bij
        (fun i (_hi : i ∈ (Finset.univ : Finset (Fin (n - 1)))) =>
          ((i : ℕ) + 1 : ℕ)) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Icc]
        constructor
        · omega
        · have hit := i.isLt
          omega
      · intro i hi j hj hij
        apply Fin.ext
        exact Nat.succ.inj hij
      · intro r hr
        simp only [Finset.mem_Icc] at hr
        have hlt : r - 1 < n - 1 := by omega
        refine ⟨⟨r - 1, hlt⟩, Finset.mem_univ _, ?_⟩
        exact Nat.sub_add_cancel hr.1
      · intro i hi
        simp

theorem integral_dysonBetaProduct_rpow_eq_gammaRatio (n : ℕ)
    (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : Fin (n - 1) → ℝ, (dysonBetaProduct n x) ^ s
        ∂(Measure.pi (dysonBetaMeasure n))) =
      Real.Gamma (1 + (n : ℝ) * s) / Real.Gamma (1 + s) ^ n := by
  rw [integral_dysonBetaProduct_rpow n hn s hs,
    ProbabilityTheory.betaMellinProduct_eq_gammaRatio n (by omega) s hs]

theorem integral_dysonBetaProduct_pow (n q : ℕ) (hn : 2 ≤ n) :
    (∫ x : Fin (n - 1) → ℝ, (dysonBetaProduct n x) ^ q
        ∂(Measure.pi (dysonBetaMeasure n))) =
      (((n * q).factorial : ℝ) / (q.factorial : ℝ) ^ n) := by
  calc
    _ = ∫ x : Fin (n - 1) → ℝ, (dysonBetaProduct n x) ^ (q : ℝ)
          ∂(Measure.pi (dysonBetaMeasure n)) := by
      apply integral_congr_ae
      filter_upwards with x
      exact (Real.rpow_natCast (dysonBetaProduct n x) q).symm
    _ = Real.Gamma (1 + (n : ℝ) * (q : ℝ)) /
          Real.Gamma (1 + (q : ℝ)) ^ n :=
      integral_dysonBetaProduct_rpow_eq_gammaRatio n hn q (by positivity)
    _ = _ := by
      have hnum : 1 + (n : ℝ) * (q : ℝ) = ((n * q : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have hden : 1 + (q : ℝ) = (q : ℝ) + 1 := by ring
      rw [hnum, hden, Real.Gamma_nat_eq_factorial,
        Real.Gamma_nat_eq_factorial]

end LogarithmicMorrisFull
