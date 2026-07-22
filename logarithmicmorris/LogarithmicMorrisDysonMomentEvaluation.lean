import logarithmicmorris.LogarithmicMorrisDysonMomentComparison
import logarithmicmorris.LogarithmicMorrisDysonAssembly

/-! # Evaluation of the odd circular Dyson integral by compact moments -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory

lemma unitTorus_volume_eq_haarPi (n : ℕ) :
    (volume : Measure (UnitAddTorus (Fin n))) =
      Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle) := by
  rw [MeasureTheory.volume_pi]
  congr 1
  funext i
  exact unitVolume_eq_haar

lemma circularMorrisIntegrand_dyson_eq_rpow (S : Setup) (k : ℕ)
    (t : UnitAddTorus (Fin S.n)) :
    circularMorrisIntegrand (dysonSetup S k) t =
      (((circularDiscriminantSq S.n t) ^
        ((k : ℝ) + 1 / 2) : ℝ) : ℂ) := by
  simp only [circularMorrisIntegrand, dysonSetup_n, dysonSetup_a,
    dysonSetup_b, dysonSetup_K, pow_zero, mul_one, Finset.prod_const_one,
    one_mul]
  have hr :
      (circularDiscriminantSq S.n t) ^ ((k : ℝ) + 1 / 2) =
        ∏ p ∈ increasingPairs S.n,
          ‖fourier 1 (t p.1) - fourier 1 (t p.2)‖ ^ (2 * k + 1) := by
    unfold circularDiscriminantSq
    rw [← Real.finset_prod_rpow]
    · apply Finset.prod_congr rfl
      intro p hp
      let d : ℝ := ‖fourier 1 (t p.1) - fourier 1 (t p.2)‖
      have hd : 0 ≤ d := norm_nonneg _
      change (d ^ (2 : ℕ)) ^ ((k : ℝ) + 1 / 2) = d ^ (2 * k + 1)
      calc
        (d ^ (2 : ℕ)) ^ ((k : ℝ) + 1 / 2) =
            (d ^ (2 : ℝ)) ^ ((k : ℝ) + 1 / 2) := by
          congr 1
          exact (Real.rpow_natCast d 2).symm
        _ =
            d ^ ((2 : ℝ) * ((k : ℝ) + 1 / 2)) :=
          (Real.rpow_mul hd 2 ((k : ℝ) + 1 / 2)).symm
        _ = d ^ ((2 * k + 1 : ℕ) : ℝ) := by
          congr 1
          push_cast
          ring
        _ = d ^ (2 * k + 1) := Real.rpow_natCast d (2 * k + 1)
    · intro p hp
      positivity
  rw [hr]
  simp

theorem circularMorrisIntegral_dyson_eq_gammaRatio (S : Setup) (k : ℕ) :
    circularMorrisIntegral (dysonSetup S k) =
      (Real.Gamma (1 + (S.n : ℝ) * ((k : ℝ) + 1 / 2)) /
        Real.Gamma (1 + ((k : ℝ) + 1 / 2)) ^ S.n : ℝ) := by
  by_cases hnone : S.n = 1
  · have harg : 0 < (1 : ℝ) + ((k : ℝ) + 1 / 2) := by positivity
    have hg : Real.Gamma ((1 : ℝ) + ((k : ℝ) + 1 / 2)) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos harg)
    unfold circularMorrisIntegral
    change (∫ t : UnitAddTorus (Fin S.n),
      circularMorrisIntegrand (dysonSetup S k) t) = _
    rw [unitTorus_volume_eq_haarPi]
    simp_rw [circularMorrisIntegrand_dyson_eq_rpow]
    rw [hnone]
    have hpairs : increasingPairs 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro p hp
      simp only [increasingPairs, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      have hleft := p.1.isLt
      have hright := p.2.isLt
      omega
    rw [show (∫ t : UnitAddTorus (Fin 1),
        (((circularDiscriminantSq 1 t) ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Fin 1 => AddCircle.haarAddCircle)) = 1 by
      simp [circularDiscriminantSq, hpairs]]
    norm_num [hg]
  have hnpos : 0 < S.n := by
    rw [S.odd_rank]
    omega
  have hn : 2 ≤ S.n := by
    omega
  have hs : 0 ≤ (k : ℝ) + 1 / 2 := by positivity
  unfold circularMorrisIntegral
  change (∫ t : UnitAddTorus (Fin S.n),
      circularMorrisIntegrand (dysonSetup S k) t) = _
  rw [unitTorus_volume_eq_haarPi]
  simp_rw [circularMorrisIntegrand_dyson_eq_rpow]
  have hreal :
    (∫ t : UnitAddTorus (Fin S.n),
        circularDiscriminantSq S.n t ^ ((k : ℝ) + 1 / 2)
          ∂(Measure.pi fun _ : Fin S.n => AddCircle.haarAddCircle)) =
      Real.Gamma (1 + (S.n : ℝ) * ((k : ℝ) + 1 / 2)) /
        Real.Gamma (1 + ((k : ℝ) + 1 / 2)) ^ S.n := by
    calc
      (∫ t : UnitAddTorus (Fin S.n),
          circularDiscriminantSq S.n t ^ ((k : ℝ) + 1 / 2)
            ∂(Measure.pi fun _ : Fin S.n => AddCircle.haarAddCircle)) =
          ∫ x : Fin (S.n - 1) → ℝ,
          dysonBetaProduct S.n x ^ ((k : ℝ) + 1 / 2)
            ∂(Measure.pi (dysonBetaMeasure S.n)) :=
        integral_circularDiscriminantSq_rpow_eq_betaProduct
          S.n hn ((k : ℝ) + 1 / 2) hs
      _ = _ := integral_dysonBetaProduct_rpow_eq_gammaRatio
        S.n hn ((k : ℝ) + 1 / 2) hs
  calc
    (∫ t : UnitAddTorus (Fin S.n),
        (((circularDiscriminantSq S.n t) ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Fin S.n => AddCircle.haarAddCircle)) =
      (((∫ t : UnitAddTorus (Fin S.n),
          circularDiscriminantSq S.n t ^ ((k : ℝ) + 1 / 2)
            ∂(Measure.pi fun _ : Fin S.n => AddCircle.haarAddCircle)) : ℝ) : ℂ) :=
        integral_ofReal
    _ = _ := congrArg Complex.ofReal hreal

theorem circularMorrisIntegral_dyson_proved (S : Setup) (k : ℕ) :
    circularMorrisIntegral (dysonSetup S k) =
      gammaPochhammerPart (dysonSetup S k) (dysonSetup S k).K := by
  rw [circularMorrisIntegral_dyson_eq_gammaRatio]
  have hnum :
      1 + ((dysonSetup S k).n : ℂ) * ((dysonSetup S k).K : ℂ) / 2 =
        ((1 + (S.n : ℝ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ) := by
    simp only [dysonSetup_n, dysonSetup_K]
    push_cast
    ring
  have hden :
      1 + ((dysonSetup S k).K : ℂ) / 2 =
        ((1 + ((k : ℝ) + 1 / 2) : ℝ) : ℂ) := by
    simp only [dysonSetup_K]
    push_cast
    ring
  unfold gammaPochhammerPart
  simp only [dysonSetup_a, dysonSetup_b, Nat.zero_add, pochhammer_zero,
    mul_one, div_one, Finset.prod_const_one]
  rw [hnum, hden, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simpa only [dysonSetup_n, Complex.ofReal_div, Complex.ofReal_pow]

theorem logarithmicMorris_dyson_proved (S : Setup) (k : ℕ) :
    LogarithmicMorrisStatement (dysonSetup S k) := by
  exact logarithmicMorris_dyson_of_circular S k
    (circularMorrisIntegral_dyson_proved S k)

end LogarithmicMorrisFull
