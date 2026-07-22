import logarithmicmorris.ScratchLogPfaff
import logarithmicmorris.ScratchCircularSymmetry

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

theorem kernel_mul_permAlternatingLog_ordered (S : Setup)
    (θ : Fin S.n → ℝ)
    (horder : ∀ i j, i < j → θ i < θ j)
    (hwidth : ∀ i j, i < j → θ j - θ i < 2 * Real.pi) :
    torusEval (morrisKernel S) (angleTorus θ) *
        permAlternatingSum (standardPairedLog S) (angleTorus θ) =
      (S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m *
        circularMorrisIntegrand S (angleTorus θ) := by
  rw [torusEval_morrisKernel_ordered S θ horder hwidth,
    permAlternatingSum_standardPairedLog_ordered S θ horder hwidth]
  have hpow : (-Real.pi * Complex.I) ^ S.m =
      (Real.pi : ℂ) ^ S.m * (-Complex.I) ^ S.m := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hphase := neg_I_chamber_phase S.m
  rw [show
    (-Complex.I) ^ (S.m * S.n) * circularMorrisIntegrand S (angleTorus θ) *
        ((S.m.factorial : ℂ) *
          ((Real.pi : ℂ) ^ S.m * (-Complex.I) ^ S.m)) =
      ((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) *
        (((-Complex.I) ^ (S.m * S.n) * (-Complex.I) ^ S.m) *
          circularMorrisIntegrand S (angleTorus θ)) by ring]
  have hphaseS :
      (-Complex.I) ^ (S.m * S.n) * (-Complex.I) ^ S.m = 1 := by
    rw [S.odd_rank]
    exact hphase
  rw [hphaseS]
  ring

theorem kernel_mul_permAlternatingLog_of_injective (S : Setup)
    (t : UnitAddTorus (Fin S.n)) (ht : Function.Injective t) :
    torusEval (morrisKernel S) t *
        permAlternatingSum (standardPairedLog S) t =
      (S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m *
        circularMorrisIntegrand S t := by
  let σ := sortingPerm t
  let θ := sortingAngles t
  have h := kernel_mul_permAlternatingLog_ordered S θ
    (sortingAngles_order t ht) (sortingAngles_width t)
  rw [angleTorus_sortingAngles] at h
  change
    torusEval (morrisKernel S) (permuteTorus σ t) *
        permAlternatingSum (standardPairedLog S) (permuteTorus σ t) =
      (S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m *
        circularMorrisIntegrand S (permuteTorus σ t) at h
  rw [torusEval_morrisKernel_permute,
    permAlternatingSum_permute, circularMorrisIntegrand_permute] at h
  have hs := permSign_sq_complex σ
  calc
    torusEval (morrisKernel S) t *
        permAlternatingSum (standardPairedLog S) t =
      (((σ.sign : ℤ) : ℂ) * ((σ.sign : ℤ) : ℂ)) *
        (torusEval (morrisKernel S) t *
          permAlternatingSum (standardPairedLog S) t) := by rw [hs]; simp
    _ = (((σ.sign : ℤ) : ℂ) * torusEval (morrisKernel S) t) *
        (((σ.sign : ℤ) : ℂ) *
          permAlternatingSum (standardPairedLog S) t) := by ring
    _ = (S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m *
        circularMorrisIntegrand S t := h

theorem torusEval_morrisKernel_eq_zero_of_collision (S : Setup)
    (t : UnitAddTorus (Fin S.n)) {i j : Fin S.n}
    (hij : i < j) (heq : t i = t j) :
    torusEval (morrisKernel S) t = 0 := by
  rw [torusEval_morrisKernel]
  have hp : (i, j) ∈ increasingPairs S.n := by
    simp [increasingPairs, hij]
  have hV :
      (∏ p ∈ increasingPairs S.n,
        (fourier 1 (t p.1) - fourier 1 (t p.2))) = 0 := by
    apply Finset.prod_eq_zero hp
    rw [heq]
    ring
  rw [hV]
  ring

theorem circularMorrisIntegrand_eq_zero_of_collision (S : Setup)
    (t : UnitAddTorus (Fin S.n)) {i j : Fin S.n}
    (hij : i < j) (heq : t i = t j) :
    circularMorrisIntegrand S t = 0 := by
  simp only [circularMorrisIntegrand]
  have hp : (i, j) ∈ increasingPairs S.n := by
    simp [increasingPairs, hij]
  have hD :
      (∏ p ∈ increasingPairs S.n,
        (‖fourier 1 (t p.1) - fourier 1 (t p.2)‖ : ℂ) ^ S.K) = 0 := by
    apply Finset.prod_eq_zero hp
    rw [heq]
    simp [S.K_ne_zero]
  rw [hD, mul_zero]

theorem kernel_mul_permAlternatingLog_of_not_injective (S : Setup)
    (t : UnitAddTorus (Fin S.n)) (ht : ¬Function.Injective t) :
    torusEval (morrisKernel S) t *
        permAlternatingSum (standardPairedLog S) t =
      (S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m *
        circularMorrisIntegrand S t := by
  simp only [Function.Injective, not_forall] at ht
  obtain ⟨i, j, heq, hne⟩ := ht
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · rw [torusEval_morrisKernel_eq_zero_of_collision S t hijlt heq,
      circularMorrisIntegrand_eq_zero_of_collision S t hijlt heq]
    ring
  · rw [torusEval_morrisKernel_eq_zero_of_collision S t hjilt heq.symm,
      circularMorrisIntegrand_eq_zero_of_collision S t hjilt heq.symm]
    ring

theorem kernel_mul_permAlternatingLog (S : Setup)
    (t : UnitAddTorus (Fin S.n)) :
    torusEval (morrisKernel S) t *
        permAlternatingSum (standardPairedLog S) t =
      (S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m *
        circularMorrisIntegrand S t := by
  by_cases ht : Function.Injective t
  · exact kernel_mul_permAlternatingLog_of_injective S t ht
  · exact kernel_mul_permAlternatingLog_of_not_injective S t ht

theorem torusLogIntegral_eq_circular (S : Setup)
    (hbase : MeasureTheory.Integrable
      (fun t : UnitAddTorus (Fin S.n) =>
        torusEval (morrisKernel S) t * standardPairedLog S t)) :
    (∫ t : UnitAddTorus (Fin S.n),
        torusEval (morrisKernel S) t * standardPairedLog S t) =
      (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral S := by
  have hInt : ∀ σ : Equiv.Perm (Fin S.n),
      MeasureTheory.Integrable (fun t =>
        torusEval (morrisKernel S) t *
          standardPairedLog S (permuteTorus σ t)) := by
    intro σ
    exact integrable_alternating_mul_permute
      (torusEval (morrisKernel S)) (standardPairedLog S)
      (torusEval_morrisKernel_permute S) hbase σ
  have havg := integral_mul_permAlternatingSum
    (torusEval (morrisKernel S)) (standardPairedLog S)
    (torusEval_morrisKernel_permute S) hInt
  have hpoint :
      (∫ t : UnitAddTorus (Fin S.n),
        torusEval (morrisKernel S) t *
          permAlternatingSum (standardPairedLog S) t) =
        ((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) *
          circularMorrisIntegral S := by
    calc
      (∫ t : UnitAddTorus (Fin S.n),
          torusEval (morrisKernel S) t *
            permAlternatingSum (standardPairedLog S) t) =
        ∫ t : UnitAddTorus (Fin S.n),
          ((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) *
            circularMorrisIntegrand S t := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          exact kernel_mul_permAlternatingLog S t
      _ = ((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) *
          circularMorrisIntegral S := by
        rw [MeasureTheory.integral_const_mul]
        simp only [circularMorrisIntegral]
  have heq :
      (S.n.factorial : ℂ) *
          (∫ t : UnitAddTorus (Fin S.n),
            torusEval (morrisKernel S) t * standardPairedLog S t) =
        ((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) *
          circularMorrisIntegral S := havg.symm.trans hpoint
  have hn : (S.n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero S.n
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).2
  simpa [mul_comm] using heq

end LogarithmicMorrisFull
