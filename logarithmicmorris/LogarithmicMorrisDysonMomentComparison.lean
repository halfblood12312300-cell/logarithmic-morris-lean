import logarithmicmorris.LogarithmicMorrisEvenMoments
import logarithmicmorris.LogarithmicMorrisDysonBetaProduct

/-! # Compact moment comparison for the circular discriminant -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory Set

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A common compact upper bound for the two random variables used below. -/
def dysonMomentBound (n : ℕ) : ℝ :=
  (4 : ℝ) ^ (increasingPairs n).card + (n : ℝ) ^ n

lemma circularDiscriminantSq_nonneg (n : ℕ)
    (t : UnitAddTorus (Fin n)) :
    0 ≤ circularDiscriminantSq n t := by
  unfold circularDiscriminantSq
  positivity

lemma fourier_sub_norm_le_two {x y : UnitAddCircle} :
    ‖fourier 1 x - fourier 1 y‖ ≤ 2 := by
  calc
    _ ≤ ‖fourier 1 x‖ + ‖fourier 1 y‖ := norm_sub_le _ _
    _ = 2 := by simp [fourier_apply] <;> norm_num

lemma circularDiscriminantSq_le (n : ℕ)
    (t : UnitAddTorus (Fin n)) :
    circularDiscriminantSq n t ≤
      (4 : ℝ) ^ (increasingPairs n).card := by
  unfold circularDiscriminantSq
  calc
    ∏ p ∈ increasingPairs n,
        ‖fourier 1 (t p.1) - fourier 1 (t p.2)‖ ^ 2 ≤
        ∏ _p ∈ increasingPairs n, (4 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        nlinarith [fourier_sub_norm_le_two
          (x := t p.1) (y := t p.2),
          norm_nonneg (fourier 1 (t p.1) - fourier 1 (t p.2))]
    _ = _ := by simp

lemma dysonMomentBound_nonneg (n : ℕ) : 0 ≤ dysonMomentBound n := by
  unfold dysonMomentBound
  positivity

lemma circularDiscriminantSq_le_bound (n : ℕ)
    (t : UnitAddTorus (Fin n)) :
    circularDiscriminantSq n t ≤ dysonMomentBound n := by
  unfold dysonMomentBound
  exact le_add_of_nonneg_right (by positivity)
    |>.trans' (circularDiscriminantSq_le n t)

lemma dysonBetaProduct_le_bound (n : ℕ)
    (x : Fin (n - 1) → ℝ) :
    dysonBetaProduct n x ≤ dysonMomentBound n := by
  unfold dysonMomentBound
  exact le_add_of_nonneg_left (by positivity)
    |>.trans' (dysonBetaProduct_le n x)

lemma continuous_circularDiscriminantSq (n : ℕ) :
    Continuous (circularDiscriminantSq n) := by
  unfold circularDiscriminantSq
  fun_prop

lemma continuous_dysonBetaProduct (n : ℕ) :
    Continuous (dysonBetaProduct n) := by
  unfold dysonBetaProduct clampUnit
  fun_prop

def circularMomentPoint (n : ℕ) (t : UnitAddTorus (Fin n)) :
    Set.Icc (0 : ℝ) (dysonMomentBound n) :=
  ⟨circularDiscriminantSq n t,
    circularDiscriminantSq_nonneg n t,
    circularDiscriminantSq_le_bound n t⟩

def betaMomentPoint (n : ℕ) (x : Fin (n - 1) → ℝ) :
    Set.Icc (0 : ℝ) (dysonMomentBound n) :=
  ⟨dysonBetaProduct n x,
    dysonBetaProduct_nonneg n x,
    dysonBetaProduct_le_bound n x⟩

lemma measurable_circularMomentPoint (n : ℕ) :
    Measurable (circularMomentPoint n) := by
  exact (continuous_circularDiscriminantSq n).subtype_mk _ |>.measurable

lemma measurable_betaMomentPoint (n : ℕ) :
    Measurable (betaMomentPoint n) := by
  exact (continuous_dysonBetaProduct n).subtype_mk _ |>.measurable

def circularMomentMeasure (n : ℕ) :
    Measure (Set.Icc (0 : ℝ) (dysonMomentBound n)) :=
  Measure.map (circularMomentPoint n) (volume : Measure (UnitAddTorus (Fin n)))

def betaMomentMeasure (n : ℕ) :
    Measure (Set.Icc (0 : ℝ) (dysonMomentBound n)) :=
  Measure.map (betaMomentPoint n) (Measure.pi (dysonBetaMeasure n))

theorem integral_circularDiscriminantSq_rpow_eq_betaProduct
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) :
    (∫ t : UnitAddTorus (Fin n), (circularDiscriminantSq n t) ^ s) =
      ∫ x : Fin (n - 1) → ℝ, (dysonBetaProduct n x) ^ s
        ∂(Measure.pi (dysonBetaMeasure n)) := by
  let μ := circularMomentMeasure n
  let ν := betaMomentMeasure n
  letI : IsProbabilityMeasure μ := by
    unfold μ circularMomentMeasure
    exact Measure.isProbabilityMeasure_map
      (measurable_circularMomentPoint n).aemeasurable
  letI (i : Fin (n - 1)) : IsProbabilityMeasure (dysonBetaMeasure n i) :=
    dysonBetaMeasure_isProbability n hn i
  letI : IsProbabilityMeasure ν := by
    unfold ν betaMomentMeasure
    exact Measure.isProbabilityMeasure_map
      (measurable_betaMomentPoint n).aemeasurable
  have hmom : ∀ q : ℕ,
      (∫ x, (x.1 : ℝ) ^ q ∂μ) = ∫ x, (x.1 : ℝ) ^ q ∂ν := by
    intro q
    calc
      (∫ x, (x.1 : ℝ) ^ q ∂μ) =
          ∫ t : UnitAddTorus (Fin n),
            (circularDiscriminantSq n t) ^ q := by
        unfold μ circularMomentMeasure
        rw [integral_map (measurable_circularMomentPoint n).aemeasurable]
        · rfl
        · fun_prop
      _ = (((n * q).factorial : ℝ) / (q.factorial : ℝ) ^ n) :=
        integral_circularDiscriminantSq_pow n q
      _ = ∫ x : Fin (n - 1) → ℝ,
            (dysonBetaProduct n x) ^ q
              ∂(Measure.pi (dysonBetaMeasure n)) :=
        (integral_dysonBetaProduct_pow n q hn).symm
      _ = ∫ x, (x.1 : ℝ) ^ q ∂ν := by
        unfold ν betaMomentMeasure
        rw [integral_map (measurable_betaMomentPoint n).aemeasurable]
        · rfl
        · fun_prop
  let f : C(Set.Icc (0 : ℝ) (dysonMomentBound n), ℝ) :=
    ⟨fun x => (x.1 : ℝ) ^ s,
      (Real.continuous_rpow_const hs).comp continuous_subtype_val⟩
  have hcontinuous :=
    integral_continuous_eq_of_moments_on_Icc (dysonMomentBound n) μ ν hmom f
  calc
    (∫ t : UnitAddTorus (Fin n), (circularDiscriminantSq n t) ^ s) =
        ∫ x, f x ∂μ := by
      unfold μ circularMomentMeasure
      rw [integral_map (measurable_circularMomentPoint n).aemeasurable]
      · rfl
      · exact f.continuous.aestronglyMeasurable
    _ = ∫ x, f x ∂ν := hcontinuous
    _ = ∫ x : Fin (n - 1) → ℝ,
          (dysonBetaProduct n x) ^ s
            ∂(Measure.pi (dysonBetaMeasure n)) := by
      unfold ν betaMomentMeasure
      rw [integral_map (measurable_betaMomentPoint n).aemeasurable]
      · rfl
      · exact f.continuous.aestronglyMeasurable

end LogarithmicMorrisFull
