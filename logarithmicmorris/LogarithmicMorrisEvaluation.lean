import Mathlib
import Mathlib.Analysis.Fourier.AddCircleMulti
import logarithmicmorris.LogarithmicMorrisFullBasic

/-!
# Evaluation of finite Laurent polynomials on a complex torus
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open Set Algebra Submodule MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The multiplicative character of an exponent vector at nonzero values. -/
def exponentCharacter {σ : Type*} (x : σ → ℂˣ) :
    Multiplicative (MultiLaurent.Exponent σ) →* ℂ := by
  classical
  exact
    { toFun := fun d =>
        (((Multiplicative.toAdd d).prod fun i z => x i ^ z : ℂˣ) : ℂ)
      map_one' := by simp
      map_mul' := fun d e => by
        change (((Multiplicative.toAdd d + Multiplicative.toAdd e).prod
          fun i z => x i ^ z : ℂˣ) : ℂ) = _
        rw [Finsupp.prod_add_index]
        · rfl
        · intro i hi
          simp
        · intro i hi a b
          exact zpow_add (x i) a b }

/-- Evaluation as a `ℚ`-algebra homomorphism. -/
def evalLaurent {σ : Type*} (x : σ → ℂˣ) :
    MultiLaurent.Polynomial σ ℚ →ₐ[ℚ] ℂ :=
  (AddMonoidAlgebra.lift ℚ ℂ (MultiLaurent.Exponent σ)) (exponentCharacter x)

@[simp] theorem evalLaurent_monomial {σ : Type*} (x : σ → ℂˣ)
    (d : MultiLaurent.Exponent σ) (c : ℚ) :
    evalLaurent x (MultiLaurent.monomial d c) =
      (c : ℂ) * exponentCharacter x (Multiplicative.ofAdd d) := by
  simp [evalLaurent, MultiLaurent.monomial, AddMonoidAlgebra.lift_single,
    Algebra.smul_def]

@[simp] theorem evalLaurent_X {σ : Type*} (x : σ → ℂˣ)
    (d : MultiLaurent.Exponent σ) :
    evalLaurent x (MultiLaurent.X d : MultiLaurent.Polynomial σ ℚ) =
      exponentCharacter x (Multiplicative.ofAdd d) := by
  simp [MultiLaurent.X]

@[simp] theorem exponentCharacter_single {σ : Type*} (x : σ → ℂˣ)
    (i : σ) (z : ℤ) :
    exponentCharacter x (Multiplicative.ofAdd (Finsupp.single i z)) =
      (x i : ℂ) ^ z := by
  simp [exponentCharacter]

@[simp] theorem evalLaurent_var {σ : Type*} (x : σ → ℂˣ) (i : σ) :
    evalLaurent x (MultiLaurent.var i : MultiLaurent.Polynomial σ ℚ) = x i := by
  simp [MultiLaurent.var]

@[simp] theorem evalLaurent_varInv {σ : Type*} (x : σ → ℂˣ) (i : σ) :
    evalLaurent x (MultiLaurent.varInv i : MultiLaurent.Polynomial σ ℚ) =
      (x i : ℂ)⁻¹ := by
  simp [MultiLaurent.varInv, zpow_neg, zpow_one]

/-- The unit-circle point `e^{iθ}` as a unit. -/
def circleUnit (θ : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _)

@[simp] theorem circleUnit_coe (θ : ℝ) :
    (circleUnit θ : ℂ) = Complex.exp (θ * Complex.I) := rfl

/-- A point of the additive circle, regarded as a nonzero complex number. -/
def addCircleUnit (t : UnitAddCircle) : ℂˣ :=
  Units.mk0 (t.toCircle : ℂ) (Circle.coe_ne_zero t.toCircle)

@[simp] theorem addCircleUnit_coe (t : UnitAddCircle) :
    (addCircleUnit t : ℂ) = fourier 1 t := by
  simp [addCircleUnit, fourier_one]

theorem addCircleUnit_zpow (t : UnitAddCircle) (z : ℤ) :
    (addCircleUnit t : ℂ) ^ z = fourier z t := by
  rw [addCircleUnit]
  change (t.toCircle : ℂ) ^ z = fourier z t
  rw [← Circle.coe_zpow, ← AddCircle.toCircle_zsmul, ← fourier_apply]

theorem exponentCharacter_addCircle {σ : Type*} [Fintype σ]
    (t : UnitAddTorus σ) (d : MultiLaurent.Exponent σ) :
    exponentCharacter (fun i => addCircleUnit (t i)) (Multiplicative.ofAdd d) =
      UnitAddTorus.mFourier (fun i => d i) t := by
  classical
  simp only [exponentCharacter]
  change (((∏ i ∈ d.support, addCircleUnit (t i) ^ d i : ℂˣ) : ℂ)) =
    ∏ i : σ, fourier (d i) (t i)
  push_cast
  simp_rw [addCircleUnit_zpow]
  apply Finset.prod_subset (Finset.subset_univ d.support)
  intro i hi hnot
  have hdi : d i = 0 := by
    simpa [Finsupp.mem_support_iff] using hnot
  simp [hdi, fourier_zero]

theorem integral_mFourier {σ : Type*} [Fintype σ] (d : σ → ℤ) :
    (∫ t : UnitAddTorus σ, UnitAddTorus.mFourier d t) =
      if d = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := σ))) (0 : σ → ℤ) d
  simp only [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, map_one, mul_one] at h
  simpa only [eq_comm] using h

/-- Evaluation of a Laurent polynomial on the normalized unit torus. -/
def torusEval {σ : Type*} [Fintype σ]
    (F : MultiLaurent.Polynomial σ ℚ) (t : UnitAddTorus σ) : ℂ :=
  evalLaurent (fun i => addCircleUnit (t i)) F

theorem torusEval_monomial {σ : Type*} [Fintype σ]
    (d : MultiLaurent.Exponent σ) (c : ℚ) (t : UnitAddTorus σ) :
    torusEval (MultiLaurent.monomial d c) t =
      (c : ℂ) * UnitAddTorus.mFourier (fun i => d i) t := by
  rw [torusEval, evalLaurent_monomial, exponentCharacter_addCircle]

theorem continuous_torusEval {σ : Type*} [Fintype σ]
    (F : MultiLaurent.Polynomial σ ℚ) : Continuous (torusEval F) := by
  classical
  induction F using MultiLaurent.induction_on with
  | h0 =>
      simpa only [torusEval, map_zero] using
        (continuous_const : Continuous (fun _ : UnitAddTorus σ => (0 : ℂ)))
  | hadd F G hF hG =>
      have heq : torusEval (F + G) = torusEval F + torusEval G := by
        funext t
        simp [torusEval]
      rw [heq]
      exact hF.add hG
  | hmono d c =>
      rw [show torusEval (MultiLaurent.monomial d c) =
          fun t => (c : ℂ) * UnitAddTorus.mFourier (fun i => d i) t by
        funext t
        exact torusEval_monomial d c t]
      exact continuous_const.mul (UnitAddTorus.mFourier _).continuous

/-- Fourier orthogonality identifies the normalized torus integral with the
constant coefficient. -/
theorem integral_torusEval {σ : Type*} [Fintype σ]
    (F : MultiLaurent.Polynomial σ ℚ) :
    (∫ t : UnitAddTorus σ, torusEval F t) =
      ((MultiLaurent.constantTerm F : ℚ) : ℂ) := by
  classical
  induction F using MultiLaurent.induction_on with
  | h0 => simp [torusEval]
  | hadd F G hF hG =>
      rw [show torusEval (F + G) = torusEval F + torusEval G by
        funext t
        simp [torusEval]]
      change (∫ t : UnitAddTorus σ, torusEval F t + torusEval G t) = _
      rw [integral_add]
      · rw [hF, hG]
        simp
      · simpa only [integrableOn_univ] using
          (ContinuousOn.integrableOn_compact isCompact_univ
            (continuous_torusEval F).continuousOn)
      · simpa only [integrableOn_univ] using
          (ContinuousOn.integrableOn_compact isCompact_univ
            (continuous_torusEval G).continuousOn)
  | hmono d c =>
      rw [show torusEval (MultiLaurent.monomial d c) =
          fun t => (c : ℂ) * UnitAddTorus.mFourier (fun i => d i) t by
        funext t
        exact torusEval_monomial d c t]
      rw [integral_const_mul, integral_mFourier]
      by_cases hd : d = 0
      · have hfun : (fun i => d i) = 0 := by
          funext i
          simp [hd]
        rw [if_pos hfun]
        simp [hd, MultiLaurent.constantTerm, MultiLaurent.monomial]
      · have hfun : (fun i => d i) ≠ 0 := by
          intro h
          apply hd
          ext i
          exact congrFun h i
        rw [if_neg hfun]
        simp [hd, MultiLaurent.constantTerm, MultiLaurent.monomial]

end LogarithmicMorrisFull
