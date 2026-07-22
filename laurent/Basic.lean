import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# 多变量 Laurent 多项式：基础定义

指数向量是 `σ →₀ ℤ`，多变量 Laurent 多项式是该加法群上的群代数。
-/

open scoped BigOperators

namespace MultiLaurent

/-- 有限支撑的整数指数向量。 -/
abbrev Exponent (σ : Type*) := σ →₀ ℤ

/-- 系数在 `R` 中、变量由 `σ` 标号的多变量 Laurent 多项式。 -/
abbrev Polynomial (σ : Type*) (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R (Exponent σ)

/-- Laurent 单项式 `c X^d`。 -/
noncomputable def monomial {σ R : Type*} [Semiring R] (d : Exponent σ) (c : R) :
    Polynomial σ R := Finsupp.single d c

/-- `X^d`。 -/
noncomputable def X {σ R : Type*} [Semiring R] (d : Exponent σ) : Polynomial σ R :=
  monomial d 1

/-- 第 `i` 个变量。 -/
noncomputable def var {σ R : Type*} [Semiring R] (i : σ) : Polynomial σ R :=
  X (Finsupp.single i 1)

/-- 第 `i` 个变量的逆。 -/
noncomputable def varInv {σ R : Type*} [Semiring R] (i : σ) : Polynomial σ R :=
  X (Finsupp.single i (-1))

@[simp] theorem monomial_apply {σ R : Type*} [Semiring R]
    [DecidableEq (Exponent σ)] (d e : Exponent σ) (c : R) :
    monomial d c e = if d = e then c else 0 := by
  classical
  simp only [monomial, Finsupp.single_apply]

@[simp] theorem monomial_zero_coeff {σ R : Type*} [Semiring R]
    (d : Exponent σ) : monomial d (0 : R) = 0 := by
  simp [monomial]

@[simp] theorem X_zero {σ R : Type*} [Semiring R] :
    X (0 : Exponent σ) = (1 : Polynomial σ R) := by
  rfl

theorem monomial_mul_monomial {σ R : Type*} [Semiring R]
    (d e : Exponent σ) (a b : R) :
    monomial d a * monomial e b = monomial (d + e) (a * b) := by
  exact AddMonoidAlgebra.single_mul_single d e a b

@[simp] theorem X_mul_X {σ R : Type*} [Semiring R] (d e : Exponent σ) :
    X (R := R) d * X e = X (d + e) := by
  simpa [X] using monomial_mul_monomial d e (1 : R) 1

@[simp] theorem var_mul_varInv {σ R : Type*} [CommSemiring R] (i : σ) :
    var (R := R) i * varInv i = 1 := by
  simp only [var, varInv, X_mul_X]
  rw [← Finsupp.single_add]
  simp

theorem X_pow {σ R : Type*} [Semiring R] (d : Exponent σ) (n : ℕ) :
    X (R := R) d ^ n = X (n • d) := by
  simp only [X, monomial]
  rw [AddMonoidAlgebra.single_pow]
  simp

theorem induction_on {σ R : Type*} [Semiring R] {P : Polynomial σ R → Prop}
    (p : Polynomial σ R) (h0 : P 0)
    (hadd : ∀ p q, P p → P q → P (p + q))
    (hmono : ∀ d c, P (monomial d c)) : P p := by
  induction p using Finsupp.induction with
  | zero => exact h0
  | single_add d c p _ _ hp =>
      exact hadd _ _ (hmono d c) hp

end MultiLaurent
