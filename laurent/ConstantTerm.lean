import laurent.Basic

/-! # 多变量 Laurent 多项式的常数项 -/

open scoped BigOperators

namespace MultiLaurent

/-- 指数 `d` 的系数，作为线性映射。 -/
def coeff {σ R : Type*} [Semiring R] (d : Exponent σ) :
    Polynomial σ R →ₗ[R] R where
  toFun p := p d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 多变量常数项算子。 -/
def constantTerm {σ R : Type*} [Semiring R] : Polynomial σ R →ₗ[R] R :=
  coeff 0

@[simp] theorem coeff_apply {σ R : Type*} [Semiring R]
    (d : Exponent σ) (p : Polynomial σ R) : coeff d p = p d := rfl

@[simp] theorem constantTerm_apply {σ R : Type*} [Semiring R]
    (p : Polynomial σ R) : constantTerm p = p 0 := rfl

@[simp] theorem coeff_monomial {σ R : Type*} [Semiring R]
    [DecidableEq (Exponent σ)] (d e : Exponent σ) (c : R) :
    coeff e (monomial d c) = if d = e then c else 0 := by
  exact monomial_apply d e c

@[simp] theorem constantTerm_monomial {σ R : Type*} [Semiring R]
    [DecidableEq (Exponent σ)] (d : Exponent σ) (c : R) :
    constantTerm (monomial d c) = if d = 0 then c else 0 := by
  simp [constantTerm]

@[simp] theorem constantTerm_X {σ R : Type*} [Semiring R]
    [DecidableEq (Exponent σ)] (d : Exponent σ) :
    constantTerm (X d : Polynomial σ R) = if d = 0 then 1 else 0 := by
  simp [X]

/-- 乘积的系数是有限卷积。 -/
theorem coeff_mul {σ R : Type*} [Semiring R] [DecidableEq σ] (p q : Polynomial σ R)
    (d : Exponent σ) :
    coeff d (p * q) = p.sum fun a pa => q.sum fun b qb => if a + b = d then pa * qb else 0 := by
  exact AddMonoidAlgebra.mul_apply p q d

/-- 常数项是互为相反指数的系数之有限卷积。 -/
theorem constantTerm_mul {σ R : Type*} [Semiring R] (p q : Polynomial σ R) :
    constantTerm (p * q) = p.sum fun d c => c * q (-d) := by
  simpa [constantTerm, coeff] using (AddMonoidAlgebra.mul_apply_left p q 0)

/-- 乘以 Laurent 单项式等价于平移待抽取的系数。 -/
theorem coeff_X_mul {σ R : Type*} [Semiring R] (d e : Exponent σ)
    (p : Polynomial σ R) :
    coeff e (X d * p) = coeff (e - d) p := by
  simpa [coeff, X, monomial, sub_eq_add_neg, add_comm] using
    (AddMonoidAlgebra.single_mul_apply p (1 : R) d e)

/-- 常数项方法最常用的“乘单项式后取常数项 = 取相反指数系数”。 -/
theorem constantTerm_X_mul {σ R : Type*} [Semiring R] (d : Exponent σ)
    (p : Polynomial σ R) :
    constantTerm (X d * p) = coeff (-d) p := by
  simpa [constantTerm] using coeff_X_mul d 0 p

end MultiLaurent
