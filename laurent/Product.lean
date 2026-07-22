import laurent.Rename

/-! # 有限乘积与常数项展开框架 -/

open scoped BigOperators
open Finset

namespace MultiLaurent

/-- 单项式的有限乘积仍是单项式。 -/
theorem prod_monomial {σ R ι : Type*} [CommSemiring R]
    (s : Finset ι) (d : ι → Exponent σ) (c : ι → R) :
    ∏ i ∈ s, monomial (d i) (c i) =
      monomial (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      simp [ha, ih, monomial_mul_monomial]

/-- 单项式有限乘积的常数项由总指数是否为零决定。 -/
theorem constantTerm_prod_monomial {σ R ι : Type*} [CommSemiring R]
    [DecidableEq σ] (s : Finset ι) (d : ι → Exponent σ) (c : ι → R) :
    constantTerm (∏ i ∈ s, monomial (d i) (c i)) =
      if ∑ i ∈ s, d i = 0 then ∏ i ∈ s, c i else 0 := by
  rw [prod_monomial]
  exact constantTerm_monomial _ _

/-- 递推加入一个因子时的常数项卷积公式。 -/
theorem constantTerm_mul_eq_sum_support {σ R : Type*} [CommSemiring R]
    (p q : Polynomial σ R) :
    constantTerm (p * q) = ∑ d ∈ p.support, p d * q (-d) := by
  simpa [Finsupp.sum] using constantTerm_mul p q

end MultiLaurent
