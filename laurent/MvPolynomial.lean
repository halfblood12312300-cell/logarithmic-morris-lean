import laurent.ConstantTerm
import Mathlib.Algebra.MvPolynomial.Eval

/-! # 普通多项式到 Laurent 多项式的自然嵌入 -/

namespace MultiLaurent

/-- 自然数指数向量嵌入整数指数向量。 -/
noncomputable def ofNatExponent {σ : Type*} : (σ →₀ ℕ) →+ Exponent σ :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

theorem ofNatExponent_injective {σ : Type*} :
    Function.Injective (ofNatExponent (σ := σ)) := by
  exact Finsupp.mapRange_injective _ (map_zero (Nat.castAddMonoidHom ℤ))
    Int.ofNat_injective

/-- 将普通多变量多项式视为没有负指数的 Laurent 多项式。 -/
noncomputable def ofMvPolynomial {σ R : Type*} [CommSemiring R] :
    MvPolynomial σ R →ₐ[R] Polynomial σ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R ofNatExponent

@[simp] theorem ofMvPolynomial_C {σ R : Type*} [CommSemiring R] (c : R) :
    ofMvPolynomial (MvPolynomial.C c : MvPolynomial σ R) = monomial 0 c := by
  simp [ofMvPolynomial, monomial, AddMonoidAlgebra.mapDomainAlgHom]

theorem ofMvPolynomial_monomial {σ R : Type*} [CommSemiring R]
    (d : σ →₀ ℕ) (c : R) :
    ofMvPolynomial (MvPolynomial.monomial d c) =
      monomial (ofNatExponent d) c := by
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem ofMvPolynomial_X {σ R : Type*} [CommSemiring R] (i : σ) :
    ofMvPolynomial (MvPolynomial.X i : MvPolynomial σ R) = var i := by
  change ofMvPolynomial (MvPolynomial.monomial (Finsupp.single i 1) 1) = var i
  rw [ofMvPolynomial_monomial]
  congr 1
  ext j
  by_cases hij : i = j <;> simp [ofNatExponent, hij]

/-- 普通多项式的常数项与嵌入后的 Laurent 常数项一致。 -/
theorem constantTerm_ofMvPolynomial {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    constantTerm (ofMvPolynomial p) = MvPolynomial.constantCoeff p := by
  change Finsupp.mapDomain (ofNatExponent (σ := σ)) p 0 = MvPolynomial.coeff 0 p
  simpa using
    (Finsupp.mapDomain_apply ofNatExponent_injective p (0 : σ →₀ ℕ))

theorem ofMvPolynomial_injective {σ R : Type*} [CommSemiring R] :
    Function.Injective (ofMvPolynomial : MvPolynomial σ R → Polynomial σ R) := by
  exact Finsupp.mapDomain_injective ofNatExponent_injective

end MultiLaurent
