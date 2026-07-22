import laurent.Rename

/-! # 同时取所有变量的逆 -/

namespace MultiLaurent

/-- 指数向量取负。 -/
noncomputable def negExponent {σ : Type*} : Exponent σ ≃+ Exponent σ :=
  AddEquiv.neg _

/-- 代换 `X_i ↦ X_i⁻¹`。 -/
noncomputable def invertVariables {σ R : Type*} [Semiring R] :
    Polynomial σ R →+* Polynomial σ R :=
  AddMonoidAlgebra.mapDomainRingHom R negExponent.toAddMonoidHom

@[simp] theorem invertVariables_monomial {σ R : Type*} [Semiring R]
    (d : Exponent σ) (c : R) :
    invertVariables (monomial d c) = monomial (-d) c := by
  simp [invertVariables, negExponent, monomial,
    AddMonoidAlgebra.mapDomainRingHom_apply]

@[simp] theorem invertVariables_X {σ R : Type*} [Semiring R] (d : Exponent σ) :
    invertVariables (X d : Polynomial σ R) = X (-d) := by
  simp [X]

@[simp] theorem invertVariables_involutive {σ R : Type*} [Semiring R]
    (p : Polynomial σ R) : invertVariables (invertVariables p) = p := by
  ext d
  change Finsupp.mapDomain (negExponent (σ := σ))
      (Finsupp.mapDomain negExponent p) d = p d
  have h1 := Finsupp.mapDomain_apply
    (negExponent (σ := σ)).injective
    (Finsupp.mapDomain (negExponent (σ := σ)) p) (-d)
  have h2 := Finsupp.mapDomain_apply
    (negExponent (σ := σ)).injective p d
  simpa [negExponent] using h1.trans h2

theorem invertVariables_bijective {σ R : Type*} [Semiring R] :
    Function.Bijective (invertVariables : Polynomial σ R → Polynomial σ R) := by
  simpa [invertVariables, AddMonoidAlgebra.mapDomainRingHom_apply] using
    (show Function.Bijective
        (Finsupp.mapDomain (M := R) (negExponent (σ := σ))) from
      ⟨Finsupp.mapDomain_injective negExponent.injective,
        Finsupp.mapDomain_surjective negExponent.surjective⟩)

@[simp] theorem constantTerm_invertVariables {σ R : Type*} [Semiring R]
    (p : Polynomial σ R) : constantTerm (invertVariables p) = constantTerm p := by
  change Finsupp.mapDomain (negExponent (σ := σ)) p 0 = p 0
  simpa [negExponent] using
    (Finsupp.mapDomain_apply (negExponent (σ := σ)).injective p
      (0 : Exponent σ))

theorem coeff_invertVariables {σ R : Type*} [Semiring R]
    (d : Exponent σ) (p : Polynomial σ R) :
    coeff d (invertVariables p) = coeff (-d) p := by
  change Finsupp.mapDomain (negExponent (σ := σ)) p d = p (-d)
  simpa [negExponent] using
    (Finsupp.mapDomain_apply (negExponent (σ := σ)).injective p (-d))

end MultiLaurent
