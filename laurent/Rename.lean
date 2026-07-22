import laurent.ConstantTerm
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # 变量重命名与常数项不变性 -/

namespace MultiLaurent

/-- 指数向量沿变量映射前推。 -/
noncomputable def renameExponent {σ τ : Type*} (f : σ → τ) : Exponent σ →+ Exponent τ :=
  Finsupp.mapDomain.addMonoidHom f

/-- Laurent 多项式的变量重命名。 -/
noncomputable def rename {σ τ R : Type*} [Semiring R] (f : σ → τ) :
    Polynomial σ R →+* Polynomial τ R :=
  AddMonoidAlgebra.mapDomainRingHom R (renameExponent f)

@[simp] theorem rename_monomial {σ τ R : Type*} [Semiring R]
    (f : σ → τ) (d : Exponent σ) (c : R) :
    rename f (monomial d c) = monomial (renameExponent f d) c := by
  simp [rename, monomial, AddMonoidAlgebra.mapDomainRingHom_apply]

theorem rename_mul {σ τ R : Type*} [Semiring R] (f : σ → τ)
    (p q : Polynomial σ R) : rename f (p * q) = rename f p * rename f q := by
  exact map_mul (rename f) p q

theorem rename_constantTerm_of_injective {σ τ R : Type*} [Semiring R]
    (f : σ → τ) (hf : Function.Injective f) (p : Polynomial σ R) :
    constantTerm (rename f p) = constantTerm p := by
  have he : Function.Injective (renameExponent f) :=
    Finsupp.mapDomain_injective hf
  simpa [rename, renameExponent, constantTerm, coeff,
    AddMonoidAlgebra.mapDomainRingHom_apply] using
      (Finsupp.mapDomain_apply he p (0 : Exponent σ))

theorem rename_bijective {σ τ R : Type*} [Semiring R]
    (e : σ ≃ τ) : Function.Bijective (rename (R := R) e) := by
  have he : Function.Bijective (renameExponent e) := by
    exact ⟨Finsupp.mapDomain_injective e.injective,
      Finsupp.mapDomain_surjective e.surjective⟩
  simpa [rename, AddMonoidAlgebra.mapDomainRingHom_apply] using
    (show Function.Bijective
        (Finsupp.mapDomain (M := R) (renameExponent e)) from
      ⟨Finsupp.mapDomain_injective he.1,
        Finsupp.mapDomain_surjective he.2⟩)

end MultiLaurent
