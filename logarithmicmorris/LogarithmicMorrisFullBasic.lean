import laurent

/-!
# Concrete data for the logarithmic Morris identity

This file gives a finite, non-opaque interpretation of the two sides of
Theorem 1.3 after specialization to the odd integer `K = 2k + 1`.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- Parameters in Theorem 1.3, with `n = 2m+1`. -/
structure Setup where
  n : ℕ
  m : ℕ
  k : ℕ
  a : ℕ
  b : ℕ
  odd_rank : n = 2 * m + 1

namespace Setup

/-- The odd Morris exponent `K = 2k+1`. -/
def K (S : Setup) : ℕ := 2 * S.k + 1

@[simp] theorem K_pos (S : Setup) : 0 < S.K := by
  simp [K]

@[simp] theorem K_ne_zero (S : Setup) : S.K ≠ 0 := by
  exact Nat.ne_of_gt S.K_pos

@[simp] theorem n_pos (S : Setup) : 0 < S.n := by
  rw [S.odd_rank]
  omega

@[simp] theorem n_ne_zero (S : Setup) : S.n ≠ 0 := by
  exact Nat.ne_of_gt S.n_pos

/-- The zero-based index of `x_{2r+1}` in the `r`-th logarithmic pair. -/
def leftVertex (S : Setup) (r : Fin S.m) : Fin S.n :=
  ⟨2 * r.1, by rw [S.odd_rank]; omega⟩

/-- The zero-based index of `x_{2r+2}` in the `r`-th logarithmic pair. -/
def rightVertex (S : Setup) (r : Fin S.m) : Fin S.n :=
  ⟨2 * r.1 + 1, by rw [S.odd_rank]; omega⟩

/-- The unique vertex outside the standard near-perfect matching. -/
def lastVertex (S : Setup) : Fin S.n :=
  ⟨2 * S.m, by rw [S.odd_rank]; omega⟩

end Setup

/-! ## Finite Laurent-polynomial kernel -/

abbrev Exponent (n : ℕ) := MultiLaurent.Exponent (Fin n)

abbrev Laurent (R : Type*) [Semiring R] (n : ℕ) :=
  MultiLaurent.Polynomial (Fin n) R

/-- All ordered pairs of distinct vertices. -/
def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2

/-- All pairs `i < j`. -/
def increasingPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- The Laurent monomial `x_i/x_j`. -/
def ratio {R : Type*} [CommSemiring R] {n : ℕ} (i j : Fin n) : Laurent R n :=
  MultiLaurent.var i * MultiLaurent.varInv j

/-- The Vandermonde product `∏_{i<j} (x_i-x_j)`. -/
def vandermonde {R : Type*} [CommRing R] (n : ℕ) : Laurent R n :=
  ∏ p ∈ increasingPairs n,
    (MultiLaurent.var p.1 - MultiLaurent.var p.2)

/-- The symmetric polynomial/Laurent-polynomial factor `f_ab(X)`. -/
def abKernel {R : Type*} [CommRing R] (S : Setup) : Laurent R S.n :=
  ∏ i : Fin S.n,
    (1 - MultiLaurent.var i) ^ S.a *
      (1 - MultiLaurent.varInv i) ^ S.b

/-- The finite Laurent polynomial `F_ab(X)` from equation (5.10):

`Δ(X) ∏ᵢ xᵢ⁻ᵐ (1-xᵢ)^a (1-xᵢ⁻¹)^b
       ∏_{i≠j} (1-xᵢ/xⱼ)^k`.
-/
def morrisKernel (S : Setup) : Laurent ℚ S.n :=
  vandermonde S.n *
    (∏ i : Fin S.n,
      MultiLaurent.varInv i ^ S.m *
        (1 - MultiLaurent.var i) ^ S.a *
        (1 - MultiLaurent.varInv i) ^ S.b) *
    (∏ p ∈ orderedPairs S.n, (1 - ratio p.1 p.2) ^ S.k)

/-! ## The standard logarithmic coefficient functional -/

/-- The exponent constraints imposed by
`∏_{r=0}^{m-1} log(1-x_{2r+2}/x_{2r+1})` when extracting a constant term. -/
def StandardLogAdmissible (S : Setup) (e : Exponent S.n) : Prop :=
  (∀ r : Fin S.m,
      0 < e (S.leftVertex r) ∧
        e (S.rightVertex r) = -e (S.leftVertex r)) ∧
    e S.lastVertex = 0

/-- Coefficient contributed by the standard product of logarithms.

For each pair, `log(1-z) = -∑_{q>0} z^q/q`; hence an admissible exponent
contributes the product of `-1/q`. -/
def standardLogWeight (S : Setup) (e : Exponent S.n) : ℚ := by
  classical
  exact if StandardLogAdmissible S e then
      ∏ r : Fin S.m, (-1 : ℚ) / (e (S.leftVertex r) : ℚ)
    else
      0

/-- Constant term after multiplication by the standard `m` logarithms.  The
Laurent polynomial has finite support, so this sum is finite. -/
def standardLogCT (S : Setup) (F : Laurent ℚ S.n) : ℚ :=
  ∑ e ∈ F.support, F e * standardLogWeight S e

/-- The concrete left-hand side of Theorem 1.3. -/
def logarithmicMorrisLHS (S : Setup) : ℚ :=
  standardLogCT S (morrisKernel S)

/-! ## Explicit right-hand side -/

/-- Double factorial. -/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

@[simp] theorem doubleFactorial_zero : doubleFactorial 0 = 1 := rfl
@[simp] theorem doubleFactorial_one : doubleFactorial 1 = 1 := rfl
@[simp] theorem doubleFactorial_succ_succ (n : ℕ) :
    doubleFactorial (n + 2) = (n + 2) * doubleFactorial n := rfl

def rhsFactor (S : Setup) (i : ℕ) : ℚ :=
  ((doubleFactorial (2 * S.a + 2 * S.b + i * S.K) : ℚ) *
      (doubleFactorial ((i + 1) * S.K) : ℚ)) /
    ((doubleFactorial (2 * S.a + i * S.K) : ℚ) *
      (doubleFactorial (2 * S.b + i * S.K) : ℚ) *
      (doubleFactorial S.K : ℚ))

/-- The displayed double-factorial product in Theorem 1.3. -/
def logarithmicMorrisRHS (S : Setup) : ℚ :=
  ((1 : ℚ) / (doubleFactorial S.n : ℚ)) *
    ∏ i ∈ Finset.range S.n, rhsFactor S i

/-- Concrete statement of the logarithmic Morris constant-term identity. -/
def LogarithmicMorrisStatement (S : Setup) : Prop :=
  logarithmicMorrisLHS S = logarithmicMorrisRHS S

end LogarithmicMorrisFull
