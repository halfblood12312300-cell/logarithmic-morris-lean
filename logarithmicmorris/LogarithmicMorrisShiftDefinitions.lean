import logarithmicmorris.ScratchStandardLogLinearity

/-! Definitions for the Adamović--Milas endpoint-parameter shift. -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- Replace the endpoint parameters while retaining rank and interaction. -/
def Setup.withAB (S : Setup) (a b : ℕ) : Setup where
  n := S.n
  m := S.m
  k := S.k
  a := a
  b := b
  odd_rank := S.odd_rank

@[simp] theorem Setup.withAB_n (S : Setup) (a b : ℕ) : (S.withAB a b).n = S.n := rfl
@[simp] theorem Setup.withAB_m (S : Setup) (a b : ℕ) : (S.withAB a b).m = S.m := rfl
@[simp] theorem Setup.withAB_k (S : Setup) (a b : ℕ) : (S.withAB a b).k = S.k := rfl
@[simp] theorem Setup.withAB_a (S : Setup) (a b : ℕ) : (S.withAB a b).a = a := rfl
@[simp] theorem Setup.withAB_b (S : Setup) (a b : ℕ) : (S.withAB a b).b = b := rfl
@[simp] theorem Setup.withAB_K (S : Setup) (a b : ℕ) : (S.withAB a b).K = S.K := rfl

/-- Elementary symmetric polynomial of degree `r` in `-x₁,…,-xₙ`. -/
def signedElementary (n r : ℕ) : Laurent ℚ n :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card = r),
    ∏ i ∈ T, (-MultiLaurent.var i)

/-- Insert the signed elementary polynomial into the logarithmic kernel. -/
def shiftFamily (S : Setup) (a b r : ℕ) : ℚ :=
  standardLogCT (S.withAB a b)
    (morrisKernel (S.withAB a b) * signedElementary (S.withAB a b).n r)

end LogarithmicMorrisFull
