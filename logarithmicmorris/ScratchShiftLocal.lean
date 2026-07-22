import logarithmicmorris.LogarithmicMorrisShiftDefinitions
import logarithmicmorris.ScratchGoodBoundary
import logarithmicmorris.ScratchKernelEval

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

set_option maxHeartbeats 1000000

/-- Laurent Euler derivative in coordinate `i`. -/
def localEuler {n : ℕ} (i : Fin n) (F : Laurent ℚ n) : Laurent ℚ n :=
  F.sum fun e c => MultiLaurent.monomial e ((e i : ℚ) * c)

@[simp] lemma localEuler_zero {n : ℕ} (i : Fin n) :
    localEuler i (0 : Laurent ℚ n) = 0 := by
  simp [localEuler]

lemma localEuler_add {n : ℕ} (i : Fin n) (F G : Laurent ℚ n) :
    localEuler i (F + G) = localEuler i F + localEuler i G := by
  classical
  unfold localEuler
  rw [Finsupp.sum_add_index']
  · simp
  · intro e c d
    simp [MultiLaurent.monomial, mul_add]

lemma localEuler_monomial {n : ℕ} (i : Fin n) (e : Exponent n) (c : ℚ) :
    localEuler i (MultiLaurent.monomial e c) =
      MultiLaurent.monomial e ((e i : ℚ) * c) := by
  classical
  simp [localEuler, MultiLaurent.monomial]

lemma local_smul_monomial {n : ℕ} (c d : ℚ) (e : Exponent n) :
    c • MultiLaurent.monomial e d = MultiLaurent.monomial e (c * d) := by
  ext z
  by_cases hze : z = e
  · subst z
    simp [MultiLaurent.monomial]
  · simp [MultiLaurent.monomial, hze]

lemma localEuler_smul {n : ℕ} (i : Fin n) (c : ℚ) (F : Laurent ℚ n) :
    localEuler i (c • F) = c • localEuler i F := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp
  | hadd F G hF hG => simp [smul_add, localEuler_add, hF, hG]
  | hmono e d =>
      rw [local_smul_monomial]
      rw [localEuler_monomial, localEuler_monomial]
      rw [local_smul_monomial]
      congr 1
      ring

lemma localEuler_mul {n : ℕ} (i : Fin n) (F G : Laurent ℚ n) :
    localEuler i (F * G) = localEuler i F * G + F * localEuler i G := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp
  | hadd F H hF hH =>
      simp [add_mul, localEuler_add, hF, hH]
      ring
  | hmono e c =>
      induction G using MultiLaurent.induction_on with
      | h0 => simp
      | hadd G H hG hH =>
          simp [mul_add, localEuler_add, hG, hH]
          ring
      | hmono d q =>
          rw [show MultiLaurent.monomial e c * MultiLaurent.monomial d q =
            MultiLaurent.monomial (e + d) (c * q) by
              simp [MultiLaurent.monomial,
                AddMonoidAlgebra.single_mul_single]]
          rw [localEuler_monomial, localEuler_monomial, localEuler_monomial]
          rw [show MultiLaurent.monomial e ((e i : ℚ) * c) *
              MultiLaurent.monomial d q =
            MultiLaurent.monomial (e + d) (((e i : ℚ) * c) * q) by
              simp only [MultiLaurent.monomial,
                AddMonoidAlgebra.single_mul_single],
            show MultiLaurent.monomial e c *
                MultiLaurent.monomial d ((d i : ℚ) * q) =
              MultiLaurent.monomial (e + d) (c * ((d i : ℚ) * q)) by
                simp only [MultiLaurent.monomial,
                  AddMonoidAlgebra.single_mul_single]]
          rw [Finsupp.add_apply, Int.cast_add]
          unfold MultiLaurent.monomial
          rw [← AddMonoidAlgebra.single_add]
          congr 1
          ring

@[simp] lemma localEuler_one {n : ℕ} (i : Fin n) :
    localEuler i (1 : Laurent ℚ n) = 0 := by
  change localEuler i (MultiLaurent.monomial 0 1) = 0
  rw [localEuler_monomial]
  simp [MultiLaurent.monomial]

lemma localEuler_neg {n : ℕ} (i : Fin n) (F : Laurent ℚ n) :
    localEuler i (-F) = -localEuler i F := by
  simpa only [neg_smul, one_smul] using localEuler_smul i (-1 : ℚ) F

lemma localEuler_sub {n : ℕ} (i : Fin n) (F G : Laurent ℚ n) :
    localEuler i (F - G) = localEuler i F - localEuler i G := by
  rw [sub_eq_add_neg, sub_eq_add_neg, localEuler_add, localEuler_neg]

lemma localEuler_pow_succ {n : ℕ} (i : Fin n) (F : Laurent ℚ n) (q : ℕ) :
    localEuler i (F ^ (q + 1)) =
      ((q + 1 : ℕ) : ℚ) • (F ^ q * localEuler i F) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show q + 1 + 1 = (q + 1) + 1 by omega, pow_succ,
        localEuler_mul, ih]
      push_cast
      simp only [smul_add, Algebra.smul_def]
      norm_num [map_add]
      rw [← AddMonoidAlgebra.one_def]
      ring

lemma localEuler_var_same {n : ℕ} (i : Fin n) :
    localEuler i (MultiLaurent.var i : Laurent ℚ n) = MultiLaurent.var i := by
  rw [show (MultiLaurent.var i : Laurent ℚ n) =
    MultiLaurent.monomial (Finsupp.single i 1) 1 by
      rfl, localEuler_monomial]
  simp [Finsupp.single_apply]

lemma localEuler_var_of_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    localEuler i (MultiLaurent.var j : Laurent ℚ n) = 0 := by
  rw [show (MultiLaurent.var j : Laurent ℚ n) =
    MultiLaurent.monomial (Finsupp.single j 1) 1 by
      rfl, localEuler_monomial]
  simp [Finsupp.single_apply, hji]

lemma localEuler_varInv_same {n : ℕ} (i : Fin n) :
    localEuler i (MultiLaurent.varInv i : Laurent ℚ n) =
      -MultiLaurent.varInv i := by
  rw [show (MultiLaurent.varInv i : Laurent ℚ n) =
    MultiLaurent.monomial (Finsupp.single i (-1)) 1 by
      rfl, localEuler_monomial]
  have hneg :
      MultiLaurent.monomial (Finsupp.single i (-1)) (-1 : ℚ) =
        -MultiLaurent.monomial (Finsupp.single i (-1)) (1 : ℚ) := by
    ext z
    by_cases hz : z = Finsupp.single i (-1)
    · subst z
      simp [MultiLaurent.monomial]
    · simp [MultiLaurent.monomial, hz]
  simpa using hneg

lemma localEuler_varInv_of_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    localEuler i (MultiLaurent.varInv j : Laurent ℚ n) = 0 := by
  rw [show (MultiLaurent.varInv j : Laurent ℚ n) =
    MultiLaurent.monomial (Finsupp.single j (-1)) 1 by
      rfl, localEuler_monomial]
  simp [Finsupp.single_apply, hji]

lemma localEuler_varInv_pow_same {n : ℕ} (i : Fin n) (d : ℕ) :
    localEuler i ((MultiLaurent.varInv i : Laurent ℚ n) ^ d) =
      -((d : ℕ) : ℚ) • (MultiLaurent.varInv i : Laurent ℚ n) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, localEuler_mul, ih, localEuler_varInv_same]
      push_cast
      simp only [Algebra.smul_def, neg_mul, mul_neg]
      norm_num [map_add, map_neg]
      rw [← AddMonoidAlgebra.one_def]
      ring

lemma localEuler_varInv_pow_of_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (d : ℕ) :
    localEuler i ((MultiLaurent.varInv j : Laurent ℚ n) ^ d) = 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, localEuler_mul, ih, localEuler_varInv_of_ne i j hji]
      simp

lemma localEuler_one_sub_var_pow_succ {n : ℕ} (i : Fin n) (t : ℕ) :
    localEuler i (((1 : Laurent ℚ n) - MultiLaurent.var i) ^ (t + 1)) =
      -(((t + 1 : ℕ) : ℚ)) •
        (MultiLaurent.var i *
          ((1 : Laurent ℚ n) - MultiLaurent.var i) ^ t) := by
  rw [localEuler_pow_succ, localEuler_sub, localEuler_one,
    localEuler_var_same]
  simp only [zero_sub, Algebra.smul_def]
  rw [map_neg]
  ring

lemma localEuler_one_sub_var_pow_of_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (t : ℕ) :
    localEuler i (((1 : Laurent ℚ n) - MultiLaurent.var j) ^ t) = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, localEuler_mul, ih, localEuler_sub, localEuler_one,
        localEuler_var_of_ne i j hji]
      simp

lemma localEuler_finset_sum {n : ℕ} {I : Type*} (i : Fin n)
    (s : Finset I) (F : I → Laurent ℚ n) :
    localEuler i (∑ j ∈ s, F j) = ∑ j ∈ s, localEuler i (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih => simp [hjs, localEuler_add, ih]

lemma localEuler_finset_prod {n : ℕ} {I : Type*} [DecidableEq I] (i : Fin n)
    (s : Finset I) (F : I → Laurent ℚ n) :
    localEuler i (∏ j ∈ s, F j) =
      ∑ j ∈ s, localEuler i (F j) * ∏ l ∈ s.erase j, F l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, localEuler_mul, ih]
      rw [Finset.sum_insert hjs]
      have herasej : (insert j s).erase j = s := by simp [hjs]
      rw [herasej]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      have hjl : j ≠ l := by exact fun h => hjs (h ▸ hl)
      rw [Finset.erase_insert_of_ne hjl]
      rw [Finset.prod_insert]
      · ring
      · exact fun hjmem => hjs (Finset.mem_of_mem_erase hjmem)

def localSignedDelete (n r : ℕ) (i : Fin n) : Laurent ℚ n :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => T.card = r ∧ i ∉ T),
    ∏ j ∈ T, (-MultiLaurent.var j)

lemma localEuler_localSignedDelete (n r : ℕ) (i : Fin n) :
    localEuler i (localSignedDelete n r i) = 0 := by
  classical
  unfold localSignedDelete
  rw [localEuler_finset_sum]
  apply Finset.sum_eq_zero
  intro T hT
  rw [localEuler_finset_prod]
  apply Finset.sum_eq_zero
  intro j hj
  have hiT : i ∉ T := (Finset.mem_filter.mp hT).2.2
  have hji : j ≠ i := fun h => hiT (h ▸ hj)
  rw [localEuler_neg, localEuler_var_of_ne i j hji]
  simp

lemma sum_localSignedDelete (n r : ℕ) :
    (∑ i : Fin n, localSignedDelete n r i) =
      ((n - r : ℕ) : ℚ) • signedElementary n r := by
  classical
  unfold localSignedDelete signedElementary
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hcard : T.card = r
  · simp only [hcard, true_and]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcardle : T.card ≤ n := by
      simpa using Finset.card_le_univ T
    rw [Finset.filter_notMem_eq_sdiff,
      Finset.card_sdiff_of_subset (Finset.subset_univ T)]
    simp only [Finset.card_univ, Fintype.card_fin, hcard, if_pos]
    rw [Algebra.smul_def]
    rfl
  · simp [hcard]

lemma sum_var_mul_localSignedDelete (n r : ℕ) :
    (∑ i : Fin n, (-MultiLaurent.var i) * localSignedDelete n r i) =
      (((r + 1 : ℕ) : ℚ) • signedElementary n (r + 1)) := by
  classical
  let leftSet := (Finset.univ : Finset (Fin n)).sigma fun i =>
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => T.card = r ∧ i ∉ T)
  let rightSet :=
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun U => U.card = r + 1)).sigma fun U => U
  have hleft :
      (∑ i : Fin n, (-MultiLaurent.var i) * localSignedDelete n r i) =
        ∑ x ∈ leftSet,
          (-MultiLaurent.var x.1) *
            ∏ j ∈ x.2, (-MultiLaurent.var j) := by
    unfold localSignedDelete leftSet
    simp_rw [Finset.mul_sum]
    exact Finset.sum_sigma' _ _ _
  have hright :
      (((r + 1 : ℕ) : ℚ) • signedElementary n (r + 1)) =
        ∑ y ∈ rightSet, ∏ j ∈ y.1, (-MultiLaurent.var j) := by
    unfold signedElementary rightSet
    rw [Finset.sum_sigma]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    have hcard : U.card = r + 1 := (Finset.mem_filter.mp hU).2
    simp only [Sigma.fst]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hcard, Algebra.smul_def]
    push_cast
    rfl
  rw [hleft, hright]
  refine Finset.sum_bij
    (fun x _ => ⟨insert x.1 x.2, x.1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [leftSet, rightSet, Finset.mem_sigma,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨by rw [Finset.card_insert_of_notMem hx.2, hx.1],
      Finset.mem_insert_self _ _⟩
  · intro x hx y hy hxy
    simp only [leftSet, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx hy
    cases x with
    | mk i T =>
      cases y with
      | mk j U =>
        simp only [Sigma.mk.injEq] at hxy ⊢
        rcases hxy with ⟨hij, hset⟩
        have hij' : i = j := eq_of_heq hset
        subst j
        refine ⟨rfl, ?_⟩
        have hTi : i ∉ T := hx.2
        have hUi : i ∉ U := hy.2
        exact heq_of_eq (by
          rw [← Finset.erase_insert hTi, hij, Finset.erase_insert hUi])
  · intro y hy
    cases y with
    | mk U i =>
      simp only [rightSet, Finset.mem_sigma, Finset.mem_filter,
        Finset.mem_univ, true_and] at hy
      refine ⟨⟨i, U.erase i⟩, ?_, ?_⟩
      · simp only [leftSet, Finset.mem_sigma, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rw [Finset.card_erase_of_mem hy.2, hy.1]
          omega
        · exact Finset.notMem_erase i U
      · simp only [Sigma.mk.injEq]
        exact ⟨Finset.insert_erase hy.2, HEq.rfl⟩
  · intro x hx
    simp only [leftSet, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rw [Finset.prod_insert hx.2]

lemma one_sub_varInv {n : ℕ} (i : Fin n) :
    (1 - (MultiLaurent.varInv i : Laurent ℚ n)) =
      -MultiLaurent.varInv i * (1 - MultiLaurent.var i) := by
  have hunit : (MultiLaurent.varInv i : Laurent ℚ n) * MultiLaurent.var i = 1 := by
    rw [mul_comm, MultiLaurent.var_mul_varInv]
  calc
    (1 - (MultiLaurent.varInv i : Laurent ℚ n)) =
        MultiLaurent.varInv i * MultiLaurent.var i - MultiLaurent.varInv i := by
      rw [hunit]
    _ = -MultiLaurent.varInv i * (1 - MultiLaurent.var i) := by ring

lemma endpoint_factor_normalize {n a b m : ℕ} (i : Fin n) :
    (MultiLaurent.varInv i ^ m *
        (1 - MultiLaurent.var i) ^ a *
        (1 - MultiLaurent.varInv i) ^ b : Laurent ℚ n) =
      (-1 : Laurent ℚ n) ^ b * MultiLaurent.varInv i ^ (m + b) *
        (1 - MultiLaurent.var i) ^ (a + b) := by
  rw [one_sub_varInv, mul_pow, neg_pow, pow_add, pow_add]
  ring

lemma orderedPair_factor {n : ℕ} (i j : Fin n) :
    ((1 - ratio i j) * (1 - ratio j i) : Laurent ℚ n) =
      -(MultiLaurent.varInv i * MultiLaurent.varInv j) *
        (MultiLaurent.var i - MultiLaurent.var j) ^ 2 := by
  have hi : (MultiLaurent.var i : Laurent ℚ n) * MultiLaurent.varInv i = 1 :=
    MultiLaurent.var_mul_varInv i
  have hj : (MultiLaurent.var j : Laurent ℚ n) * MultiLaurent.varInv j = 1 :=
    MultiLaurent.var_mul_varInv j
  unfold ratio
  let xi : Laurent ℚ n := MultiLaurent.var i
  let xj : Laurent ℚ n := MultiLaurent.var j
  let ui : Laurent ℚ n := MultiLaurent.varInv i
  let uj : Laurent ℚ n := MultiLaurent.varInv j
  have hi' : xi * ui = 1 := hi
  have hj' : xj * uj = 1 := hj
  have hcross : xi * xj * ui * uj = 1 := by
    calc
      xi * xj * ui * uj = (xi * ui) * (xj * uj) := by ring
      _ = 1 := by rw [hi', hj']; ring
  have hxi : ui * uj * xi ^ 2 = xi * uj := by
    calc
      ui * uj * xi ^ 2 = (xi * ui) * (xi * uj) := by ring
      _ = xi * uj := by rw [hi']; ring
  have hxj : ui * uj * xj ^ 2 = xj * ui := by
    calc
      ui * uj * xj ^ 2 = (xj * uj) * (xj * ui) := by ring
      _ = xj * ui := by rw [hj']; ring
  have hmiddle : ui * uj * xi * xj = 1 := by
    calc
      ui * uj * xi * xj = xi * xj * ui * uj := by ring
      _ = 1 := hcross
  calc
    ((1 : Laurent ℚ n) - xi * uj) * ((1 : Laurent ℚ n) - xj * ui) =
        1 - xi * uj - xj * ui + xi * xj * ui * uj := by ring
    _ = 2 - xi * uj - xj * ui := by rw [hcross]; ring
    _ = -(ui * uj) * (xi - xj) ^ 2 := by
      symm
      calc
        -(ui * uj) * (xi - xj) ^ 2 =
            -(ui * uj * xi ^ 2) + 2 * (ui * uj * xi * xj) -
              (ui * uj * xj ^ 2) := by ring
        _ = 2 - xi * uj - xj * ui := by rw [hxi, hxj, hmiddle]; ring

lemma orderedPair_factor_pow {n k : ℕ} (i j : Fin n) :
    ((1 - ratio i j) ^ k * (1 - ratio j i) ^ k : Laurent ℚ n) =
      (-1 : Laurent ℚ n) ^ k *
        (MultiLaurent.varInv i * MultiLaurent.varInv j) ^ k *
        (MultiLaurent.var i - MultiLaurent.var j) ^ (2 * k) := by
  rw [← mul_pow, orderedPair_factor, mul_pow, neg_pow, pow_mul]

lemma prod_increasing_incidence {R : Type*} [CommMonoid R]
    (n : ℕ) (f : Fin n → R) :
    (∏ p ∈ increasingPairs n, f p.1 * f p.2) =
      ∏ i : Fin n, (f i) ^ (n - 1) := by
  classical
  rw [← prod_orderedPairs_generic n (fun p : Fin n × Fin n => f p.1)]
  unfold orderedPairs
  simp only [Finset.prod_filter]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show (∏ j : Fin n, if (i, j).1 ≠ (i, j).2 then f (i, j).1 else 1) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f i by
    calc
      (∏ j : Fin n, if (i, j).1 ≠ (i, j).2 then f (i, j).1 else 1) =
          ∏ j : Fin n, if j ∈ (Finset.univ : Finset (Fin n)).erase i then
            f i else 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji, Ne.symm hji]
      _ = ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f i :=
        Fintype.prod_ite_mem _ _]
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

def normalizedMorrisKernel (S : Setup) : Laurent ℚ S.n :=
  (-1 : Laurent ℚ S.n) ^
      (S.n * S.b + (increasingPairs S.n).card * S.k) *
    vandermonde S.n ^ S.K *
    ∏ i : Fin S.n,
      MultiLaurent.varInv i ^ (S.b + S.m * S.K) *
        (1 - MultiLaurent.var i) ^ (S.a + S.b)

lemma morrisKernel_eq_normalized (S : Setup) :
    morrisKernel S = normalizedMorrisKernel S := by
  unfold morrisKernel normalizedMorrisKernel
  rw [prod_orderedPairs_generic]
  simp_rw [endpoint_factor_normalize, orderedPair_factor_pow]
  simp only [Finset.prod_mul_distrib]
  rw [show (∏ _i : Fin S.n, (-1 : Laurent ℚ S.n) ^ S.b) =
      (-1 : Laurent ℚ S.n) ^ (S.n * S.b) by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← pow_mul]
        congr 1
        simp [Nat.mul_comm]]
  rw [show (∏ _p ∈ increasingPairs S.n,
        (-1 : Laurent ℚ S.n) ^ S.k) =
      (-1 : Laurent ℚ S.n) ^ ((increasingPairs S.n).card * S.k) by
        rw [Finset.prod_const]
        rw [← pow_mul]
        congr 1
        simp [Nat.mul_comm]]
  simp_rw [mul_pow]
  rw [prod_increasing_incidence S.n
    (fun i : Fin S.n => (MultiLaurent.varInv i : Laurent ℚ S.n) ^ S.k)]
  rw [show (∏ p ∈ increasingPairs S.n,
        (MultiLaurent.var p.1 - MultiLaurent.var p.2) ^ (2 * S.k)) =
      vandermonde S.n ^ (2 * S.k) by
        unfold vandermonde
        rw [Finset.prod_pow]]
  change
    vandermonde S.n *
        ((-1 : Laurent ℚ S.n) ^ (S.n * S.b) *
          (∏ i : Fin S.n, MultiLaurent.varInv i ^ (S.m + S.b)) *
          ∏ i : Fin S.n, (1 - MultiLaurent.var i) ^ (S.a + S.b)) *
        ((-1 : Laurent ℚ S.n) ^ ((increasingPairs S.n).card * S.k) *
          (∏ i : Fin S.n, (MultiLaurent.varInv i ^ S.k) ^ (S.n - 1)) *
          vandermonde S.n ^ (2 * S.k)) = _
  have hnsub : S.n - 1 = 2 * S.m := by rw [S.odd_rank]; omega
  let sb : Laurent ℚ S.n := (-1) ^ (S.n * S.b)
  let sk : Laurent ℚ S.n := (-1) ^ ((increasingPairs S.n).card * S.k)
  let st : Laurent ℚ S.n :=
    (-1) ^ (S.n * S.b + (increasingPairs S.n).card * S.k)
  let V : Laurent ℚ S.n := vandermonde S.n
  let P₁ : Laurent ℚ S.n :=
    ∏ i : Fin S.n, MultiLaurent.varInv i ^ (S.m + S.b)
  let P₂ : Laurent ℚ S.n :=
    ∏ i : Fin S.n, (MultiLaurent.varInv i ^ S.k) ^ (S.n - 1)
  let P : Laurent ℚ S.n :=
    ∏ i : Fin S.n, MultiLaurent.varInv i ^ (S.b + S.m * S.K)
  let E : Laurent ℚ S.n :=
    ∏ i : Fin S.n, (1 - MultiLaurent.var i) ^ (S.a + S.b)
  have hsign : sb * sk = st := by
    dsimp [sb, sk, st]
    rw [← pow_add]
  have hV : V * V ^ (2 * S.k) = V ^ S.K := by
    calc
      V * V ^ (2 * S.k) = V ^ (2 * S.k) * V := by ring
      _ = V ^ (2 * S.k + 1) := (pow_succ V (2 * S.k)).symm
      _ = V ^ S.K := by simp [Setup.K]
  have hP : P₁ * P₂ = P := by
    dsimp [P₁, P₂, P]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hnsub, ← pow_mul, ← pow_add]
    congr 1
    simp [Setup.K]
    ring
  change V * (sb * P₁ * E) * (sk * P₂ * V ^ (2 * S.k)) =
    st * V ^ S.K * (P * E)
  calc
    V * (sb * P₁ * E) * (sk * P₂ * V ^ (2 * S.k)) =
        (sb * sk) * (V * V ^ (2 * S.k)) * (P₁ * P₂) * E := by ring
    _ = st * V ^ S.K * P * E := by rw [hsign, hV, hP]
    _ = st * V ^ S.K * (P * E) := by ring

def localEndpointFactor (n d t : ℕ) (i : Fin n) : Laurent ℚ n :=
  MultiLaurent.varInv i ^ d *
    ((1 : Laurent ℚ n) - MultiLaurent.var i) ^ t

def localEndpointProduct (n d t : ℕ) : Laurent ℚ n :=
  ∏ i : Fin n, localEndpointFactor n d t i

lemma localEuler_localEndpointFactor_same (n d t : ℕ) (i : Fin n) :
    localEuler i (localEndpointFactor n d t i) =
      -((d : ℕ) : ℚ) • localEndpointFactor n d t i +
        MultiLaurent.varInv i ^ d *
          localEuler i (((1 : Laurent ℚ n) - MultiLaurent.var i) ^ t) := by
  unfold localEndpointFactor
  rw [localEuler_mul, localEuler_varInv_pow_same]
  simp only [Algebra.smul_def]
  ring

lemma localEuler_localEndpointFactor_of_ne (n d t : ℕ) (i j : Fin n)
    (hji : j ≠ i) :
    localEuler i (localEndpointFactor n d t j) = 0 := by
  unfold localEndpointFactor
  rw [localEuler_mul, localEuler_varInv_pow_of_ne i j hji,
    localEuler_one_sub_var_pow_of_ne i j hji]
  simp

lemma localEuler_localEndpointProduct (n d t : ℕ) (i : Fin n) :
    localEuler i (localEndpointProduct n d t) =
      localEuler i (localEndpointFactor n d t i) *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          localEndpointFactor n d t j := by
  classical
  unfold localEndpointProduct
  rw [localEuler_finset_prod]
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    rw [localEuler_localEndpointFactor_of_ne n d t i j hji]
    simp
  · simp

lemma localEndpointProduct_eq_factor_mul_erase (n d t : ℕ) (i : Fin n) :
    localEndpointProduct n d t =
      localEndpointFactor n d t i *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          localEndpointFactor n d t j := by
  classical
  unfold localEndpointProduct
  simpa [Finset.erase_eq] using
    (Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)
      (localEndpointFactor n d t))

lemma one_sub_var_mul_localEuler_endpointProduct (n d t : ℕ) (i : Fin n) :
    ((1 : Laurent ℚ n) - MultiLaurent.var i) *
        localEuler i (localEndpointProduct n d t) =
      -((d : ℕ) : ℚ) •
          (((1 : Laurent ℚ n) - MultiLaurent.var i) *
            localEndpointProduct n d t) -
        ((t : ℕ) : ℚ) •
          (MultiLaurent.var i * localEndpointProduct n d t) := by
  classical
  cases t with
  | zero =>
      rw [localEuler_localEndpointProduct,
        localEuler_localEndpointFactor_same]
      rw [localEndpointProduct_eq_factor_mul_erase n d 0 i]
      simp [localEndpointFactor]
  | succ t =>
      rw [localEuler_localEndpointProduct,
        localEuler_localEndpointFactor_same,
        localEuler_one_sub_var_pow_succ]
      rw [localEndpointProduct_eq_factor_mul_erase]
      unfold localEndpointFactor
      push_cast
      simp only [Algebra.smul_def]
      norm_num [map_add, map_neg]
      rw [← AddMonoidAlgebra.one_def]
      ring

def localShiftFactor (n r : ℕ) (i : Fin n) : Laurent ℚ n :=
  ((1 : Laurent ℚ n) - MultiLaurent.var i) * localSignedDelete n r i

lemma localEuler_localShiftFactor (n r : ℕ) (i : Fin n) :
    localEuler i (localShiftFactor n r i) =
      (-MultiLaurent.var i) * localSignedDelete n r i := by
  unfold localShiftFactor
  rw [localEuler_mul, localEuler_sub, localEuler_one,
    localEuler_var_same, localEuler_localSignedDelete]
  ring

lemma sum_localShiftFactor (n r : ℕ) :
    (∑ i : Fin n, localShiftFactor n r i) =
      ((n - r : ℕ) : ℚ) • signedElementary n r +
        (((r + 1 : ℕ) : ℚ) • signedElementary n (r + 1)) := by
  calc
    (∑ i : Fin n, localShiftFactor n r i) =
        (∑ i : Fin n, localSignedDelete n r i) +
          ∑ i : Fin n,
            (-MultiLaurent.var i) * localSignedDelete n r i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold localShiftFactor
      ring
    _ = _ := by
      rw [sum_localSignedDelete, sum_var_mul_localSignedDelete]

lemma localShiftFactor_mul_localEuler_endpointProduct
    (n d t r : ℕ) (i : Fin n) :
    localShiftFactor n r i * localEuler i (localEndpointProduct n d t) =
      -((d : ℕ) : ℚ) •
          (localShiftFactor n r i * localEndpointProduct n d t) +
        ((t : ℕ) : ℚ) •
          (((-MultiLaurent.var i) * localSignedDelete n r i) *
            localEndpointProduct n d t) := by
  calc
    localShiftFactor n r i * localEuler i (localEndpointProduct n d t) =
        localSignedDelete n r i *
          (((1 : Laurent ℚ n) - MultiLaurent.var i) *
            localEuler i (localEndpointProduct n d t)) := by
      unfold localShiftFactor
      ring
    _ = localSignedDelete n r i *
        (-((d : ℕ) : ℚ) •
            (((1 : Laurent ℚ n) - MultiLaurent.var i) *
              localEndpointProduct n d t) -
          ((t : ℕ) : ℚ) •
            (MultiLaurent.var i * localEndpointProduct n d t)) := by
      rw [one_sub_var_mul_localEuler_endpointProduct]
    _ = _ := by
      unfold localShiftFactor
      simp only [Algebra.smul_def]
      norm_num [map_neg]
      ring

lemma sum_localShift_derivative_endpoint
    (n d t r : ℕ) :
    (Finset.univ.sum fun i : Fin n =>
        localEuler (n := n) i (localShiftFactor n r i) *
            localEndpointProduct n d t +
          localShiftFactor n r i *
            localEuler i (localEndpointProduct n d t)) =
      -(((d : ℕ) : ℚ) * ((n - r : ℕ) : ℚ)) •
          (signedElementary n r * localEndpointProduct n d t) +
        ((((r + 1 : ℕ) : ℚ) *
            (((t + 1 : ℕ) : ℚ) - ((d : ℕ) : ℚ))) •
          (signedElementary n (r + 1) * localEndpointProduct n d t)) := by
  classical
  simp_rw [localEuler_localShiftFactor,
    localShiftFactor_mul_localEuler_endpointProduct]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [sum_var_mul_localSignedDelete]
  rw [← Finset.smul_sum]
  rw [← Finset.sum_mul]
  rw [sum_localShiftFactor]
  rw [← Finset.smul_sum]
  rw [← Finset.sum_mul]
  rw [sum_var_mul_localSignedDelete]
  simp only [Algebra.smul_def]
  push_cast
  norm_num [map_add, map_sub, map_neg, map_mul]
  ring

def localSignedDeleteTwo (n r : ℕ) (i j : Fin n) : Laurent ℚ n :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => T.card = r ∧ i ∉ T ∧ j ∉ T),
    ∏ l ∈ T, (-MultiLaurent.var l)

lemma sum_localSignedDeleteTwo_fixed (n r : ℕ) (i : Fin n) :
    (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        localSignedDeleteTwo n r i j) =
      ((n - r - 1 : ℕ) : ℚ) • localSignedDelete n r i := by
  classical
  unfold localSignedDeleteTwo localSignedDelete
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hgood : T.card = r ∧ i ∉ T
  · simp only [hgood.1, hgood.2, true_and, if_pos]
    simp only [not_false_eq_true, true_and, if_true]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hsub : T ⊆ (Finset.univ : Finset (Fin n)).erase i := by
      intro j hj
      exact Finset.mem_erase.mpr
        ⟨fun hji => hgood.2 (hji ▸ hj), Finset.mem_univ j⟩
    rw [Finset.filter_notMem_eq_sdiff,
      Finset.card_sdiff_of_subset hsub]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, hgood.1]
    rw [Algebra.smul_def]
    push_cast
    have hrle : r ≤ n - 1 := by
      rw [← hgood.1]
      simpa [Finset.card_erase_of_mem (Finset.mem_univ i)] using
        (Finset.card_le_card hsub)
    have hnat : n - 1 - r = n - r - 1 := by omega
    rw [hnat]
  · by_cases hcard : T.card = r
    · have hiT : i ∈ T := by
        by_contra hiT
        exact hgood ⟨hcard, hiT⟩
      simp [hcard, hiT]
    · simp [hcard]

lemma sum_var_localSignedDeleteTwo_fixed (n r : ℕ) (i : Fin n) :
    (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (-MultiLaurent.var j) * localSignedDeleteTwo n r i j) =
      (((r + 1 : ℕ) : ℚ) • localSignedDelete n (r + 1) i) := by
  classical
  let leftSet := ((Finset.univ : Finset (Fin n)).erase i).sigma fun j =>
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => T.card = r ∧ i ∉ T ∧ j ∉ T)
  let rightSet :=
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun U => U.card = r + 1 ∧ i ∉ U)).sigma fun U => U
  have hleft :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          (-MultiLaurent.var j) * localSignedDeleteTwo n r i j) =
        ∑ x ∈ leftSet,
          (-MultiLaurent.var x.1) *
            ∏ l ∈ x.2, (-MultiLaurent.var l) := by
    unfold localSignedDeleteTwo leftSet
    simp_rw [Finset.mul_sum]
    exact Finset.sum_sigma' _ _ _
  have hright :
      (((r + 1 : ℕ) : ℚ) • localSignedDelete n (r + 1) i) =
        ∑ y ∈ rightSet, ∏ l ∈ y.1, (-MultiLaurent.var l) := by
    unfold localSignedDelete rightSet
    rw [Finset.sum_sigma]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    have hcard : U.card = r + 1 := (Finset.mem_filter.mp hU).2.1
    simp only [Sigma.fst]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hcard, Algebra.smul_def]
    push_cast
    rfl
  rw [hleft, hright]
  refine Finset.sum_bij
    (fun x _ => ⟨insert x.1 x.2, x.1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [leftSet, rightSet, Finset.mem_sigma,
      Finset.mem_filter] at hx ⊢
    have hji : x.1 ≠ i := (Finset.mem_erase.mp hx.1).1
    exact ⟨⟨Finset.mem_univ _,
      by rw [Finset.card_insert_of_notMem hx.2.2.2.2, hx.2.2.1],
      by
        intro hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · exact hji hi.symm
        · exact hx.2.2.2.1 hi⟩,
      Finset.mem_insert_self _ _⟩
  · intro x hx y hy hxy
    simp only [leftSet, Finset.mem_sigma, Finset.mem_filter] at hx hy
    cases x with
    | mk j T =>
      cases y with
      | mk l U =>
        simp only [Sigma.mk.injEq] at hxy ⊢
        rcases hxy with ⟨hset, hjl⟩
        have hjl' : j = l := eq_of_heq hjl
        subst l
        refine ⟨rfl, ?_⟩
        have hjT : j ∉ T := hx.2.2.2.2
        have hjU : j ∉ U := hy.2.2.2.2
        exact heq_of_eq (by
          rw [← Finset.erase_insert hjT, hset,
            Finset.erase_insert hjU])
  · intro y hy
    cases y with
    | mk U j =>
      simp only [rightSet, Finset.mem_sigma, Finset.mem_filter] at hy
      have hji : j ≠ i := fun hji => hy.1.2.2 (hji ▸ hy.2)
      refine ⟨⟨j, U.erase j⟩, ?_, ?_⟩
      · simp only [leftSet, Finset.mem_sigma, Finset.mem_filter]
        constructor
        · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
        · exact ⟨Finset.mem_univ _,
            by rw [Finset.card_erase_of_mem hy.2, hy.1.2.1]; omega,
            ⟨fun hi => hy.1.2.2 (Finset.mem_of_mem_erase hi),
              Finset.notMem_erase j U⟩⟩
      · simp only [Sigma.mk.injEq]
        exact ⟨Finset.insert_erase hy.2, HEq.rfl⟩
  · intro x hx
    simp only [leftSet, Finset.mem_sigma, Finset.mem_filter] at hx
    rw [Finset.prod_insert hx.2.2.2.2]

lemma sum_orderedPairs_as_erase {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : Fin n × Fin n → R) :
    (∑ p ∈ orderedPairs n, f p) =
      ∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        f (i, j) := by
  classical
  unfold orderedPairs
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro hij
      exact ⟨fun hji => hij hji.symm, trivial⟩
    · rintro ⟨hji, -⟩
      exact fun hij => hji hij.symm
  · intro j hj
    rfl

lemma sum_ordered_localSignedDeleteTwo (n r : ℕ) :
    (∑ p ∈ orderedPairs n,
        localSignedDeleteTwo n r p.1 p.2) =
      (((n - r - 1 : ℕ) : ℚ) * ((n - r : ℕ) : ℚ)) •
        signedElementary n r := by
  rw [sum_orderedPairs_as_erase]
  simp_rw [sum_localSignedDeleteTwo_fixed]
  rw [← Finset.smul_sum, sum_localSignedDelete]
  simp only [Algebra.smul_def]
  norm_num [map_mul]
  ring

lemma sum_ordered_negVars_localSignedDeleteTwo (n r : ℕ) :
    (∑ p ∈ orderedPairs n,
        ((-MultiLaurent.var p.1) + (-MultiLaurent.var p.2)) *
          localSignedDeleteTwo n r p.1 p.2) =
      (2 * ((n - r - 1 : ℕ) : ℚ) * ((r + 1 : ℕ) : ℚ)) •
        signedElementary n (r + 1) := by
  rw [sum_orderedPairs_as_erase]
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_localSignedDeleteTwo_fixed]
  simp_rw [mul_smul_comm]
  rw [← Finset.smul_sum]
  rw [sum_var_mul_localSignedDelete]
  simp_rw [sum_var_localSignedDeleteTwo_fixed]
  rw [← Finset.smul_sum, sum_localSignedDelete]
  rw [show n - (r + 1) = n - r - 1 by omega]
  simp only [Algebra.smul_def]
  push_cast
  norm_num [map_add, map_mul, map_ofNat]
  ring_nf

lemma sum_ordered_mulVars_localSignedDeleteTwo (n r : ℕ) :
    (∑ p ∈ orderedPairs n,
        ((-MultiLaurent.var p.1) * (-MultiLaurent.var p.2)) *
          localSignedDeleteTwo n r p.1 p.2) =
      ((((r + 1 : ℕ) : ℚ) * ((r + 2 : ℕ) : ℚ)) •
        signedElementary n (r + 2)) := by
  rw [sum_orderedPairs_as_erase]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [sum_var_localSignedDeleteTwo_fixed]
  simp_rw [mul_smul_comm]
  rw [← Finset.smul_sum]
  rw [sum_var_mul_localSignedDelete]
  simp only [Algebra.smul_def]
  push_cast
  norm_num [map_add, map_mul, map_ofNat]
  ring_nf

@[simp] lemma localSignedDelete_zero (n : ℕ) (i : Fin n) :
    localSignedDelete n 0 i = 1 := by
  classical
  unfold localSignedDelete
  rw [Finset.sum_eq_single ∅]
  · simp [AddMonoidAlgebra.one_def]
  · intro T hT hT0
    have hcard : T.card = 0 := (Finset.mem_filter.mp hT).2.1
    exact (hT0 (Finset.card_eq_zero.mp hcard)).elim
  · simp

lemma localSignedDelete_succ_decompose (n r : ℕ) (i j : Fin n)
    (hij : i ≠ j) :
    localSignedDelete n (r + 1) i =
      localSignedDeleteTwo n (r + 1) i j +
        (-MultiLaurent.var j) * localSignedDeleteTwo n r i j := by
  classical
  let base := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun T => T.card = r + 1 ∧ i ∉ T)
  let f : Finset (Fin n) → Laurent ℚ n := fun T =>
    ∏ l ∈ T, (-MultiLaurent.var l)
  have hbranch :
      (∑ T ∈ base.filter (fun T => j ∈ T), f T) =
        (-MultiLaurent.var j) * localSignedDeleteTwo n r i j := by
    unfold localSignedDeleteTwo
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun T _ => T.erase j) ?_ ?_ ?_ ?_
    · intro T hT
      simp only [base, Finset.mem_filter] at hT ⊢
      exact ⟨Finset.mem_univ _,
        by rw [Finset.card_erase_of_mem hT.2, hT.1.2.1]; omega,
        ⟨fun hi => hT.1.2.2 (Finset.mem_of_mem_erase hi),
          Finset.notMem_erase j T⟩⟩
    · intro T hT U hU hTU
      simp only [base, Finset.mem_filter] at hT hU
      change T.erase j = U.erase j at hTU
      rw [← Finset.insert_erase hT.2, hTU,
        Finset.insert_erase hU.2]
    · intro U hU
      simp only [Finset.mem_filter] at hU
      refine ⟨insert j U, ?_, ?_⟩
      · simp only [base, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _,
          by rw [Finset.card_insert_of_notMem hU.2.2.2, hU.2.1],
          by
            intro hi
            rcases Finset.mem_insert.mp hi with hi | hi
            · exact hij hi
            · exact hU.2.2.1 hi⟩,
          Finset.mem_insert_self _ _⟩
      · exact Finset.erase_insert hU.2.2.2
    · intro T hT
      simp only [base, Finset.mem_filter] at hT
      have hprod := Finset.mul_prod_erase T
        (fun l : Fin n => (-MultiLaurent.var l : Laurent ℚ n)) hT.2
      simpa [f, mul_comm] using hprod.symm
  have hsplit := Finset.sum_filter_add_sum_filter_not base
    (fun T => j ∈ T) f
  unfold localSignedDelete
  change (∑ T ∈ base, f T) = _
  rw [← hsplit, hbranch, add_comm]
  congr 1
  unfold localSignedDeleteTwo
  apply Finset.sum_congr
  · ext T
    simp only [base, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · intro T hT
    rfl

lemma localSignedDeleteTwo_comm (n r : ℕ) (i j : Fin n) :
    localSignedDeleteTwo n r i j = localSignedDeleteTwo n r j i := by
  classical
  unfold localSignedDeleteTwo
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · intro T hT
    rfl

def localPairQuotient (n : ℕ) : ℕ → Fin n → Fin n → Laurent ℚ n
  | 0, i, j =>
      (1 : Laurent ℚ n) - MultiLaurent.var i - MultiLaurent.var j
  | r + 1, i, j =>
      ((1 : Laurent ℚ n) - MultiLaurent.var i - MultiLaurent.var j) *
          localSignedDeleteTwo n (r + 1) i j +
        MultiLaurent.var i * MultiLaurent.var j *
          localSignedDeleteTwo n r i j

lemma localPairQuotient_comm (n r : ℕ) (i j : Fin n) :
    localPairQuotient n r i j = localPairQuotient n r j i := by
  cases r with
  | zero => simp [localPairQuotient]; ring
  | succ r =>
      simp only [localPairQuotient]
      rw [localSignedDeleteTwo_comm n (r + 1) i j,
        localSignedDeleteTwo_comm n r i j]
      ring

lemma localShift_pair_factor (n r : ℕ) (i j : Fin n) (hij : i ≠ j) :
    MultiLaurent.var i * localShiftFactor n r i -
        MultiLaurent.var j * localShiftFactor n r j =
      (MultiLaurent.var i - MultiLaurent.var j) *
        localPairQuotient n r i j := by
  cases r with
  | zero =>
      simp [localShiftFactor, localPairQuotient]
      ring
  | succ r =>
      unfold localShiftFactor
      rw [localSignedDelete_succ_decompose n r i j hij,
        localSignedDelete_succ_decompose n r j i hij.symm]
      rw [localSignedDeleteTwo_comm n (r + 1) j i,
        localSignedDeleteTwo_comm n r j i]
      unfold localPairQuotient
      ring

/-- The quotient that occurs when two unweighted shift factors are
subtracted.  This is the finite elementary-symmetric remainder in the
Adamović--Milas logarithmic derivative argument. -/
def localPairLogRemainder (n : ℕ) : ℕ → Fin n → Fin n → Laurent ℚ n
  | 0, _i, _j => 1
  | r + 1, i, j =>
      localSignedDeleteTwo n (r + 1) i j -
        localSignedDeleteTwo n r i j

lemma localShiftFactor_sub_factor (n r : ℕ) (i j : Fin n) (hij : i ≠ j) :
    localShiftFactor n r i - localShiftFactor n r j =
      (MultiLaurent.var j - MultiLaurent.var i) *
        localPairLogRemainder n r i j := by
  cases r with
  | zero =>
      simp [localShiftFactor, localPairLogRemainder]
  | succ r =>
      unfold localShiftFactor
      rw [localSignedDelete_succ_decompose n r i j hij,
        localSignedDelete_succ_decompose n r j i hij.symm]
      rw [localSignedDeleteTwo_comm n (r + 1) j i,
        localSignedDeleteTwo_comm n r j i]
      unfold localPairLogRemainder
      ring

@[simp] lemma localSignedDeleteTwo_zero (n : ℕ) (i j : Fin n) :
    localSignedDeleteTwo n 0 i j = 1 := by
  classical
  unfold localSignedDeleteTwo
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T hT hT0
    exact (hT0 (Finset.card_eq_zero.mp
      (Finset.mem_filter.mp hT).2.1)).elim
  · simp

lemma sum_ordered_localPairQuotient (n r : ℕ) :
    (∑ p ∈ orderedPairs n, localPairQuotient n r p.1 p.2) =
      (((n - r - 1 : ℕ) : ℚ) * ((n - r : ℕ) : ℚ)) •
          signedElementary n r +
        (((r + 1 : ℕ) : ℚ) *
          (2 * ((n - r - 1 : ℕ) : ℚ) + ((r : ℕ) : ℚ))) •
          signedElementary n (r + 1) := by
  cases r with
  | zero =>
      have hpoint (p : Fin n × Fin n) :
          localPairQuotient n 0 p.1 p.2 =
            localSignedDeleteTwo n 0 p.1 p.2 +
              ((-MultiLaurent.var p.1) + (-MultiLaurent.var p.2)) *
                localSignedDeleteTwo n 0 p.1 p.2 := by
        rw [localSignedDeleteTwo_zero]
        simp [localPairQuotient]
        ring
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib,
        sum_ordered_localSignedDeleteTwo,
        sum_ordered_negVars_localSignedDeleteTwo]
      simp only [Algebra.smul_def]
      push_cast
      norm_num [map_add, map_mul, map_ofNat]
  | succ r =>
      have hpoint (p : Fin n × Fin n) :
          localPairQuotient n (r + 1) p.1 p.2 =
            localSignedDeleteTwo n (r + 1) p.1 p.2 +
              ((-MultiLaurent.var p.1) + (-MultiLaurent.var p.2)) *
                localSignedDeleteTwo n (r + 1) p.1 p.2 +
              ((-MultiLaurent.var p.1) * (-MultiLaurent.var p.2)) *
                localSignedDeleteTwo n r p.1 p.2 := by
        unfold localPairQuotient
        ring
      simp_rw [hpoint]
      simp_rw [Finset.sum_add_distrib]
      rw [sum_ordered_localSignedDeleteTwo,
        sum_ordered_negVars_localSignedDeleteTwo,
        sum_ordered_mulVars_localSignedDeleteTwo]
      simp only [Algebra.smul_def]
      push_cast
      norm_num [map_add, map_mul, map_ofNat]
      ring_nf

lemma sum_decreasingPairs_generic {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : Fin n × Fin n → R) :
    (∑ p ∈ decreasingPairs n, f p) =
      ∑ p ∈ increasingPairs n, f (p.2, p.1) := by
  classical
  let swap : Fin n × Fin n → Fin n × Fin n := fun p => (p.2, p.1)
  rw [← image_swap_increasingPairs n, Finset.sum_image]
  intro p hp q hq heq
  simpa [swap] using congrArg swap heq

lemma two_sum_increasing_localPairQuotient (n r : ℕ) :
    (2 : ℚ) •
        (∑ p ∈ increasingPairs n, localPairQuotient n r p.1 p.2) =
      (((n - r - 1 : ℕ) : ℚ) * ((n - r : ℕ) : ℚ)) •
          signedElementary n r +
        (((r + 1 : ℕ) : ℚ) *
          (2 * ((n - r - 1 : ℕ) : ℚ) + ((r : ℕ) : ℚ))) •
          signedElementary n (r + 1) := by
  rw [← sum_ordered_localPairQuotient]
  rw [orderedPairs_eq_union,
    Finset.sum_union (disjoint_increasing_decreasing n),
    sum_decreasingPairs_generic]
  have hswap :
      (∑ p ∈ increasingPairs n, localPairQuotient n r p.2 p.1) =
        ∑ p ∈ increasingPairs n, localPairQuotient n r p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact localPairQuotient_comm n r p.2 p.1
  rw [hswap]
  simp only [Algebra.smul_def]
  norm_num [map_ofNat]
  ring

def localDifference (n : ℕ) (p : Fin n × Fin n) : Laurent ℚ n :=
  MultiLaurent.var p.1 - MultiLaurent.var p.2

lemma vandermonde_eq_prod_localDifference (n : ℕ) :
    (vandermonde n : Laurent ℚ n) =
      ∏ p ∈ increasingPairs n, localDifference n p := rfl

lemma localEuler_vandermonde (n : ℕ) (i : Fin n) :
    localEuler i (vandermonde n : Laurent ℚ n) =
      ∑ p ∈ increasingPairs n,
        localEuler i (localDifference n p) *
          ∏ q ∈ (increasingPairs n).erase p, localDifference n q := by
  unfold vandermonde localDifference
  exact localEuler_finset_prod i (increasingPairs n)
    (fun p : Fin n × Fin n =>
      (MultiLaurent.var p.1 - MultiLaurent.var p.2 : Laurent ℚ n))

lemma sum_weight_mul_localEuler_var (n : ℕ)
    (H : Fin n → Laurent ℚ n) (j : Fin n) :
    (∑ i : Fin n, H i * localEuler i (MultiLaurent.var j)) =
      H j * MultiLaurent.var j := by
  classical
  rw [Finset.sum_eq_single j]
  · rw [localEuler_var_same]
  · intro i hi hij
    rw [localEuler_var_of_ne i j (Ne.symm hij)]
    simp
  · simp

lemma sum_weight_mul_localEuler_difference (n : ℕ)
    (H : Fin n → Laurent ℚ n) (u v : Fin n) :
    (∑ i : Fin n,
        H i * localEuler i
          ((MultiLaurent.var u - MultiLaurent.var v : Laurent ℚ n))) =
      H u * MultiLaurent.var u - H v * MultiLaurent.var v := by
  simp_rw [localEuler_sub, mul_sub]
  rw [Finset.sum_sub_distrib,
    sum_weight_mul_localEuler_var,
    sum_weight_mul_localEuler_var]

lemma sum_localShift_mul_localEuler_vandermonde (n r : ℕ) :
    (∑ i : Fin n,
        localShiftFactor n r i *
          localEuler i (vandermonde n : Laurent ℚ n)) =
      (vandermonde n : Laurent ℚ n) *
        ∑ p ∈ increasingPairs n, localPairQuotient n r p.1 p.2 := by
  classical
  simp_rw [localEuler_vandermonde, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show localDifference n p =
      (MultiLaurent.var p.1 - MultiLaurent.var p.2 : Laurent ℚ n) by rfl]
  rw [sum_weight_mul_localEuler_difference n
    (fun i => localShiftFactor n r i) p.1 p.2]
  have hpne : p.1 ≠ p.2 := by
    have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    omega
  rw [show localShiftFactor n r p.1 * MultiLaurent.var p.1 -
      localShiftFactor n r p.2 * MultiLaurent.var p.2 =
        MultiLaurent.var p.1 * localShiftFactor n r p.1 -
          MultiLaurent.var p.2 * localShiftFactor n r p.2 by ring]
  rw [localShift_pair_factor n r p.1 p.2 hpne]
  calc
    (MultiLaurent.var p.1 - MultiLaurent.var p.2) *
          localPairQuotient n r p.1 p.2 *
          ∏ q ∈ (increasingPairs n).erase p, localDifference n q =
        (localDifference n p *
          ∏ q ∈ (increasingPairs n).erase p, localDifference n q) *
            localPairQuotient n r p.1 p.2 := by
      unfold localDifference
      ring
    _ = (vandermonde n : Laurent ℚ n) *
          localPairQuotient n r p.1 p.2 := by
      rw [vandermonde_eq_prod_localDifference]
      rw [Finset.mul_prod_erase (increasingPairs n)
        (localDifference n) hp]

lemma local_mul_smul_mul_reorder {n : ℕ} (c : ℚ)
    (A B C : Laurent ℚ n) :
    A * (c • (B * C)) = c • (B * (A * C)) := by
  simp only [Algebra.smul_def]
  ring

lemma sum_localShift_mul_localEuler_vandermonde_pow
    (n r q : ℕ) :
    (∑ i : Fin n,
        localShiftFactor n r i *
          localEuler i ((vandermonde n : Laurent ℚ n) ^ (q + 1))) =
      (((q + 1 : ℕ) : ℚ) •
        ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
          ∑ p ∈ increasingPairs n,
            localPairQuotient n r p.1 p.2)) := by
  simp_rw [localEuler_pow_succ]
  simp_rw [local_mul_smul_mul_reorder]
  rw [← Finset.smul_sum]
  simp_rw [← Finset.mul_sum]
  rw [sum_localShift_mul_localEuler_vandermonde]
  rw [pow_succ]
  ring

lemma sum_localEuler_shift_core_eq (n d t r q : ℕ) :
    (Finset.univ.sum fun i : Fin n =>
        localEuler i
          (localShiftFactor n r i *
            ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
              localEndpointProduct n d t))) =
      (vandermonde n : Laurent ℚ n) ^ (q + 1) *
        (Finset.univ.sum fun i : Fin n =>
          localEuler i (localShiftFactor n r i) *
              localEndpointProduct n d t +
            localShiftFactor n r i *
              localEuler i (localEndpointProduct n d t)) +
      localEndpointProduct n d t *
        (Finset.univ.sum fun i : Fin n =>
          localShiftFactor n r i *
            localEuler i ((vandermonde n : Laurent ℚ n) ^ (q + 1))) := by
  have hpoint (i : Fin n) :
      localEuler i
          (localShiftFactor n r i *
            ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
              localEndpointProduct n d t)) =
        (vandermonde n : Laurent ℚ n) ^ (q + 1) *
          (localEuler i (localShiftFactor n r i) *
              localEndpointProduct n d t +
            localShiftFactor n r i *
              localEuler i (localEndpointProduct n d t)) +
        localEndpointProduct n d t *
          (localShiftFactor n r i *
            localEuler i ((vandermonde n : Laurent ℚ n) ^ (q + 1))) := by
    rw [localEuler_mul, localEuler_mul]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

lemma two_sum_localEuler_shift_core (n d t r q : ℕ) :
    (2 : ℚ) •
      (Finset.univ.sum fun i : Fin n =>
        localEuler i
          (localShiftFactor n r i *
            ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
              localEndpointProduct n d t))) =
      (-2 * ((d : ℕ) : ℚ) * ((n - r : ℕ) : ℚ) +
          ((q + 1 : ℕ) : ℚ) * ((n - r - 1 : ℕ) : ℚ) *
            ((n - r : ℕ) : ℚ)) •
        ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
          localEndpointProduct n d t * signedElementary n r) +
      (2 * ((r + 1 : ℕ) : ℚ) *
            (((t + 1 : ℕ) : ℚ) - ((d : ℕ) : ℚ)) +
          ((q + 1 : ℕ) : ℚ) * ((r + 1 : ℕ) : ℚ) *
            (2 * ((n - r - 1 : ℕ) : ℚ) + ((r : ℕ) : ℚ))) •
        ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
          localEndpointProduct n d t * signedElementary n (r + 1)) := by
  rw [sum_localEuler_shift_core_eq]
  rw [sum_localShift_derivative_endpoint]
  rw [sum_localShift_mul_localEuler_vandermonde_pow]
  have hQ := two_sum_increasing_localPairQuotient n r
  simp only [Algebra.smul_def] at hQ ⊢
  push_cast at hQ ⊢
  norm_num [map_add, map_sub, map_neg, map_mul, map_ofNat] at hQ ⊢
  linear_combination
    ((vandermonde n : Laurent ℚ n) ^ (q + 1) *
      localEndpointProduct n d t *
        ((q : Laurent ℚ n) + 1)) * hQ

def localMorrisSign (S : Setup) (b : ℕ) : Laurent ℚ S.n :=
  (-1 : Laurent ℚ S.n) ^
    (S.n * b + (increasingPairs S.n).card * S.k)

def localMorrisCore (S : Setup) (a b : ℕ) : Laurent ℚ S.n :=
  (vandermonde S.n : Laurent ℚ S.n) ^ S.K *
    localEndpointProduct S.n (b + S.m * S.K) (a + b)

lemma morrisKernel_withAB_eq_sign_mul_core (S : Setup) (a b : ℕ) :
    morrisKernel (S.withAB a b) =
      localMorrisSign S b * localMorrisCore S a b := by
  rw [morrisKernel_eq_normalized]
  unfold normalizedMorrisKernel localMorrisSign localMorrisCore
  unfold localEndpointProduct localEndpointFactor
  simp only [Setup.withAB_n, Setup.withAB_m, Setup.withAB_k,
    Setup.withAB_a, Setup.withAB_b, Setup.withAB_K]
  ring

lemma localEuler_neg_one_pow {n : ℕ} (i : Fin n) (c : ℕ) :
    localEuler i ((-1 : Laurent ℚ n) ^ c) = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [pow_succ, localEuler_mul, ih]
      simp [localEuler_neg]

def localShiftDerivativeSum (S : Setup) (a b r : ℕ) : Laurent ℚ S.n :=
  ∑ i : Fin S.n,
    localEuler i
      (localShiftFactor S.n r i *
        (show Laurent ℚ S.n from morrisKernel (S.withAB a b)))

def localCoreDerivativeSum (S : Setup) (a b r : ℕ) : Laurent ℚ S.n :=
  ∑ i : Fin S.n,
    localEuler i
      (localShiftFactor S.n r i * localMorrisCore S a b)

lemma localShiftDerivativeSum_eq_sign_core
    (S : Setup) (a b r : ℕ) :
    localShiftDerivativeSum S a b r =
      localMorrisSign S b * localCoreDerivativeSum S a b r := by
  classical
  unfold localShiftDerivativeSum localCoreDerivativeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [morrisKernel_withAB_eq_sign_mul_core]
  rw [show localShiftFactor S.n r i *
      (localMorrisSign S b * localMorrisCore S a b) =
        localMorrisSign S b *
          (localShiftFactor S.n r i * localMorrisCore S a b) by ring]
  rw [localEuler_mul]
  have hsign : localEuler i (localMorrisSign S b) = 0 := by
    exact localEuler_neg_one_pow i _
  rw [hsign]
  ring

lemma two_localCoreDerivativeSum (S : Setup) (a b r : ℕ) (hr : r < S.n) :
    (2 : ℚ) • localCoreDerivativeSum S a b r =
      -(((S.n - r : ℕ) : ℚ) * (2 * b + r * S.K : ℕ)) •
          (localMorrisCore S a b * signedElementary S.n r) +
        (((r + 1 : ℕ) : ℚ) *
          (2 * a + 2 + (S.n - r - 1) * S.K : ℕ)) •
          (localMorrisCore S a b * signedElementary S.n (r + 1)) := by
  have hK : S.K - 1 + 1 = S.K :=
    Nat.sub_add_cancel S.K_pos
  have h := two_sum_localEuler_shift_core S.n
    (b + S.m * S.K) (a + b) r (S.K - 1)
  unfold localCoreDerivativeSum localMorrisCore
  rw [hK] at h
  have hnmr : S.n - r = 2 * S.m + 1 - r := by rw [S.odd_rank]
  have hnm1 : S.n - r - 1 = 2 * S.m - r := by
    rw [S.odd_rank] at hr ⊢
    omega
  have hnm1' : 2 * S.m + 1 - r - 1 = 2 * S.m - r := by
    rw [S.odd_rank] at hr
    omega
  have hrm : r ≤ 2 * S.m := by
    rw [S.odd_rank] at hr
    omega
  have hrm1 : r ≤ 2 * S.m + 1 := by omega
  convert h using 1 <;>
    simp only [Algebra.smul_def] at * <;>
    push_cast at * <;>
    norm_num [map_add, map_sub, map_neg, map_mul, map_ofNat] at *
  · rw [hnmr, hnm1']
    push_cast [Nat.cast_sub hrm, Nat.cast_sub hrm1]
    ring

lemma two_localShiftDerivativeSum (S : Setup) (a b r : ℕ) (hr : r < S.n) :
    (2 : ℚ) • localShiftDerivativeSum S a b r =
      -(((S.n - r : ℕ) : ℚ) * (2 * b + r * S.K : ℕ)) •
          ((show Laurent ℚ S.n from morrisKernel (S.withAB a b)) *
            signedElementary S.n r) +
        (((r + 1 : ℕ) : ℚ) *
          (2 * a + 2 + (S.n - r - 1) * S.K : ℕ)) •
          ((show Laurent ℚ S.n from morrisKernel (S.withAB a b)) *
            signedElementary S.n (r + 1)) := by
  rw [localShiftDerivativeSum_eq_sign_core]
  rw [show (2 : ℚ) •
      (localMorrisSign S b * localCoreDerivativeSum S a b r) =
        localMorrisSign S b *
          ((2 : ℚ) • localCoreDerivativeSum S a b r) by
    simp only [Algebra.smul_def]
    ring]
  rw [two_localCoreDerivativeSum S a b r hr]
  rw [morrisKernel_withAB_eq_sign_mul_core]
  simp only [Algebra.smul_def]
  ring

end LogarithmicMorrisFull
