import logarithmicmorris.LogarithmicMorrisGoodLagrange

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

set_option maxHeartbeats 1000000

def NegNormalized {n : ℕ} (k : Fin n) (F : Laurent ℚ n) : Prop :=
  (∀ e, F e ≠ 0 → e k ≤ 0) ∧
  (∀ e, e k = 0 → F e = if e = 0 then 1 else 0)

lemma negNormalized_one {n : ℕ} (k : Fin n) :
    NegNormalized k (1 : Laurent ℚ n) := by
  classical
  constructor
  · intro e he
    by_cases h : e = 0
    · simp [h]
    · simp [AddMonoidAlgebra.one_def, h] at he
  · intro e he
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply]
    simp [eq_comm]

lemma negNormalized_mul {n : ℕ} {k : Fin n} {F G : Laurent ℚ n}
    (hF : NegNormalized k F) (hG : NegNormalized k G) :
    NegNormalized k (F * G) := by
  classical
  constructor
  · intro e he
    have hmem : e ∈ (F * G).support := Finsupp.mem_support_iff.mpr he
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_mul F G hmem)
    have huk := hF.1 u (Finsupp.mem_support_iff.mp hu)
    have hvk := hG.1 v (Finsupp.mem_support_iff.mp hv)
    rw [← huv]
    simp only [Finsupp.add_apply]
    omega
  · intro e hek
    change MultiLaurent.coeff e (F * G) = _
    rw [MultiLaurent.coeff_mul]
    rw [Finsupp.sum]
    have hF0 : F 0 = 1 := by simpa using hF.2 0 (by simp)
    have hF0mem : 0 ∈ F.support := by
      rw [Finsupp.mem_support_iff, hF0]
      norm_num
    rw [Finset.sum_eq_single 0]
    · rw [Finsupp.sum]
      by_cases he0 : e = 0
      · subst e
        have hG0 : G 0 = 1 := by simpa using hG.2 0 (by simp)
        have hG0mem : 0 ∈ G.support := by
          rw [Finsupp.mem_support_iff, hG0]
          norm_num
        rw [Finset.sum_eq_single 0]
        · simp [hF0, hG0]
        · intro v hv hv0
          simp only [ite_eq_right_iff]
          intro hveq
          exact (hv0 (by simpa using hveq)).elim
        · exact fun h => (h hG0mem).elim
      · have hGe : G e = 0 := by
          simpa [he0] using hG.2 e hek
        by_cases hemem : e ∈ G.support
        · rw [Finset.sum_eq_single e]
          · simp [hF0, hGe, he0]
          · intro v hv hve
            simp only [zero_add, ite_eq_right_iff]
            exact fun h => (hve h).elim
          · exact fun h => (h hemem).elim
        · rw [Finset.sum_eq_zero]
          · simp [he0]
          · intro v hv
            have hve : v ≠ e := by
              intro hve
              exact hemem (hve ▸ hv)
            simp [hve, he0]
    · intro u hu hu0
      rw [Finsupp.sum, Finset.sum_eq_zero]
      intro v hv
      by_cases huv : u + v = e
      · have huk := hF.1 u (Finsupp.mem_support_iff.mp hu)
        have hvk := hG.1 v (Finsupp.mem_support_iff.mp hv)
        have hsum : u k + v k = 0 := by
          rw [← Finsupp.add_apply, huv, hek]
        have huK0 : u k = 0 := by omega
        have hFu : F u = 0 := by simpa [hu0] using hF.2 u huK0
        exact (Finsupp.mem_support_iff.mp hu hFu).elim
      · simp [huv]
    · exact fun h => (h hF0mem).elim

lemma negNormalized_one_sub_X {n : ℕ} (k : Fin n)
    (d : MultiLaurent.Exponent (Fin n)) (hd : d k = -1) :
    NegNormalized k (1 - MultiLaurent.X d : Laurent ℚ n) := by
  classical
  constructor
  · intro e he
    by_cases he0 : e = 0
    · simp [he0]
    by_cases hed : e = d
    · subst e
      simpa [hd]
    · rw [Finsupp.sub_apply] at he
      simp only [AddMonoidAlgebra.one_def, MultiLaurent.X,
        MultiLaurent.monomial, AddMonoidAlgebra.single_apply] at he
      have h0e : ¬(0 : MultiLaurent.Exponent (Fin n)) = e :=
        fun h => he0 h.symm
      have hde : ¬d = e := fun h => hed h.symm
      simp [h0e, hde] at he
  · intro e hek
    by_cases he0 : e = 0
    · subst e
      have hd0 : d ≠ 0 := by
        intro h
        have := congrArg (fun z => z k) h
        simp [hd] at this
      rw [Finsupp.sub_apply]
      simp [AddMonoidAlgebra.one_def, MultiLaurent.X,
        MultiLaurent.monomial, hd0, eq_comm]
    · have hed : e ≠ d := by
        intro h
        subst e
        omega
      rw [Finsupp.sub_apply]
      simp [AddMonoidAlgebra.one_def, MultiLaurent.X,
        MultiLaurent.monomial, he0, hed, eq_comm]

lemma negNormalized_pow {n : ℕ} {k : Fin n} {F : Laurent ℚ n}
    (hF : NegNormalized k F) (a : ℕ) : NegNormalized k (F ^ a) := by
  classical
  induction a with
  | zero => simpa using negNormalized_one k
  | succ a ih => simpa [pow_succ] using negNormalized_mul ih hF

lemma ratio_eq_X {n : ℕ} (i j : Fin n) :
    (ratio i j : Laurent ℚ n) =
      MultiLaurent.X (Finsupp.single i 1 + Finsupp.single j (-1)) := by
  unfold ratio MultiLaurent.var MultiLaurent.varInv
  rw [MultiLaurent.X_mul_X]

lemma negNormalized_one_sub_ratio_pow {n : ℕ} {k i : Fin n}
    (hik : i ≠ k) (a : ℕ) :
    NegNormalized k ((1 - ratio i k : Laurent ℚ n) ^ a) := by
  rw [ratio_eq_X]
  apply negNormalized_pow (negNormalized_one_sub_X k _ ?_) a
  simp [Finsupp.add_apply, Finsupp.single_apply, hik]

lemma negNormalized_prod {n : ℕ} {k : Fin n} {I : Type*}
    (s : Finset I) (F : I → Laurent ℚ n)
    (hF : ∀ i ∈ s, NegNormalized k (F i)) :
    NegNormalized k (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using negNormalized_one k
  | @insert i s hi ih =>
      simp only [Finset.prod_insert, hi, not_false_eq_true]
      exact negNormalized_mul (hF i (Finset.mem_insert_self i s))
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

def CoordZero {n : ℕ} (k : Fin n) (F : Laurent ℚ n) : Prop :=
  ∀ e, F e ≠ 0 → e k = 0

lemma coordZero_one {n : ℕ} (k : Fin n) :
    CoordZero k (1 : Laurent ℚ n) := by
  classical
  intro e he
  by_cases h : e = 0
  · simp [h]
  · simp [AddMonoidAlgebra.one_def, h] at he

lemma coordZero_mul {n : ℕ} {k : Fin n} {F G : Laurent ℚ n}
    (hF : CoordZero k F) (hG : CoordZero k G) : CoordZero k (F * G) := by
  classical
  intro e he
  have hmem : e ∈ (F * G).support := Finsupp.mem_support_iff.mpr he
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_mul F G hmem)
  rw [← huv, Finsupp.add_apply, hF u (Finsupp.mem_support_iff.mp hu),
    hG v (Finsupp.mem_support_iff.mp hv), add_zero]

lemma coordZero_one_sub_X {n : ℕ} (k : Fin n)
    (d : MultiLaurent.Exponent (Fin n)) (hd : d k = 0) :
    CoordZero k (1 - MultiLaurent.X d : Laurent ℚ n) := by
  classical
  intro e he
  by_cases he0 : e = 0
  · simp [he0]
  by_cases hed : e = d
  · simpa [hed, hd]
  · rw [Finsupp.sub_apply] at he
    simp only [AddMonoidAlgebra.one_def, MultiLaurent.X,
      MultiLaurent.monomial, AddMonoidAlgebra.single_apply] at he
    have h0e : ¬(0 : MultiLaurent.Exponent (Fin n)) = e :=
      fun h => he0 h.symm
    have hde : ¬d = e := fun h => hed h.symm
    simp [h0e, hde] at he

lemma coordZero_pow {n : ℕ} {k : Fin n} {F : Laurent ℚ n}
    (hF : CoordZero k F) (a : ℕ) : CoordZero k (F ^ a) := by
  classical
  induction a with
  | zero => simpa using coordZero_one k
  | succ a ih => simpa [pow_succ] using coordZero_mul ih hF

lemma coordZero_one_sub_ratio_pow {n : ℕ} {k i j : Fin n}
    (hik : i ≠ k) (hjk : j ≠ k) (a : ℕ) :
    CoordZero k ((1 - ratio i j : Laurent ℚ n) ^ a) := by
  rw [ratio_eq_X]
  apply coordZero_pow (coordZero_one_sub_X k _ ?_) a
  simp [Finsupp.add_apply, Finsupp.single_apply, hik, hjk]

lemma coordZero_prod {n : ℕ} {k : Fin n} {I : Type*}
    (s : Finset I) (F : I → Laurent ℚ n)
    (hF : ∀ i ∈ s, CoordZero k (F i)) :
    CoordZero k (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coordZero_one k
  | @insert i s hi ih =>
      simp only [Finset.prod_insert, hi, not_false_eq_true]
      exact coordZero_mul (hF i (Finset.mem_insert_self i s))
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

lemma constantTerm_mul_of_coordZero_negNormalized {n : ℕ} {k : Fin n}
    {A H : Laurent ℚ n} (hA : CoordZero k A) (hH : NegNormalized k H) :
    MultiLaurent.constantTerm (A * H) = MultiLaurent.constantTerm A := by
  classical
  rw [MultiLaurent.constantTerm_mul]
  calc
    A.sum (fun e c => c * H (-e)) =
        A.sum (fun e c => if e = 0 then c else 0) := by
      apply Finsupp.sum_congr
      intro e he
      have hek : e k = 0 := hA e (Finsupp.mem_support_iff.mp he)
      have hnegk : (-e) k = 0 := by simp [Finsupp.neg_apply, hek]
      rw [hH.2 (-e) hnegk]
      by_cases he0 : e = 0
      · subst e
        simp
      · have hne0 : -e ≠ 0 := neg_ne_zero.mpr he0
        simp [he0, hne0]
    _ = A 0 := Finsupp.sum_ite_self_eq' A 0
    _ = MultiLaurent.constantTerm A := rfl

/-- Good's generalized Dyson kernel on an active set of variables. -/
def goodKernel (n : ℕ) (S : Finset (Fin n)) (a : Fin n → ℕ) : Laurent ℚ n :=
  ∏ i ∈ S, ∏ j ∈ S.erase i, (1 - ratio i j) ^ (a i)

def goodRowOn (n : ℕ) (S : Finset (Fin n)) (i : Fin n) : Laurent ℚ n :=
  ∏ j ∈ S.erase i, (1 - ratio i j)

lemma goodRowOn_ne_zero (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    goodRowOn n S i ≠ 0 := by
  unfold goodRowOn
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  intro h
  have hv : (MultiLaurent.var i : Laurent ℚ n) = MultiLaurent.var j := by
    have hr : (MultiLaurent.var i : Laurent ℚ n) *
        MultiLaurent.varInv j = 1 := by
      simpa [ratio] using (sub_eq_zero.mp h).symm
    calc
      MultiLaurent.var i = MultiLaurent.var i * 1 := by rw [mul_one]
      _ = MultiLaurent.var i *
          (MultiLaurent.varInv j * MultiLaurent.var j) := by
        rw [mul_comm (MultiLaurent.varInv j) (MultiLaurent.var j),
          MultiLaurent.var_mul_varInv]
      _ = (MultiLaurent.var i * MultiLaurent.varInv j) *
          MultiLaurent.var j := by rw [mul_assoc]
      _ = MultiLaurent.var j := by rw [hr]; simp
  exact hji ((laurent_var_injective n hv).symm)

lemma goodRowOn_product_identity (n : ℕ) (S : Finset (Fin n))
    (hS : S.Nonempty) :
    (∏ i ∈ S, goodRowOn n S i) =
      ∑ i ∈ S, ∏ j ∈ S.erase i, goodRowOn n S j := by
  let R := Laurent ℚ n
  let F := FractionRing R
  let ι : R →+* F := algebraMap R F
  let v : Fin n → F := fun i => ι (MultiLaurent.var i)
  have hv_inj : Function.Injective v := by
    intro i j h
    apply laurent_var_injective n
    exact IsFractionRing.injective R F h
  have hlag := Lagrange.sum_basis (s := S) (v := v) hv_inj.injOn hS
  have heval := congrArg (Polynomial.eval (0 : F)) hlag
  simp at heval
  have hrecip : (∑ i ∈ S, (ι (goodRowOn n S i))⁻¹) = 1 := by
    calc
      (∑ i ∈ S, (ι (goodRowOn n S i))⁻¹) =
          ∑ i ∈ S, Polynomial.eval 0 (Lagrange.basis S v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold goodRowOn
        rw [map_prod]
        simp only [map_sub, map_one, map_mul, ratio]
        simp only [Lagrange.basis, Polynomial.eval_prod,
          Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, zero_sub]
        rw [← Finset.prod_inv_distrib]
        apply Finset.prod_congr rfl
        intro j hj
        have hvj : v j ≠ 0 := by
          intro hzero
          have : (MultiLaurent.var j : R) = 0 :=
            IsFractionRing.injective R F (by simpa [v, ι] using hzero)
          have hm := congrArg (fun p : R => p * MultiLaurent.varInv j) this
          dsimp at hm
          simp only [zero_mul] at hm
          change (MultiLaurent.var j : R) * MultiLaurent.varInv j = 0 at hm
          rw [MultiLaurent.var_mul_varInv] at hm
          simp at hm
        have hdiff : v i - v j ≠ 0 :=
          sub_ne_zero.mpr (hv_inj.ne (Finset.mem_erase.mp hj).1.symm)
        have hvinv : ι (MultiLaurent.varInv j) = (v j)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          change ι (MultiLaurent.varInv j) * ι (MultiLaurent.var j) = 1
          rw [mul_comm, ← map_mul, MultiLaurent.var_mul_varInv, map_one]
        rw [hvinv]
        have hbase : 1 - v i * (v j)⁻¹ = -(v i - v j) * (v j)⁻¹ := by
          calc
            1 - v i * (v j)⁻¹ = v j * (v j)⁻¹ - v i * (v j)⁻¹ := by
              rw [mul_inv_cancel₀ hvj]
            _ = -(v i - v j) * (v j)⁻¹ := by ring
        rw [hbase, mul_inv_rev, inv_inv]
        have hneg : (-(v i - v j))⁻¹ = -((v i - v j)⁻¹) := by
          rw [show -(v i - v j) = (-1 : F) * (v i - v j) by ring,
            mul_inv_rev]
          norm_num
          ring
        rw [hneg]
        ring
      _ = Polynomial.eval 0 (∑ i ∈ S, Lagrange.basis S v i) := by
        exact (map_sum (Polynomial.evalRingHom (0 : F))
          (fun i : Fin n => Lagrange.basis S v i) S).symm
      _ = 1 := heval
  apply IsFractionRing.injective R F
  simp only [map_prod, map_sum, map_mul]
  have hrowmap : ∀ i : Fin n, ι (goodRowOn n S i) ≠ 0 := fun i => by
    simpa [ι] using (IsFractionRing.injective R F).ne
      (goodRowOn_ne_zero n S i)
  calc
    (∏ i ∈ S, ι (goodRowOn n S i)) =
        (∏ i ∈ S, ι (goodRowOn n S i)) * 1 := by ring
    _ = (∏ i ∈ S, ι (goodRowOn n S i)) *
        (∑ i ∈ S, (ι (goodRowOn n S i))⁻¹) := by rw [hrecip]
    _ = ∑ i ∈ S, (∏ j ∈ S, ι (goodRowOn n S j)) *
        (ι (goodRowOn n S i))⁻¹ := by rw [Finset.mul_sum]
    _ = ∑ i ∈ S, ∏ j ∈ S.erase i, ι (goodRowOn n S j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.prod_eq_mul_prod_diff_singleton hi]
      rw [mul_comm (ι (goodRowOn n S i)), mul_assoc,
        mul_inv_cancel₀ (hrowmap i), mul_one]
      simp [Finset.erase_eq]

lemma goodKernel_boundary_factorization {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) (k : Fin n) (hk : k ∈ S) (hak : a k = 0) :
    goodKernel n S a =
      goodKernel n (S.erase k) a *
        ∏ i ∈ S.erase k, (1 - ratio i k) ^ (a i) := by
  classical
  unfold goodKernel
  rw [Finset.prod_eq_mul_prod_diff_singleton hk]
  simp only [hak, pow_zero, Finset.prod_const_one, mul_one, one_mul]
  rw [← Finset.prod_mul_distrib]
  rw [show S \ {k} = S.erase k by simp [Finset.erase_eq]]
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  have hset : S.erase i = insert k ((S.erase k).erase i) := by
    ext j
    by_cases hjk : j = k <;> simp [hjk, hk, hik, Ne.symm hik]
  rw [hset, Finset.prod_insert]
  · ring
  · simp [hik]

lemma goodKernel_erase_coordZero {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) (k : Fin n) :
    CoordZero k (goodKernel n (S.erase k) a) := by
  classical
  unfold goodKernel
  apply coordZero_prod (S.erase k)
  intro i hi
  apply coordZero_prod ((S.erase k).erase i)
  intro j hj
  exact coordZero_one_sub_ratio_pow
    (Finset.mem_erase.mp hi).1
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj)).1
    (a i)

lemma goodKernel_boundary_tail_negNormalized {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) (k : Fin n) :
    NegNormalized k (∏ i ∈ S.erase k, (1 - ratio i k) ^ (a i)) := by
  classical
  apply negNormalized_prod (S.erase k)
  intro i hi
  exact negNormalized_one_sub_ratio_pow (Finset.mem_erase.mp hi).1 (a i)

lemma constantTerm_goodKernel_boundary {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) (k : Fin n) (hk : k ∈ S) (hak : a k = 0) :
    MultiLaurent.constantTerm (goodKernel n S a) =
      MultiLaurent.constantTerm (goodKernel n (S.erase k) a) := by
  rw [goodKernel_boundary_factorization S a k hk hak]
  exact constantTerm_mul_of_coordZero_negNormalized
    (goodKernel_erase_coordZero S a k)
    (goodKernel_boundary_tail_negNormalized S a k)

lemma goodKernel_eq_prod_goodRowOn_pow {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) :
    goodKernel n S a = ∏ i ∈ S, (goodRowOn n S i) ^ (a i) := by
  classical
  unfold goodKernel goodRowOn
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_pow]

def goodDec {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update a i (a i - 1)

@[simp] lemma goodDec_same {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    goodDec a i i = a i - 1 := by simp [goodDec]

@[simp] lemma goodDec_of_ne {n : ℕ} (a : Fin n → ℕ) {i j : Fin n}
    (hji : j ≠ i) : goodDec a i j = a j := by simp [goodDec, hji]

lemma goodKernel_recurrence {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (a : Fin n → ℕ) (ha : ∀ i ∈ S, 0 < a i) :
    goodKernel n S a = ∑ i ∈ S, goodKernel n S (goodDec a i) := by
  classical
  rw [goodKernel_eq_prod_goodRowOn_pow]
  let B : Laurent ℚ n :=
    ∏ i ∈ S, (goodRowOn n S i) ^ (a i - 1)
  calc
    (∏ i ∈ S, (goodRowOn n S i) ^ a i) =
        ∏ i ∈ S, (goodRowOn n S i) ^ (a i - 1) *
          goodRowOn n S i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← pow_succ]
      congr 1
      have hai := ha i hi
      omega
    _ = B * ∏ i ∈ S, goodRowOn n S i := by
      unfold B
      rw [Finset.prod_mul_distrib]
    _ = B * (∑ i ∈ S,
          ∏ j ∈ S.erase i, goodRowOn n S j) := by
      rw [goodRowOn_product_identity n S hS]
    _ = ∑ i ∈ S, B *
          (∏ j ∈ S.erase i, goodRowOn n S j) := by
      rw [Finset.mul_sum]
    _ = ∑ i ∈ S, goodKernel n S (goodDec a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [goodKernel_eq_prod_goodRowOn_pow]
      calc
        B * (∏ j ∈ S.erase i, goodRowOn n S j) =
            (goodRowOn n S i) ^ (a i - 1) *
              ((∏ j ∈ S.erase i,
                  (goodRowOn n S j) ^ (a j - 1)) *
                ∏ j ∈ S.erase i, goodRowOn n S j) := by
          unfold B
          rw [Finset.prod_eq_mul_prod_diff_singleton hi]
          simp only [Finset.erase_eq]
          ring
        _ = (goodRowOn n S i) ^ (a i - 1) *
              ∏ j ∈ S.erase i,
                ((goodRowOn n S j) ^ (a j - 1) * goodRowOn n S j) := by
          rw [Finset.prod_mul_distrib]
        _ = (goodRowOn n S i) ^ (goodDec a i i) *
              ∏ j ∈ S.erase i,
                (goodRowOn n S j) ^ (goodDec a i j) := by
          simp only [goodDec_same]
          congr 1
          apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          rw [goodDec_of_ne a hji, ← pow_succ]
          congr 1
          have haj := ha j (Finset.mem_of_mem_erase hj)
          omega
        _ = ∏ j ∈ S,
              (goodRowOn n S j) ^ (goodDec a i j) := by
          rw [Finset.prod_eq_mul_prod_diff_singleton hi]
          simp only [Finset.erase_eq]

lemma constantTerm_goodKernel_recurrence {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (a : Fin n → ℕ) (ha : ∀ i ∈ S, 0 < a i) :
    MultiLaurent.constantTerm (goodKernel n S a) =
      ∑ i ∈ S, MultiLaurent.constantTerm (goodKernel n S (goodDec a i)) := by
  rw [goodKernel_recurrence S hS a ha]
  simp only [map_sum]

def goodFormula {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℕ) : ℚ :=
  ((∑ i ∈ S, a i).factorial : ℚ) /
    ∏ i ∈ S, (a i).factorial

lemma goodFormula_boundary {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) (k : Fin n) (hk : k ∈ S) (hak : a k = 0) :
    goodFormula S a = goodFormula (S.erase k) a := by
  classical
  unfold goodFormula
  rw [Finset.sum_eq_add_sum_diff_singleton hk,
    Finset.prod_eq_mul_prod_diff_singleton hk]
  simp [hak, Finset.erase_eq]

lemma sum_goodDec {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℕ)
    (i : Fin n) (hi : i ∈ S) (hai : 0 < a i) :
    ∑ j ∈ S, goodDec a i j = (∑ j ∈ S, a j) - 1 := by
  classical
  rw [Finset.sum_eq_add_sum_diff_singleton hi,
    Finset.sum_eq_add_sum_diff_singleton hi]
  simp only [goodDec_same]
  have hrest : ∑ j ∈ S \ {i}, goodDec a i j =
      ∑ j ∈ S \ {i}, a j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact goodDec_of_ne a (Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hj).2)
  rw [hrest]
  omega

lemma prod_factorial_goodDec {n : ℕ} (S : Finset (Fin n))
    (a : Fin n → ℕ) (i : Fin n) (hi : i ∈ S) :
    (∏ j ∈ S, (goodDec a i j).factorial : ℕ) =
      (a i - 1).factorial *
        ∏ j ∈ S.erase i, (a j).factorial := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton hi]
  simp only [goodDec_same]
  simp only [Finset.erase_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [goodDec_of_ne a (Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hj).2)]

lemma goodFormula_dec {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℕ)
    (i : Fin n) (hi : i ∈ S) (hai : 0 < a i) :
    goodFormula S (goodDec a i) =
      goodFormula S a * (a i : ℚ) / ((∑ j ∈ S, a j : ℕ) : ℚ) := by
  classical
  let T := ∑ j ∈ S, a j
  let P := ∏ j ∈ S.erase i, (a j).factorial
  have hTi : a i ≤ T := by
    unfold T
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi
  have hTpos : 0 < T := lt_of_lt_of_le hai hTi
  have hTfac : T.factorial = T * (T - 1).factorial := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hTpos)
    rw [hu, Nat.factorial_succ]
    simp
  have haifac : (a i).factorial = a i * (a i - 1).factorial := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hai)
    rw [hu, Nat.factorial_succ]
    simp
  unfold goodFormula
  rw [sum_goodDec S a i hi hai, prod_factorial_goodDec S a i hi]
  rw [Finset.prod_eq_mul_prod_diff_singleton hi]
  simp only [Finset.erase_eq]
  dsimp [T, P] at hTfac hTpos ⊢
  have hTq : (∑ j ∈ S, (a j : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hTpos
  push_cast [hTfac, haifac]
  field_simp [hTq,
    show ((a i - 1).factorial : ℚ) ≠ 0 by positivity,
    show ((∏ j ∈ S \ {i}, (a j).factorial : ℕ) : ℚ) ≠ 0 by positivity]
  all_goals ring

lemma goodFormula_recurrence {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (a : Fin n → ℕ) (ha : ∀ i ∈ S, 0 < a i) :
    goodFormula S a = ∑ i ∈ S, goodFormula S (goodDec a i) := by
  classical
  let T := ∑ j ∈ S, a j
  have hTpos : 0 < T := by
    obtain ⟨i, hi⟩ := hS
    exact lt_of_lt_of_le (ha i hi)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi)
  calc
    goodFormula S a = goodFormula S a * (T : ℚ) / (T : ℚ) := by
      field_simp [show (T : ℚ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hTpos]
    _ = ∑ i ∈ S, goodFormula S a * (a i : ℚ) / (T : ℚ) := by
      rw [← Finset.sum_div]
      rw [← Finset.mul_sum]
      norm_cast
    _ = ∑ i ∈ S, goodFormula S (goodDec a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (goodFormula_dec S a i hi (ha i hi)).symm

theorem constantTerm_goodKernel_aux {n : ℕ} (M : ℕ) :
    ∀ (S : Finset (Fin n)) (a : Fin n → ℕ),
      (∑ i ∈ S, a i) + S.card ≤ M →
      MultiLaurent.constantTerm (goodKernel n S a) = goodFormula S a := by
  induction M with
  | zero =>
      intro S a hM
      have hcard : S.card = 0 := by omega
      have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      subst S
      simp [goodKernel, goodFormula, MultiLaurent.constantTerm_apply,
        AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply]
  | succ M ih =>
      intro S a hM
      by_cases hsmall : (∑ i ∈ S, a i) + S.card ≤ M
      · exact ih S a hsmall
      by_cases hSempty : S = ∅
      · subst S
        simp [goodKernel, goodFormula, MultiLaurent.constantTerm_apply,
          AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply]
      have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
      by_cases hz : ∃ k ∈ S, a k = 0
      · obtain ⟨k, hk, hak⟩ := hz
        rw [constantTerm_goodKernel_boundary S a k hk hak,
          goodFormula_boundary S a k hk hak]
        apply ih (S.erase k) a
        have hsum : ∑ i ∈ S.erase k, a i = ∑ i ∈ S, a i := by
          rw [Finset.sum_eq_add_sum_diff_singleton hk, hak, zero_add]
          simp [Finset.erase_eq]
        have hcard : (S.erase k).card = S.card - 1 :=
          Finset.card_erase_of_mem hk
        have hcardpos : 0 < S.card := Finset.card_pos.mpr hS
        rw [hsum, hcard]
        omega
      · have ha : ∀ i ∈ S, 0 < a i := by
          intro i hi
          have : a i ≠ 0 := fun h => hz ⟨i, hi, h⟩
          omega
        rw [constantTerm_goodKernel_recurrence S hS a ha,
          goodFormula_recurrence S hS a ha]
        apply Finset.sum_congr rfl
        intro i hi
        apply ih S (goodDec a i)
        rw [sum_goodDec S a i hi (ha i hi)]
        have hTpos : 0 < ∑ j ∈ S, a j :=
          lt_of_lt_of_le (ha i hi)
            (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi)
        omega

theorem constantTerm_goodKernel {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℕ) :
    MultiLaurent.constantTerm (goodKernel n S a) = goodFormula S a := by
  exact constantTerm_goodKernel_aux ((∑ i ∈ S, a i) + S.card) S a le_rfl

def goodDecreasingPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.2 < p.1

lemma orderedPairs_eq_increasing_union_goodDecreasing (n : ℕ) :
    orderedPairs n = increasingPairs n ∪ goodDecreasingPairs n := by
  ext p
  simp only [orderedPairs, increasingPairs, goodDecreasingPairs,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  omega

lemma disjoint_increasing_goodDecreasing (n : ℕ) :
    Disjoint (increasingPairs n) (goodDecreasingPairs n) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  simp [increasingPairs, goodDecreasingPairs] at hp hq
  omega

lemma image_swap_increasingPairs_good (n : ℕ) :
    (increasingPairs n).image (fun p : Fin n × Fin n => (p.2, p.1)) =
      goodDecreasingPairs n := by
  ext p
  simp only [Finset.mem_image, increasingPairs, goodDecreasingPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨(p.2, p.1), hp, by simp⟩

lemma prod_goodDecreasingPairs_generic {R : Type*} [CommMonoid R]
    (n : ℕ) (f : Fin n × Fin n → R) :
    (∏ p ∈ goodDecreasingPairs n, f p) =
      ∏ p ∈ increasingPairs n, f (p.2, p.1) := by
  let swap : Fin n × Fin n → Fin n × Fin n := fun p => (p.2, p.1)
  have himage : (increasingPairs n).image swap = goodDecreasingPairs n :=
    image_swap_increasingPairs_good n
  rw [← himage, Finset.prod_image]
  intro p hp q hq heq
  simpa [swap] using congrArg swap heq

lemma prod_orderedPairs_generic {R : Type*} [CommMonoid R]
    (n : ℕ) (f : Fin n × Fin n → R) :
    (∏ p ∈ orderedPairs n, f p) =
      ∏ p ∈ increasingPairs n, f p * f (p.2, p.1) := by
  rw [orderedPairs_eq_increasing_union_goodDecreasing,
    Finset.prod_union (disjoint_increasing_goodDecreasing n),
    prod_goodDecreasingPairs_generic]
  rw [← Finset.prod_mul_distrib]

lemma goodKernel_univ_eq_ordered {n q : ℕ} :
    goodKernel n Finset.univ (fun _ => q) =
      ∏ p ∈ orderedPairs n, (1 - ratio p.1 p.2) ^ q := by
  classical
  unfold goodKernel orderedPairs
  simp only [Finset.prod_filter]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Fintype.prod_ite_mem]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, Ne.symm hji]

lemma goodFormula_univ_const (n q : ℕ) :
    goodFormula (Finset.univ : Finset (Fin n)) (fun _ => q) =
      (((n * q).factorial : ℚ) / (q.factorial : ℚ) ^ n) := by
  simp [goodFormula, Finset.sum_const, Finset.prod_const]

end LogarithmicMorrisFull
