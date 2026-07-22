import logarithmicmorris.ScratchShiftLocal
import logarithmicmorris.LogarithmicMorrisKOne
import laurent.Rename
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Vanishing of the logarithmic shift derivative

This file formalizes the remaining, genuinely logarithmic part of the
Adamović--Milas parameter-shift argument.  Everything here is finite: the
one-sided logarithmic coefficient is represented by `standardLogWeight`, and
the apparent infinite telescoping is proved monomial-by-monomial.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

set_option maxHeartbeats 1000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

@[simp] lemma renameExponent_equiv_apply {α : Type*} (σ : Equiv.Perm α)
    (e : MultiLaurent.Exponent α) (i : α) :
    MultiLaurent.renameExponent σ e i = e (σ.symm i) := by
  exact Finsupp.mapDomain_equiv_apply e i

@[simp] lemma rename_var_equiv {α : Type*} (σ : Equiv.Perm α)
    (i : α) :
    MultiLaurent.rename (R := ℚ) σ (MultiLaurent.var i) =
      MultiLaurent.var (σ i) := by
  rw [show (MultiLaurent.var i : MultiLaurent.Polynomial α ℚ) =
      MultiLaurent.monomial (Finsupp.single i 1) 1 by rfl,
    MultiLaurent.rename_monomial]
  congr 1
  exact Finsupp.mapDomain_single

@[simp] lemma rename_varInv_equiv {α : Type*} (σ : Equiv.Perm α)
    (i : α) :
    MultiLaurent.rename (R := ℚ) σ (MultiLaurent.varInv i) =
      MultiLaurent.varInv (σ i) := by
  rw [show (MultiLaurent.varInv i : MultiLaurent.Polynomial α ℚ) =
      MultiLaurent.monomial (Finsupp.single i (-1)) 1 by rfl,
    MultiLaurent.rename_monomial]
  congr 1
  exact Finsupp.mapDomain_single

lemma prod_increasingPairs_eq_prod_Ioi_local {R : Type*} [CommMonoid R]
    {n : ℕ} (f : Fin n → Fin n → R) :
    (∏ p ∈ increasingPairs n, f p.1 p.2) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
  simp only [increasingPairs, Finset.prod_filter]
  simp_rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
  exact (Finset.prod_product _ _ _).trans rfl

lemma vandermonde_eq_sign_det_local (n : ℕ) :
    (vandermonde (R := ℚ) n) =
      (-1 : Laurent ℚ n) ^ (increasingPairs n).card *
        (Matrix.vandermonde
          (fun i : Fin n => MultiLaurent.var (R := ℚ) i)).det := by
  rw [vandermonde, Matrix.det_vandermonde]
  rw [← prod_increasingPairs_eq_prod_Ioi_local]
  simp only [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  ring

lemma rename_vandermonde_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MultiLaurent.rename (R := ℚ) σ (vandermonde n) =
      ((σ.sign : ℤ) : Laurent ℚ n) * vandermonde n := by
  rw [vandermonde_eq_sign_det_local]
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [RingHom.map_det]
  have hmatrix :
      (Matrix.vandermonde
          (fun i : Fin n => MultiLaurent.var (R := ℚ) (σ i))) =
        (Matrix.vandermonde
          (fun i : Fin n => MultiLaurent.var (R := ℚ) i)).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  have hmapmatrix :
      (MultiLaurent.rename (R := ℚ) σ).mapMatrix
          (Matrix.vandermonde
            (fun i : Fin n => MultiLaurent.var (R := ℚ) i)) =
        Matrix.vandermonde
          (fun i : Fin n => MultiLaurent.var (R := ℚ) (σ i)) := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [hmapmatrix]
  rw [hmatrix, Matrix.det_permute]
  ring

lemma rename_localEndpointProduct_perm (n d t : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MultiLaurent.rename (R := ℚ) σ (localEndpointProduct n d t) =
      localEndpointProduct n d t := by
  unfold localEndpointProduct localEndpointFactor
  simp only [map_prod, map_mul, map_pow, map_sub, map_one,
    rename_varInv_equiv, rename_var_equiv]
  simpa using (Equiv.prod_comp σ
    (fun i : Fin n =>
      (MultiLaurent.varInv (R := ℚ) i : Laurent ℚ n) ^ d *
        (1 - MultiLaurent.var i) ^ t))

lemma rename_localMorrisCore_swap (S : Setup) (a b : ℕ)
    (u v : Fin S.n) (huv : u ≠ v) :
    MultiLaurent.rename (R := ℚ) (Equiv.swap u v)
        (localMorrisCore S a b) =
      -localMorrisCore S a b := by
  unfold localMorrisCore
  rw [map_mul, map_pow, rename_vandermonde_perm,
    rename_localEndpointProduct_perm]
  rw [Equiv.Perm.sign_swap huv]
  have hodd : (-1 : Laurent ℚ S.n) ^ S.K = -1 := by
    rw [Setup.K, pow_succ, pow_mul]
    norm_num
  norm_num
  rw [neg_pow, hodd]
  ring

lemma rename_morrisKernel_swap (S : Setup) (a b : ℕ)
    (u v : Fin S.n) (huv : u ≠ v) :
    MultiLaurent.rename (R := ℚ) (Equiv.swap u v)
        (morrisKernel (S.withAB a b)) =
      -morrisKernel (S.withAB a b) := by
  rw [morrisKernel_withAB_eq_sign_mul_core]
  rw [map_mul]
  rw [rename_localMorrisCore_swap S a b u v huv]
  have hsign : MultiLaurent.rename (R := ℚ) (Equiv.swap u v)
      (localMorrisSign S b) = localMorrisSign S b := by
    simp [localMorrisSign]
  rw [hsign]
  ring

lemma Setup.withAB_self (S : Setup) : S.withAB S.a S.b = S := by
  cases S
  rfl

lemma rename_morrisKernel_swap_any (S : Setup)
    (u v : Fin S.n) (huv : u ≠ v) :
    MultiLaurent.rename (R := ℚ) (Equiv.swap u v) (morrisKernel S) =
      -morrisKernel S := by
  have h := rename_morrisKernel_swap S S.a S.b u v huv
  simpa [S.withAB_self] using h

lemma Setup.leftVertex_injective (S : Setup) :
    Function.Injective S.leftVertex := by
  intro p q hpq
  apply Fin.ext
  have h := congrArg Fin.val hpq
  simp [Setup.leftVertex] at h
  omega

lemma Setup.rightVertex_injective (S : Setup) :
    Function.Injective S.rightVertex := by
  intro p q hpq
  apply Fin.ext
  have h := congrArg Fin.val hpq
  simp [Setup.rightVertex] at h
  omega

lemma Setup.leftVertex_ne_rightVertex (S : Setup)
    (p q : Fin S.m) : S.leftVertex p ≠ S.rightVertex q := by
  intro h
  have hv := congrArg Fin.val h
  simp [Setup.leftVertex, Setup.rightVertex] at hv
  omega

lemma Setup.rightVertex_ne_leftVertex (S : Setup)
    (p q : Fin S.m) : S.rightVertex p ≠ S.leftVertex q :=
  (S.leftVertex_ne_rightVertex q p).symm

lemma Setup.leftVertex_ne_lastVertex (S : Setup)
    (p : Fin S.m) : S.leftVertex p ≠ S.lastVertex := by
  intro h
  have hv := congrArg Fin.val h
  simp [Setup.leftVertex, Setup.lastVertex] at hv
  omega

lemma Setup.rightVertex_ne_lastVertex (S : Setup)
    (p : Fin S.m) : S.rightVertex p ≠ S.lastVertex := by
  intro h
  have hv := congrArg Fin.val h
  simp [Setup.rightVertex, Setup.lastVertex] at hv
  omega

def leftLastSwap (S : Setup) (q : Fin S.m) : Equiv.Perm (Fin S.n) :=
  Equiv.swap (S.leftVertex q) S.lastVertex

def rightLastSwap (S : Setup) (q : Fin S.m) : Equiv.Perm (Fin S.n) :=
  Equiv.swap (S.rightVertex q) S.lastVertex

@[simp] lemma leftLastSwap_left (S : Setup) (q : Fin S.m) :
    leftLastSwap S q (S.leftVertex q) = S.lastVertex := by
  simp [leftLastSwap]

@[simp] lemma leftLastSwap_last (S : Setup) (q : Fin S.m) :
    leftLastSwap S q S.lastVertex = S.leftVertex q := by
  simp [leftLastSwap]

@[simp] lemma leftLastSwap_right (S : Setup) (q : Fin S.m) :
    leftLastSwap S q (S.rightVertex q) = S.rightVertex q := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact S.rightVertex_ne_leftVertex q q
  · exact S.rightVertex_ne_lastVertex q

@[simp] lemma leftLastSwap_left_other (S : Setup) (q p : Fin S.m)
    (hpq : p ≠ q) :
    leftLastSwap S q (S.leftVertex p) = S.leftVertex p := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun h => hpq (S.leftVertex_injective h)
  · exact S.leftVertex_ne_lastVertex p

@[simp] lemma leftLastSwap_right_other (S : Setup) (q p : Fin S.m) :
    leftLastSwap S q (S.rightVertex p) = S.rightVertex p := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact S.rightVertex_ne_leftVertex p q
  · exact S.rightVertex_ne_lastVertex p

@[simp] lemma rightLastSwap_right (S : Setup) (q : Fin S.m) :
    rightLastSwap S q (S.rightVertex q) = S.lastVertex := by
  simp [rightLastSwap]

@[simp] lemma rightLastSwap_last (S : Setup) (q : Fin S.m) :
    rightLastSwap S q S.lastVertex = S.rightVertex q := by
  simp [rightLastSwap]

@[simp] lemma rightLastSwap_left (S : Setup) (q : Fin S.m) :
    rightLastSwap S q (S.leftVertex q) = S.leftVertex q := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact S.leftVertex_ne_rightVertex q q
  · exact S.leftVertex_ne_lastVertex q

@[simp] lemma rightLastSwap_left_other (S : Setup) (q p : Fin S.m) :
    rightLastSwap S q (S.leftVertex p) = S.leftVertex p := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact S.leftVertex_ne_rightVertex p q
  · exact S.leftVertex_ne_lastVertex p

@[simp] lemma rightLastSwap_right_other (S : Setup) (q p : Fin S.m)
    (hpq : p ≠ q) :
    rightLastSwap S q (S.rightVertex p) = S.rightVertex p := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun h => hpq (S.rightVertex_injective h)
  · exact S.rightVertex_ne_lastVertex p

@[simp] lemma leftLastSwap_symm (S : Setup) (q : Fin S.m) :
    (leftLastSwap S q).symm = leftLastSwap S q := by
  simp [leftLastSwap]

@[simp] lemma rightLastSwap_symm (S : Setup) (q : Fin S.m) :
    (rightLastSwap S q).symm = rightLastSwap S q := by
  simp [rightLastSwap]

@[simp] lemma renameExponent_leftLast_left (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    MultiLaurent.renameExponent (leftLastSwap S q) e (S.leftVertex q) =
      e S.lastVertex := by
  rw [renameExponent_equiv_apply, leftLastSwap_symm, leftLastSwap_left]

@[simp] lemma renameExponent_leftLast_right (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    MultiLaurent.renameExponent (leftLastSwap S q) e (S.rightVertex q) =
      e (S.rightVertex q) := by
  rw [renameExponent_equiv_apply, leftLastSwap_symm, leftLastSwap_right]

@[simp] lemma renameExponent_leftLast_last (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    MultiLaurent.renameExponent (leftLastSwap S q) e S.lastVertex =
      e (S.leftVertex q) := by
  rw [renameExponent_equiv_apply, leftLastSwap_symm, leftLastSwap_last]

@[simp] lemma renameExponent_leftLast_left_other (S : Setup)
    (q p : Fin S.m) (hpq : p ≠ q) (e : Exponent S.n) :
    MultiLaurent.renameExponent (leftLastSwap S q) e (S.leftVertex p) =
      e (S.leftVertex p) := by
  rw [renameExponent_equiv_apply, leftLastSwap_symm,
    leftLastSwap_left_other S q p hpq]

@[simp] lemma renameExponent_leftLast_right_other (S : Setup)
    (q p : Fin S.m) (e : Exponent S.n) :
    MultiLaurent.renameExponent (leftLastSwap S q) e (S.rightVertex p) =
      e (S.rightVertex p) := by
  rw [renameExponent_equiv_apply, leftLastSwap_symm,
    leftLastSwap_right_other]

@[simp] lemma renameExponent_rightLast_left (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    MultiLaurent.renameExponent (rightLastSwap S q) e (S.leftVertex q) =
      e (S.leftVertex q) := by
  rw [renameExponent_equiv_apply, rightLastSwap_symm, rightLastSwap_left]

@[simp] lemma renameExponent_rightLast_right (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    MultiLaurent.renameExponent (rightLastSwap S q) e (S.rightVertex q) =
      e S.lastVertex := by
  rw [renameExponent_equiv_apply, rightLastSwap_symm, rightLastSwap_right]

@[simp] lemma renameExponent_rightLast_last (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    MultiLaurent.renameExponent (rightLastSwap S q) e S.lastVertex =
      e (S.rightVertex q) := by
  rw [renameExponent_equiv_apply, rightLastSwap_symm, rightLastSwap_last]

@[simp] lemma renameExponent_rightLast_left_other (S : Setup)
    (q p : Fin S.m) (e : Exponent S.n) :
    MultiLaurent.renameExponent (rightLastSwap S q) e (S.leftVertex p) =
      e (S.leftVertex p) := by
  rw [renameExponent_equiv_apply, rightLastSwap_symm,
    rightLastSwap_left_other]

@[simp] lemma renameExponent_rightLast_right_other (S : Setup)
    (q p : Fin S.m) (hpq : p ≠ q) (e : Exponent S.n) :
    MultiLaurent.renameExponent (rightLastSwap S q) e (S.rightVertex p) =
      e (S.rightVertex p) := by
  rw [renameExponent_equiv_apply, rightLastSwap_symm,
    rightLastSwap_right_other S q p hpq]

lemma standardLogCT_monomial_clean (S : Setup)
    (e : Exponent S.n) (c : ℚ) :
    standardLogCT S (MultiLaurent.monomial e c) =
      c * standardLogWeight S e := by
  exact standardLogCT_monomial S e c

lemma standardLogCT_neg_clean (S : Setup) (F : Laurent ℚ S.n) :
    standardLogCT S (-F) = -standardLogCT S F := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [standardLogCT_eq_finsupp_sum]
  | hadd F G hF hG =>
      rw [show -(F + G) = -F + -G by abel,
        standardLogCT_add_clean, hF, hG,
        standardLogCT_add_clean]
      ring
  | hmono e c =>
      rw [show -MultiLaurent.monomial e c =
          MultiLaurent.monomial e (-c) by
        ext d
        by_cases hde : d = e <;>
          simp [MultiLaurent.monomial, hde]]
      rw [standardLogCT_monomial_clean,
        standardLogCT_monomial_clean]
      ring

lemma standardLogCT_smul_clean (S : Setup) (c : ℚ)
    (F : Laurent ℚ S.n) :
    standardLogCT S (c • F) = c * standardLogCT S F := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [standardLogCT_eq_finsupp_sum]
  | hadd F G hF hG =>
      simp [smul_add, standardLogCT_add_clean, hF, hG]
      ring
  | hmono e d =>
      rw [local_smul_monomial, standardLogCT_monomial_clean,
        standardLogCT_monomial_clean]
      ring

lemma standardLogCT_sub_clean (S : Setup) (F G : Laurent ℚ S.n) :
    standardLogCT S (F - G) = standardLogCT S F - standardLogCT S G := by
  rw [sub_eq_add_neg, standardLogCT_add_clean, standardLogCT_neg_clean]
  ring

/-- The admissibility conditions for all logarithmic pairs except `q`, plus
the condition at the unmatched final vertex. -/
def OtherLogAdmissible (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) : Prop :=
  (∀ p : Fin S.m, p ≠ q →
      0 < e (S.leftVertex p) ∧
        e (S.rightVertex p) = -e (S.leftVertex p)) ∧
    e S.lastVertex = 0

/-- Coefficient functional after omitting the logarithm belonging to `q`.
The two vertices of that pair and the unmatched vertex are all constrained to
exponent zero. -/
def OmittedLogAdmissible (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) : Prop :=
  e (S.leftVertex q) = 0 ∧ e (S.rightVertex q) = 0 ∧
    OtherLogAdmissible S q e

def omittedLogWeight (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) : ℚ := by
  classical
  exact if OmittedLogAdmissible S q e then
      ∏ p ∈ (Finset.univ : Finset (Fin S.m)).erase q,
        (-1 : ℚ) / (e (S.leftVertex p) : ℚ)
    else 0

def omittedLogCT (S : Setup) (q : Fin S.m)
    (F : Laurent ℚ S.n) : ℚ :=
  F.sum fun e c => c * omittedLogWeight S q e

lemma omittedLogCT_zero (S : Setup) (q : Fin S.m) :
    omittedLogCT S q (0 : Laurent ℚ S.n) = 0 := by
  simp [omittedLogCT]

lemma omittedLogCT_add (S : Setup) (q : Fin S.m)
    (F G : Laurent ℚ S.n) :
    omittedLogCT S q (F + G) =
      omittedLogCT S q F + omittedLogCT S q G := by
  classical
  unfold omittedLogCT
  rw [Finsupp.sum_add_index (h_zero := fun e => by simp)
    (h_add := fun e he c d => by ring)]

lemma omittedLogCT_monomial (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) (c : ℚ) :
    omittedLogCT S q (MultiLaurent.monomial e c) =
      c * omittedLogWeight S q e := by
  classical
  simp [omittedLogCT, MultiLaurent.monomial]

lemma omittedLogCT_neg (S : Setup) (q : Fin S.m)
    (F : Laurent ℚ S.n) :
    omittedLogCT S q (-F) = -omittedLogCT S q F := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [omittedLogCT_zero]
  | hadd F G hF hG => simp [omittedLogCT_add, hF, hG]
  | hmono e c =>
      rw [show -MultiLaurent.monomial e c =
          MultiLaurent.monomial e (-c) by
        ext d
        by_cases hde : d = e <;>
          simp [MultiLaurent.monomial, hde]]
      rw [omittedLogCT_monomial, omittedLogCT_monomial]
      ring

lemma omittedLogCT_sub (S : Setup) (q : Fin S.m)
    (F G : Laurent ℚ S.n) :
    omittedLogCT S q (F - G) =
      omittedLogCT S q F - omittedLogCT S q G := by
  rw [sub_eq_add_neg, omittedLogCT_add, omittedLogCT_neg]
  ring

/-- Increase the left exponent and decrease the right exponent of pair `q`.
This is the exponent shift between the two adjacent terms in the finite
telescoping argument. -/
def pairShiftExponent (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) : Exponent S.n :=
  e + Finsupp.single (S.leftVertex q) 1 -
    Finsupp.single (S.rightVertex q) 1

@[simp] lemma pairShiftExponent_left (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    pairShiftExponent S q e (S.leftVertex q) =
      e (S.leftVertex q) + 1 := by
  simp [pairShiftExponent, Finsupp.single_apply,
    S.leftVertex_ne_rightVertex q q]

@[simp] lemma pairShiftExponent_right (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    pairShiftExponent S q e (S.rightVertex q) =
      e (S.rightVertex q) - 1 := by
  simp [pairShiftExponent, Finsupp.single_apply,
    S.rightVertex_ne_leftVertex q q]

@[simp] lemma pairShiftExponent_left_other (S : Setup) (q p : Fin S.m)
    (hpq : p ≠ q) (e : Exponent S.n) :
    pairShiftExponent S q e (S.leftVertex p) =
      e (S.leftVertex p) := by
  have hll : S.leftVertex p ≠ S.leftVertex q :=
    fun h => hpq (S.leftVertex_injective h)
  have hlr := S.leftVertex_ne_rightVertex p q
  simp [pairShiftExponent, Finsupp.single_apply, hll, hlr]

@[simp] lemma pairShiftExponent_right_other (S : Setup) (q p : Fin S.m)
    (hpq : p ≠ q) (e : Exponent S.n) :
    pairShiftExponent S q e (S.rightVertex p) =
      e (S.rightVertex p) := by
  have hrl := S.rightVertex_ne_leftVertex p q
  have hrr : S.rightVertex p ≠ S.rightVertex q :=
    fun h => hpq (S.rightVertex_injective h)
  simp [pairShiftExponent, Finsupp.single_apply, hrl, hrr]

@[simp] lemma pairShiftExponent_last (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    pairShiftExponent S q e S.lastVertex = e S.lastVertex := by
  have hlastl := (S.leftVertex_ne_lastVertex q).symm
  have hlastr := (S.rightVertex_ne_lastVertex q).symm
  simp [pairShiftExponent, Finsupp.single_apply, hlastl, hlastr]

lemma standardLogAdmissible_iff_pair_other (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    StandardLogAdmissible S e ↔
      (0 < e (S.leftVertex q) ∧
        e (S.rightVertex q) = -e (S.leftVertex q)) ∧
        OtherLogAdmissible S q e := by
  constructor
  · rintro ⟨hpairs, hlast⟩
    exact ⟨hpairs q, ⟨fun p _hpq => hpairs p, hlast⟩⟩
  · rintro ⟨hq, hother, hlast⟩
    constructor
    · intro p
      by_cases hpq : p = q
      · simpa [hpq] using hq
      · exact hother p hpq
    · exact hlast

lemma otherLogAdmissible_pairShift_iff (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    OtherLogAdmissible S q (pairShiftExponent S q e) ↔
      OtherLogAdmissible S q e := by
  constructor
  · rintro ⟨hpairs, hlast⟩
    constructor
    · intro p hpq
      simpa [pairShiftExponent_left_other S q p hpq,
        pairShiftExponent_right_other S q p hpq] using hpairs p hpq
    · simpa using hlast
  · rintro ⟨hpairs, hlast⟩
    constructor
    · intro p hpq
      simpa [pairShiftExponent_left_other S q p hpq,
        pairShiftExponent_right_other S q p hpq] using hpairs p hpq
    · simpa using hlast

lemma standardLogAdmissible_pairShift_iff (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    StandardLogAdmissible S (pairShiftExponent S q e) ↔
      (0 ≤ e (S.leftVertex q) ∧
        e (S.rightVertex q) = -e (S.leftVertex q)) ∧
        OtherLogAdmissible S q e := by
  rw [standardLogAdmissible_iff_pair_other S q,
    otherLogAdmissible_pairShift_iff]
  simp only [pairShiftExponent_left, pairShiftExponent_right]
  constructor
  · rintro ⟨⟨hpos, heq⟩, hother⟩
    exact ⟨⟨by omega, by omega⟩, hother⟩
  · rintro ⟨⟨hnonneg, heq⟩, hother⟩
    exact ⟨⟨by omega, by omega⟩, hother⟩

def otherLogProduct (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) : ℚ :=
  ∏ p ∈ (Finset.univ : Finset (Fin S.m)).erase q,
    (-1 : ℚ) / (e (S.leftVertex p) : ℚ)

lemma standardLogWeight_pair_formula (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    standardLogWeight S e =
      if (0 < e (S.leftVertex q) ∧
          e (S.rightVertex q) = -e (S.leftVertex q)) ∧
          OtherLogAdmissible S q e then
        ((-1 : ℚ) / (e (S.leftVertex q) : ℚ)) *
          otherLogProduct S q e
      else 0 := by
  classical
  unfold standardLogWeight
  rw [standardLogAdmissible_iff_pair_other S q e]
  split_ifs with h
  · unfold otherLogProduct
    rw [Finset.mul_prod_erase (Finset.univ : Finset (Fin S.m))
      (fun p => (-1 : ℚ) / (e (S.leftVertex p) : ℚ))
      (Finset.mem_univ q)]
  · rfl

lemma standardLogWeight_pairShift_formula (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    standardLogWeight S (pairShiftExponent S q e) =
      if (0 ≤ e (S.leftVertex q) ∧
          e (S.rightVertex q) = -e (S.leftVertex q)) ∧
          OtherLogAdmissible S q e then
        ((-1 : ℚ) / ((e (S.leftVertex q) + 1 : ℤ) : ℚ)) *
          otherLogProduct S q e
      else 0 := by
  classical
  unfold standardLogWeight
  rw [standardLogAdmissible_pairShift_iff S q e]
  split_ifs with h
  · rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin S.m))
      (fun p => (-1 : ℚ) /
        ((pairShiftExponent S q e) (S.leftVertex p) : ℚ))
      (Finset.mem_univ q)]
    rw [pairShiftExponent_left]
    congr 1
    unfold otherLogProduct
    apply Finset.prod_congr rfl
    intro p hp
    have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
    rw [pairShiftExponent_left_other S q p hpq]
  · rfl

lemma omittedLogWeight_formula (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    omittedLogWeight S q e =
      if e (S.leftVertex q) = 0 ∧ e (S.rightVertex q) = 0 ∧
          OtherLogAdmissible S q e then
        otherLogProduct S q e
      else 0 := by
  classical
  unfold omittedLogWeight OmittedLogAdmissible otherLogProduct
  by_cases h : e (S.leftVertex q) = 0 ∧ e (S.rightVertex q) = 0 ∧
      OtherLogAdmissible S q e <;> simp [h]

/-- The finite one-step telescoping identity behind a single logarithmic
pair.  The second exponent is obtained from the first by moving one unit from
the right variable to the left variable. -/
lemma logarithmicWeight_telescope (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    ((e (S.leftVertex q) : ℤ) : ℚ) * standardLogWeight S e -
        (((e (S.leftVertex q) + 1 : ℤ) : ℚ) *
          standardLogWeight S (pairShiftExponent S q e)) =
      omittedLogWeight S q e := by
  rw [standardLogWeight_pair_formula,
    standardLogWeight_pairShift_formula,
    omittedLogWeight_formula]
  by_cases hother : OtherLogAdmissible S q e
  · by_cases hrel : e (S.rightVertex q) = -e (S.leftVertex q)
    · by_cases hpos : 0 < e (S.leftVertex q)
      · have hnonneg : 0 ≤ e (S.leftVertex q) := le_of_lt hpos
        have hne : ((e (S.leftVertex q) : ℤ) : ℚ) ≠ 0 := by
          exact_mod_cast (ne_of_gt hpos)
        have hne1 : (((e (S.leftVertex q) + 1 : ℤ) : ℚ)) ≠ 0 := by
          exact_mod_cast (by omega : e (S.leftVertex q) + 1 ≠ 0)
        have hl0 : e (S.leftVertex q) ≠ 0 := ne_of_gt hpos
        have hstd :
            (0 < e (S.leftVertex q) ∧
              e (S.rightVertex q) = -e (S.leftVertex q)) ∧
              OtherLogAdmissible S q e := ⟨⟨hpos, hrel⟩, hother⟩
        have hshift :
            (0 ≤ e (S.leftVertex q) ∧
              e (S.rightVertex q) = -e (S.leftVertex q)) ∧
              OtherLogAdmissible S q e := ⟨⟨hnonneg, hrel⟩, hother⟩
        have homit : ¬(e (S.leftVertex q) = 0 ∧
            e (S.rightVertex q) = 0 ∧ OtherLogAdmissible S q e) := by
          intro h
          exact hl0 h.1
        rw [if_pos hstd, if_pos hshift, if_neg homit]
        field_simp
        ring
      · by_cases hzero : e (S.leftVertex q) = 0
        · have hright : e (S.rightVertex q) = 0 := by omega
          have hnonneg : 0 ≤ e (S.leftVertex q) := by omega
          simp [hpos, hzero, hright, hrel, hother, hnonneg]
        · have hneg : e (S.leftVertex q) < 0 := by omega
          have hnnonneg : ¬0 ≤ e (S.leftVertex q) := by omega
          simp [hpos, hzero, hneg, hnnonneg, hrel, hother]
    · have homit : ¬(e (S.leftVertex q) = 0 ∧
          e (S.rightVertex q) = 0) := by
        rintro ⟨hl, hr⟩
        apply hrel
        omega
      simp [hother, hrel, homit]
  · simp [hother]

def rightInsertedExponent (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) : Exponent S.n :=
  Finsupp.single (S.rightVertex q) 1 + e

@[simp] lemma rightInsertedExponent_left (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    rightInsertedExponent S q e (S.leftVertex q) =
      e (S.leftVertex q) := by
  simp [rightInsertedExponent, Finsupp.single_apply,
    S.leftVertex_ne_rightVertex q q]

@[simp] lemma rightInsertedExponent_right (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    rightInsertedExponent S q e (S.rightVertex q) =
      e (S.rightVertex q) + 1 := by
  simp [rightInsertedExponent]
  ring

lemma pairShift_rightInsertedExponent (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    pairShiftExponent S q (rightInsertedExponent S q e) =
      Finsupp.single (S.leftVertex q) 1 + e := by
  ext i
  by_cases hir : i = S.rightVertex q
  · subst i
    simp [pairShiftExponent, rightInsertedExponent,
      Finsupp.single_apply, S.rightVertex_ne_leftVertex q q]
  · by_cases hil : i = S.leftVertex q
    · subst i
      simp [pairShiftExponent, rightInsertedExponent,
        Finsupp.single_apply, S.leftVertex_ne_rightVertex q q]
      ring
    · simp [pairShiftExponent, rightInsertedExponent,
        Finsupp.single_apply, hir, hil]

lemma var_mul_monomial_local {n : ℕ} (i : Fin n)
    (e : Exponent n) (c : ℚ) :
    (MultiLaurent.var i : Laurent ℚ n) * MultiLaurent.monomial e c =
      MultiLaurent.monomial (Finsupp.single i 1 + e) c := by
  rw [show (MultiLaurent.var i : Laurent ℚ n) =
    MultiLaurent.monomial (Finsupp.single i 1) 1 by rfl]
  rw [MultiLaurent.monomial_mul_monomial]
  simp

lemma difference_mul_monomial_pair (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) (c : ℚ) :
    ((MultiLaurent.var (S.rightVertex q) -
        MultiLaurent.var (S.leftVertex q)) : Laurent ℚ S.n) *
        MultiLaurent.monomial e c =
      MultiLaurent.monomial (rightInsertedExponent S q e) c -
        MultiLaurent.monomial
          (pairShiftExponent S q (rightInsertedExponent S q e)) c := by
  rw [sub_mul, var_mul_monomial_local, var_mul_monomial_local]
  rw [pairShift_rightInsertedExponent]
  rfl

/-- A logarithmic pair turns the Euler derivative of a difference factor
into the boundary functional with that logarithm omitted.  The proof is
finite induction over Laurent monomials. -/
lemma standardLogCT_localEuler_pairDifference (S : Setup) (q : Fin S.m)
    (G : Laurent ℚ S.n) :
    standardLogCT S
        (localEuler (S.leftVertex q)
          ((MultiLaurent.var (S.rightVertex q) -
              MultiLaurent.var (S.leftVertex q)) * G)) =
      omittedLogCT S q
        (MultiLaurent.var (S.rightVertex q) * G) := by
  induction G using MultiLaurent.induction_on with
  | h0 => simp [localEuler_zero, standardLogCT_eq_finsupp_sum,
      omittedLogCT_zero]
  | hadd F G hF hG =>
      rw [mul_add, localEuler_add, standardLogCT_add_clean,
        hF, hG, mul_add, omittedLogCT_add]
  | hmono e c =>
      let d := rightInsertedExponent S q e
      rw [difference_mul_monomial_pair, localEuler_sub,
        localEuler_monomial, localEuler_monomial,
        standardLogCT_sub_clean,
        standardLogCT_monomial_clean,
        standardLogCT_monomial_clean,
        var_mul_monomial_local,
        omittedLogCT_monomial]
      change
        (((d (S.leftVertex q) : ℤ) : ℚ) * c) *
              standardLogWeight S d -
            ((((pairShiftExponent S q d) (S.leftVertex q) : ℤ) : ℚ) * c) *
              standardLogWeight S (pairShiftExponent S q d) =
          c * omittedLogWeight S q d
      rw [pairShiftExponent_left]
      have htel := logarithmicWeight_telescope S q d
      linear_combination c * htel

lemma standardLogCT_rightEuler_eq_neg_leftEuler (S : Setup)
    (q : Fin S.m) (F : Laurent ℚ S.n) :
    standardLogCT S (localEuler (S.rightVertex q) F) =
      -standardLogCT S (localEuler (S.leftVertex q) F) := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [localEuler_zero, standardLogCT_eq_finsupp_sum]
  | hadd F G hF hG =>
      rw [localEuler_add, localEuler_add,
        standardLogCT_add_clean, standardLogCT_add_clean,
        hF, hG]
      ring
  | hmono e c =>
      rw [localEuler_monomial, localEuler_monomial,
        standardLogCT_monomial_clean, standardLogCT_monomial_clean]
      unfold standardLogWeight
      by_cases hadm : StandardLogAdmissible S e
      · rw [if_pos hadm]
        have hpair := hadm.1 q
        rw [hpair.2]
        push_cast
        ring
      · rw [if_neg hadm]
        ring

lemma standardLogCT_pairEuler_eq_difference (S : Setup) (q : Fin S.m)
    (A B : Laurent ℚ S.n) :
    standardLogCT S
        (localEuler (S.leftVertex q) A +
          localEuler (S.rightVertex q) B) =
      standardLogCT S (localEuler (S.leftVertex q) (A - B)) := by
  rw [standardLogCT_add_clean,
    standardLogCT_rightEuler_eq_neg_leftEuler,
    localEuler_sub, standardLogCT_sub_clean]
  ring

/-- The contribution of one logarithmic pair to the summed shift derivative
is the three-variable boundary term appearing in the paper. -/
lemma standardLogCT_shiftDerivative_pair (S : Setup) (a b r : ℕ)
    (q : Fin S.m) :
    standardLogCT (S.withAB a b)
        (localEuler ((S.withAB a b).leftVertex q)
            (localShiftFactor (S.withAB a b).n r
                ((S.withAB a b).leftVertex q) *
              morrisKernel (S.withAB a b)) +
          localEuler ((S.withAB a b).rightVertex q)
            (localShiftFactor (S.withAB a b).n r
                ((S.withAB a b).rightVertex q) *
              morrisKernel (S.withAB a b))) =
      omittedLogCT (S.withAB a b) q
        (MultiLaurent.var ((S.withAB a b).rightVertex q) *
          (localPairLogRemainder (S.withAB a b).n r
              ((S.withAB a b).leftVertex q)
              ((S.withAB a b).rightVertex q) *
            morrisKernel (S.withAB a b))) := by
  let Sab : Setup := S.withAB a b
  change standardLogCT Sab
      (localEuler (Sab.leftVertex q)
          (localShiftFactor Sab.n r (Sab.leftVertex q) * morrisKernel Sab) +
        localEuler (Sab.rightVertex q)
          (localShiftFactor Sab.n r (Sab.rightVertex q) * morrisKernel Sab)) =
    omittedLogCT Sab q
      (MultiLaurent.var (Sab.rightVertex q) *
        (localPairLogRemainder Sab.n r (Sab.leftVertex q)
            (Sab.rightVertex q) * morrisKernel Sab))
  rw [standardLogCT_pairEuler_eq_difference]
  rw [show localShiftFactor Sab.n r (Sab.leftVertex q) * morrisKernel Sab -
      localShiftFactor Sab.n r (Sab.rightVertex q) * morrisKernel Sab =
        (MultiLaurent.var (Sab.rightVertex q) -
            MultiLaurent.var (Sab.leftVertex q)) *
          (localPairLogRemainder Sab.n r (Sab.leftVertex q)
              (Sab.rightVertex q) * morrisKernel Sab) by
    rw [← sub_mul]
    rw [localShiftFactor_sub_factor Sab.n r
      (Sab.leftVertex q) (Sab.rightVertex q)
      (Sab.leftVertex_ne_rightVertex q q)]
    ring]
  exact standardLogCT_localEuler_pairDifference Sab q _

lemma omittedLogAdmissible_rename_leftLast_iff (S : Setup)
    (q : Fin S.m) (e : Exponent S.n) :
    OmittedLogAdmissible S q
        (MultiLaurent.renameExponent (leftLastSwap S q) e) ↔
      OmittedLogAdmissible S q e := by
  constructor
  · rintro ⟨hl, hr, hpairs, hlast⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hlast
    · simpa using hr
    · intro p hpq
      simpa [renameExponent_leftLast_left_other S q p hpq,
        renameExponent_leftLast_right_other S q p] using hpairs p hpq
    · simpa using hl
  · rintro ⟨hl, hr, hpairs, hlast⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hlast
    · simpa using hr
    · intro p hpq
      simpa [renameExponent_leftLast_left_other S q p hpq,
        renameExponent_leftLast_right_other S q p] using hpairs p hpq
    · simpa using hl

lemma omittedLogAdmissible_rename_rightLast_iff (S : Setup)
    (q : Fin S.m) (e : Exponent S.n) :
    OmittedLogAdmissible S q
        (MultiLaurent.renameExponent (rightLastSwap S q) e) ↔
      OmittedLogAdmissible S q e := by
  constructor
  · rintro ⟨hl, hr, hpairs, hlast⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hl
    · simpa using hlast
    · intro p hpq
      simpa [renameExponent_rightLast_left_other S q p,
        renameExponent_rightLast_right_other S q p hpq] using hpairs p hpq
    · simpa using hr
  · rintro ⟨hl, hr, hpairs, hlast⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hl
    · simpa using hlast
    · intro p hpq
      simpa [renameExponent_rightLast_left_other S q p,
        renameExponent_rightLast_right_other S q p hpq] using hpairs p hpq
    · simpa using hr

lemma otherLogProduct_rename_leftLast (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    otherLogProduct S q
        (MultiLaurent.renameExponent (leftLastSwap S q) e) =
      otherLogProduct S q e := by
  unfold otherLogProduct
  apply Finset.prod_congr rfl
  intro p hp
  have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
  rw [renameExponent_leftLast_left_other S q p hpq]

lemma otherLogProduct_rename_rightLast (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    otherLogProduct S q
        (MultiLaurent.renameExponent (rightLastSwap S q) e) =
      otherLogProduct S q e := by
  unfold otherLogProduct
  apply Finset.prod_congr rfl
  intro p hp
  rw [renameExponent_rightLast_left_other S q p]

lemma omittedLogWeight_rename_leftLast (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    omittedLogWeight S q
        (MultiLaurent.renameExponent (leftLastSwap S q) e) =
      omittedLogWeight S q e := by
  classical
  unfold omittedLogWeight
  by_cases h : OmittedLogAdmissible S q e
  · rw [if_pos h,
      if_pos ((omittedLogAdmissible_rename_leftLast_iff S q e).mpr h)]
    exact otherLogProduct_rename_leftLast S q e
  · rw [if_neg h,
      if_neg (fun hren => h
        ((omittedLogAdmissible_rename_leftLast_iff S q e).mp hren))]

lemma omittedLogWeight_rename_rightLast (S : Setup) (q : Fin S.m)
    (e : Exponent S.n) :
    omittedLogWeight S q
        (MultiLaurent.renameExponent (rightLastSwap S q) e) =
      omittedLogWeight S q e := by
  classical
  unfold omittedLogWeight
  by_cases h : OmittedLogAdmissible S q e
  · rw [if_pos h,
      if_pos ((omittedLogAdmissible_rename_rightLast_iff S q e).mpr h)]
    exact otherLogProduct_rename_rightLast S q e
  · rw [if_neg h,
      if_neg (fun hren => h
        ((omittedLogAdmissible_rename_rightLast_iff S q e).mp hren))]

lemma omittedLogCT_rename_leftLast (S : Setup) (q : Fin S.m)
    (F : Laurent ℚ S.n) :
    omittedLogCT S q
        (MultiLaurent.rename (R := ℚ) (leftLastSwap S q) F) =
      omittedLogCT S q F := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [omittedLogCT_zero]
  | hadd F G hF hG =>
      rw [map_add, omittedLogCT_add, omittedLogCT_add, hF, hG]
  | hmono e c =>
      rw [MultiLaurent.rename_monomial,
        omittedLogCT_monomial, omittedLogCT_monomial,
        omittedLogWeight_rename_leftLast]

lemma omittedLogCT_rename_rightLast (S : Setup) (q : Fin S.m)
    (F : Laurent ℚ S.n) :
    omittedLogCT S q
        (MultiLaurent.rename (R := ℚ) (rightLastSwap S q) F) =
      omittedLogCT S q F := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [omittedLogCT_zero]
  | hadd F G hF hG =>
      rw [map_add, omittedLogCT_add, omittedLogCT_add, hF, hG]
  | hmono e c =>
      rw [MultiLaurent.rename_monomial,
        omittedLogCT_monomial, omittedLogCT_monomial,
        omittedLogWeight_rename_rightLast]

lemma omittedLogCT_eq_zero_of_leftLast_antisymmetric (S : Setup)
    (q : Fin S.m) (F : Laurent ℚ S.n)
    (hanti : MultiLaurent.rename (R := ℚ) (leftLastSwap S q) F = -F) :
    omittedLogCT S q F = 0 := by
  have hinv := omittedLogCT_rename_leftLast S q F
  rw [hanti, omittedLogCT_neg] at hinv
  linarith

lemma omittedLogCT_eq_zero_of_rightLast_antisymmetric (S : Setup)
    (q : Fin S.m) (F : Laurent ℚ S.n)
    (hanti : MultiLaurent.rename (R := ℚ) (rightLastSwap S q) F = -F) :
    omittedLogCT S q F = 0 := by
  have hinv := omittedLogCT_rename_rightLast S q F
  rw [hanti, omittedLogCT_neg] at hinv
  linarith

lemma omittedLogCT_finset_sum (S : Setup) (q : Fin S.m)
    {I : Type*} (s : Finset I) (F : I → Laurent ℚ S.n) :
    omittedLogCT S q (∑ i ∈ s, F i) =
      ∑ i ∈ s, omittedLogCT S q (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omittedLogCT_zero]
  | @insert i s his ih => simp [his, omittedLogCT_add, ih]

def localSignedSubsetMonomial (n : ℕ) (T : Finset (Fin n)) :
    Laurent ℚ n :=
  ∏ i ∈ T, (-MultiLaurent.var i)

lemma rename_localSignedSubset_leftLast (S : Setup) (q : Fin S.m)
    (T : Finset (Fin S.n))
    (hleft : S.leftVertex q ∉ T) (hlast : S.lastVertex ∉ T) :
    MultiLaurent.rename (R := ℚ) (leftLastSwap S q)
        (localSignedSubsetMonomial S.n T) =
      localSignedSubsetMonomial S.n T := by
  unfold localSignedSubsetMonomial
  simp only [map_prod, map_neg, rename_var_equiv]
  apply Finset.prod_congr rfl
  intro i hi
  have hil : i ≠ S.leftVertex q := fun h => hleft (h ▸ hi)
  have hit : i ≠ S.lastVertex := fun h => hlast (h ▸ hi)
  rw [show leftLastSwap S q i = i by
    exact Equiv.swap_apply_of_ne_of_ne hil hit]

lemma rename_localSignedSubset_rightLast (S : Setup) (q : Fin S.m)
    (T : Finset (Fin S.n))
    (hright : S.rightVertex q ∉ T) (hlast : S.lastVertex ∉ T) :
    MultiLaurent.rename (R := ℚ) (rightLastSwap S q)
        (localSignedSubsetMonomial S.n T) =
      localSignedSubsetMonomial S.n T := by
  unfold localSignedSubsetMonomial
  simp only [map_prod, map_neg, rename_var_equiv]
  apply Finset.prod_congr rfl
  intro i hi
  have hir : i ≠ S.rightVertex q := fun h => hright (h ▸ hi)
  have hit : i ≠ S.lastVertex := fun h => hlast (h ▸ hi)
  rw [show rightLastSwap S q i = i by
    exact Equiv.swap_apply_of_ne_of_ne hir hit]

def localBoundarySubsetTerm (S : Setup) (q : Fin S.m)
    (T : Finset (Fin S.n)) : Laurent ℚ S.n :=
  MultiLaurent.var (S.rightVertex q) *
    (localSignedSubsetMonomial S.n T * morrisKernel S)

lemma localBoundarySubsetTerm_anti_of_last_notMem (S : Setup)
    (q : Fin S.m) (T : Finset (Fin S.n))
    (hleft : S.leftVertex q ∉ T) (hlast : S.lastVertex ∉ T) :
    MultiLaurent.rename (R := ℚ) (leftLastSwap S q)
        (localBoundarySubsetTerm S q T) =
      -localBoundarySubsetTerm S q T := by
  have hsubset := rename_localSignedSubset_leftLast S q T hleft hlast
  have hkernel :
      MultiLaurent.rename (R := ℚ) (leftLastSwap S q) (morrisKernel S) =
        -morrisKernel S := by
    simpa [leftLastSwap] using
      (rename_morrisKernel_swap_any S (S.leftVertex q) S.lastVertex
        (S.leftVertex_ne_lastVertex q))
  unfold localBoundarySubsetTerm
  simp only [map_mul, rename_var_equiv]
  rw [leftLastSwap_right, hsubset, hkernel]
  ring

lemma localSignedSubsetMonomial_extract_last (S : Setup)
    (T : Finset (Fin S.n)) (hlast : S.lastVertex ∈ T) :
    localSignedSubsetMonomial S.n T =
      (-MultiLaurent.var S.lastVertex) *
        localSignedSubsetMonomial S.n (T.erase S.lastVertex) := by
  unfold localSignedSubsetMonomial
  exact (Finset.mul_prod_erase T
    (fun i : Fin S.n => (-MultiLaurent.var i : Laurent ℚ S.n)) hlast).symm

lemma localBoundarySubsetTerm_anti_of_last_mem (S : Setup)
    (q : Fin S.m) (T : Finset (Fin S.n))
    (hright : S.rightVertex q ∉ T) (hlast : S.lastVertex ∈ T) :
    MultiLaurent.rename (R := ℚ) (rightLastSwap S q)
        (localBoundarySubsetTerm S q T) =
      -localBoundarySubsetTerm S q T := by
  have hrightErase : S.rightVertex q ∉ T.erase S.lastVertex := by
    intro h
    exact hright (Finset.mem_of_mem_erase h)
  have hlastErase : S.lastVertex ∉ T.erase S.lastVertex :=
    Finset.notMem_erase _ _
  have hsubset := rename_localSignedSubset_rightLast S q
    (T.erase S.lastVertex) hrightErase hlastErase
  have hkernel :
      MultiLaurent.rename (R := ℚ) (rightLastSwap S q) (morrisKernel S) =
        -morrisKernel S := by
    simpa [rightLastSwap] using
      (rename_morrisKernel_swap_any S (S.rightVertex q) S.lastVertex
        (S.rightVertex_ne_lastVertex q))
  unfold localBoundarySubsetTerm
  rw [localSignedSubsetMonomial_extract_last S T hlast]
  simp only [map_mul, map_neg, rename_var_equiv]
  rw [rightLastSwap_right, rightLastSwap_last, hsubset, hkernel]
  ring

lemma omittedLogCT_localBoundarySubsetTerm_eq_zero (S : Setup)
    (q : Fin S.m) (T : Finset (Fin S.n))
    (hleft : S.leftVertex q ∉ T) (hright : S.rightVertex q ∉ T) :
    omittedLogCT S q (localBoundarySubsetTerm S q T) = 0 := by
  by_cases hlast : S.lastVertex ∈ T
  · exact omittedLogCT_eq_zero_of_rightLast_antisymmetric S q _
      (localBoundarySubsetTerm_anti_of_last_mem S q T hright hlast)
  · exact omittedLogCT_eq_zero_of_leftLast_antisymmetric S q _
      (localBoundarySubsetTerm_anti_of_last_notMem S q T hleft hlast)

lemma omittedLogCT_deleteTwo_boundary_eq_zero (S : Setup)
    (q : Fin S.m) (d : ℕ) :
    omittedLogCT S q
        (MultiLaurent.var (S.rightVertex q) *
          (localSignedDeleteTwo S.n d (S.leftVertex q)
              (S.rightVertex q) * morrisKernel S)) = 0 := by
  classical
  let base := (Finset.univ : Finset (Finset (Fin S.n))).filter
    (fun T => T.card = d ∧ S.leftVertex q ∉ T ∧ S.rightVertex q ∉ T)
  unfold localSignedDeleteTwo
  change omittedLogCT S q
      (MultiLaurent.var (S.rightVertex q) *
        ((∑ T ∈ base, localSignedSubsetMonomial S.n T) *
          morrisKernel S)) = 0
  have hpoly :
      MultiLaurent.var (S.rightVertex q) *
          ((∑ T ∈ base, localSignedSubsetMonomial S.n T) *
            morrisKernel S) =
        ∑ T ∈ base, localBoundarySubsetTerm S q T := by
    calc
      MultiLaurent.var (S.rightVertex q) *
          ((∑ T ∈ base, localSignedSubsetMonomial S.n T) *
            morrisKernel S) =
          MultiLaurent.var (S.rightVertex q) *
            (∑ T ∈ base,
              localSignedSubsetMonomial S.n T * morrisKernel S) := by
                rw [Finset.sum_mul]
      _ = ∑ T ∈ base,
          MultiLaurent.var (S.rightVertex q) *
            (localSignedSubsetMonomial S.n T * morrisKernel S) := by
              rw [Finset.mul_sum]
      _ = ∑ T ∈ base, localBoundarySubsetTerm S q T := rfl
  rw [hpoly, omittedLogCT_finset_sum]
  apply Finset.sum_eq_zero
  intro T hT
  have hcond := (Finset.mem_filter.mp hT).2
  exact omittedLogCT_localBoundarySubsetTerm_eq_zero S q T
    hcond.2.1 hcond.2.2

lemma omittedLogCT_logRemainder_boundary_eq_zero (S : Setup)
    (q : Fin S.m) (r : ℕ) :
    omittedLogCT S q
        (MultiLaurent.var (S.rightVertex q) *
          (localPairLogRemainder S.n r (S.leftVertex q)
              (S.rightVertex q) * morrisKernel S)) = 0 := by
  cases r with
  | zero =>
      simpa [localPairLogRemainder, localSignedDeleteTwo_zero] using
        (omittedLogCT_deleteTwo_boundary_eq_zero S q 0)
  | succ r =>
      rw [show MultiLaurent.var (S.rightVertex q) *
          (localPairLogRemainder S.n (r + 1) (S.leftVertex q)
              (S.rightVertex q) * morrisKernel S) =
        MultiLaurent.var (S.rightVertex q) *
            (localSignedDeleteTwo S.n (r + 1) (S.leftVertex q)
                (S.rightVertex q) * morrisKernel S) -
          MultiLaurent.var (S.rightVertex q) *
            (localSignedDeleteTwo S.n r (S.leftVertex q)
                (S.rightVertex q) * morrisKernel S) by
        unfold localPairLogRemainder
        ring]
      rw [omittedLogCT_sub,
        omittedLogCT_deleteTwo_boundary_eq_zero,
        omittedLogCT_deleteTwo_boundary_eq_zero]
      ring

lemma standardLogCT_shiftDerivative_pair_eq_zero (S : Setup)
    (a b r : ℕ) (q : Fin S.m) :
    standardLogCT (S.withAB a b)
        (localEuler ((S.withAB a b).leftVertex q)
            (localShiftFactor (S.withAB a b).n r
                ((S.withAB a b).leftVertex q) *
              morrisKernel (S.withAB a b)) +
          localEuler ((S.withAB a b).rightVertex q)
            (localShiftFactor (S.withAB a b).n r
                ((S.withAB a b).rightVertex q) *
              morrisKernel (S.withAB a b))) = 0 := by
  rw [standardLogCT_shiftDerivative_pair]
  exact omittedLogCT_logRemainder_boundary_eq_zero (S.withAB a b) q r

lemma standardLogCT_lastEuler_eq_zero (S : Setup)
    (F : Laurent ℚ S.n) :
    standardLogCT S (localEuler S.lastVertex F) = 0 := by
  induction F using MultiLaurent.induction_on with
  | h0 => simp [localEuler_zero, standardLogCT_eq_finsupp_sum]
  | hadd F G hF hG =>
      rw [localEuler_add, standardLogCT_add_clean, hF, hG]
      ring
  | hmono e c =>
      rw [localEuler_monomial, standardLogCT_monomial_clean]
      unfold standardLogWeight
      by_cases hadm : StandardLogAdmissible S e
      · rw [if_pos hadm, hadm.2]
        norm_num
      · rw [if_neg hadm]
        ring

lemma standardLogCT_fintype_sum_clean (S : Setup)
    {I : Type*} [Fintype I] (F : I → Laurent ℚ S.n) :
    standardLogCT S (∑ i, F i) = ∑ i, standardLogCT S (F i) := by
  simpa using standardLogCT_finset_sum_clean S (Finset.univ : Finset I) F

lemma sum_setup_vertices {A : Type*} [AddCommMonoid A]
    (S : Setup) (f : Fin S.n → A) :
    (∑ i : Fin S.n, f i) =
      (∑ q : Fin S.m, (f (S.leftVertex q) + f (S.rightVertex q))) +
        f S.lastVertex := by
  rcases S with ⟨n, m, k, a, b, hn⟩
  subst n
  simpa [Setup.leftVertex, Setup.rightVertex, Setup.lastVertex,
    pairLeft, pairRight, pairUnmatched] using
      (sum_over_standard_pairs m f)

/-- The complete logarithmic part of the Adamović--Milas shift argument:
the standard logarithmic coefficient of the summed total Euler derivative
vanishes, including the unmatched final coordinate. -/
lemma standardLogCT_localShiftDerivativeSum_eq_zero (S : Setup)
    (a b r : ℕ) :
    standardLogCT (S.withAB a b) (localShiftDerivativeSum S a b r) = 0 := by
  let Sab : Setup := S.withAB a b
  unfold localShiftDerivativeSum
  change standardLogCT Sab
      (∑ i : Fin Sab.n,
        localEuler i
          (localShiftFactor Sab.n r i * morrisKernel Sab)) = 0
  rw [standardLogCT_fintype_sum_clean]
  rw [sum_setup_vertices Sab]
  have hpairs :
      (∑ q : Fin Sab.m,
        (standardLogCT Sab
            (localEuler (Sab.leftVertex q)
              (localShiftFactor Sab.n r (Sab.leftVertex q) *
                morrisKernel Sab)) +
          standardLogCT Sab
            (localEuler (Sab.rightVertex q)
              (localShiftFactor Sab.n r (Sab.rightVertex q) *
                morrisKernel Sab)))) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rw [← standardLogCT_add_clean]
    exact standardLogCT_shiftDerivative_pair_eq_zero S a b r q
  rw [hpairs]
  rw [standardLogCT_lastEuler_eq_zero]
  ring

end LogarithmicMorrisFull
