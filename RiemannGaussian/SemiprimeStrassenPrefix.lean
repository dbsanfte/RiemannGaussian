/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLehmanCoverage
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# A complete small-factor prefix from one degree-B polynomial

Strassen's additive cover has B roots and B evaluation points. Its B²
integer candidates need not be materialized. The polynomial and all target
values are retained, including a column whose GCD is the entire modulus.
Such a column triggers at most one length-B leaf scan.

The no-factor result is equivalent to coprimality of the original factorial
prefix when B² < N. This supplies the exact premise of the complete Lehman
complement. The query count below excludes polynomial construction and
evaluation; no full one-sixth bit-operation theorem is inferred.
-/

namespace RiemannGaussian.SemiprimeStrassenPrefix

open scoped BigOperators
open Polynomial
open SemiprimeCartesianCompletion SemiprimeGroupSelection

/-- One polynomial for all blocks of the public integer prefix. -/
noncomputable def blockPolynomial {R : Type*} [CommRing R] (B : ℕ) : R[X] :=
  ∏ i ∈ Finset.range B, (X + C ((i+1 : ℕ) : R))

/-- Every evaluation keeps exactly its original integer block. -/
theorem blockPolynomial_eval {R : Type*} [CommRing R] (B j : ℕ) :
    (blockPolynomial (R := R) B).eval ((j*B : ℕ) : R) =
      ((B*(j+1)).descFactorial B : R) := by
  have h : (∏ i ∈ Finset.range B, (j*B+i+1)) = (B*(j+1)).descFactorial B := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm B j,
      Nat.add_descFactorial_eq_ascFactorial, Nat.ascFactorial_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i _
    omega
  simp only [blockPolynomial, eval_prod, eval_add, eval_X, eval_C]
  rw [← h, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring

/-- The joined modular detector equals the original factorial, without
constructing that factorial as an integer in the polynomial algorithm. -/
theorem blockPolynomial_joined {R : Type*} [CommRing R] (B : ℕ) :
    (∏ j ∈ Finset.range B,
      (blockPolynomial (R := R) B).eval ((j*B : ℕ) : R)) = ((B^2).factorial : R) := by
  simp_rw [blockPolynomial_eval]
  rw [← Nat.cast_prod, ← SemiprimeGroupCoverage.prefixProduct,
    SemiprimeGroupCoverage.prefixProduct_eq_factorial]

/-- Lazy canonical residues for one ambiguous polynomial column. -/
def blockLeaves (N B j : ℕ) : List ℕ :=
  (List.range B).map fun i => (j*B+i+1) % N

/-- B evaluated columns, identified by the public block index. -/
noncomputable def blockColumns (N B : ℕ) : List (ℕ × ℕ) :=
  (List.range B).map fun j =>
    (j, ((blockPolynomial (R := ZMod N) B).eval ((j*B : ℕ) : ZMod N)).val)

/-- Recover the first nonunit block, with a single lazy leaf scan if the
aggregate GCD is N. No B-by-B candidate list is an input. -/
noncomputable def factorPrefix (N B : ℕ) : Option ℕ :=
  recoverColumns N (blockLeaves N B) (blockColumns N B)

/-- A polynomial column has precisely the same GCD as its lazy leaves. -/
theorem block_column_gcd_eq (N B j : ℕ) :
    N.gcd ((blockPolynomial (R := ZMod N) B).eval ((j*B : ℕ) : ZMod N)).val =
      N.gcd (blockLeaves N B j).prod := by
  have h : ((blockLeaves N B j).prod : ZMod N) =
      (blockPolynomial (R := ZMod N) B).eval ((j*B : ℕ) : ZMod N) := by
    simp only [blockLeaves, Nat.cast_list_prod, List.map_map,
      blockPolynomial, eval_prod, eval_add, eval_X, eval_C]
    rw [← List.prod_toFinset _ (List.nodup_range (n := B)), List.toFinset_range]
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [Function.comp_apply]
    rw [ZMod.natCast_mod]
    push_cast
    ring
  rw [← h, ZMod.val_natCast, Nat.gcd_rec N,
    Nat.gcd_rec N ((blockLeaves N B j).prod), Nat.mod_mod]

/-- Every represented integer is positive and inside the quadratic cover. -/
theorem block_integer_bounds {B i j : ℕ} (hi : i < B) (hj : j < B) :
    0 < j*B+i+1 ∧ j*B+i+1 ≤ B^2 := by
  have hB : 0 < B := by omega
  have hjB : (j+1)*B ≤ B*B := Nat.mul_le_mul_right B (by omega)
  constructor
  · omega
  · nlinarith

/-- In the original input regime every lazy leaf is nonzero modulo N.
This is what makes whole-modulus column recovery complete. -/
theorem blockLeaves_bounds {N B j : ℕ} (hcover : B^2 < N) (hj : j < B) :
    ∀ v ∈ blockLeaves N B j, 0 < v ∧ v < N := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  have hb := block_integer_bounds (List.mem_range.mp hi) hj
  rw [Nat.mod_eq_of_lt (hb.2.trans_lt hcover)]
  exact ⟨hb.1, hb.2.trans_lt hcover⟩

/-- Every integer in the prefix occurs at a public block/leaf position. -/
theorem prefix_integer_decomposition {B k : ℕ} (hk : 0 < k) (hkB : k ≤ B^2) :
    ∃ j i : ℕ, j < B ∧ i < B ∧ k = j*B+i+1 := by
  have hB : 0 < B := by nlinarith
  refine ⟨(k-1)/B, (k-1)%B, ?_, Nat.mod_lt _ hB, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul hB).mpr
    have hk' : k-1 < B^2 := by omega
    simpa only [pow_two] using hk'
  · have he := Nat.mod_add_div (k-1) B
    rw [Nat.mul_comm B] at he
    omega

/-- A returned factor is certified for every modulus and cover width. -/
theorem prefix_sound {N B d : ℕ} (hh : factorPrefix N B = some d) :
    ProperDivisor N d := recoverColumns_sound hh

/-- Every nonunit integer in the full prefix forces successful recovery.
Both hidden primes may be in one block; no separating-column premise is
assumed. -/
theorem prefix_succeeds_of_nonunit {N B k : ℕ} (hcover : B^2 < N)
    (hk : 0 < k) (hkB : k ≤ B^2) (hg : N.gcd k ≠ 1) :
    ∃ d, factorPrefix N B = some d := by
  obtain ⟨j, i, hj, hi, he⟩ := prefix_integer_decomposition hk hkB
  apply recoverColumns_succeeds
  · intro c hc
    obtain ⟨j', _, rfl⟩ := List.mem_map.mp hc
    exact block_column_gcd_eq N B j'
  · intro c hc
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hc
    exact blockLeaves_bounds hcover (List.mem_range.mp hj')
  · let v := ((blockPolynomial (R := ZMod N) B).eval ((j*B : ℕ) : ZMod N)).val
    refine ⟨(j, v), List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
    change N.gcd ((blockPolynomial (R := ZMod N) B).eval ((j*B : ℕ) : ZMod N)).val ≠ 1
    rw [block_column_gcd_eq]
    intro hunit
    have hleaf : k ∈ blockLeaves N B j := by
      apply List.mem_map.mpr
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      rw [← he, Nat.mod_eq_of_lt (hkB.trans_lt hcover)]
    exact hg (Nat.coprime_list_prod_right_iff.mp hunit k hleaf)

/-- This unconditional prefix covers every small proper divisor,
including repeated prime factors. -/
theorem prefix_succeeds_of_small_divisor {N B p : ℕ} (hcover : B^2 < N)
    (hp : 1 < p) (hpN : p ∣ N) (hpB : p ≤ B^2) :
    ∃ d, factorPrefix N B = some d := by
  apply prefix_succeeds_of_nonunit hcover (by omega) hpB
  rw [Nat.gcd_eq_right hpN]
  omega

/-- A failed prefix excludes every nonunit integer in its whole cover. -/
theorem prefix_none_coprime_integer {N B k : ℕ} (hcover : B^2 < N)
    (hnone : factorPrefix N B = none) (hk : 0 < k) (hkB : k ≤ B^2) :
    N.Coprime k := by
  change N.gcd k = 1
  by_contra h
  obtain ⟨d, hd⟩ := prefix_succeeds_of_nonunit hcover hk hkB h
  rw [hnone] at hd
  contradiction

/-- No-factor recovery supplies exactly the original factorial-clear
premise, with no reference primes, orders or smoothness assumptions. -/
theorem prefix_none_implies_clear {N B : ℕ} (hcover : B^2 < N)
    (hnone : factorPrefix N B = none) :
    N.gcd (SemiprimeGroupCoverage.prefixProduct B) = 1 := by
  rw [SemiprimeGroupCoverage.prefixProduct_eq_factorial]
  have h : ∀ k : ℕ, k ≤ B^2 → N.Coprime k.factorial := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [Nat.factorial_succ]
      exact (prefix_none_coprime_integer hcover hnone (Nat.succ_pos k) hk).mul_right
        (ih (by omega))
  exact h (B^2) le_rfl

/-- Modular reduction of a block changes no GCD of its integer value. -/
theorem block_column_gcd_eq_descFactorial (N B j : ℕ) :
    N.gcd ((blockPolynomial (R := ZMod N) B).eval ((j*B : ℕ) : ZMod N)).val =
      N.gcd ((B*(j+1)).descFactorial B) := by
  rw [blockPolynomial_eval, ZMod.val_natCast, Nat.gcd_rec N,
    Nat.gcd_rec N ((B*(j+1)).descFactorial B), Nat.mod_mod]

private theorem recoverColumns_none_of_units (N : ℕ) (leaves : ℕ → List ℕ)
    (columns : List (ℕ × ℕ)) (hu : ∀ c ∈ columns, N.gcd c.2 = 1) :
    recoverColumns N leaves columns = none := by
  induction columns with
  | nil => rfl
  | cons c tail ih =>
    rcases c with ⟨j, v⟩
    rw [recoverColumns, if_pos (hu (j, v) (by simp))]
    exact ih (fun c hc => hu c (List.mem_cons_of_mem _ hc))

/-- The compressed prefix has exactly the same complete no-small-factor
criterion as the original B²-term factorial detector. -/
theorem prefix_none_iff_clear {N B : ℕ} (hcover : B^2 < N) :
    factorPrefix N B = none ↔ N.gcd (SemiprimeGroupCoverage.prefixProduct B) = 1 := by
  constructor
  · exact prefix_none_implies_clear hcover
  · intro hclear
    apply recoverColumns_none_of_units
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    rw [block_column_gcd_eq_descFactorial]
    change N.Coprime (SemiprimeGroupCoverage.prefixProduct B) at hclear
    exact Nat.coprime_prod_right_iff.mp hclear j (Finset.mem_range.mpr (List.mem_range.mp hj))

/-- The exact prefix/complement interface rules out every small prime,
without providing the algorithm with that prime. -/
theorem prefix_none_excludes_small_prime {N B p : ℕ} (hcover : B^2 < N)
    (hp : p.Prime) (hpN : p ∣ N) (hnone : factorPrefix N B = none) : B^2 < p := by
  apply SemiprimeGroupCoverage.failed_prefix_excludes_small_prime hp hpN
  rw [← SemiprimeGroupCoverage.prefixProduct_eq_factorial]
  exact prefix_none_implies_clear hcover hnone

/-- The polynomial is the exact root product of B supplied roots. -/
theorem blockPolynomial_eq_rootPolynomial {R : Type*} [CommRing R] (B : ℕ) :
    blockPolynomial (R := R) B = rootPolynomial (Finset.range B)
      (fun i => -((i+1 : ℕ) : R)) := by
  simp only [blockPolynomial, rootPolynomial, map_neg, sub_neg_eq_add]

/-- The input polynomial has degree B over every nonzero coefficient ring. -/
theorem blockPolynomial_degree {R : Type*} [CommRing R] [Nontrivial R] (B : ℕ) :
    (blockPolynomial (R := R) B).natDegree = B := by
  rw [blockPolynomial_eq_rootPolynomial]
  simpa only [rootPolynomial, Finset.card_range] using
    natDegree_finsetProd_X_sub_C_eq_card (Finset.range B) (fun i => -((i+1 : ℕ) : R))

/-- Each leaf list has B entries and is constructed only if needed. -/
theorem blockLeaves_length (N B j : ℕ) : (blockLeaves N B j).length = B := by
  simp [blockLeaves]

/-- Only B polynomial evaluations are supplied to recovery. -/
theorem blockColumns_length (N B : ℕ) : (blockColumns N B).length = B := by
  simp [blockColumns]

/-- The complete prefix needs at most 2B GCD queries after polynomial
evaluation, even if the first nonunit column has GCD N. Polynomial and
bit-operation costs are separate obligations. -/
theorem prefix_gcd_bound (N B : ℕ) :
    recoveryGcdCount N (blockLeaves N B) (blockColumns N B) ≤ 2*B := by
  have h := recoveryGcdCount_le (n := N) (cap := B)
    (columns := blockColumns N B) (leaves := blockLeaves N B)
    (fun c _ => (blockLeaves_length N B c.1).le)
  simpa only [blockColumns_length, two_mul] using h

/-- Every nontrivial ceiling-sixth-root input lies above the entire
quadratic prefix. Small inputs are handled by the finite baseline. -/
theorem sixth_budget_prefix_below_input {N B : ℕ} (hB : 4 ≤ B)
    (hlower : (B-1)^6 < N) : B^2 < N := by
  have hpow : B^2 ≤ B^4 := by
    have h := Nat.le_pow (a := B^2) (by decide : 0 < 2)
    convert h using 1
    ring
  exact hpow.trans_lt ((SemiprimeGroupCoverage.sixth_budget_above_quadratic_prefix hB).trans hlower)

/-- Replace the factorial-prefix construction with the B-point polynomial
batch; retain the universally correct literal Lehman complement. This is
an algorithm specification, not a formal fast-polynomial implementation. -/
noncomputable def factorByBatchCover (N B : ℕ) : Option ℕ :=
  if B < 4 ∨ N.sqrt^2 = N then SemiprimeLehmanCoverage.factorByCover N B
  else match factorPrefix N B with
    | some d => some d
    | none => SemiprimeLehmanCoverage.factorAfterPrefix N B

/-- Every result from the updated public factorizer is a proper divisor. -/
theorem factorByBatchCover_sound {N B d : ℕ}
    (hh : factorByBatchCover N B = some d) : ProperDivisor N d := by
  unfold factorByBatchCover at hh
  split_ifs at hh with hearly
  · exact SemiprimeLehmanCoverage.factorByCover_sound hh
  · cases hp : factorPrefix N B with
    | none => exact SemiprimeLehmanCoverage.factorAfterPrefix_sound (by simpa only [hp] using hh)
    | some d' =>
      have he : d' = d := by simpa only [hp, Option.some.injEq] using hh
      subst d'
      exact prefix_sound hp

/-- Universal correctness survives the compressed prefix replacement.
All small-factor, square and arbitrary-factor-ratio cases are retained. -/
theorem factorByBatchCover_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hbudget : p*q ≤ B^6) (hlower : (B-1)^6 < p*q) :
    ∃ d, factorByBatchCover (p*q) B = some d := by
  by_cases hearly : B < 4 ∨ (p*q).sqrt^2 = p*q
  · obtain ⟨d, hd⟩ := SemiprimeLehmanCoverage.factorByCover_semiprime hp hq hpq hbudget hlower
    exact ⟨d, by simpa only [factorByBatchCover, if_pos hearly] using hd⟩
  · have hB : 4 ≤ B := by omega
    have hsquare : (p*q).sqrt^2 ≠ p*q := fun h => hearly (Or.inr h)
    have hstrict : p < q := by
      apply lt_of_le_of_ne hpq
      intro heq
      apply hsquare
      rw [← heq]
      simp [← pow_two]
    cases hprefix : factorPrefix (p*q) B with
    | some d => exact ⟨d, by simp only [factorByBatchCover, if_neg hearly, hprefix]⟩
    | none =>
      have hclear := prefix_none_implies_clear (sixth_budget_prefix_below_input hB hlower) hprefix
      obtain ⟨d, hd⟩ := SemiprimeLehmanCoverage.factorAfterPrefix_succeeds
        hp hq hstrict (by omega) hbudget hclear
      exact ⟨d, by simpa only [factorByBatchCover, if_neg hearly, hprefix] using hd⟩

/-- One public input; the width is obtained solely from its sixth-power
budget. The centre-coupled complement still exceeds the target work. -/
noncomputable def factor (N : ℕ) : Option ℕ :=
  factorByBatchCover N (SemiprimeLehmanCoverage.sixthWidth N)

/-- Soundness requires no semiprimality promise. -/
theorem factor_sound {N d : ℕ} (hh : factor N = some d) : ProperDivisor N d :=
  factorByBatchCover_sound hh

/-- Every prime product is factored by the updated full specification,
including squares and either ordering. No one-sixth bit bound is claimed. -/
theorem factor_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ d, factor (p*q) = some d ∧ ProperDivisor (p*q) d := by
  have hN : 0 < p*q := Nat.mul_pos hp.pos hq.pos
  have hbudget := SemiprimeLehmanCoverage.sixthWidth_upper (p*q)
  have hlower := SemiprimeLehmanCoverage.sixthWidth_lower hN
  have hs : ∃ d, factor (p*q) = some d := by
    rcases le_total p q with hpq | hqp
    · exact factorByBatchCover_semiprime hp hq hpq hbudget hlower
    · have h := factorByBatchCover_semiprime hq hp hqp
        (SemiprimeLehmanCoverage.sixthWidth_upper (q*p))
        (SemiprimeLehmanCoverage.sixthWidth_lower (Nat.mul_pos hq.pos hp.pos))
      simpa only [factor, Nat.mul_comm] using h
  obtain ⟨d, hd⟩ := hs
  exact ⟨d, hd, factor_sound hd⟩

/-- A block containing both primes has GCD N, but its lazy scan still
returns a proper factor. This certificate uses the exact polynomial. -/
theorem saturated_column_control :
    Nat.gcd 35 ((4*(1+1)).descFactorial 4) = 35 ∧
      factorPrefix 35 4 = some 5 := by
  have hc : blockColumns 35 4 = [(0,24), (1,0), (2,15), (3,0)] := by
    simp only [blockColumns]
    simp only [blockPolynomial_eval]
    norm_num [List.range_succ, Nat.descFactorial, ZMod.val_natCast, ZMod.val_ofNat]
  rw [factorPrefix, hc]
  norm_num [List.range_succ, Nat.descFactorial, blockLeaves, recoverColumns, scanProper, checkedSignal]

/- The reference small-factor algorithm is Strassen's polynomial method,
as recalled in Harvey, arXiv:2010.05450, Proposition 2.5. The implementation
cost theorem and the full implicit Lehman search remain separate. -/

end RiemannGaussian.SemiprimeStrassenPrefix
