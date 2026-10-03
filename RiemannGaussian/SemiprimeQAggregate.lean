/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBulkNorm
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Transposed scalar q-products retain a growing coefficient degree

The full aggregate is a first-order scalar q-recurrence, but its
coefficient degree is the number of rows. Transposing the shared
construction replaces the row/point grid by a degree-r*s baby
polynomial and L/s giant points. Its explicit input floor still
has B^(3/2) scale. This restricts this construction, not all
implicit aggregate algorithms or integer factorisation methods.
-/

namespace RiemannGaussian.SemiprimeQAggregate

open scoped BigOperators
open Polynomial SemiprimeIntervalJet SemiprimeMultiplierNorm

/-- Original row norms, retaining all target factors before transposition. -/
def rowAggregate {K : Type*} [CommRing K] (alpha : K) (target : ℕ → K) (r L : ℕ) : K :=
  ∏ i ∈ Finset.range r, intervalProduct alpha (target i) L

/-- Monic polynomial coefficient of the scalar q-recurrence. -/
noncomputable def recurrenceCoeff {K : Type*} [CommRing K] (target : ℕ → K) (r : ℕ) : K[X] :=
  ∏ i ∈ Finset.range r, (X-C (target i))

/-- The scalar sequence has a single changing coefficient polynomial. -/
noncomputable def qPrefix {K : Type*} [CommRing K] (alpha : K) (target : ℕ → K) (r L : ℕ) : K :=
  ∏ u ∈ Finset.range L, (recurrenceCoeff target r).eval (alpha^u)

/-- Order one does not mean constant coefficient degree. -/
theorem qPrefix_succ {K : Type*} [CommRing K] (alpha : K) (target : ℕ → K) (r L : ℕ) :
    qPrefix alpha target r (L+1)=qPrefix alpha target r L*(recurrenceCoeff target r).eval (alpha^L) :=
  Finset.prod_range_succ _ _

/-- Exact row/column transposition retains the full original product up to its sign. -/
theorem qPrefix_eq_rowAggregate {K : Type*} [CommRing K]
    (alpha : K) (target : ℕ → K) (r L : ℕ) :
    qPrefix alpha target r L=(-1 : K)^(r*L)*rowAggregate alpha target r L := by
  simp only [qPrefix,recurrenceCoeff,eval_prod,eval_sub,eval_X,eval_C]
  have hf (u i : ℕ) : alpha^u-target i=-(target i-alpha^u) := by ring
  simp_rw [hf,Finset.prod_neg]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_range,←pow_mul]
  congr 1
  exact Finset.prod_comm

/-- Every row contributes one monic linear factor, including repeated or zero targets. -/
theorem recurrenceCoeff_monic {K : Type*} [CommRing K] (target : ℕ → K) (r : ℕ) :
    (recurrenceCoeff target r).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- The coefficient degree is exactly r, even over a composite-modulus ring. -/
theorem recurrenceCoeff_natDegree {K : Type*} [CommRing K] [Nontrivial K]
    (target : ℕ → K) (r : ℕ) : (recurrenceCoeff target r).natDegree=r := by
  unfold recurrenceCoeff
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

/-- One transposed normalized baby polynomial; its roots are target_i*alpha^(-u). -/
noncomputable def normalizedBlock {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r s : ℕ) : K[X] :=
  ∏ u ∈ Finset.range s, recurrenceCoeff
    (fun i => target i*((((alpha^u)⁻¹ : Kˣ) : K))) r

/-- Transposed baby polynomials remain monic without field division. -/
theorem normalizedBlock_monic {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r s : ℕ) :
    (normalizedBlock alpha target r s).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => recurrenceCoeff_monic _ _)

/-- Transposition has not removed coefficient storage: the baby degree is exactly r*s. -/
theorem normalizedBlock_natDegree {K : Type*} [CommRing K] [Nontrivial K]
    (alpha : Kˣ) (target : ℕ → K) (r s : ℕ) :
    (normalizedBlock alpha target r s).natDegree=r*s := by
  unfold normalizedBlock
  rw [natDegree_prod_of_monic _ _ (fun _ _ => recurrenceCoeff_monic _ _)]
  simp only [recurrenceCoeff_natDegree,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  exact Nat.mul_comm _ _

/-- An exact exponent block keeps all original row targets. -/
def originalBlock {K : Type*} [CommRing K]
    (alpha : K) (target : ℕ → K) (r offset s : ℕ) : K :=
  ∏ u ∈ Finset.range s, ∏ i ∈ Finset.range r, (target i-alpha^(offset+u))

/-- At offset zero the blocked source is the original row aggregate. -/
theorem originalBlock_zero {K : Type*} [CommRing K] (alpha : K) (target : ℕ → K) (r L : ℕ) :
    originalBlock alpha target r 0 L=rowAggregate alpha target r L := by
  simp only [originalBlock,Nat.zero_add,rowAggregate,intervalProduct]
  exact Finset.prod_comm

/-- Exact block splitting keeps the original interval and its tail. -/
theorem originalBlock_split {K : Type*} [CommRing K]
    (alpha : K) (target : ℕ → K) (r offset L M : ℕ) :
    originalBlock alpha target r offset (L+M)=
      originalBlock alpha target r offset L*originalBlock alpha target r (offset+L) M := by
  unfold originalBlock
  rw [Finset.prod_range_add]
  simp only [Nat.add_assoc]

/-- Unit phase of one transposed block; it is proof-side data, not a detector call. -/
def blockPhase {K : Type*} [CommRing K] (alpha : Kˣ) (r s : ℕ) : Kˣ :=
  ∏ u ∈ Finset.range s, (-alpha^u)^r

/-- Unit normalization of one factor preserves its original target. -/
theorem factor_rephase {K : Type*} [CommRing K] (a : Kˣ) (x z : K) :
    x-(a : K)*z=(-(a : K))*(z-x*((a⁻¹ : Kˣ) : K)) := by
  have hi : (a : K)*((a⁻¹ : Kˣ) : K)=1 := by simp
  linear_combination -x*hi

/-- The monic transposed block has the exact original block GCD after unit rephasing. -/
theorem originalBlock_rephase {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r offset s : ℕ) :
    originalBlock (alpha : K) target r offset s=
      (blockPhase alpha r s : K)*(normalizedBlock alpha target r s).eval ((alpha : K)^offset) := by
  have hf (u i : ℕ) : target i-(alpha : K)^(offset+u)=
      (-((alpha^u : Kˣ) : K))*
        ((alpha : K)^offset-target i*((((alpha^u)⁻¹ : Kˣ) : K))) := by
    rw [Nat.add_comm offset u,pow_add,←Units.val_pow_eq_pow_val]
    exact factor_rephase _ _ _
  simp only [originalBlock,hf,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,
    blockPhase,normalizedBlock,recurrenceCoeff,eval_prod,eval_sub,eval_X,eval_C,
    Units.coe_prod,Units.val_pow_eq_pow_val,Units.val_neg]

/-- Full-block scalar fold contains no derivative or per-row norm outputs. -/
noncomputable def qBlocks {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r s : ℕ) : ℕ → K
  | 0 => 1
  | J+1 => qBlocks alpha target r s J*
      (normalizedBlock alpha target r s).eval ((alpha : K)^(J*s))

/-- Full blocks recover the same original prefix up to a public unit. -/
theorem qBlocks_rephase {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r s J : ℕ) :
    originalBlock (alpha : K) target r 0 (J*s)=
      (((blockPhase alpha r s)^J : Kˣ) : K)*qBlocks alpha target r s J := by
  induction J with
  | zero => simp [originalBlock,qBlocks]
  | succ J ih =>
    rw [Nat.succ_mul,originalBlock_split,ih,originalBlock_rephase]
    simp only [qBlocks,pow_succ,Units.val_mul,Nat.zero_add]
    ring

/-- Transposed full blocks and the exact original tail. -/
noncomputable def qDetector {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r L s : ℕ) : K :=
  qBlocks alpha target r s (L/s)*
    (normalizedBlock alpha target r (L%s)).eval ((alpha : K)^((L/s)*s))

/-- Transposed detection preserves the original product through one omitted unit phase. -/
theorem qDetector_rephase {K : Type*} [CommRing K]
    (alpha : Kˣ) (target : ℕ → K) (r L s : ℕ) :
    rowAggregate (alpha : K) target r L=
      ((((blockPhase alpha r s)^(L/s)*blockPhase alpha r (L%s) : Kˣ) : K))*
        qDetector alpha target r L s := by
  have he : (L/s)*s+L%s=L := by
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div L s
  rw [←originalBlock_zero]
  calc
    _ = originalBlock (alpha : K) target r 0 ((L/s)*s+L%s) := by rw [he]
    _ = _ := by
      rw [originalBlock_split,qBlocks_rephase,originalBlock_rephase]
      simp only [Nat.zero_add,Units.val_mul,qDetector]
      ring

/-- The transposed candidate detects exactly the old aggregate GCD, including saturation. -/
theorem qDetector_gcd {N : ℕ} (alpha : (ZMod N)ˣ) (target : ℕ → ZMod N) (r L s : ℕ) :
    N.gcd (qDetector alpha target r L s).val=N.gcd (rowAggregate (alpha : ZMod N) target r L).val := by
  rw [qDetector_rephase]
  exact (SemiprimeRHCancellation.unit_mul_gcd_eq _ _).symm

/-- Explicit transposed coefficient degrees and giant-point counts, including the exact tail. -/
def qInputs (r L s : ℕ) : ℕ := r*s+L/s+r*(L%s)+1

/-- Any positive block width still pays the square-root row/interval scale
in this explicit transposed polynomial representation. -/
theorem qInputs_squared_floor {r L s : ℕ} (hr : 0<r) (hs : 0<s) :
    4*r*L<(qInputs r L s)^2 := by
  have he := Nat.mod_add_div L s
  have ht := Nat.mod_lt L hs
  have hc : L<s*(L/s+1) := by nlinarith
  have hp : r*L<(r*s)*(L/s+1) := by nlinarith [Nat.mul_lt_mul_of_pos_left hc hr]
  have hz : 4*(r : ℤ)*L<(((r*s : ℕ) : ℤ)+((L/s+1 : ℕ) : ℤ))^2 := by
    have hh : (r : ℤ)*L<((r*s : ℕ) : ℤ)*((L/s+1 : ℕ) : ℤ) := by exact_mod_cast hp
    nlinarith [sq_nonneg (((r*s : ℕ) : ℤ)-((L/s+1 : ℕ) : ℤ))]
  have hn : 4*r*L<(r*s+(L/s+1))^2 := by exact_mod_cast hz
  have hle : r*s+(L/s+1)≤qInputs r L s := by unfold qInputs; omega
  exact hn.trans_le (Nat.pow_le_pow_left hle 2)

/-- The complete 2B-row, H=(2B)^2 transposed layout has the same B^(3/2)
floor as the original orientation, for every positive block width. -/
theorem qInputs_full_floor {B s : ℕ} (hB : 0<B) (hs : 0<s) :
    32*B^3<(qInputs (2*B) (normLength B) s)^2 := by
  have h := qInputs_squared_floor (r:=2*B) (L:=normLength B) (by omega) hs
  convert h using 1
  unfold normLength
  ring

end RiemannGaussian.SemiprimeQAggregate
