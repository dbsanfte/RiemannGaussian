/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeIntervalJet

/-!
# Exact shared blocks retain the three interval channels

One baby polynomial and its two derivatives serve many row targets. Unit
normalization of each exponent block retains the full product and both
marked derivatives. Padding to full blocks remains within the local-period
range already certified by the public short search, so every original
proper hit remains recoverable.

This certifies the algebra behind a shared blocked evaluator. The explicit
degree/point lists still have the B^(3/2) reshape scale, and its GMP engine
and total bit-operation cost remain unverified. Directly pooling first jets
can erase their labels when more than one factor is zero; row channels stay
separate in the shared evaluator.
-/

namespace RiemannGaussian.SemiprimeSharedIntervalJet

open scoped BigOperators
open Polynomial
open SemiprimeIntervalJet

/-- One factor of an original exponent block. -/
def blockFactor {R : Type*} [CommRing R] (alpha x : R) (o u : ℕ) : R :=
  x-alpha^(o+u)

/-- The product of one complete exponent block. -/
def blockProduct {R : Type*} [CommRing R] (alpha x : R) (o s : ℕ) : R :=
  ∏ u ∈ Finset.range s, blockFactor alpha x o u

/-- The omitted-factor product within one block. -/
def blockCofactor {R : Type*} [CommRing R] (alpha x : R) (o s u : ℕ) : R :=
  ∏ v ∈ (Finset.range s).erase u, blockFactor alpha x o v

/-- The target derivative within one block. -/
def blockTargetDerivative {R : Type*} [CommRing R] (alpha x : R) (o s : ℕ) : R :=
  ∑ u ∈ Finset.range s, blockCofactor alpha x o s u

/-- The logarithmic base derivative retains the original absolute index
o+u, including the offset created by the block decomposition. -/
def blockBaseDerivative {R : Type*} [CommRing R] (alpha x : R) (o s : ℕ) : R :=
  -∑ u ∈ Finset.range s, ((o+u : ℕ) : R)*alpha^(o+u)*blockCofactor alpha x o s u

/-- The complete target polynomial for an exponent block. -/
noncomputable def blockPolynomial {R : Type*} [CommRing R] (alpha : R) (o s : ℕ) : R[X] :=
  ∏ u ∈ Finset.range s, (X-C (alpha^(o+u)))

/-- Block products are evaluations of the original target polynomial. -/
theorem blockProduct_eq_eval {R : Type*} [CommRing R] (alpha x : R) (o s : ℕ) :
    blockProduct alpha x o s=(blockPolynomial alpha o s).eval x := by
  simp only [blockPolynomial, eval_prod, eval_sub, eval_X, eval_C,
    blockProduct, blockFactor]

/-- The block's target derivative is a literal polynomial derivative. -/
theorem blockTargetDerivative_eq_derivative {R : Type*} [CommRing R]
    (alpha x : R) (o s : ℕ) :
    blockTargetDerivative alpha x o s=(blockPolynomial alpha o s).derivative.eval x := by
  simp only [blockPolynomial, derivative_prod_finset, derivative_X_sub_C, mul_one,
    eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C, blockTargetDerivative,
    blockCofactor, blockFactor]

/-- A generic logarithmic derivative keeps each literal exponent in a
finite product, including exponent zero without a singular division. -/
theorem weightedProduct_logDerivative {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (e : ι → ℕ) (alpha x : R) :
    alpha*(∏ u ∈ S, (C x-X^(e u) : R[X])).derivative.eval alpha=
      -∑ u ∈ S, (e u : R)*alpha^(e u)*
        ∏ v ∈ S.erase u, (x-alpha^(e v)) := by
  classical
  simp only [derivative_prod_finset, derivative_sub, derivative_C, derivative_X_pow,
    zero_sub, eval_finsetSum, eval_mul, eval_prod, eval_sub, eval_C, eval_pow,
    eval_X, eval_neg]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases he : e u=0
  · simp [he]
  · have hp : alpha^(e u-1)*alpha=alpha^(e u) := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ e u by omega)]
    calc
      alpha*((∏ v ∈ S.erase u, (x-alpha^(e v)))*
          -((e u : R)*alpha^(e u-1))) =
        -((e u : R)*(alpha^(e u-1)*alpha)*
          ∏ v ∈ S.erase u, (x-alpha^(e v))) := by ring
      _ = _ := by rw [hp]

/-- The block's marked derivative equals the base derivative of the
original product, with the target held fixed. -/
theorem blockBaseDerivative_eq_derivative {R : Type*} [CommRing R]
    (alpha x : R) (o s : ℕ) :
    blockBaseDerivative alpha x o s=
      alpha*(∏ u ∈ Finset.range s, (C x-X^(o+u) : R[X])).derivative.eval alpha := by
  exact (weightedProduct_logDerivative (Finset.range s) (fun u => o+u) alpha x).symm

/-- Exact common-phase extraction retains each original block factor. -/
theorem blockFactor_rescale {R : Type*} [CommRing R] (alpha z : R) (o u : ℕ) :
    blockFactor alpha (alpha^o*z) o u=alpha^o*(z-alpha^u) := by
  simp only [blockFactor, pow_add, mul_sub]

/-- One normalized baby polynomial supplies the full block detector. -/
theorem blockProduct_rescale {R : Type*} [CommRing R] (alpha z : R) (o s : ℕ) :
    blockProduct alpha (alpha^o*z) o s=(alpha^o)^s*intervalProduct alpha z s := by
  simp only [blockProduct, blockFactor_rescale, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, intervalProduct]

/-- Cofactor rescaling pays exactly the s-1 remaining phases. -/
theorem blockCofactor_rescale {R : Type*} [CommRing R] (alpha z : R)
    (o : ℕ) {s u : ℕ} (hu : u<s) :
    blockCofactor alpha (alpha^o*z) o s u=
      (alpha^o)^(s-1)*cofactor alpha z s u := by
  simp only [blockCofactor, blockFactor_rescale, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hu),
    Finset.card_range, cofactor]

/-- The derivative uses the same baby polynomial at the normalized point. -/
theorem blockTargetDerivative_rescale {R : Type*} [CommRing R] (alpha z : R)
    (o s : ℕ) :
    blockTargetDerivative alpha (alpha^o*z) o s=
      (alpha^o)^(s-1)*targetDerivative alpha z s := by
  unfold blockTargetDerivative targetDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  exact blockCofactor_rescale alpha z o (Finset.mem_range.mp hu)

/-- The unlabelled cofactor moment expresses the drift of a normalized
target. This identity is valid even when the detector is zero. -/
theorem cofactor_first_moment {R : Type*} [CommRing R] (alpha z : R) (s : ℕ) :
    (∑ u ∈ Finset.range s, alpha^u*cofactor alpha z s u)=
      z*targetDerivative alpha z s-(s : R)*intervalProduct alpha z s := by
  have hh : ∑ u ∈ Finset.range s,
      (z*cofactor alpha z s u-alpha^u*cofactor alpha z s u)=
      ∑ _u ∈ Finset.range s, intervalProduct alpha z s := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [← sub_mul]
    exact Finset.mul_prod_erase (Finset.range s) (fun v => z-alpha^v) hu
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hh
  change z*targetDerivative alpha z s-
    (∑ u ∈ Finset.range s, alpha^u*cofactor alpha z s u)=
    (s : R)*intervalProduct alpha z s at hh
  linear_combination -hh

/-- The full base derivative retains both the original exponent offset
and the normalized-point drift. No factor is removed by a quotient. -/
theorem blockBaseDerivative_rescale {R : Type*} [CommRing R] (alpha z : R)
    (o : ℕ) {s : ℕ} (hs : 0 < s) :
    blockBaseDerivative alpha (alpha^o*z) o s=
      (alpha^o)^s*((o : R)*(s : R)*intervalProduct alpha z s+
        baseDerivative alpha z s-(o : R)*z*targetDerivative alpha z s) := by
  have hphase : alpha^o*(alpha^o)^(s-1)=(alpha^o)^s := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  have hh : blockBaseDerivative alpha (alpha^o*z) o s=
      (alpha^o)^s*(baseDerivative alpha z s-
        (o : R)*∑ u ∈ Finset.range s, alpha^u*cofactor alpha z s u) := by
    unfold blockBaseDerivative baseDerivative
    rw [mul_sub, mul_neg, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [blockCofactor_rescale alpha z o (Finset.mem_range.mp hu), pow_add, Nat.cast_add]
    calc
      -(((o : R)+(u : R))*(alpha^o*alpha^u)*
          ((alpha^o)^(s-1)*cofactor alpha z s u)) =
        -((alpha^o)^s*(u : R)*alpha^u*cofactor alpha z s u)-
          (alpha^o)^s*((o : R)*(alpha^u*cofactor alpha z s u)) := by
            rw [← hphase]
            ring
      _ = _ := by ring
  rw [hh, cofactor_first_moment]
  ring

/-- Exact concatenation of the original interval products. -/
theorem intervalProduct_split {R : Type*} [CommRing R] (alpha x : R) (L M : ℕ) :
    intervalProduct alpha x (L+M)=intervalProduct alpha x L*blockProduct alpha x L M := by
  exact Finset.prod_range_add (fun u => x-alpha^u) L M

/-- The target polynomial splits along the same original exponent block. -/
theorem intervalPolynomial_split {R : Type*} [CommRing R] (alpha : R) (L M : ℕ) :
    SemiprimeCartesianCompletion.rootPolynomial (Finset.range (L+M)) (fun u => alpha^u)=
      SemiprimeCartesianCompletion.rootPolynomial (Finset.range L) (fun u => alpha^u)*
        blockPolynomial alpha L M := by
  exact Finset.prod_range_add (fun u => X-C (alpha^u)) L M

/-- Product-rule concatenation preserves the target-derivative channel. -/
theorem targetDerivative_split {R : Type*} [CommRing R] (alpha x : R) (L M : ℕ) :
    targetDerivative alpha x (L+M)=targetDerivative alpha x L*blockProduct alpha x L M+
      intervalProduct alpha x L*blockTargetDerivative alpha x L M := by
  rw [targetDerivative_eq_derivative, intervalPolynomial_split, derivative_mul,
    eval_add, eval_mul, eval_mul, ← targetDerivative_eq_derivative,
    ← blockTargetDerivative_eq_derivative, ← blockProduct_eq_eval]
  have hP : (SemiprimeCartesianCompletion.rootPolynomial
      (Finset.range L) (fun u => alpha^u)).eval x=intervalProduct alpha x L := by
    simp only [SemiprimeCartesianCompletion.rootPolynomial, eval_prod,
      eval_sub, eval_X, eval_C, intervalProduct]
  rw [hP]

/-- Product-rule concatenation preserves the labelled base derivative. -/
theorem baseDerivative_split {R : Type*} [CommRing R] (alpha x : R) (L M : ℕ) :
    baseDerivative alpha x (L+M)=baseDerivative alpha x L*blockProduct alpha x L M+
      intervalProduct alpha x L*blockBaseDerivative alpha x L M := by
  have hprod : (∏ u ∈ Finset.range (L+M), (C x-X^u : R[X]))=
      (∏ u ∈ Finset.range L, (C x-X^u : R[X]))*
        ∏ u ∈ Finset.range M, (C x-X^(L+u) : R[X]) :=
    Finset.prod_range_add (fun u => (C x-X^u : R[X])) L M
  rw [baseDerivative_eq_derivative, hprod, derivative_mul, eval_add, eval_mul, eval_mul]
  rw [baseDerivative_eq_derivative, blockBaseDerivative_eq_derivative]
  simp only [eval_prod, eval_sub, eval_C, eval_pow, eval_X, intervalProduct,
    blockProduct, blockFactor]
  ring

/-- Product-rule composition keeps the two derivative channels separate. -/
def combineJets {R : Type*} [CommRing R] (v w : R × R × R) : R × R × R :=
  (v.1*w.1, v.2.1*w.1+v.1*w.2.1, v.2.2*w.1+v.1*w.2.2)

/-- The literal triple attached to one original exponent block. -/
def blockJet {R : Type*} [CommRing R] (alpha x : R) (o s : ℕ) : R × R × R :=
  (blockProduct alpha x o s, blockTargetDerivative alpha x o s,
    blockBaseDerivative alpha x o s)

/-- A finite sequence of blocks uses product-rule composition, without
materializing all pair differences or geometric interval targets. -/
def blockedJet {R : Type*} [CommRing R] (alpha x : R) (m J : ℕ) : R × R × R :=
  (List.range J).foldl (fun v j => combineJets v (blockJet alpha x (j*m) m)) (1, 0, 0)

/-- Appending a block performs exactly one triple composition. -/
theorem blockedJet_succ {R : Type*} [CommRing R] (alpha x : R) (m J : ℕ) :
    blockedJet alpha x m (J+1)=
      combineJets (blockedJet alpha x m J) (blockJet alpha x (J*m) m) := by
  simp [blockedJet, List.range_succ, List.foldl_append]

/-- The literal block fold is exactly the original padded interval's
product and two derivatives, over every commutative ring. -/
theorem blockedJet_exact {R : Type*} [CommRing R] (alpha x : R) (m J : ℕ) :
    blockedJet alpha x m J=(intervalProduct alpha x (J*m),
      targetDerivative alpha x (J*m), baseDerivative alpha x (J*m)) := by
  induction J with
  | zero => simp [blockedJet, intervalProduct, targetDerivative, baseDerivative]
  | succ J ih =>
    rw [blockedJet_succ, ih, Nat.succ_mul, intervalProduct_split,
      targetDerivative_split, baseDerivative_split]
    rfl

/-- One shared baby polynomial carries the base derivative for every
normalized evaluation point. -/
noncomputable def babyBasePolynomial {R : Type*} [CommRing R] (alpha : R) (m : ℕ) : R[X] :=
  baseDerivative (C alpha) X m

/-- Evaluating the common base-derivative polynomial gives precisely
the marked scalar derivative at the normalized target. -/
theorem babyBasePolynomial_eval {R : Type*} [CommRing R] (alpha z : R) (m : ℕ) :
    (babyBasePolynomial alpha m).eval z=baseDerivative alpha z m := by
  simpa only [babyBasePolynomial, Polynomial.coe_evalRingHom, eval_C, eval_X]
    using baseDerivative_map (Polynomial.evalRingHom z) (C alpha) X m

/-- The normalized point for one original block uses a checked unit
inverse, even when its target is a nonunit. -/
def normalizedPoint {R : Type*} [CommRing R] (alpha : Rˣ) (x : R) (m j : ℕ) : R :=
  (((alpha^(j*m))⁻¹ : Rˣ) : R)*x

/-- The normalized point retains the original row after phase restoration. -/
theorem normalizedPoint_phase {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) (m j : ℕ) :
    (alpha : R)^(j*m)*normalizedPoint alpha x m j=x := by
  unfold normalizedPoint
  rw [← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul]
  simp only [mul_inv_cancel, Units.val_one, one_mul]

/-- A shared baby polynomial, its target derivative and its labelled
base derivative compute the same triple for each original block. -/
noncomputable def normalizedBlockJet {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) (m j : ℕ) : R × R × R :=
  let z := normalizedPoint alpha x m j
  let c := (alpha : R)^(j*m)
  let h := c^m
  let A := SemiprimeCartesianCompletion.rootPolynomial (Finset.range m)
    (fun u => (alpha : R)^u)
  let H := babyBasePolynomial (alpha : R) m
  (h*A.eval z, h*((((alpha^(j*m))⁻¹ : Rˣ) : R))*A.derivative.eval z,
    h*((j*m : ℕ)*((m : ℕ) : R)*A.eval z+H.eval z-
      ((j*m : ℕ) : R)*z*A.derivative.eval z))

/-- The normalized block circuit preserves all three original channels.
This proves its algebra, independently of a multipoint backend's cost. -/
theorem normalizedBlockJet_eq {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    normalizedBlockJet alpha x m j=blockJet (alpha : R) x (j*m) m := by
  let z := normalizedPoint alpha x m j
  have hz : (alpha : R)^(j*m)*z=x := normalizedPoint_phase alpha x m j
  have hP : (SemiprimeCartesianCompletion.rootPolynomial (Finset.range m)
      (fun u => (alpha : R)^u)).eval z=intervalProduct (alpha : R) z m := by
    simp only [SemiprimeCartesianCompletion.rootPolynomial, eval_prod,
      eval_sub, eval_X, eval_C, intervalProduct]
  have hphase : ((alpha : R)^(j*m))^m*
      ((((alpha^(j*m))⁻¹ : Rˣ) : R))=((alpha : R)^(j*m))^(m-1) := by
    have he : ((alpha : R)^(j*m))^m=
        ((alpha : R)^(j*m))^(m-1)*(alpha : R)^(j*m) := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [he, mul_assoc]
    have hc : (alpha : R)^(j*m)*((((alpha^(j*m))⁻¹ : Rˣ) : R))=1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
      simp only [mul_inv_cancel, Units.val_one]
    rw [hc, mul_one]
  have hbP := blockProduct_rescale (alpha : R) z (j*m) m
  have hbD := blockTargetDerivative_rescale (alpha : R) z (j*m) m
  have hbE := blockBaseDerivative_rescale (alpha : R) z (j*m) hm
  rw [hz] at hbP hbD hbE
  unfold normalizedBlockJet blockJet
  change _=(blockProduct (alpha : R) x (j*m) m,
    blockTargetDerivative (alpha : R) x (j*m) m,
    blockBaseDerivative (alpha : R) x (j*m) m)
  rw [hbP, hbD, hbE]
  simp only [hP, ← targetDerivative_eq_derivative, babyBasePolynomial_eval,
    hphase, z]

/-- A normalized block fold reuses the same three baby polynomials at
every point; none of those polynomials depends on its row target. -/
noncomputable def sharedBlockedJet {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) (m J : ℕ) : R × R × R :=
  (List.range J).foldl (fun v j => combineJets v (normalizedBlockJet alpha x m j)) (1, 0, 0)

/-- The shared-polynomial circuit computes the exact three interval
scalars, including zero rows and nonunit targets. -/
theorem sharedBlockedJet_exact {R : Type*} [CommRing R]
    (alpha : Rˣ) (x : R) {m : ℕ} (hm : 0 < m) (J : ℕ) :
    sharedBlockedJet alpha x m J=(intervalProduct (alpha : R) x (J*m),
      targetDerivative (alpha : R) x (J*m), baseDerivative (alpha : R) x (J*m)) := by
  simp only [sharedBlockedJet, normalizedBlockJet_eq alpha x hm]
  exact blockedJet_exact (alpha : R) x m J

/-- Normalized points for several row targets, with only one block
point list rather than a list of all interval factors. -/
def sharedPoints {R : Type*} [CommRing R] (alpha : Rˣ)
    (targets : List R) (m J : ℕ) : List R :=
  targets.flatMap fun x => (List.range J).map (normalizedPoint alpha x m)

/-- The common multipoint list has exactly rows times blocks entries. -/
theorem sharedPoints_length {R : Type*} [CommRing R] (alpha : Rˣ)
    (targets : List R) (m J : ℕ) :
    (sharedPoints alpha targets m J).length=targets.length*J := by
  simp [sharedPoints, List.length_flatMap, List.sum_replicate]

/-- Number of complete blocks covering the original target interval. -/
def blockCount (B m : ℕ) : ℕ := 3*B^2/m+1

/-- The padded interval includes every original exponent. -/
theorem padded_contains_original {B m : ℕ} (hm : 0 < m) :
    3*B^2+1 ≤ m*blockCount B m := by
  have hh := Nat.mod_add_div (3*B^2) m
  have hr := Nat.mod_lt (3*B^2) hm
  unfold blockCount
  nlinarith

/-- Padding adds fewer than m exponents, rather than a separate tail
of up to m factors for every row. -/
theorem padded_length_le {B m : ℕ} : m*blockCount B m ≤ 3*B^2+m := by
  have hh := Nat.div_mul_le_self (3*B^2) m
  unfold blockCount
  nlinarith

/-- The public long-period certificate leaves room for full blocks
whenever m≤B². The added targets remain distinct in both fields. -/
theorem padded_below_short_square {B m : ℕ} (hB : 0 < B) (hmB : m ≤ B^2) :
    m*blockCount B m < (2*B+1)*(2*B+1) := by
  have hh := padded_length_le (B := B) (m := m)
  nlinarith

/-- A successful original centre-free row survives full-block padding.
Both period conditions come from the public short-search certificate. -/
theorem exists_recoverable_padded_row {p q B m b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hB : 0 < B) (hm : 0 < m) (hmB : m ≤ B^2)
    (hbudget : p*q ≤ B^6)
    (hprefix : (p*q).gcd (SemiprimeGroupCoverage.prefixProduct B)=1)
    (hcover : m*blockCount B m ≤ b^2) (g : (ZMod (p*q))ˣ)
    (hclear : (p*q).gcd ((SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))-1).val=1)
    (hnone : SemiprimeCentreFreeCover.recoverShort
      (SemiprimeCentreFreeCover.projectedUnit g B) (2*B+1)=none) :
    ∃ a : ℕ, 0 < a ∧ a ≤ B ∧
      ∃ d, recoverInterval (SemiprimeCentreFreeCover.projectedUnit g B)
        ((SemiprimeCentreFreeCover.projectedUnit g B)^(a*(p*q)+B^2))
        (m*blockCount B m) b=some d := by
  have hlong := SemiprimeCentreFreeCover.failed_projected_short_forces_long hp hq g
    (by omega) hclear hnone
  obtain ⟨a, k, ha, haB, hk, hhit⟩ :=
    SemiprimeCentreFreeCover.exists_projected_proper_hit hp hq hpq hB hbudget hprefix g
      (by nlinarith [hlong.1]) (by nlinarith [hlong.2])
  have hpad := padded_below_short_square hB hmB
  have hcontains := padded_contains_original (B := B) hm
  have hP : orderOf (ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))) =
      orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
        (SemiprimeCentreFreeCover.projectedUnit g B)) :=
    orderOf_units (y := Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
      (SemiprimeCentreFreeCover.projectedUnit g B))
  have hQ : orderOf (ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (SemiprimeCentreFreeCover.projectedUnit g B : ZMod (p*q))) =
      orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
        (SemiprimeCentreFreeCover.projectedUnit g B)) :=
    orderOf_units (y := Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom
      (SemiprimeCentreFreeCover.projectedUnit g B))
  refine ⟨a, ha, haB, ?_⟩
  apply recoverInterval_succeeds_of_proper_hit hp hq hpq _ _
    (by omega : k < m*blockCount B m) hcover
    (hP.symm ▸ (hpad.trans hlong.1).le) (hQ.symm ▸ (hpad.trans hlong.2).le)
  simpa only [Units.val_pow_eq_pow_val] using hhit

/-- Sharing one polynomial and its two derivatives changes the constant
number of coefficient/point lists, not the existing reshape input floor. -/
theorem shared_input_floor {B m : ℕ} (hB : 0 < B) (hm : 0 < m) :
    12*B^3 < (m+B*blockCount B m)^2 := by
  exact SemiprimeCentreFreeCover.explicit_reshape_input_bound hB hm

/-- An explicit width chosen for one group of R rows. For B≥4 and R≤B
the public quadratic cap is unnecessary; smaller widths remain capped
by the executable and covered by the parameterized padding theorem. -/
def sharedWidth (B R : ℕ) : ℕ := Nat.sqrt (R*(3*B^2+1))+1

/-- The selected width is positive without any arithmetic promise. -/
theorem sharedWidth_pos (B R : ℕ) : 0 < sharedWidth B R := by
  unfold sharedWidth
  omega

/-- In the nontrivial asymptotic regime, every group width fits the
extra period range supplied by the public short-search certificate. -/
theorem sharedWidth_le_quadratic {B R : ℕ} (hB : 4 ≤ B) (hR : R ≤ B) :
    sharedWidth B R ≤ B^2 := by
  have hquad : B ≤ B^2 := by nlinarith
  have hcubic : 4*B^2 ≤ B^3 := by
    nlinarith [Nat.mul_le_mul_right (B^2) hB]
  have hquartic : 4*B^3 ≤ (B^2)^2 := by
    nlinarith [Nat.mul_le_mul_right (B^3) hB]
  have hh : R*(3*B^2+1) < (B^2)^2 := by
    nlinarith [Nat.mul_le_mul_right (3*B^2+1) hR]
  have hs := Nat.sqrt_lt'.mpr hh
  unfold sharedWidth
  omega

/-- Exact upper bound on the degree/point inputs for one shared group.
It counts explicit construction, not the multipoint engine's bit cost. -/
theorem shared_group_input_bound {B R : ℕ} (hR : R ≤ B) :
    sharedWidth B R+R*blockCount B (sharedWidth B R) ≤ 3*sharedWidth B R := by
  let m := sharedWidth B R
  have hm : 0 < m := sharedWidth_pos B R
  have hsq : R*(3*B^2+1) < m*m := by
    simpa [m, sharedWidth] using Nat.lt_succ_sqrt (R*(3*B^2+1))
  have hdiv := Nat.mul_le_mul_left R (Nat.div_mul_le_self (3*B^2) m)
  have hf : R*(3*B^2/m)<m := by
    apply (Nat.mul_lt_mul_left hm).mp
    nlinarith
  have hrL : R ≤ 3*B^2+1 := by nlinarith
  have hr : R<m := by
    have hh := Nat.le_sqrt'.mpr (show R^2 ≤ R*(3*B^2+1) by nlinarith)
    dsimp [m, sharedWidth]
    omega
  change m+R*(3*B^2/m+1) ≤ 3*m
  nlinarith

/-- The upper construction bound has B^(3/2) scale for a complete
group of B rows. It is not the missing every-run sixth-root bit bound. -/
theorem shared_group_squared_bound {B R : ℕ} (hR : R ≤ B) :
    (sharedWidth B R+R*blockCount B (sharedWidth B R))^2 ≤
      18*R*(3*B^2+1)+18 := by
  have hh := shared_group_input_bound hR
  have hs := Nat.sqrt_le' (R*(3*B^2+1))
  have he : (sharedWidth B R)^2 ≤ 2*(R*(3*B^2+1))+2 := by
    unfold sharedWidth
    nlinarith [sq_nonneg ((Nat.sqrt (R*(3*B^2+1)) : ℤ)-1)]
  nlinarith [Nat.mul_self_le_mul_self hh]

/-- Multiplying first jets erases both marked derivatives if two row
products vanish. Keeping row labels separate avoids this information loss. -/
theorem two_zero_rows_erase_first_jet {R : Type*} [CommRing R]
    {p q : R} (d e f h : R) (hp : p=0) (hq : q=0) :
    p*q=0 ∧ d*q+p*f=0 ∧ e*q+p*h=0 := by
  simp [hp, hq]

/-- Two checked local roots imply saturation over the entire semiprime
ring, retaining every original exponent in the detector. -/
theorem intervalProduct_zero_of_local_roots {p q L k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (alpha x : ZMod (p*q)) (hk : k<L) (hl : l<L)
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) x=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) alpha)^k)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) x=
      (ZMod.castHom (dvd_mul_left q p) (ZMod q) alpha)^l) :
    intervalProduct alpha x L=0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply zero_of_prime_reductions hp hq hpq
  · rw [intervalProduct_map, intervalProduct_zero_iff]
    exact ⟨k, hk, hP⟩
  · rw [intervalProduct_map, intervalProduct_zero_iff]
    exact ⟨l, hl, hQ⟩

set_option maxRecDepth 32768 in
/-- Exact public row targets, two different local indices per row and
the shared all-row padding dimensions for the saved control. -/
theorem control_shared_local_roots :
    Nat.Prime 44963 ∧ Nat.Prime 62347 ∧
    (1823692905 : ZMod (44963*62347))^(9*(44963*62347)+38^2)=964233038 ∧
    (1823692905 : ZMod (44963*62347))^(13*(44963*62347)+38^2)=387888406 ∧
    (964233038 : ZMod 44963)=(1823692905 : ZMod 44963)^542 ∧
    (964233038 : ZMod 62347)=(1823692905 : ZMod 62347)^862 ∧
    (585688580 : ZMod 44963)=(542 : ZMod 44963) ∧
    (585688580 : ZMod 62347)=(862 : ZMod 62347) ∧
    sharedWidth 38 38=406 ∧ blockCount 38 406=11 ∧
    406*blockCount 38 406=4466 ∧
    406+38*blockCount 38 406=824 := by
  norm_num [sharedWidth, blockCount]
  reduce_mod_char
  norm_num

/-- Both distinct rows in the control are saturated and simple. Pooling
their first jets loses every channel, despite retaining the row data
being sufficient for individual index recovery. -/
theorem control_pool_erases_first_jets :
    intervalProduct (1823692905 : ZMod (44963*62347)) 964233038 4466=0 ∧
    intervalProduct (1823692905 : ZMod (44963*62347)) 387888406 4466=0 ∧
    IsUnit (targetDerivative (1823692905 : ZMod (44963*62347)) 964233038 4466) ∧
    IsUnit (targetDerivative (1823692905 : ZMod (44963*62347)) 387888406 4466) ∧
    combineJets
      (intervalProduct (1823692905 : ZMod (44963*62347)) 964233038 4466,
        targetDerivative (1823692905 : ZMod (44963*62347)) 964233038 4466,
        baseDerivative (1823692905 : ZMod (44963*62347)) 964233038 4466)
      (intervalProduct (1823692905 : ZMod (44963*62347)) 387888406 4466,
        targetDerivative (1823692905 : ZMod (44963*62347)) 387888406 4466,
        baseDerivative (1823692905 : ZMod (44963*62347)) 387888406 4466)=(0, 0, 0) := by
  obtain ⟨hp, hq, _, _, h9P, h9Q, _⟩ := control_shared_local_roots
  obtain ⟨_, _, h13P, h13Q, _⟩ := control_saturated_local_roots
  have h9 : intervalProduct (1823692905 : ZMod (44963*62347)) 964233038 4466=0 :=
    intervalProduct_zero_of_local_roots hp hq (by norm_num) _ _
      (by norm_num : 542 < 4466) (by norm_num : 862 < 4466)
      (by simpa only [map_ofNat] using h9P) (by simpa only [map_ofNat] using h9Q)
  have h13 : intervalProduct (1823692905 : ZMod (44963*62347)) 387888406 4466=0 :=
    intervalProduct_zero_of_local_roots hp hq (by norm_num) _ _
      (by norm_num : 2639 < 4466) (by norm_num : 4067 < 4466)
      (by simpa only [map_ofNat] using h13P) (by simpa only [map_ofNat] using h13Q)
  have hLP : 4466 ≤ orderOf (ZMod.castHom (dvd_mul_right 44963 62347) (ZMod 44963)
      (1823692905 : ZMod (44963*62347))) := by
    simp only [map_ofNat, SemiprimeCentreFreeCover.control_long_local_orders.1]
    norm_num
  have hLQ : 4466 ≤ orderOf (ZMod.castHom (dvd_mul_left 62347 44963) (ZMod 62347)
      (1823692905 : ZMod (44963*62347))) := by
    simp only [map_ofNat, SemiprimeCentreFreeCover.control_long_local_orders.2.1]
    norm_num
  refine ⟨h9, h13, saturated_targetDerivative_isUnit hp hq _ _ hLP hLQ h9,
    saturated_targetDerivative_isUnit hp hq _ _ hLP hLQ h13, ?_⟩
  simp [combineJets, h9, h13]

end RiemannGaussian.SemiprimeSharedIntervalJet
