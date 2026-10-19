/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerPolynomialAudit
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The extra logarithmic valuation channel of an adjacent Pascal minor

This literal two-feature determinant is not a polynomial of one binomial
valuation. Its exact product identity nevertheless reduces its full phased
valuation packet to two existing linear binomial packets and one endpoint.
The additional channel is bounded by the endpoint logarithm. No estimate
of the two original binomial packets, aggregate row saving, cross-prime
nonlinear estimate, or RH exclusion is asserted.

There are three different observations. `valuationPacket` uses the BASE
prime phase times the complete valuation. A consecutive divisibility
tower would phase orders one through that valuation, and is not used here.
`gammaMinorPacket` instead uses the six actual factorial floors, keeping
each original denominator `d=p^r` and its phase. The finite carry-level
regression shows why the latter two observations cannot be identified.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorPascalMinorAudit

/-- The actual adjacent two-by-two Pascal determinant, with natural
subtraction. Positivity and the product identity are proved below. -/
def adjacentMinor (k t : ℕ) : ℕ :=
  (k+t).choose k * (k+t+1).choose (k+1) -
    (k+t).choose (k+1) * (k+t+1).choose k

/-- Adjacent minors have no additional large integer after clearing
the one literal endpoint denominator. Both distinct binomials remain. -/
theorem adjacentMinor_mul_endpoint (k t : ℕ) :
    adjacentMinor k t * (k+1) = (k+t).choose k * (k+t+1).choose k := by
  have h₁ := Nat.add_one_mul_choose_eq (k+t) k
  have h₂ := Nat.choose_succ_right_eq (k+t) k
  have h₃ := Nat.choose_mul_succ_eq (k+t) k
  have hs : k+t-k=t := by omega
  have hs' : k+t+1-k=t+1 := by omega
  rw [hs] at h₂
  rw [hs'] at h₃
  have hpos : 0 < (k+t).choose k * (k+t+1).choose k :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hle : (k+t).choose (k+1) * (k+t+1).choose k ≤
      (k+t).choose k * (k+t+1).choose (k+1) := by nlinarith
  unfold adjacentMinor
  rw [Nat.sub_mul]
  apply Nat.sub_eq_of_eq_add
  nlinarith

/-- This concrete determinant is nonzero at every literal nonnegative
row and column endpoint; no numerical rank assumption is used. -/
theorem adjacentMinor_pos (k t : ℕ) : 0 < adjacentMinor k t := by
  have h := adjacentMinor_mul_endpoint k t
  have hp : 0 < (k+t).choose k * (k+t+1).choose k :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  nlinarith

/-- The precise six-factorial identity underlying the later orderwise
Gamma representation of this actual nonzero integer determinant. -/
theorem adjacentMinor_factorial_identity (k t : ℕ) :
    adjacentMinor k t * k.factorial * (k+1).factorial * t.factorial * (t+1).factorial =
      (k+t).factorial * (k+t+1).factorial := by
  have hA := Nat.choose_mul_factorial_mul_factorial (show k≤k+t by omega)
  have hB := Nat.choose_mul_factorial_mul_factorial (show k≤k+t+1 by omega)
  rw [show k+t-k=t by omega] at hA
  rw [show k+t+1-k=t+1 by omega] at hB
  calc
    _ = (adjacentMinor k t*(k+1))*(k.factorial*t.factorial)*
        (k.factorial*(t+1).factorial) := by rw [Nat.factorial_succ]; ring
    _ = ((k+t).choose k*k.factorial*t.factorial)*
        ((k+t+1).choose k*k.factorial*(t+1).factorial) := by
      rw [adjacentMinor_mul_endpoint]; ring
    _ = _ := by rw [hA,hB]

/-- Complete valuations, with an arbitrary common prime subset and
arbitrary complex codes. For primes these are exactly `padicValNat`. -/
def valuationPacket (P : Finset ℕ) (N : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*phase p*(N.factorization p : ℂ)

/-- Explicit bridge to the existing literal Kummer packet; no carry
orders or base-prime phases have been changed. -/
theorem valuationPacket_choose (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (a b : ℕ) (phase : ℕ → ℂ) :
    valuationPacket P ((a+b).choose b) phase =
      ArithmeticOperatorKummerPolynomialAudit.polynomialPacket P a b 1 phase := by
  unfold valuationPacket ArithmeticOperatorKummerPolynomialAudit.polynomialPacket
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.factorization_def _ (hP p hp)]
  simp [ArithmeticOperatorKummerPolynomialAudit.valuation]

/-- Integer product factorization is retained before any norm. -/
theorem valuationPacket_mul (P : Finset ℕ) (phase : ℕ → ℂ)
    {A B : ℕ} (hA : A≠0) (hB : B≠0) :
    valuationPacket P (A*B) phase =
      valuationPacket P A phase + valuationPacket P B phase := by
  unfold valuationPacket
  rw [Nat.factorization_mul hA hB]
  simp_rw [Finsupp.add_apply,Nat.cast_add,mul_add]
  exact Finset.sum_add_distrib

/-- Any exact positive product relation gives an exact phased packet
identity. This does not identify the packet with an ordinary real log. -/
theorem valuationPacket_of_product {D R A B : ℕ}
    (hD : D≠0) (hR : R≠0) (hA : A≠0) (hB : B≠0)
    (hprod : D*R=A*B) (P : Finset ℕ) (phase : ℕ → ℂ) :
    valuationPacket P D phase - valuationPacket P A phase - valuationPacket P B phase =
      -valuationPacket P R phase := by
  have he := congrArg (fun N => valuationPacket P N phase) hprod
  rw [valuationPacket_mul P phase hD hR,valuationPacket_mul P phase hA hB] at he
  linear_combination he

/-- A bounded complex code cannot exceed the full ordinary logarithmic
valuation mass of one positive integer. Subsets need not contain its factors. -/
theorem norm_valuationPacket_le_log (P : Finset ℕ) (N : ℕ) (phase : ℕ → ℂ)
    (hphase : ∀ p∈P, ‖phase p‖≤1) :
    ‖valuationPacket P N phase‖ ≤ Real.log N := by
  let f : ℕ → ℝ := fun p => (N.factorization p : ℝ)*Real.log p
  have hf (p : ℕ) : 0≤f p := by dsimp [f]; positivity
  have hs : (∑ p∈P,f p) ≤ ∑ p∈N.factorization.support,f p := by
    calc
      _ ≤ ∑ p∈P∪N.factorization.support,f p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun p _ _ => hf p)
      _ = _ := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro p _ hp
        have hz : N.factorization p=0 := Finsupp.notMem_support_iff.mp hp
        simp [f,hz]
  have ht (p : ℕ) (hp : p∈P) :
      ‖(Real.log p : ℂ)*phase p*(N.factorization p : ℂ)‖ ≤ f p := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
    calc
      _ ≤ Real.log p*1*(N.factorization p : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hphase p hp) (Real.log_natCast_nonneg p))
          (by positivity)
      _ = _ := by dsimp [f]; ring
  calc
    _ ≤ ∑ p∈P, ‖(Real.log p : ℂ)*phase p*(N.factorization p : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p∈P,f p := Finset.sum_le_sum ht
    _ ≤ ∑ p∈N.factorization.support,f p := hs
    _ = Real.log N := (Real.log_nat_eq_sum_factorization N).symm

/-- The exact additional determinant channel retains the complete
valuation, arbitrary moving prime subset, and actual height code. -/
theorem adjacentMinor_packet_residual (P : Finset ℕ) (phase : ℕ → ℂ) (k t : ℕ) :
    valuationPacket P (adjacentMinor k t) phase -
      valuationPacket P ((k+t).choose k) phase -
      valuationPacket P ((k+t+1).choose k) phase =
        -valuationPacket P (k+1) phase := by
  exact valuationPacket_of_product (adjacentMinor_pos k t).ne' (by omega)
    (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
    (adjacentMinor_mul_endpoint k t) P phase

/-- Terminal finite source budget: only the genuinely additional minor
channel is logarithmic; the two original binomial sources stay unpaid. -/
theorem norm_adjacentMinor_residual_le (P : Finset ℕ) (phase : ℕ → ℂ)
    (hphase : ∀ p∈P, ‖phase p‖≤1) (k t X : ℕ) (hcut : k+t+1≤X) :
    ‖valuationPacket P (adjacentMinor k t) phase -
      valuationPacket P ((k+t).choose k) phase -
      valuationPacket P ((k+t+1).choose k) phase‖ ≤ Real.log X := by
  rw [adjacentMinor_packet_residual,norm_neg]
  exact (norm_valuationPacket_le_log P (k+1) phase hphase).trans
    (Real.log_le_log (by positivity) (by exact_mod_cast (show k+1≤X by omega)))

/-- The six literal factorial floors in the adjacent-minor product
formula. This is its factorial representation, not a canonical tower
of consecutive orders through `v_p(adjacentMinor k t)`. -/
def gammaMinorLayer (k t d : ℕ) : ℤ :=
  ((k+t)/d : ℕ)+((k+t+1)/d : ℕ)-(k/d : ℕ)-((k+1)/d : ℕ)-
    (t/d : ℕ)-((t+1)/d : ℕ)

/-- An exact order-by-order identity BEFORE the actual prime-power
phase is applied. No Kummer carry locations have been replaced by counts. -/
theorem gammaMinorLayer_eq (k t d : ℕ) :
    gammaMinorLayer k t d =
      (ArithmeticOperatorKummerCutoff.binomialCarry k t d : ℤ)+
      ArithmeticOperatorKummerCutoff.binomialCarry k (t+1) d-
      (if d∣k+1 then (1 : ℤ) else 0) := by
  unfold gammaMinorLayer
  rw [ArithmeticOperatorKummerCutoff.binomialCarry_eq_sub,
    ArithmeticOperatorKummerCutoff.binomialCarry_eq_sub]
  simp only [←Nat.add_assoc]
  have hk := @Nat.succ_div k d
  split_ifs <;> simp_all <;> omega

/-- Literal cutoff binomial carry observation, retaining every integer
denominator and therefore every prime-power order. -/
def carryPacket (X a b : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ d∈Finset.Icc 1 X,
    (ArithmeticOperatorKummerCutoff.binomialCarry a b d : ℂ)*w d

/-- The adjacent determinant's literal factorial-floor observation. -/
def gammaMinorPacket (X k t : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ d∈Finset.Icc 1 X, (gammaMinorLayer k t d : ℂ)*w d

/-- Endpoint extraction keeps the full actual divisor/cofactor cutoff.
Weights may include order-dependent height, modular or Gaussian codes. -/
theorem gammaMinorPacket_residual (X k t : ℕ) (hcut : k+1≤X) (w : ℕ → ℂ) :
    gammaMinorPacket X k t w - carryPacket X k t w - carryPacket X k (t+1) w =
      -∑ d∈(k+1).divisors,w d := by
  have hf : (Finset.Icc 1 X).filter (fun d => d∣k+1) = (k+1).divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,by omega⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
        (Nat.le_of_dvd (by omega) hd).trans hcut⟩,hd⟩
  have hl (d : ℕ) : (gammaMinorLayer k t d : ℂ) =
      (ArithmeticOperatorKummerCutoff.binomialCarry k t d : ℂ)+
      (ArithmeticOperatorKummerCutoff.binomialCarry k (t+1) d : ℂ)-
      (if d∣k+1 then (1 : ℂ) else 0) := by
    rw [gammaMinorLayer_eq]
    push_cast
    split_ifs <;> simp
  unfold gammaMinorPacket carryPacket
  simp_rw [hl,sub_mul,add_mul]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hi : (∑ d∈Finset.Icc 1 X,(if d∣k+1 then (1 : ℂ) else 0)*w d) =
      ∑ d∈(k+1).divisors,w d := by
    simp only [ite_mul,one_mul,zero_mul]
    rw [←Finset.sum_filter,hf]
  rw [hi]
  ring

/-- Full prime-power phases do not enlarge one endpoint divisor mass.
This retains the prime-leg-only twist; no cofactor phase is inserted. -/
theorem norm_primeLegDivisor_le_log (phase : ℕ → ℂ) (n : ℕ)
    (hphase : ∀ d∈n.divisors, ‖phase d‖≤1) :
    ‖ArithmeticOperatorGammaTwistAudit.primeLegDivisor phase n‖ ≤ Real.log n := by
  unfold ArithmeticOperatorGammaTwistAudit.primeLegDivisor
  calc
    _ ≤ ∑ d∈n.divisors, ‖(ArithmeticFunction.vonMangoldt d : ℂ)*phase d‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d∈n.divisors, ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (hphase d hd)
    _ = _ := ArithmeticFunction.vonMangoldt_sum

/-- Terminal ACTUAL prime-power-phase budget for this factorial lift:
the additional minor channel is logarithmic, while both original
phase-retaining binomial carry packets remain completely unpaid. -/
theorem norm_gammaMinor_residual_le (X k t : ℕ) (hcut : k+t+1≤X)
    (phase : ℕ → ℂ) (hphase : ∀ d∈(k+1).divisors, ‖phase d‖≤1) :
    ‖gammaMinorPacket X k t (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*phase d)-
      carryPacket X k t (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*phase d)-
      carryPacket X k (t+1) (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*phase d)‖ ≤
        Real.log X := by
  rw [gammaMinorPacket_residual X k t (by omega),norm_neg]
  exact (norm_primeLegDivisor_le_log phase (k+1) hphase).trans
    (Real.log_le_log (by positivity) (by exact_mod_cast (show k+1≤X by omega)))

/-- The actual nonzero-height phase is evaluated at every denominator
`d=p^r`, rather than at its base prime or at a consecutive valuation index. -/
theorem norm_gammaMinor_height_residual_le (X k t : ℕ) (hcut : k+t+1≤X) (y : ℝ) :
    ‖gammaMinorPacket X k t (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*
        SuzukiCarryCorrelation.primePhase y d)-
      carryPacket X k t (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*
        SuzukiCarryCorrelation.primePhase y d)-
      carryPacket X k (t+1) (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*
        SuzukiCarryCorrelation.primePhase y d)‖ ≤ Real.log X := by
  apply norm_gammaMinor_residual_le X k t hcut
  intro d _
  exact (SuzukiCarryCorrelation.norm_primePhase y d).le

/-- Exact small regression: the unique binary carry of `choose(4,2)`
is at order two. Its count one does not place that carry at order one. -/
theorem central_six_carry_level :
    ArithmeticOperatorKummerPolynomialAudit.carryOrders 2 2 2 1 = {2} ∧
      ArithmeticOperatorKummerPolynomialAudit.valuation 2 2 2 = 1 := by
  have hc : ArithmeticOperatorKummerPolynomialAudit.carryOrders 2 2 2 1 = {2} := by decide
  refine ⟨hc,?_⟩
  rw [ArithmeticOperatorKummerPolynomialAudit.valuation_eq_card Nat.prime_two
    (by norm_num : 2+2≤2^(2*1)),hc]
  simp

/-- A single moving adjacent-minor factorial lift adds no source at any
positive power exponent. Arbitrary moving unit codes and the literal
dyadic cutoff remain; no exterior row cardinality has been absorbed. -/
theorem tendsto_scaled_gammaMinor_residual
    (k t : ℕ → ℕ) (hcut : ∀ J, k J+t J+1≤2^(2*J))
    (phase : ℕ → ℕ → ℂ) (hphase : ∀ J d, d∈(k J+1).divisors → ‖phase J d‖≤1)
    {beta : ℝ} (hbeta : 0<beta) :
    Filter.Tendsto (fun J : ℕ =>
      (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      (gammaMinorPacket (2^(2*J)) (k J) (t J)
          (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*phase J d)-
        carryPacket (2^(2*J)) (k J) (t J)
          (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*phase J d)-
        carryPacket (2^(2*J)) (k J) (t J+1)
          (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*phase J d)))
      Filter.atTop (𝓝 0) := by
  let r := Real.exp (-2*beta*Real.log 2)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1).const_mul
    (2*Real.log 2)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (a := fun J : ℕ => (2*Real.log 2)*((J : ℝ)^1*r^J)) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  have hb := norm_gammaMinor_residual_le (2^(2*J)) (k J) (t J) (hcut J)
    (phase J) (hphase J)
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul,pow_one]
  dsimp [r]
  ring

end RiemannGaussian.ArithmeticOperatorPascalMinorAudit

#lint+ in RiemannGaussian.ArithmeticOperatorPascalMinorAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty Pascal-minor source audit."
  logInfo m!"Pascal minor source: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-carry-determinant-source"
  IO.FS.writeFile ".lake/arithmetic-operator-carry-determinant-source/axioms.json"
    (Json.mkObj [("scope",toJson "actual adjacent Pascal minor, base-prime valuation packets, and separately the full prime-power-phase factorial lift; only additional channel is logarithmic and has zero positive-power source; original two binomial packets unpaid"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
