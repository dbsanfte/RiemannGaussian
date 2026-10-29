/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalChildGrowth
import RiemannGaussian.SemiprimeD1PhasePolynomialArithmetic

/-! # Original scalar bounds for retained phase arithmetic
Acquired sources and menus remain actual. No intermediate shape, fit, report or
requested coefficient is supplied as an executable input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1PhysicalPhasePolynomial
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCallTree
open SemiprimeReportPolynomialGrowth
open SemiprimeD1PhysicalPhaseBudget SemiprimeD1PhysicalChildPolynomial
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Scalar cap for actual current coefficient-vector length. -/
def vectorCap (S : ℕ) : ℕ := inflation S*(S+1)

/-- Whole actual arithmetic overhead per retained mode, including all64 groups. -/
def modeEnvelope (S : ℕ) : ℕ :=
  64*(SemiprimeD1JetRingBounds.mulBudget (S+1) (vectorCap S) (inflation S) (inflation S)+8)+
  (9*inflation S+3*vectorCap S+8)+
  (vectorCap S*(6*vectorCap S+11*inflation S+9*inflation S+17)+10*vectorCap S+5)+3

/-- Every actual retained coefficient-block read/copy is included. -/
def blockEnvelope (S : ℕ) : ℕ :=
  inflation S*(S*(3*vectorCap S+3*inflation S+5)+5*S+5)

/-- Native phase-control stages are retained separately from physical arithmetic. -/
def controlEnvelope (S : ℕ) : ℕ := 10*(4*S+inflation S+2)

/-- Actual current shape and width follow the original input dimension caps. -/
theorem current_fields (parent : Call) (a u : ℕ) (i : Fin a) (S : ℕ)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S) (hN : 2^(a+1) ≤ S) :
    (current parent a u i).rank ≤ vectorCap S ∧
    (current parent a u i).precision ≤ inflation S ∧
    (current parent a u i).axes.length ≤ S+1 := by
  have hq:=fresh_axis_bound parent a u i S huM hM
  have hprec:=precision_bound parent a u i S hu huM hM ha hp hN
  constructor
  · change (SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val))*parent.ctx.rank ≤ _
    exact Nat.mul_le_mul hq (hrank.trans (Nat.le_succ S))
  constructor
  · exact hprec
  · simpa only [current,List.length_cons] using Nat.add_le_add_right haxes 1

/-- Mode-loop arithmetic is bounded by a fixed polynomial in original caps. -/
theorem modeOverhead_bound (parent : Call) (a u : ℕ) (i : Fin a) (S : ℕ)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S) (hN : 2^(a+1) ≤ S) :
    modeOverhead (current parent a u i) ≤ modeEnvelope S := by
  have hc:=current_fields parent a u i S hu huM hM ha hp hrank haxes hN
  unfold modeOverhead SemiprimeD1LeafCounterBounds.productBudget SemiprimeD1LeafCounterBounds.oneBudget
    SemiprimeD1JetAffineCoefficientBounds.addBudget modeEnvelope
    SemiprimeD1JetRingBounds.mulBudget SemiprimeD1JetRingBounds.mulAtBudget SemiprimeD1JetRingBounds.termBudget
  have hcurRank:=hc.1
  have hcurPrecision:=hc.2.1
  have hcurAxes:=hc.2.2
  gcongr

/-- Literal block-copy scalar arithmetic has the same original cap. -/
theorem block_bound (parent : Call) (a u : ℕ) (i : Fin a) (S : ℕ)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S) (hN : 2^(a+1) ≤ S) :
    let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
    let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
    q*(parent.ctx.rank*(3*(current parent a u i).rank+3*source.precision+5)+5*parent.ctx.rank+5) ≤
      blockEnvelope S := by
  have hc:=current_fields parent a u i S hu huM hM ha hp hrank haxes hN
  have hq:=fresh_axis_bound parent a u i S huM hM
  dsimp only
  unfold blockEnvelope
  have hcurRank:=hc.1
  have hcurPrecision:=hc.2.1
  gcongr
  exact precision_bound parent a u i S hu huM hM ha hp hN

/-- The executed order loop cannot increment more often than its finite fuel. -/
theorem order_value_le (fuel n : ℕ) : (SemiprimeD1RecoveryScalarRun.orderFuel fuel n).value ≤ fuel := by
  induction fuel generalizing n with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [SemiprimeD1RecoveryScalarRun.orderFuel]
    split
    · exact Nat.zero_le _
    split
    · exact Nat.add_le_add_right (ih (n/2)) 1
    · exact Nat.zero_le _



/-- All scalar arithmetic/native-control coefficients besides source and child
producers. No variable grid/table exponential is folded into this function. -/
def arithmeticOnly (S : ℕ) : ℕ :=
  (8*S+11)+freshBudget S+modeEnvelope S+vectorCap S+1+
    blockEnvelope S+controlEnvelope S+11*S+20

/-- Actual original source factor plus physical phase arithmetic coefficients. -/
def arithmeticBase (S : ℕ) : ℕ :=
  SemiprimeD1PhysicalSourcePolynomial.sourceFactor
    (SemiprimeD1PhysicalNetworkSourceBudget.inflation S)+arithmeticOnly S

/-- A child producer factor is retained with all64 actual groups. -/
def phaseFactor (S C : ℕ) : ℕ := arithmeticBase S+64*C

/-- The actual phase arithmetic coefficients are fixed polynomials. -/
theorem arithmeticOnly_monomial : SemiprimeReportPolynomialGrowth.Bound arithmeticOnly := by
  change Bound (fun S => arithmeticOnly S)
  simp only [arithmeticOnly,freshBudget,modeEnvelope,vectorCap,blockEnvelope,controlEnvelope,inflation,
    SemiprimeD1JetRingBounds.mulBudget,SemiprimeD1JetRingBounds.mulAtBudget,SemiprimeD1JetRingBounds.termBudget]
  boundArithmetic

/-- The original source is bounded by its proved actual producer polynomial. -/
theorem arithmeticBase_monomial : SemiprimeReportPolynomialGrowth.Bound arithmeticBase := by
  unfold arithmeticBase
  exact SemiprimeReportPolynomialGrowth.add_bound
    SemiprimeD1PhysicalNetworkSourceBudget.factor_monomial arithmeticOnly_monomial

/-- Fixed child scalar growth composes with all actual phase arithmetic. -/
theorem phaseFactor_monomial {C : ℕ → ℕ → ℕ}
    (hc : SemiprimeD1ChildPrefactorPolynomial.Bound C) :
    SemiprimeD1ChildPrefactorPolynomial.Bound (fun S a => phaseFactor S (C S a)) := by
  unfold phaseFactor
  exact SemiprimeD1ChildPrefactorPolynomial.add_bound
    (SemiprimeD1PhysicalChildGrowth.lift_bound arithmeticBase_monomial)
    (SemiprimeD1ChildPrefactorPolynomial.mul_bound
      (SemiprimeD1ChildPrefactorPolynomial.constant_bound 64) hc)

/-- Every literal phase coefficient is included, while retaining source and
child producer multiplicities outside the scalar coefficient. -/
theorem coefficient_le (S C : ℕ) :
    SemiprimeD1PhasePolynomialArithmetic.coefficient (8*S+11)
      (SemiprimeD1PhysicalSourcePolynomial.sourceFactor
        (SemiprimeD1PhysicalNetworkSourceBudget.inflation S))
      (freshBudget S) C (modeEnvelope S) (vectorCap S) (blockEnvelope S) (controlEnvelope S) ≤
    phaseFactor S C := by
  unfold SemiprimeD1PhasePolynomialArithmetic.coefficient phaseFactor arithmeticBase arithmeticOnly
  omega

end RiemannGaussian.SemiprimeD1PhysicalPhasePolynomial
