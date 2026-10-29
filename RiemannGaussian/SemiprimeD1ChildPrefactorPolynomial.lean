/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkClock
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Polynomial scalar prefactors with the grid cardinality kept explicit
The grid exponent and its power are separately capped. No substitution replaces
2^a by 2^S when deriving fixed polynomial scalar overheads.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeD1ChildPrefactorPolynomial
open SemiprimeD1JetAxes

/-- Uniform growth on actual exponent/cardinality pairs. -/
def Bound (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ C k : ℕ, ∀ S a, a ≤ S → 2^a ≤ S → f S a ≤ C*(S+1)^k

/-- Fixed constants have a uniform envelope. -/
theorem constant_bound (c : ℕ) : Bound (fun _ _ => c) := by
  exact ⟨c,0,by intros; simp⟩

/-- The scalar cap is polynomial in itself. -/
theorem scalar_bound : Bound (fun S _ => S) := by
  exact ⟨1,1,by intros; simp⟩

/-- The original grid exponent is bounded without exponentiating the cap. -/
theorem exponent_bound : Bound (fun _ a => a) := by
  exact ⟨1,1,by intro S a ha hp; simpa using ha.trans (Nat.le_succ S)⟩

/-- The actual grid cardinality is a separate capped scalar. -/
theorem grid_bound : Bound (fun _ a => 2^a) := by
  exact ⟨1,1,by intro S a ha hp; simpa using hp.trans (Nat.le_succ S)⟩

/-- Sum closure fixes the constants before all original parameters. -/
theorem add_bound {f g : ℕ → ℕ → ℕ} (hf : Bound f) (hg : Bound g) :
    Bound (fun S a => f S a+g S a) := by
  obtain ⟨C,k,hf⟩:=hf
  obtain ⟨D,l,hg⟩:=hg
  refine ⟨C+D,k+l,?_⟩
  intro S a ha hp
  have hk:=Nat.pow_le_pow_right (by omega : 0 < S+1) (Nat.le_add_right k l)
  have hl:=Nat.pow_le_pow_right (by omega : 0 < S+1) (Nat.le_add_left l k)
  calc
    _ ≤ C*(S+1)^k+D*(S+1)^l := Nat.add_le_add (hf S a ha hp) (hg S a ha hp)
    _ ≤ C*(S+1)^(k+l)+D*(S+1)^(k+l) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hk) (Nat.mul_le_mul_left D hl)
    _ = _ := by ring

/-- Product closure constructs fixed monomial witnesses. -/
theorem mul_bound {f g : ℕ → ℕ → ℕ} (hf : Bound f) (hg : Bound g) :
    Bound (fun S a => f S a*g S a) := by
  obtain ⟨C,k,hf⟩:=hf
  obtain ⟨D,l,hg⟩:=hg
  refine ⟨C*D,k+l,?_⟩
  intro S a ha hp
  calc
    _ ≤ (C*(S+1)^k)*(D*(S+1)^l) := Nat.mul_le_mul (hf S a ha hp) (hg S a ha hp)
    _ = _ := by rw [pow_add]; ring

/-- Fixed powers preserve the uniform monomial form. -/
theorem pow_bound {f : ℕ → ℕ → ℕ} (hf : Bound f) (m : ℕ) :
    Bound (fun S a => (f S a)^m) := by
  obtain ⟨C,k,hf⟩:=hf
  refine ⟨C^m,k*m,?_⟩
  intro S a ha hp
  calc
    _ ≤ (C*(S+1)^k)^m := Nat.pow_le_pow_left (hf S a ha hp) m
    _ = _ := by rw [mul_pow,pow_mul]

/-- Subtraction only decreases the derived cap. -/
theorem sub_bound {f g : ℕ → ℕ → ℕ} (hf : Bound f) :
    Bound (fun S a => f S a-g S a) := by
  obtain ⟨C,k,hf⟩:=hf
  exact ⟨C,k,by intro S a ha hp; exact (Nat.sub_le _ _).trans (hf S a ha hp)⟩

open Lean Elab Tactic
/-- Closure for fixed arithmetic with separately bounded original powers. -/
syntax "gridBoundArithmetic" : tactic
elab_rules : tactic
  | `(tactic| gridBoundArithmetic) => do
    let target ← Lean.instantiateMVars (← getMainTarget)
    let f ← Lean.instantiateMVars (target.getArg! 0)
    let body := (Lean.mkApp (Lean.mkApp (f.liftLooseBVars 0 2)
      (Lean.mkBVar 1)) (Lean.mkBVar 0)).headBeta
    if !body.hasLooseBVars then
      evalTactic (← `(tactic| exact constant_bound _))
    else if body matches .bvar 1 then
      evalTactic (← `(tactic| exact scalar_bound))
    else if body matches .bvar 0 then
      evalTactic (← `(tactic| exact exponent_bound))
    else
      let name := body.getAppFn.constName?
      if name == some ``HAdd.hAdd || name == some ``Nat.add then
        evalTactic (← `(tactic| apply add_bound <;> gridBoundArithmetic))
      else if name == some ``HMul.hMul || name == some ``Nat.mul then
        evalTactic (← `(tactic| apply mul_bound <;> gridBoundArithmetic))
      else if name == some ``HSub.hSub || name == some ``Nat.sub then
        evalTactic (← `(tactic| apply sub_bound <;> gridBoundArithmetic))
      else if name == some ``HPow.hPow || name == some ``Pow.pow || name == some ``Nat.pow then
        if body.getArg! (body.getAppNumArgs-1) matches .bvar 0 then
          evalTactic (← `(tactic| exact grid_bound))
        else
          evalTactic (← `(tactic| apply pow_bound <;> gridBoundArithmetic))
      else
        throwError "unsupported arithmetic node: {body}"

/-- A context cap with polynomial rank AND axis-list length. -/
def axes (S : ℕ) : List ℕ := List.replicate S 1++[S+1]

/-- Original and current metadata fields are capped by actual finite products. -/
def context (S : ℕ) : SemiprimeD1JetAxes.Context := ⟨axes S,S+1⟩

/-- Pure scalar prefactor envelope; the original grid exponent remains separate. -/
def envelope (S a : ℕ) : ℕ :=
  SemiprimeD1ChildNetworkClock.prefactor (context S) (axes S)
    S a S S S S S S S S S S S S S S S S S



/-- The actual scalar prefactor admits fixed constants uniformly in the capped
original grid exponent and cardinality. No variable exponential is hidden. -/
theorem envelope_monomial : Bound envelope := by
  unfold envelope
  simp only [SemiprimeD1ChildNetworkClock.prefactor,
    SemiprimeD1ChildClockFactor.leftPolynomial,
    SemiprimeD1ChildClockFactor.rightPolynomial,
    SemiprimeD1ChildClockFactor.rightControls,
    SemiprimeD1ChildClockFactor.cacheCoefficient,
    SemiprimeD1ChildTableClock.lookupBudget,
    SemiprimeD1ChildTableCopy.liftBudget,
    SemiprimeD1PacketEntryClock.wireClock,
    SemiprimeD1PacketEntryClock.gatherClock,
    SemiprimeD1PacketEntryClock.nonAffineClock,
    SemiprimeD1PacketEntryClock.entryPolynomial,
    SemiprimeD1PacketArithmeticClock.mulClock,
    SemiprimeD1PacketArithmeticClock.addClock,
    SemiprimeD1PacketArithmeticClock.oneClock,
    SemiprimeD1PacketArithmeticClock.signClock,
    SemiprimeD1PacketArithmeticClock.baseClock,
    SemiprimeD1PacketArithmeticClock.rowBaseClock,
    SemiprimeD1PacketCoefficientClock.sameBitClock,
    SemiprimeD1PacketCoefficientClock.coefficientClock,
    SemiprimeD1PacketCoefficientClock.recipeClock,
    SemiprimeD1PacketSourceClock.powerClock,
    SemiprimeD1PacketSourceClock.sourceTermClock,
    SemiprimeD1PacketSourceClock.sourceFactorClock,
    SemiprimeD1JetKernelBitsBounds.integerBudget,
    SemiprimeD1JetKernelBitsBounds.integerVectorBudget,
    SemiprimeD1JetKernelBitsBounds.linearBudget,
    SemiprimeD1JetKernelBitsBounds.entryBudget,
    SemiprimeD1JetModeBitsBounds.geometricStage,
    SemiprimeD1JetModeBitsBounds.inverseCacheBudget,
    SemiprimeD1JetModeBitsBounds.modeBudget,
    SemiprimeD1JetRingBounds.termBudget,
    SemiprimeD1JetRingBounds.mulAtBudget,
    SemiprimeD1JetRingBounds.mulBudget,
    SemiprimeD1JetAffineCoefficientBounds.addBudget,
    SemiprimeD1JetAffineCoefficientBounds.stageConstant,
    SemiprimeSourceHistogramPortKeys.encodeBudget,context,axes,SemiprimeD1JetAxes.Context.rank,
    List.prod_append,List.prod_replicate,List.prod_cons,List.prod_nil,one_pow,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    Nat.one_mul,Nat.mul_one,pow_succ]
  gridBoundArithmetic



/-- Every scalar and literal context field is bounded before the pure polynomial
closure is used; the original exponent a is preserved on both sides. -/
theorem prefactor_le_envelope (old : SemiprimeD1JetAxes.Context) (extra : List ℕ)
    (p a D A K P T B L E NF Fchild links S W G Z O H U : ℕ)
    (hrank : old.rank ≤ U) (hprecision : old.precision ≤ U)
    (haxes : old.axes.length ≤ U) (hprod : extra.prod ≤ U) (hlen : extra.length ≤ U)
    (h : ∀ x ∈ [p,D,A,K,P,T,B,L,E,NF,Fchild,links,S,W,G,Z,O,H], x ≤ U) :
    SemiprimeD1ChildNetworkClock.prefactor old extra p a D A K P T B L E NF Fchild
      links S W G Z O H ≤ envelope U a := by
  change old.axes.prod ≤ U at hrank
  have h0 : p ≤ U := h p (by simp)
  have h1 : D ≤ U := h D (by simp)
  have h2 : A ≤ U := h A (by simp)
  have h3 : K ≤ U := h K (by simp)
  have h4 : P ≤ U := h P (by simp)
  have h5 : T ≤ U := h T (by simp)
  have h6 : B ≤ U := h B (by simp)
  have h7 : L ≤ U := h L (by simp)
  have h8 : E ≤ U := h E (by simp)
  have h9 : NF ≤ U := h NF (by simp)
  have h10 : Fchild ≤ U := h Fchild (by simp)
  have h11 : links ≤ U := h links (by simp)
  have h12 : S ≤ U := h S (by simp)
  have h13 : W ≤ U := h W (by simp)
  have h14 : G ≤ U := h G (by simp)
  have h15 : Z ≤ U := h Z (by simp)
  have h16 : O ≤ U := h O (by simp)
  have h17 : H ≤ U := h H (by simp)
  simp only [envelope,SemiprimeD1ChildNetworkClock.prefactor,
    SemiprimeD1ChildClockFactor.leftPolynomial,
    SemiprimeD1ChildClockFactor.rightPolynomial,
    SemiprimeD1ChildClockFactor.rightControls,
    SemiprimeD1ChildClockFactor.cacheCoefficient,
    SemiprimeD1ChildTableClock.lookupBudget,
    SemiprimeD1ChildTableCopy.liftBudget,
    SemiprimeD1PacketEntryClock.wireClock,
    SemiprimeD1PacketEntryClock.gatherClock,
    SemiprimeD1PacketEntryClock.nonAffineClock,
    SemiprimeD1PacketEntryClock.entryPolynomial,
    SemiprimeD1PacketArithmeticClock.mulClock,
    SemiprimeD1PacketArithmeticClock.addClock,
    SemiprimeD1PacketArithmeticClock.oneClock,
    SemiprimeD1PacketArithmeticClock.signClock,
    SemiprimeD1PacketArithmeticClock.baseClock,
    SemiprimeD1PacketArithmeticClock.rowBaseClock,
    SemiprimeD1PacketCoefficientClock.sameBitClock,
    SemiprimeD1PacketCoefficientClock.coefficientClock,
    SemiprimeD1PacketCoefficientClock.recipeClock,
    SemiprimeD1PacketSourceClock.powerClock,
    SemiprimeD1PacketSourceClock.sourceTermClock,
    SemiprimeD1PacketSourceClock.sourceFactorClock,
    SemiprimeD1JetKernelBitsBounds.integerBudget,
    SemiprimeD1JetKernelBitsBounds.integerVectorBudget,
    SemiprimeD1JetKernelBitsBounds.linearBudget,
    SemiprimeD1JetKernelBitsBounds.entryBudget,
    SemiprimeD1JetModeBitsBounds.geometricStage,
    SemiprimeD1JetModeBitsBounds.inverseCacheBudget,
    SemiprimeD1JetModeBitsBounds.modeBudget,
    SemiprimeD1JetRingBounds.termBudget,
    SemiprimeD1JetRingBounds.mulAtBudget,
    SemiprimeD1JetRingBounds.mulBudget,
    SemiprimeD1JetAffineCoefficientBounds.addBudget,
    SemiprimeD1JetAffineCoefficientBounds.stageConstant,
    SemiprimeSourceHistogramPortKeys.encodeBudget,context,axes,SemiprimeD1JetAxes.Context.rank,
    List.prod_append,List.prod_replicate,List.prod_cons,List.prod_nil,one_pow,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    Nat.one_mul,Nat.mul_one,pow_succ]
  gcongr <;> omega

end RiemannGaussian.SemiprimeD1ChildPrefactorPolynomial
