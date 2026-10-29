/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildWordClockFactor
import RiemannGaussian.SemiprimeD1ChildPrefactorPolynomial

/-! # Fixed scalar growth of the actual word-only eager child
The actual old inventory is an explicit scalar input to the coefficient; full
2^(3D) table serialization is factored separately. Original grid cardinality is
capped separately from its exponent, never replaced by an exponential cap.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeD1ChildWordPolynomial
open SemiprimeD1JetAxes SemiprimeD1ChildPrefactorPolynomial

/-- Diagonal scalar coefficient of the actual physical word/table backend. -/
def envelope (S a : ℕ) : ℕ :=
  SemiprimeD1ChildWordClockFactor.prefactor (context S) (axes S)
    S a S S S S S S S S S S S S S S S

/-- Fixed constants bound the actual expanded scalar prefactor on all original
exponent/cardinality pairs satisfying their independently derived caps. -/
theorem envelope_monomial : Bound envelope := by
  unfold envelope
  simp only [SemiprimeD1ChildWordClockFactor.prefactor,
    SemiprimeD1ChildWordClockFactor.leftFactor,
    SemiprimeD1WordPacketClockFactor.rightFactor,
    SemiprimeD1WordPacketClockFactor.storageCoefficient,
    SemiprimeD1WordPacketClockFactor.tapeCoefficient,
    SemiprimeD1ChildTableCopyTape.tapeBudget,
    SemiprimeD1ChildTableCopy.liftBudget,
    SemiprimeD1WordPacketEntryClock.wireClock,
    SemiprimeD1WordPacketEntryClock.gatherClock,
    SemiprimeD1WordPacketEntryClock.nonAffineClock,
    SemiprimeD1WordPacketEntryClock.entryPolynomial,
    SemiprimeD1WordPacketArithmeticClock.mulClock,
    SemiprimeD1WordPacketArithmeticClock.addClock,
    SemiprimeD1WordPacketArithmeticClock.oneClock,
    SemiprimeD1WordPacketArithmeticClock.signClock,
    SemiprimeD1WordPacketArithmeticClock.baseClock,
    SemiprimeD1WordPacketArithmeticClock.rowBaseClock,
    SemiprimeD1WordPacketCoefficientClock.sameBitClock,
    SemiprimeD1WordPacketCoefficientClock.modeClock,
    SemiprimeD1WordPacketCoefficientClock.coefficientClock,
    SemiprimeD1WordPacketCoefficientClock.recipeClock,
    SemiprimeD1PacketSourceClock.powerClock,
    SemiprimeD1PacketSourceClock.sourceTermClock,
    SemiprimeD1PacketSourceClock.sourceFactorClock,
    SemiprimeD1PacketArithmeticClock.mulClock,
    SemiprimeD1PacketArithmeticClock.addClock,
    SemiprimeD1PacketArithmeticClock.oneClock,
    SemiprimeD1JetWordKernelBounds.signedBudget,
    SemiprimeD1JetWordKernelBounds.sourceBudget,
    SemiprimeD1JetWordKernelBounds.linearBudget,
    SemiprimeD1JetWordKernelBounds.entryBudget,
    SemiprimeD1JetWordKernelBounds.originalWidth,
    SemiprimeD1JetWordKernelBounds.budget,
    SemiprimeD1KernelEntryBounds.stepBudget,
    SemiprimeD1KernelEntryBounds.contentWidth,
    SemiprimeD1KernelEntryBounds.denominatorWidth,
    SemiprimeD1KernelEntryBounds.budget,
    SemiprimeD1KernelProductBits.budget,
    SemiprimeD1KernelDenominatorBits.budget,
    SemiprimeD1NormalizedLinearBits.budget,
    SemiprimeD1JetWordModeScalarBounds.inverseBudget,
    SemiprimeD1JetWordModeScalarBounds.stepBudget,
    SemiprimeD1JetWordModeScalarBounds.budget,
    SemiprimeD1JetWordModeBounds.budget,
    SemiprimeD1JetModeBitsBounds.geometricStage,
    SemiprimeD1JetRingBounds.termBudget,
    SemiprimeD1JetRingBounds.mulAtBudget,
    SemiprimeD1JetRingBounds.mulBudget,
    SemiprimeD1JetAffineCoefficientBounds.addBudget,
    SemiprimeD1JetAffineCoefficientBounds.stageConstant,
    SemiprimeSourceHistogramPortKeys.encodeBudget,
    SemiprimeD1WireKernelOriginal.size,context,axes,SemiprimeD1JetAxes.Context.rank,
    List.prod_append,List.prod_replicate,List.prod_cons,List.prod_nil,one_pow,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    Nat.one_mul,Nat.mul_one,pow_succ]
  gridBoundArithmetic



/-- Literal original scalar and context fields dominate the new backend's
expanded physical/tape prefactor. Actual inventory I remains an explicit cap. -/
theorem prefactor_le_envelope (old : Context) (extra : List ℕ)
    (p a D A K P T B L E NF M I W G O H U : ℕ)
    (hrank : old.rank ≤ U) (hprecision : old.precision ≤ U)
    (haxes : old.axes.length ≤ U) (hprod : extra.prod ≤ U) (hlen : extra.length ≤ U)
    (h : ∀x∈[p,D,A,K,P,T,B,L,E,NF,M,I,W,G,O,H],x ≤ U) :
    SemiprimeD1ChildWordClockFactor.prefactor old extra p a D A K P T B L E NF M I W G O H ≤
      envelope U a := by
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
  have h10 : M ≤ U := h M (by simp)
  have h11 : I ≤ U := h I (by simp)
  have h12 : W ≤ U := h W (by simp)
  have h13 : G ≤ U := h G (by simp)
  have h14 : O ≤ U := h O (by simp)
  have h15 : H ≤ U := h H (by simp)
  simp only [envelope,SemiprimeD1ChildWordClockFactor.prefactor,
    SemiprimeD1ChildWordClockFactor.leftFactor,
    SemiprimeD1WordPacketClockFactor.rightFactor,
    SemiprimeD1WordPacketClockFactor.storageCoefficient,
    SemiprimeD1WordPacketClockFactor.tapeCoefficient,
    SemiprimeD1ChildTableCopyTape.tapeBudget,
    SemiprimeD1ChildTableCopy.liftBudget,
    SemiprimeD1WordPacketEntryClock.wireClock,
    SemiprimeD1WordPacketEntryClock.gatherClock,
    SemiprimeD1WordPacketEntryClock.nonAffineClock,
    SemiprimeD1WordPacketEntryClock.entryPolynomial,
    SemiprimeD1WordPacketArithmeticClock.mulClock,
    SemiprimeD1WordPacketArithmeticClock.addClock,
    SemiprimeD1WordPacketArithmeticClock.oneClock,
    SemiprimeD1WordPacketArithmeticClock.signClock,
    SemiprimeD1WordPacketArithmeticClock.baseClock,
    SemiprimeD1WordPacketArithmeticClock.rowBaseClock,
    SemiprimeD1WordPacketCoefficientClock.sameBitClock,
    SemiprimeD1WordPacketCoefficientClock.modeClock,
    SemiprimeD1WordPacketCoefficientClock.coefficientClock,
    SemiprimeD1WordPacketCoefficientClock.recipeClock,
    SemiprimeD1PacketSourceClock.powerClock,
    SemiprimeD1PacketSourceClock.sourceTermClock,
    SemiprimeD1PacketSourceClock.sourceFactorClock,
    SemiprimeD1PacketArithmeticClock.mulClock,
    SemiprimeD1PacketArithmeticClock.addClock,
    SemiprimeD1PacketArithmeticClock.oneClock,
    SemiprimeD1JetWordKernelBounds.signedBudget,
    SemiprimeD1JetWordKernelBounds.sourceBudget,
    SemiprimeD1JetWordKernelBounds.linearBudget,
    SemiprimeD1JetWordKernelBounds.entryBudget,
    SemiprimeD1JetWordKernelBounds.originalWidth,
    SemiprimeD1JetWordKernelBounds.budget,
    SemiprimeD1KernelEntryBounds.stepBudget,
    SemiprimeD1KernelEntryBounds.contentWidth,
    SemiprimeD1KernelEntryBounds.denominatorWidth,
    SemiprimeD1KernelEntryBounds.budget,
    SemiprimeD1KernelProductBits.budget,
    SemiprimeD1KernelDenominatorBits.budget,
    SemiprimeD1NormalizedLinearBits.budget,
    SemiprimeD1JetWordModeScalarBounds.inverseBudget,
    SemiprimeD1JetWordModeScalarBounds.stepBudget,
    SemiprimeD1JetWordModeScalarBounds.budget,
    SemiprimeD1JetWordModeBounds.budget,
    SemiprimeD1JetModeBitsBounds.geometricStage,
    SemiprimeD1JetRingBounds.termBudget,
    SemiprimeD1JetRingBounds.mulAtBudget,
    SemiprimeD1JetRingBounds.mulBudget,
    SemiprimeD1JetAffineCoefficientBounds.addBudget,
    SemiprimeD1JetAffineCoefficientBounds.stageConstant,
    SemiprimeSourceHistogramPortKeys.encodeBudget,
    SemiprimeD1WireKernelOriginal.size,context,axes,SemiprimeD1JetAxes.Context.rank,
    List.prod_append,List.prod_replicate,List.prod_cons,List.prod_nil,one_pow,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    Nat.one_mul,Nat.mul_one,pow_succ]
  gcongr <;> omega

end RiemannGaussian.SemiprimeD1ChildWordPolynomial
