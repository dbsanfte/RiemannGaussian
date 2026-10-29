/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScopeBankOriginal
import RiemannGaussian.SemiprimeReportPolynomialGrowth
/-! # Derived input-width bounds for actual occurrence-bank acquisition -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackRootScopeBankBounds
open SemiprimeD1StackRootScopeBank SemiprimeD1StackRootScopeBankExecution
open SemiprimeBitArithmetic (bitValue)

/-- Bound derived from the actual halted Edge13 execution, not a supplied tape. -/
def tapeCap (n : ℕ) : ℕ := 100000000000000000000*(n+1)^5
/-- Fixed degree-ten majorant retaining edge acquisition, record parsing and M rounds. -/
def polynomial (n : ℕ) : ℕ :=
  (1000000000000000000*(n+1)^5+1)+(15*tapeCap n+7)+
    (1000*(2*tapeCap n+1)^2+1)+1

/-- The physical six-field tape itself is bounded at its actual produced halt. -/
theorem tape_bytes (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    (SemiprimeD1StackEdgeCount.tape (records bits) []).length≤tapeCap bits.length := by
  have hb : bits≠[] := by intro he; subst bits; simp [bitValue] at hN
  obtain ⟨time,_,hr⟩:=SemiprimeD1StackEdgeCatalogueBounds.source_run_polynomial bits hb
  have hs:=SemiprimeD1StackEdgeCatalogueBounds.prefix_cells bits hb time _ hr
  have hk:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset E.Stack))=>
    Nat.zero_le ((SemiprimeD1StackEdgeCatalogueExecution.result bits k).length))
      (Finset.mem_univ (E.aux .output))
  have ht : SemiprimeD1StackEdgeCatalogueExecution.result bits (E.aux .output)=
      SemiprimeD1StackEdgeCount.tape (records bits) [] := by
    dsimp only [records]
    rw [SemiprimeD1StackEdgeCount.original_tape]
    exact SemiprimeD1StackEdgeCatalogueExecution.original_edges bits hc hN
  change (∑k:E.Stack,(SemiprimeD1StackEdgeCatalogueExecution.result bits k).length)+0≤
    tapeCap bits.length at hs
  rw [←ht]
  exact hk.trans (by simpa only [Nat.add_zero] using hs)

/-- Two actual marker pushes per complete record bound the physical M cache. -/
theorem count_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) : occurrenceCount bits≤2*tapeCap bits.length := by
  have h:=SemiprimeD1StackEdgeCount.count_le_bytes (records bits)
  have ht:=tape_bytes bits hc hN
  change (records bits).length≤_ at h
  unfold occurrenceCount wireValue
  omega

/-- Closed original-input time majorant, with no table/width/count advice. -/
theorem budget_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) : budget bits≤polynomial bits.length := by
  have ht:=tape_bytes bits hc hN
  have hm:=count_le bits hc hN
  have hsq : (occurrenceCount bits+1)^2≤(2*tapeCap bits.length+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold budget polynomial
  omega

/-- Actual closed program, not a reported unit-work assumption. -/
theorem source_run_polynomial (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    ∃m≤polynomial bits.length,SemiprimeD1StackCalls.run program m (initial bits)=some (done bits) := by
  obtain ⟨m,hm,hr⟩:=source_run bits hc hN
  exact ⟨m,hm.trans (budget_le bits hc hN),hr⟩

/-- One fixed polynomial, uniformly before all original binary inputs. -/
theorem polynomial_monomial : ∃C k:ℕ,∀n,polynomial n≤C*(n+1)^k := by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  unfold polynomial tapeCap
  boundArithmetic

end RiemannGaussian.SemiprimeD1StackRootScopeBankBounds
