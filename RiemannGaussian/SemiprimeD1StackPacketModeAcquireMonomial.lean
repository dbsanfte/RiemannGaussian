/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireResources
/-! # Fixed whole-family coefficients for acquired mode-source storage and visits
The actual weighted feasible traversal is the only nonpolynomial factor here.
The paid input envelope still includes the materialized tile count by VALUE.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireMonomial
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquireBounds SemiprimeD1StackPacketModeAcquireResources
/-- One fixed coefficient/degree bound covers the SAME whole source's storage at every input. -/
theorem cells_monomial:∃A d:Nat,∀(packets:List (List Bool)) (i precision:Nat),
    45*(inputSize packets i precision+runBound packets i precision) ≤
      A*(inputSize packets i precision+1)^d*visits packets i precision:=by
  obtain ⟨A,d,hA⟩:=polynomial_monomial
  refine ⟨45*(1+A),d+1,?_⟩
  intro packets i precision
  let s:=inputSize packets i precision
  let v:=visits packets i precision
  have hv:1 ≤ v:=Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive _ _)
  have hs:1 ≤ s+1:=by omega
  have hd:(s+1)^d ≤ (s+1)^(d+1):=Nat.pow_le_pow_right hs (by omega)
  have hn:s ≤ (s+1)^(d+1):=by
    have h:s+1 ≤ (s+1)^(d+1):=by
      simpa only [pow_one] using Nat.pow_le_pow_right hs (by omega:1 ≤ d+1)
    omega
  have hnv:s ≤ (s+1)^(d+1)*v:=hn.trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((s+1)^(d+1)) hv)
  have hb:runBound packets i precision ≤ A*(s+1)^(d+1)*v:=by
    unfold runBound
    exact Nat.mul_le_mul_right v ((hA s).trans (Nat.mul_le_mul_left A hd))
  change 45*(s+runBound packets i precision) ≤ 45*(1+A)*(s+1)^(d+1)*v
  calc
    _ ≤ 45*((s+1)^(d+1)*v+A*(s+1)^(d+1)*v):=
      Nat.mul_le_mul_left 45 (Nat.add_le_add hnv hb)
    _= _:=by ring
/-- Every genuine compiled44-role/actual-return prefix has fixed whole-family polynomial-per-visit storage. -/
theorem prefix_monomial:∃A d:Nat,∀(packets:List (List Bool)) (i precision fuel:Nat) (cfg:machine.Cfg),
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (source packets i precision)))=some cfg→
      (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
        A*(inputSize packets i precision+1)^d*visits packets i precision:=by
  obtain ⟨A,d,hA⟩:=cells_monomial
  exact ⟨A,d,fun packets i precision fuel cfg hr=>(machine_prefix_cells packets i precision fuel cfg hr).trans (hA packets i precision)⟩
/-- The original feasible-menu cardinality bound applies after physical packet and tile acquisition. -/
theorem runBound_le_leaves (packets:List (List Bool)) (i precision:Nat):
    runBound packets i precision ≤ polynomial (inputSize packets i precision)*
      ((SemiprimeD1ModeCatalog.weights (packets.length*2^(i+1)) (precision-1)).length+1)*
        (SemiprimeD1WeightedTuples.tuples
          (SemiprimeD1ModeCatalog.weights (packets.length*2^(i+1)) (precision-1)) (precision-1)).length:=by
  have h:=Nat.mul_le_mul_left (polynomial (inputSize packets i precision))
    (SemiprimeD1WeightedTuples.visits_le
      (SemiprimeD1ModeCatalog.weights (packets.length*2^(i+1)) (precision-1)) (precision-1))
  simpa only [runBound,visits,SemiprimeD1StackWeightedModeCatalogueFinish.weights,Nat.mul_assoc] using h
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireMonomial
