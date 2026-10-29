/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireExecution
/-! # Same acquired-packet source clock, polynomial per actual feasible visit
The actual tile word is paid by VALUE. No logarithmic charge replaces its
materialization, and no native catalogue/report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireBounds
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquireCount SemiprimeD1StackPacketModeAcquireOrder
open SemiprimeD1StackPacketModeAcquireExecution
open SemiprimeD1TensorTapeCodec (vectorBits vectorBits_length)
open SemiprimeReportPolynomialGrowth
namespace MB
export SemiprimeD1StackWeightedModeCatalogueBounds (polynomial acquisitionEnvelope runBound)
end MB
/-- Actual packet fields, including empty keys, have a linear complete parser/count clock. -/
theorem countTime_le (packets:List (List Bool)):countTime packets ≤ 11*(vectorBits packets).length:=by
  induction packets with
  | nil=>decide
  | cons word packets ih=>
    simp only [countTime,List.map_cons,List.sum_cons] at ih ⊢
    simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
/-- The actual acquired packet count is paid by the original packet tape. -/
theorem packets_length (packets:List (List Bool)):packets.length ≤ (vectorBits packets).length:=by
  have h:=vectorBits_length packets
  omega
/-- The entire actual order/doubling loop is quadratic in the honest envelope including computed tile VALUE. -/
theorem orderTime_le (packets:List (List Bool)) (i precision:Nat):
    orderTime i ≤ 20*(inputSize packets i precision+1)^2:=by
  let s:=inputSize packets i precision
  have hi:i ≤ s:=by
    change i ≤ (vectorBits packets).length+i+2^(i+1)+precision+1
    calc
      _ ≤ (vectorBits packets).length+i:=Nat.le_add_left _ _
      _ ≤ (vectorBits packets).length+i+2^(i+1):=Nat.le_add_right _ _
      _ ≤ (vectorBits packets).length+i+2^(i+1)+precision:=Nat.le_add_right _ _
      _ ≤ _:=Nat.le_add_right _ _
  have ht:2^(i+1) ≤ s:=by dsimp [s,inputSize];omega
  have h:=loopTime_le i 2
  have he:5*2*2^i+5=5*2^(i+1)+5:=by rw [pow_succ];ring
  rw [he] at h
  have hb:loopTime i 2 ≤ (s+1)*(5*s+5):=
    h.trans (Nat.mul_le_mul (by omega) (by omega))
  change orderTime i ≤ 20*(s+1)^2
  unfold orderTime
  nlinarith only [hb,hi]
/-- The frozen own catalogue polynomial is monotone in actual input metadata bytes. -/
theorem catalogue_polynomial_mono {n m:Nat} (h:n ≤ m):MB.polynomial n ≤ MB.polynomial m:=by
  unfold MB.polynomial MB.acquisitionEnvelope
  gcongr
/-- Same actual useful feasible traversal, after the two counts have been physically acquired. -/
def visits (packets:List (List Bool)) (i precision:Nat):Nat:=
  SemiprimeD1WeightedTuples.visits
    (SemiprimeD1StackWeightedModeCatalogueFinish.weights packets.length (2^(i+1)) precision) (precision-1)
/-- A fixed polynomial pays both new acquisition loops and the complete frozen catalogue/DFS source. -/
def polynomial (n:Nat):Nat:=100*(n+1)^2+MB.polynomial n
/-- Own whole-source bound from actual packet bytes, actual order and actual WIDTH; tile VALUE stays explicit. -/
def runBound (packets:List (List Bool)) (i precision:Nat):Nat:=
  polynomial (inputSize packets i precision)*visits packets i precision
/-- All acquisition, copies, actual nested enumeration, real returns and final halt belong to this SAME clock. -/
theorem timeBound_le (packets:List (List Bool)) (i precision:Nat):
    timeBound packets i precision ≤ runBound packets i precision:=by
  let s:=inputSize packets i precision
  let v:=visits packets i precision
  have hv:1 ≤ v:=Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive _ _)
  have hbytes:(vectorBits packets).length ≤ s:=by
    change (vectorBits packets).length ≤ (vectorBits packets).length+i+2^(i+1)+precision+1
    calc
      _ ≤ (vectorBits packets).length+i:=Nat.le_add_right _ _
      _ ≤ (vectorBits packets).length+i+2^(i+1):=Nat.le_add_right _ _
      _ ≤ (vectorBits packets).length+i+2^(i+1)+precision:=Nat.le_add_right _ _
      _ ≤ _:=Nat.le_add_right _ _
  have hn:packets.length+2^(i+1)+precision ≤ s:=by
    have h:=packets_length packets
    dsimp [s,inputSize]
    omega
  have hc:=countTime_le packets
  have ho:=orderTime_le packets i precision
  have hfront:5*(vectorBits packets).length+4+countTime packets+orderTime i+2 ≤ 100*(s+1)^2:=by
    change orderTime i ≤ 20*(s+1)^2 at ho
    nlinarith only [hbytes,hc,ho]
  have hf:5*(vectorBits packets).length+4+countTime packets+orderTime i+2 ≤ 100*(s+1)^2*v:=
    hfront.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (100*(s+1)^2) hv)
  have hm:MB.runBound packets.length (2^(i+1)) precision ≤ MB.polynomial s*v:=by
    unfold MB.runBound
    exact Nat.mul_le_mul_right v (catalogue_polynomial_mono hn)
  change timeBound packets i precision ≤ polynomial s*v
  unfold timeBound polynomial
  calc
    _ ≤ 100*(s+1)^2*v+MB.polynomial s*v:=by omega
    _= _:=by ring
/-- The actual three-input source has its own polynomial-per-visit clock after all acquisition. -/
theorem source_run_bounded (packets:List (List Bool)) (i precision:Nat):
    ∃q ≤ runBound packets i precision,
      SemiprimeD1StackCalls.run program q (source packets i precision)=some (done packets i precision):=by
  obtain ⟨q,hq,hr⟩:=source_run packets i precision
  exact ⟨q,hq.trans (timeBound_le packets i precision),hr⟩
/-- Fixed coefficient and degree precede every packet tape and every phase. -/
theorem polynomial_monomial:∃A d:Nat,∀n,polynomial n ≤ A*(n+1)^d:=by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  unfold polynomial MB.polynomial MB.acquisitionEnvelope
  boundArithmetic
/-- A universal cost statement for this SAME actual source, without packet-count or tile-count advice. -/
theorem source_run_monomial:∃A d:Nat,∀(packets:List (List Bool)) (i precision:Nat),
    ∃q ≤ A*(inputSize packets i precision+1)^d*visits packets i precision,
      SemiprimeD1StackCalls.run program q (source packets i precision)=some (done packets i precision):=by
  obtain ⟨A,d,hA⟩:=polynomial_monomial
  refine ⟨A,d,?_⟩
  intro packets i precision
  obtain ⟨q,hq,hr⟩:=source_run_bounded packets i precision
  exact ⟨q,hq.trans (Nat.mul_le_mul_right _ (hA _)),hr⟩
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireBounds
