/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalSourcePolynomial
import RiemannGaussian.SemiprimeD1ChildStateResources

/-! # Actual original-network source cost without intermediate output advice
Original layout/packing and input dimension caps derive observed packet counts,
working precision and catalogue operands. The actual menu factor stays explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace RiemannGaussian.SemiprimeD1PhysicalNetworkSourceBudget
open SemiprimeD1TensorNetwork SemiprimeD1NetworkStateResources SemiprimeD1TensorNetworkRecursion
open SemiprimeD1JetAxes SemiprimeReportPolynomialGrowth

/-- Pure scalar enlargement absorbs actual original packet/precision operands. -/
def inflation (S : ℕ) : ℕ := 100*(S+1)^2

/-- Actual acquired original-network supplier work per output mode. -/
theorem acquire_work (net : Network) (hw : WellFormed net) (D a u i p S : ℕ)
    (hd : DegreeBound net D)
    (hsmall : 2*(64^(2*a))^2*D ≤ edgeCount net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount net)
    (hu0 : 0 < u) (hu : u ≤ edgeCount net) (hi : i ≤ a)
    (hn : net.leftCount ≤ S) (hF : net.rows.length ≤ S) (hM : edgeCount net ≤ S)
    (ha : a ≤ S) (hp : p ≤ S) (hN : SemiprimeD1WireKernelOriginal.size a ≤ S)
    (hL : 64^a ≤ S) :
    let source:=SemiprimeD1ChildStateResources.source net a u i p
    source.work ≤ SemiprimeD1PhysicalSourcePolynomial.sourceFactor (inflation S)*
      (source.modes.values.length+1) := by
  let source:=SemiprimeD1ChildStateResources.source net a u i p
  have hS : S ≤ inflation S := by unfold inflation; nlinarith
  have h64 : 64 ≤ inflation S := by unfold inflation; nlinarith
  have hcount:=SemiprimeD1ChildStateResources.packets_le net hw D a hd hsmall hsize
  have hcount' : source.packets.state.packets.length ≤ inflation S := by
    change (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)).state.packets.length ≤ _
    unfold inflation
    nlinarith only [hcount,hM]
  have hh:=SemiprimeD1ModeRate.jetHeight_mul_le (edgeCount net) u hu
  have hheight : SemiprimeD1ModeRate.jetHeight (edgeCount net) u ≤ 4*edgeCount net := by
    have hm:=Nat.mul_le_mul_left (SemiprimeD1ModeRate.jetHeight (edgeCount net) u)
      (show 1 ≤ u by omega)
    simp only [Nat.mul_one] at hm
    omega
  have hpow : 2^(a-i) ≤ SemiprimeD1WireKernelOriginal.size a := by
    apply (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.sub_le a i)).trans
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : a ≤ a+1)
  have hprec : source.precision-1 ≤ inflation S := by
    have hactual:=SemiprimeD1OriginalModeAcquisition.precision_original net.leftCount
      net.rows.length 64 a u i p (arity net.rows) (owner net.rows)
    rw [SemiprimeD1TensorNetworkLayout.original_ports] at hactual
    change source.precision=SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a i p at hactual
    rw [hactual]
    have hterm:=Nat.mul_le_mul (hheight.trans (Nat.mul_le_mul_left 4 hM)) (hpow.trans hN)
    have hterm2:=Nat.mul_le_mul hM (Nat.add_le_add_right ha 1)
    apply (Nat.sub_le _ _).trans
    unfold SemiprimeD1ModeRate.workingPrecision inflation
    nlinarith only [hterm,hterm2,hp]
  have htiles : 2^(i+1) ≤ inflation S := by
    have h : 2^(i+1) ≤ SemiprimeD1WireKernelOriginal.size a := by
      apply (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : i+1 ≤ a+1)).trans
      simp only [SemiprimeD1WireKernelOriginal.size,pow_succ,Nat.mul_comm]
      omega
    exact (h.trans hN).trans hS
  have hb:=SemiprimeD1PhysicalSourceBudget.acquire_work net.leftCount net.rows.length 64 a u i p
    (arity net.rows) (owner net.rows)
  have hm : (∑ e,arity net.rows e)=edgeCount net := by
    exact (scope_eq_sum net.rows).symm
  rw [hm] at hb
  apply hb.trans
  exact SemiprimeD1PhysicalSourcePolynomial.source_budget net.leftCount net.rows.length 64 a
    (edgeCount net) u i p source.packets.state.packets.length (source.precision-1)
    source.modes.values.length (inflation S) (by omega) (hn.trans hS) (hF.trans hS) h64
    (ha.trans hS) (hM.trans hS) ((hu.trans hM).trans hS) ((hi.trans ha).trans hS)
    (hp.trans hS) (hL.trans hS) hcount' hprec htiles

/-- Monomial bounds compose with explicitly derived resource polynomials. -/
theorem compose_bound {f g : ℕ → ℕ} (hf : Bound f) (hg : Bound g) : Bound (fun S => f (g S)) := by
  obtain ⟨C,k,hf⟩:=hf
  obtain ⟨A,d,hg⟩:=hg
  refine ⟨C*(A+1)^k,d*k,?_⟩
  intro S
  have hpow : 1 ≤ (S+1)^d := Nat.one_le_pow _ _ (by omega)
  have hbase : g S+1 ≤ (A+1)*(S+1)^d := by nlinarith only [hg S,hpow]
  calc
    _ ≤ C*(g S+1)^k := hf _
    _ ≤ C*((A+1)*(S+1)^d)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase k)
    _ = _ := by rw [mul_pow,←pow_mul]; ring

/-- The actual source supplier factor has fixed monomial witnesses. -/
theorem factor_monomial : Bound (fun S =>
    SemiprimeD1PhysicalSourcePolynomial.sourceFactor (inflation S)) := by
  apply compose_bound SemiprimeD1PhysicalSourcePolynomial.sourceFactor_monomial
  unfold inflation
  boundArithmetic

end RiemannGaussian.SemiprimeD1PhysicalNetworkSourceBudget
