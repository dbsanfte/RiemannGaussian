/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalEnvelopeRate

/-! # One uniform scalar for every actual original recursive call
The scalar is 2^((lambda+1)^3), with lambda the actual ceiling logarithm.
Every cap is derived from the original reachable-state bound. Full literal
table inventory still has its additional 2^delta factor; it is not silently
replaced by this scalar.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalScalarResources
open SemiprimeD1PackingReady SemiprimeD1OriginalStateResources
open SemiprimeD1OriginalEnvelopeRate SemiprimeD1RecursiveCallTree
open SemiprimeD1TensorNetwork SemiprimeD1Schedule

/-- The literal logarithm pays the original scale as a binary power. -/
theorem scale_le_power (s : ℕ) : s ≤ 2^logarithm s :=
  (show s ≤ s+2 by omega).trans (Nat.le_pow_clog (by decide:1<2) (s+2))

/-- Every smaller binary exponent is covered by the single actual scalar. -/
theorem power_le_scalar (s e : ℕ) (h:e ≤ (logarithm s+1)^3) : 2^e ≤ scalar s :=
  Nat.pow_le_pow_right (by decide:0<(2:ℕ)) h

/-- One linear exponent reserve covers all fixed coefficients used below. -/
theorem linear_exponent_bound (s : ℕ) (hl:1000 ≤ logarithm s) :
    24*(logarithm s+1) ≤ (logarithm s+1)^3 := by
  have hs:24 ≤ (logarithm s+1)^2:=by nlinarith
  calc
    _ ≤ (logarithm s+1)^2*(logarithm s+1) := Nat.mul_le_mul_right _ hs
    _ = _ := by ring

/-- Literal scale, vertex factor and logarithmic controls share the scalar. -/
theorem base_caps (s : ℕ) (hl:1000 ≤ logarithm s) :
    s ≤ scalar s ∧5*s ≤ scalar s ∧logarithm s+1 ≤ scalar s := by
  have hs:=scale_le_power s
  have he:=linear_exponent_bound s hl
  have hp:5*s ≤ 2^(logarithm s+3):=by
    rw [pow_add]
    norm_num
    omega
  have hlarge:=power_le_scalar s (logarithm s+3) (by omega)
  have hlog:logarithm s+1 ≤ 2^logarithm s:=Nat.lt_two_pow_self
  refine ⟨hs.trans (power_le_scalar s (logarithm s) (by omega)),hp.trans hlarge,
    hlog.trans (power_le_scalar s (logarithm s) (by omega))⟩

/-- Actual stored dense rank is within the scalar; every old axis is retained. -/
theorem rankCap_le (s : ℕ) (hl:1000 ≤ logarithm s) : rankCap s ≤ scalar s := by
  have hs:=scale_le_power s
  have hbase:4*s ≤ 2^(logarithm s+2):=by rw [pow_add];norm_num;omega
  calc
    _ ≤ (2^(logarithm s+2))^(logarithm s+1) := Nat.pow_le_pow_left hbase _
    _ = 2^((logarithm s+2)*(logarithm s+1)) := by rw [pow_mul]
    _ ≤ scalar s := power_le_scalar s _ (by
      have h:logarithm s+2 ≤ (logarithm s+1)^2:=by nlinarith
      calc
        _ ≤ (logarithm s+1)^2*(logarithm s+1) := Nat.mul_le_mul_right _ h
        _ = _ := by ring)

/-- Computed precision includes all previous increments and is still scalar. -/
theorem precisionCap_le (s : ℕ) (hl:1000 ≤ logarithm s) : precisionCap s ≤ scalar s := by
  have hs:=scale_le_power s
  have hlog:logarithm s+1 ≤ 2^logarithm s:=Nat.lt_two_pow_self
  have hp:precisionCap s ≤ 2^(7*logarithm s+8):=by
    calc
      _ ≤ (2^logarithm s)*(2^8*(2^logarithm s)^2)*2^(4*logarithm s) := by
        unfold precisionCap
        gcongr
        norm_num
      _ = _ := by rw [←pow_mul,←pow_add,←pow_add,←pow_add];congr 1;ring
  exact hp.trans (power_le_scalar s _ (by have h:=linear_exponent_bound s hl;omega))

/-- The actual rounded degree cap keeps its own exponential-table role. -/
theorem degreeCap_le (s : ℕ) (hl:1000 ≤ logarithm s) : degreeCap s ≤ scalar s := by
  unfold degreeCap
  apply power_le_scalar
  have hd:(9*logarithm s+9)/10 ≤ logarithm s+1:=by omega
  exact hd.trans (by have h:=linear_exponent_bound s hl;omega)

/-- Every dimension used in one actual reachable call, before source-specific
polynomial enlargement. This record stores inequalities only, never answers. -/
structure Caps (S : ℕ) (call : Call) (a : ℕ) : Prop where
  /-- Actual left-vertex count. -/
  left : call.net.leftCount ≤ S
  /-- Actual right-row count. -/
  rows : call.net.rows.length ≤ S
  /-- Actual edge occurrences. -/
  edges : edgeCount call.net ≤ S
  /-- Actual schedule exponent. -/
  exponent : a ≤ S
  /-- Actual computed scalar precision. -/
  precision : call.ctx.precision ≤ S
  /-- Actual dense jet rank. -/
  rank : call.ctx.rank ≤ S
  /-- Actual number of inherited axes. -/
  axes : call.ctx.axes.length ≤ S
  /-- Entire actual interpolation grid. -/
  grid : 2^(a+1) ≤ S
  /-- Entire actual group-power scale. -/
  groups : 64^a ≤ S
  /-- Actual depth. -/
  depth : call.depth ≤ S

/-- CLOSED actual-state substitution, without a dimension/precision supplier. -/
theorem of_bound (s : ℕ) (call : Call) (a : ℕ) (hl:1000 ≤ logarithm s)
    (hb:Bound s call) (ha:a ≤ 4*(logarithm s/131072)) : Caps (scalar s) call a := by
  have hc:=base_caps s hl
  have hv:=hb.vertex_count
  change call.net.leftCount+call.net.rows.length ≤ 5*s at hv
  have hal:a ≤ 4*logarithm s:=(ha.trans (Nat.mul_le_mul_left _ (Nat.div_le_self _ _)))
  have he:=linear_exponent_bound s hl
  have haexp:a+1 ≤ (logarithm s+1)^3:=by omega
  have hagroup:6*a ≤ (logarithm s+1)^3:=by omega
  have hag:a ≤ scalar s:=by
    have had:a ≤ 2^(a+1):=(Nat.lt_two_pow_self (n:=a+1)).le.trans' (by omega)
    exact had.trans (power_le_scalar s _ haexp)
  refine ⟨(show call.net.leftCount ≤ 5*s by omega).trans hc.2.1,
    (show call.net.rows.length ≤ 5*s by omega).trans hc.2.1,hb.edge_count.trans hc.1,hag,
    hb.precision.trans (precisionCap_le s hl),hb.rank.trans (rankCap_le s hl),
    ?_,power_le_scalar s _ haexp,?_,hb.depth.trans hc.2.2⟩
  · rw [hb.axes_length]
    exact hb.depth.trans hc.2.2
  · calc
      _ = (2^6)^a := by norm_num
      _ = 2^(6*a) := by rw [pow_mul]
      _ ≤ scalar s := power_le_scalar s _ hagroup

end RiemannGaussian.SemiprimeD1OriginalScalarResources
