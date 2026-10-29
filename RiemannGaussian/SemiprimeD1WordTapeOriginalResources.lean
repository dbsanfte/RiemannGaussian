/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeFramePolynomial
import RiemannGaussian.SemiprimeD1OriginalScalarResources
import RiemannGaussian.SemiprimeD1OriginalInventoryScalar
import RiemannGaussian.SemiprimeD1RecursiveCallModes

/-! # Original reachable-state substitution for actual word-only reports
The scalar and heap inventory caps are derived from actual original-state
invariants. Source menus and repeated producers remain attached to actual loops.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1WordTapeOriginalResources
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCounter
open SemiprimeD1OriginalStateResources SemiprimeD1PackingReady
open SemiprimeD1OriginalEnvelopeRate (scalar)

/-- Common cap includes actual table inventory; its eager scale stays explicit. -/
def commonCap (s : ℕ) : ℕ := 100*(scalar s+1)^4*2^(degreeCap s)

/-- Every original scalar is included without changing the actual exponent a. -/
theorem scalar_le_common (s : ℕ) : scalar s ≤ commonCap s :=
  SemiprimeD1OriginalInventoryScalar.scalar_le_storageCap _ _ Nat.one_le_two_pow

/-- Fixed original data invariants bound every executed active local report.
The only remaining guards here are the original packing and path inequalities;
the original-input family endpoint discharges them from actual reachability. -/
theorem active_monomial : ∃ C k : ℕ,∀ (s : ℕ) (call : Call),
    1000 ≤ logarithm s → Bound s call → WellFormed call.net → Good call.ctx call.net →
    call.ctx.precision ≤ SemiprimeD1PrecisionEnvelope.pathCap s (logarithm s) call.depth
      (SemiprimeD1Schedule.previous (logarithm s) call.depth) →
    activeTest s (logarithm s) call.depth (edgeCount call.net)=true →
    2*(64^(2*SemiprimeD1Schedule.exponent (logarithm s) call.depth))^2*degreeCap s ≤ edgeCount call.net →
    64^(2*SemiprimeD1Schedule.exponent (logarithm s) call.depth)*
      2^SemiprimeD1Schedule.exponent (logarithm s) call.depth ≤ edgeCount call.net →
    SemiprimeD1WordTapeFrameBudget.budget s call ≤
      C*(scalar s+1)^k*2^(C*degreeCap s)*((children s call).length+1)^2 := by
  obtain ⟨C,k,hmono⟩:=SemiprimeD1WordTapeFramePolynomial.frameFactor_monomial
  refine ⟨C*101^k+k+3,4*k,?_⟩
  intro s call hl hb hw hg hpath hactive hsmall hsize
  let a:=SemiprimeD1Schedule.exponent (logarithm s) call.depth
  let u:=SemiprimeD1Schedule.levels (logarithm s) call.depth
  let U:=commonCap s
  let X:=scalar s
  let D:=2^(degreeCap s)
  have hSU : scalar s ≤ U := scalar_le_common s
  have haSmall : a ≤ 4*(logarithm s/131072) := SemiprimeD1Schedule.exponent_le _ _
  have hc:=SemiprimeD1OriginalScalarResources.of_bound s call a hl hb haSmall
  have hbase:=SemiprimeD1OriginalScalarResources.base_caps s hl
  have hdegree:degreeCap s ≤ scalar s:=SemiprimeD1OriginalScalarResources.degreeCap_le s hl
  have hInventory : SemiprimeD1NetworkStateResources.inventory call.net ≤ U :=
    hb.inventory.trans (SemiprimeD1OriginalInventoryScalar.inventoryCap_le s hl)
  have hAct:=(activeTest_correct _ _ _ _).mp hactive
  have hpGuard : ∀i : Fin a,i.val < u → call.ctx.precision*u ≤ edgeCount call.net*2^(a-i.val) := by
    intro i hi
    exact (SemiprimeD1RecursiveCallModes.state_guards s call hAct hpath i.val hi).2.1
  have haGuard : ∀i : Fin a,i.val < u → (a+1)*u ≤ 2^(a-i.val) := by
    intro i hi
    exact (SemiprimeD1RecursiveCallModes.state_guards s call hAct hpath i.val hi).2.2
  have hf:=SemiprimeD1WordTapeFramePolynomial.budget_active_bound s call a u U rfl rfl hactive
    hw hg hl hb.degree hsmall hsize hb.edge_count hpGuard haGuard
    (hc.left.trans hSU) (hc.rows.trans hSU) (hc.edges.trans hSU) (hc.exponent.trans hSU)
    (hc.precision.trans hSU) (hc.rank.trans hSU) (hc.axes.trans hSU)
    (hc.grid.trans hSU) (hc.groups.trans hSU) (hdegree.trans hSU) hInventory
    (hbase.1.trans hSU) ((by omega : logarithm s ≤ scalar s).trans hSU) (hc.depth.trans hSU)
  have hpow : 2^a ≤ U :=
    ((Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_succ a)).trans hc.grid).trans hSU
  have hm:=hmono U a (hc.exponent.trans hSU) hpow
  have hD : 1 ≤ D := Nat.one_le_two_pow
  have hbaseU : U+1 ≤ 101*(X+1)^4*D := by
    have hx : 1 ≤ (X+1)^4 := Nat.one_le_pow _ _ (by omega)
    change 100*(X+1)^4*D+1 ≤ 101*(X+1)^4*D
    have hunit : 1 ≤ (X+1)^4*D := one_le_mul_of_one_le_of_one_le hx hD
    nlinarith only [hunit]
  have hpower : C*(U+1)^k ≤ C*101^k*(X+1)^(4*k)*2^(k*degreeCap s) := by
    calc
      _ ≤ C*(101*(X+1)^4*D)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbaseU k)
      _ = _ := by
        dsimp only [D]
        rw [show k*degreeCap s=degreeCap s*k by ring,pow_mul]
        simp only [mul_pow,pow_mul]
        ring
  have hscale : C*(U+1)^k*2^(3*degreeCap s) ≤
      (C*101^k+k+3)*(scalar s+1)^(4*k)*2^((C*101^k+k+3)*degreeCap s) := by
    calc
      _ ≤ (C*101^k*(X+1)^(4*k)*2^(k*degreeCap s))*2^(3*degreeCap s) :=
        Nat.mul_le_mul_right _ hpower
      _ = C*101^k*(X+1)^(4*k)*2^((k+3)*degreeCap s) := by rw [Nat.mul_assoc,←pow_add];congr 1;ring
      _ ≤ _ := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_right _ (by omega)
        · apply Nat.pow_le_pow_right (by decide)
          exact Nat.mul_le_mul_right _ (by omega)
  calc
    _ ≤ SemiprimeD1WordTapeFramePolynomial.frameFactor U a*((children s call).length+1)^2*
        2^(3*degreeCap s) := hf
    _ = (SemiprimeD1WordTapeFramePolynomial.frameFactor U a*2^(3*degreeCap s))*
        ((children s call).length+1)^2 := by ring
    _ ≤ (C*(U+1)^k*2^(3*degreeCap s))*((children s call).length+1)^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)
    _ ≤ _ := Nat.mul_le_mul_right _ hscale



/-- CLOSED original binary-input family: every actually reached active call
obeys the uniform report bound, without packing/precision/clock advice. -/
theorem eventually_original_active : ∃ C k : ℕ,∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) (call : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) call →
      activeTest (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)) call.depth (edgeCount call.net)=true →
      SemiprimeD1WordTapeFrameBudget.budget (SemiprimeD1PublicPackingReady.scale ell) call ≤
        C*(scalar (SemiprimeD1PublicPackingReady.scale ell)+1)^k*
          2^(C*degreeCap (SemiprimeD1PublicPackingReady.scale ell))*
          ((children (SemiprimeD1PublicPackingReady.scale ell) call).length+1)^2 := by
  obtain ⟨C,k,hbound⟩:=active_monomial
  refine ⟨C,k,?_⟩
  have ht : Filter.Tendsto logarithm Filter.atTop Filter.atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (Filter.tendsto_add_atTop_nat 2)
  filter_upwards [eventually_original,
    scale_tendsto.eventually SemiprimeD1RecursiveCallPath.eventually_reach_invariant,
    scale_tendsto.eventually SemiprimeD1PackingReady.eventually_all_depths,
    (ht.comp scale_tendsto).eventually (Filter.eventually_ge_atTop (1000:ℕ))]
    with ell hstate hpath hpack hl
  intro N hN hEll fixed call hr hAct
  have hb:=hstate N hN hEll fixed call hr
  subst ell
  have hroot:=original_shape N hN fixed
  have hi:=hpath (originalCall N hN fixed) call rfl
    (SemiprimeD1RootStateResources.root_edges_le_scale N hN fixed) hroot.2.2.2
    hroot.1 hroot.2.1 hroot.2.2.1 (SemiprimeD1RootStateResources.root_global_degree N hN fixed) hr
  have hs:=SemiprimeD1RecursiveCallState.reach_shape _ _ _ hr hroot.1 hroot.2.1 hroot.2.2.1
  have hpk:=hpack call.depth (edgeCount call.net) _ ((activeTest_correct _ _ _ _).mp hAct) le_rfl
  exact hbound _ call hl hb hs.2.1 hs.2.2 hi.2.2 hAct hpk.1.le hpk.2.1.le

end RiemannGaussian.SemiprimeD1WordTapeOriginalResources
