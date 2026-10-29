/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildWordPolynomial
import RiemannGaussian.SemiprimeD1PhysicalChildGrowth

/-! # Original resource substitution for the actual word-only child
All scalar/context/inventory guards are discharged from original reachable data
at the final endpoint. Actual source and fresh reports stay linear and literal;
no old/new active clock equality is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1ChildWordOriginalPolynomial
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalOriginalPhaseBudget
open SemiprimeD1PhysicalChildPolynomial
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- The computed word-only child budget has a fixed polynomial scalar factor,
with actual parent inventory and each repeated source report retained. -/
theorem budget_bound (parent : Call) (lam a u : ℕ) (i : Fin a) (Z S : ℕ)
    (hw : WellFormed parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hMlog : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hprecision : parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (hreserve : (a+1)*u ≤ 2^(a-i.val))
    (hn : parent.net.leftCount ≤ S) (hF : parent.net.rows.length ≤ S)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S)
    (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S) (hD : 2^((9*lam+9)/10) ≤ S)
    (hInventory : SemiprimeD1NetworkStateResources.inventory parent.net ≤ S) :
    SemiprimeD1ChildWordOriginalClock.budget parent.net parent.ctx
      [SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)]
      (2^((9*lam+9)/10)) a u i Z ≤
    ((edgeCount parent.net+1)*
      ((SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).work+Z)+
      SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a)*2^(3*(2^((9*lam+9)/10))) := by

  let src:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let K:=SemiprimeD1ChildModeResources.catalogueLength parent.net a u i parent.ctx.precision
  let E:=SemiprimeD1PacketReplayBudget.budget parent.net.leftCount parent.net.rows.length
    64 a (edgeCount parent.net)
  let H:=SemiprimeD1PacketModeMaskBudget.prepareOverhead parent.net.leftCount parent.net.rows.length
    64 a (edgeCount parent.net) src.precision
  have hSI:=le_inflation S
  have hIU : inflation S ≤ scalarCap S := Nat.le_add_right _ _
  have hSU:=hSI.trans hIU
  have hmeta : SemiprimeD1ChildMetadataPolynomial.envelope (inflation S) ≤ scalarCap S :=
    Nat.le_add_left _ _
  have hprec : src.precision ≤ scalarCap S :=
    (precision_bound parent a u i S hu huM hM ha hp hN).trans hIU
  have hq : q ≤ scalarCap S := (fresh_axis_bound parent a u i S huM hM).trans hIU
  have hscalar : 2*S ≤ inflation S ∧ 2*S^2 ≤ inflation S ∧ 246*S^2 ≤ inflation S := by
    have hquad:=quadratic_le_inflation S
    constructor
    · nlinarith only [hquad]
    have hs2:=Nat.pow_le_pow_left (Nat.le_succ S) 2
    exact ⟨(Nat.mul_le_mul (by decide : 2 ≤ 1000) hs2).trans hquad,
      (Nat.mul_le_mul (by decide : 246 ≤ 1000) hs2).trans hquad⟩
  have hNF : parent.net.leftCount+parent.net.rows.length ≤ scalarCap S := by
    have h : parent.net.leftCount+parent.net.rows.length ≤ 2*S := by omega
    exact h.trans (hscalar.1.trans hIU)
  have hlinks : 2*(edgeCount parent.net)^2 ≤ scalarCap S :=
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hM 2)).trans (hscalar.2.1.trans hIU)
  have hpow : 2^a ≤ scalarCap S :=
    ((Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_succ a)).trans hN).trans hSU
  have hA : 2*2^a ≤ scalarCap S := by
    have hn' : 2^a ≤ S := (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_succ a)).trans hN
    exact (Nat.mul_le_mul_left 2 hn').trans (hscalar.1.trans hIU)
  have hK0:=SemiprimeD1ChildModeResources.catalogue_quadratic parent.net hw _ a u i
    parent.ctx.precision hd hsmall hsize hu huM hprecision hreserve
  have hK : K ≤ scalarCap S :=
    hK0.trans ((Nat.mul_le_mul_left 246 (Nat.pow_le_pow_left hM 2)).trans
      (hscalar.2.2.trans hIU))
  have hm:=metadata_fields parent a u i S hu huM hn hF hM ha hp hN hL
  dsimp only at hm
  have hdata:=hm.1.trans hmeta
  have hgraph:=hm.2.1.trans hmeta
  have horder:=hm.2.2.1.trans hmeta
  have hprepare : H ≤ scalarCap S := hm.2.2.2.1.trans hmeta
  have hreplay : E ≤ scalarCap S := hm.2.2.2.2.trans hmeta
  have hone : 1 ≤ scalarCap S := by
    have hquad:=quadratic_le_inflation S
    have hI : 1 ≤ inflation S := by
      have hpos:=Nat.one_le_pow (2:ℕ) (S+1) (by omega)
      nlinarith only [hquad,hpos]
    exact hI.trans hIU
  have hinv:=hInventory.trans hSU
  have hb:=SemiprimeD1ChildWordPolynomial.prefactor_le_envelope parent.ctx [q]
    src.precision a (2^((9*lam+9)/10)) (2*2^a) K src.precision (2^a) src.precision K E
    (parent.net.leftCount+parent.net.rows.length) (edgeCount parent.net)
    (SemiprimeD1NetworkStateResources.inventory parent.net)
    (SemiprimeD1ChildOriginalClock.dataCap parent.net a)
    (SemiprimeD1ChildOriginalClock.graphCap parent.net a)
    (SemiprimeD1ChildOriginalClock.orderCap parent.net a) H (scalarCap S)
    (hrank.trans hSU) (hp.trans hSU) (haxes.trans hSU)
    (by simpa using hq) (by simpa using hone) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hprec
      · exact hD.trans hSU
      · exact hA
      · exact hK
      · exact hprec
      · exact hpow
      · exact hprec
      · exact hK
      · exact hreplay
      · exact hNF
      · exact hM.trans hSU
      · exact hinv
      · exact hdata
      · exact hgraph
      · exact horder
      · exact hprepare)
  have hcoef:=SemiprimeD1ChildModeResources.coefficient_envelope parent.net hw lam a u i
    parent.ctx.precision hlam haSmall hMlog hd hsmall hsize hu huM hprecision hreserve
  have hf:=SemiprimeD1ChildWordClockFactor.sourceFree_factor parent.net parent.ctx [q]
    (2^((9*lam+9)/10)) a u i hcoef
  have hmports : SemiprimeD1ChildOriginalClock.ports parent.net=edgeCount parent.net :=
    (SemiprimeD1TensorNetwork.scope_eq_sum parent.net.rows).symm
  rw [hmports] at hf
  dsimp only at hf
  have hfree := hf.trans (Nat.mul_le_mul_right _ hb)
  rw [SemiprimeD1ChildWordBudgetLinear.budget_linear,hmports]
  have hcap : 1 ≤ 2^(3*(2^((9*lam+9)/10))) := Nat.one_le_two_pow
  have hsource : (edgeCount parent.net+1)*(src.work+Z) ≤
      ((edgeCount parent.net+1)*(src.work+Z))*2^(3*(2^((9*lam+9)/10))) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((edgeCount parent.net+1)*(src.work+Z)) hcap
  calc
    _ ≤ ((edgeCount parent.net+1)*(src.work+Z))*2^(3*(2^((9*lam+9)/10)))+
        SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a*2^(3*(2^((9*lam+9)/10))) :=
      Nat.add_le_add hsource hfree
    _ = _ := by ring



/-- Actual source/fresh linearity is combined with full physical tape scaling. -/
def childBudget (parent : Call) (lam a u : ℕ) (i : Fin a) : ℕ :=
  SemiprimeD1ChildWordOriginalClock.budget parent.net parent.ctx
    [SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)]
    (2^((9*lam+9)/10)) a u i (fresh parent a u i).clock

/-- Fixed scalar factor, keeping the ACTUAL mode-menu cardinality outside. -/
def factor (S a : ℕ) : ℕ :=
  (S+1)*(SemiprimeD1PhysicalSourcePolynomial.sourceFactor
    (SemiprimeD1PhysicalNetworkSourceBudget.inflation S)+freshBudget S)+
  SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a

/-- Closed original-data bound of the actual new word-only child report. -/
theorem child_budget_bound (parent : Call) (lam a u : ℕ) (i : Fin a) (S : ℕ)
    (hw : WellFormed parent.net)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hMlog : edgeCount parent.net ≤ 2^lam)
    (hd : DegreeBound parent.net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount parent.net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount parent.net)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hprecision : parent.ctx.precision*u ≤ edgeCount parent.net*2^(a-i.val))
    (hreserve : (a+1)*u ≤ 2^(a-i.val))
    (hn : parent.net.leftCount ≤ S) (hF : parent.net.rows.length ≤ S)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hrank : parent.ctx.rank ≤ S)
    (haxes : parent.ctx.axes.length ≤ S)
    (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S) (hD : 2^((9*lam+9)/10) ≤ S)
    (hInventory : SemiprimeD1NetworkStateResources.inventory parent.net ≤ S) :
    let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
    childBudget parent lam a u i ≤ factor S a*(source.modes.values.length+1)*2^(3*(2^((9*lam+9)/10))) := by

  let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let f:=SemiprimeD1PhysicalSourcePolynomial.sourceFactor
    (SemiprimeD1PhysicalNetworkSourceBudget.inflation S)
  let Z:=fresh parent a u i
  have hc:=budget_bound parent lam a u i Z.clock S hw hlam haSmall hMlog hd hsmall hsize hu huM
    hprecision hreserve hn hF hM ha hp hrank haxes hN hL hD hInventory
  have hs:=SemiprimeD1PhysicalNetworkSourceBudget.acquire_work parent.net hw _ a u i.val
    parent.ctx.precision S hd hsmall hsize hu huM i.isLt.le hn hF hM ha hp hN hL
  change source.work ≤ f*(source.modes.values.length+1) at hs
  have hprec:=precision_bound parent a u i S hu huM hM ha hp hN
  have hq:=fresh_axis_bound parent a u i S huM hM
  have hz0 : Z.clock ≤ 9*source.precision+3*(q*parent.ctx.rank)+10 :=
    SemiprimeD1FreshJetBits.acquireFresh_clock parent.ctx q source.precision
  have hz : Z.clock ≤ freshBudget S := hz0.trans (by
    unfold freshBudget
    gcongr)
  have hlen : 1 ≤ source.modes.values.length+1 := by omega
  have hzrep : freshBudget S ≤ freshBudget S*(source.modes.values.length+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (freshBudget S) hlen
  have hsum : source.work+Z.clock ≤ (f+freshBudget S)*(source.modes.values.length+1) := by
    calc
      _ ≤ f*(source.modes.values.length+1)+freshBudget S*(source.modes.values.length+1) :=
        Nat.add_le_add hs (hz.trans hzrep)
      _ = _ := by ring
  have hpre : SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a ≤
      SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a*(source.modes.values.length+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left
      (SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a) hlen
  have hinner := Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right hM 1) hsum) hpre
  dsimp only [factor]
  change childBudget parent lam a u i ≤ _
  apply hc.trans
  apply Nat.mul_le_mul_right _
  simpa only [f,source,Nat.add_mul,Nat.mul_assoc] using hinner


/-- Actual source-free physical/tape prefactor has fixed monomial growth. -/
theorem prefactor_monomial : SemiprimeD1ChildPrefactorPolynomial.Bound
    (fun S a => SemiprimeD1ChildWordPolynomial.envelope (scalarCap S) a) := by
  apply SemiprimeD1PhysicalChildGrowth.compose_bound
    SemiprimeD1ChildWordPolynomial.envelope_monomial
    SemiprimeD1PhysicalChildGrowth.scalarCap_monomial
  intro S
  exact (le_inflation S).trans (Nat.le_add_right _ _)

/-- The actual word-only child factor has fixed constants before all inputs. -/
theorem factor_monomial : SemiprimeD1ChildPrefactorPolynomial.Bound factor := by
  change SemiprimeD1ChildPrefactorPolynomial.Bound (fun S a => factor S a)
  unfold factor
  apply SemiprimeD1ChildPrefactorPolynomial.add_bound
  · apply SemiprimeD1ChildPrefactorPolynomial.mul_bound
    · exact SemiprimeD1ChildPrefactorPolynomial.add_bound
        SemiprimeD1ChildPrefactorPolynomial.scalar_bound
        (SemiprimeD1ChildPrefactorPolynomial.constant_bound 1)
    · apply SemiprimeD1ChildPrefactorPolynomial.add_bound
      · exact SemiprimeD1PhysicalChildGrowth.lift_bound
          SemiprimeD1PhysicalNetworkSourceBudget.factor_monomial
      · exact SemiprimeD1PhysicalChildGrowth.lift_bound
          SemiprimeD1PhysicalChildGrowth.freshBudget_monomial
  · exact prefactor_monomial

end RiemannGaussian.SemiprimeD1ChildWordOriginalPolynomial
