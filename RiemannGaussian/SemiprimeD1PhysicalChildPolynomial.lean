/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPrefactorPolynomial
import RiemannGaussian.SemiprimeD1ChildMetadataPolynomial
import RiemannGaussian.SemiprimeD1PhysicalOriginalPhaseBudget
import RiemannGaussian.SemiprimeD1PhysicalNetworkSourceBudget

/-! # Original child scalar resource substitution
Actual source menu/report multiplicities are retained. Numeric envelopes depend
only on original scalar dimension caps, not a supplied report or output height.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1PhysicalChildPolynomial
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalOriginalPhaseBudget
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Coarse polynomial enlargement for actual precision, catalogue and graph counts. -/
def inflation (S : ℕ) : ℕ := 1000*(S+1)^4

/-- Every original numeric metadata supplier is included after scalar enlargement. -/
def scalarCap (S : ℕ) : ℕ := inflation S+
  SemiprimeD1ChildMetadataPolynomial.envelope (inflation S)

/-- Original scalar dimensions are contained in the actual setup enlargement. -/
theorem le_inflation (S : ℕ) : S ≤ inflation S := by
  have h : S ≤ (S+1)^4 := by nlinarith [Nat.le_self_pow (by decide : 4 ≠ 0) (S+1)]
  unfold inflation
  omega

/-- A quadratic resource is contained in the fixed enlargement. -/
theorem quadratic_le_inflation (S : ℕ) : 1000*(S+1)^2 ≤ inflation S := by
  exact Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_right (by omega : 0 < S+1) (by decide : 2 ≤ 4))

/-- The acquired local precision has a closed original-dimension bound. -/
theorem precision_bound (parent : Call) (a u : ℕ) (i : Fin a) (S : ℕ)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hN : 2^(a+1) ≤ S) :
    (SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).precision ≤ inflation S := by
  have hh:=SemiprimeD1ModeRate.jetHeight_mul_le (edgeCount parent.net) u huM
  have hheight : SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u ≤ 4*edgeCount parent.net := by
    have hm:=Nat.mul_le_mul_left (SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u)
      (show 1 ≤ u by omega)
    simp only [Nat.mul_one] at hm
    omega
  have hpow : 2^(a-i.val) ≤ S :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : a-i.val ≤ a+1)).trans hN
  have hterm:=Nat.mul_le_mul (hheight.trans (Nat.mul_le_mul_left 4 hM)) hpow
  have hterm2:=Nat.mul_le_mul hM (Nat.add_le_add_right ha 1)
  have hactual:=SemiprimeD1OriginalModeAcquisition.precision_original parent.net.leftCount
    parent.net.rows.length 64 a u i.val parent.ctx.precision
    (arity parent.net.rows) (owner parent.net.rows)
  rw [SemiprimeD1TensorNetworkLayout.original_ports] at hactual
  change (SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).precision=
    SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net) u a i.val parent.ctx.precision at hactual
  rw [hactual]
  apply le_trans (b := 1000*(S+1)^2) ?_ (quadratic_le_inflation S)
  unfold SemiprimeD1ModeRate.workingPrecision
  nlinarith only [hterm,hterm2,hp]

/-- The actual new axis is small in the same original dimension cap. -/
theorem fresh_axis_bound (parent : Call) (a u : ℕ) (i : Fin a) (S : ℕ)
    (huM : u ≤ edgeCount parent.net) (hM : edgeCount parent.net ≤ S) :
    SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val) ≤ inflation S := by
  have h:= (Nat.mul_le_mul_left (SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u)
    (Nat.sub_le u i.val)).trans (SemiprimeD1ModeRate.jetHeight_mul_le _ _ huM)
  apply le_trans (b := 1000*(S+1)^2) ?_ (quadratic_le_inflation S)
  nlinarith only [h,hM]



/-- All original child metadata scalars are computed from original graph and
alphabet dimensions, with no supplier report premise. -/
theorem metadata_fields (parent : Call) (a u : ℕ) (i : Fin a) (S : ℕ)
    (hu : 0 < u) (huM : u ≤ edgeCount parent.net)
    (hn : parent.net.leftCount ≤ S) (hF : parent.net.rows.length ≤ S)
    (hM : edgeCount parent.net ≤ S) (ha : a ≤ S)
    (hp : parent.ctx.precision ≤ S) (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S) :
    let I:=inflation S
    let U:=SemiprimeD1ChildMetadataPolynomial.envelope I
    SemiprimeD1ChildOriginalClock.dataCap parent.net a ≤ U ∧
    SemiprimeD1ChildOriginalClock.graphCap parent.net a ≤ U ∧
    SemiprimeD1ChildOriginalClock.orderCap parent.net a ≤ U ∧
    SemiprimeD1PacketModeMaskBudget.prepareOverhead parent.net.leftCount parent.net.rows.length
      64 a (edgeCount parent.net)
      (SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).precision ≤ U ∧
    SemiprimeD1PacketReplayBudget.budget parent.net.leftCount parent.net.rows.length
      64 a (edgeCount parent.net) ≤ U := by
  let I:=inflation S
  have hSI:=le_inflation S
  have h64 : 64 ≤ I := by dsimp only [I,inflation]; nlinarith [Nat.one_le_pow (4:ℕ) (S+1) (by omega)]
  have hNI : 2^a ≤ I :=
    ((Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_succ a)).trans hN).trans hSI
  have hprec:=precision_bound parent a u i S hu huM hM ha hp hN
  have hr:=SemiprimeD1PhysicalSourcePolynomial.replay_budget parent.net.leftCount parent.net.rows.length
    64 a (edgeCount parent.net) I (by decide) (hn.trans hSI) (hF.trans hSI) h64
    (ha.trans hSI) (hM.trans hSI) (hL.trans hSI)
  have hg:=SemiprimeD1ChildMetadataPolynomial.graph_bound parent.net.leftCount parent.net.rows.length
    64 a (edgeCount parent.net) I (by decide) (hn.trans hSI) (hF.trans hSI) h64
    (ha.trans hSI) (hM.trans hSI) (hL.trans hSI)
  have hd:=SemiprimeD1ChildMetadataPolynomial.pullback_bound parent.net.leftCount parent.net.rows.length
    64 a (edgeCount parent.net) I (by decide) (hn.trans hSI) (hF.trans hSI) h64
    (ha.trans hSI) (hM.trans hSI) (hL.trans hSI)
  have hpr:=SemiprimeD1ChildMetadataPolynomial.prepare_bound parent.net.leftCount parent.net.rows.length
    64 a (edgeCount parent.net)
    (SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).precision I (by decide)
    (hn.trans hSI) (hF.trans hSI) h64 (ha.trans hSI) (hM.trans hSI) hprec (hL.trans hSI) hNI
  have ho : SemiprimeD1ChildOrderBudget.overhead (edgeCount parent.net) (2*(edgeCount parent.net)^2) ≤
      SemiprimeD1ChildOrderBudget.overhead I (2*I^2) := by
    unfold SemiprimeD1ChildOrderBudget.overhead
    gcongr <;> exact hM.trans hSI
  have he:=SemiprimeD1ChildMetadataPolynomial.components I
  have hm : (∑ e,arity parent.net.rows e)=edgeCount parent.net :=
    (SemiprimeD1TensorNetwork.scope_eq_sum parent.net.rows).symm
  dsimp only
  simp only [SemiprimeD1ChildOriginalClock.dataCap,SemiprimeD1ChildOriginalClock.graphCap,
    SemiprimeD1ChildOriginalClock.orderCap,SemiprimeD1ChildOriginalClock.ports,
    hm]
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  unfold SemiprimeD1ChildMetadataPolynomial.envelope at he ⊢
  dsimp only [I] at *
  omega



/-- The complete original child prefactor is a fixed scalar envelope; actual
source/fresh reports stay outside it at their exact repeated multiplicity. -/
theorem original_budget_bound (parent : Call) (lam a u : ℕ) (i : Fin a) (Z S : ℕ)
    (hw : WellFormed parent.net)
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
    (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S) (hD : 2^((9*lam+9)/10) ≤ S) :
    SemiprimeD1ChildOriginalClock.originalBudget parent.net parent.ctx
      [SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)] lam a u i Z ≤
    ((edgeCount parent.net+1)*
      ((SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i).work+Z)+
      SemiprimeD1ChildPrefactorPolynomial.envelope (scalarCap S) a)*2^(2^((9*lam+9)/10)) := by
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
  have hb:=SemiprimeD1ChildPrefactorPolynomial.prefactor_le_envelope parent.ctx [q]
    src.precision a (2^((9*lam+9)/10)) (2*2^a) K src.precision (2^a) src.precision K E
    (parent.net.leftCount+parent.net.rows.length) (edgeCount parent.net) (2*(edgeCount parent.net)^2)
    0 (SemiprimeD1ChildOriginalClock.dataCap parent.net a)
    (SemiprimeD1ChildOriginalClock.graphCap parent.net a) 0
    (SemiprimeD1ChildOriginalClock.orderCap parent.net a) H (scalarCap S)
    (hrank.trans hSU) (hp.trans hSU) (haxes.trans hSU)
    (by simpa using hq) (by simpa using hone) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
      · exact hlinks
      · exact Nat.zero_le _
      · exact hdata
      · exact hgraph
      · exact Nat.zero_le _
      · exact horder
      · exact hprepare)
  have hmports : SemiprimeD1ChildOriginalClock.ports parent.net=edgeCount parent.net :=
    (SemiprimeD1TensorNetwork.scope_eq_sum parent.net.rows).symm
  unfold SemiprimeD1ChildOriginalClock.originalBudget
  rw [hmports]
  dsimp only
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hb _)



/-- Explicit original dimension bound for the actual acquired fresh-axis word. -/
def freshBudget (S : ℕ) : ℕ := 9*inflation S+3*(inflation S*S)+10

/-- Polynomial factor multiplying the ACTUAL acquired mode-list multiplicity. -/
def factor (S a : ℕ) : ℕ :=
  (S+1)*(SemiprimeD1PhysicalSourcePolynomial.sourceFactor
    (SemiprimeD1PhysicalNetworkSourceBudget.inflation S)+freshBudget S)+
  SemiprimeD1ChildPrefactorPolynomial.envelope (scalarCap S) a

/-- Every original child-constructor report is closed in original scalar caps;
its acquired source/menu multiplicity remains literal and is not shared away. -/
theorem child_budget_bound (parent : Call) (lam a u : ℕ) (i : Fin a) (S : ℕ)
    (hw : WellFormed parent.net)
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
    (hN : 2^(a+1) ≤ S) (hL : 64^a ≤ S) (hD : 2^((9*lam+9)/10) ≤ S) :
    let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
    childBudget parent lam a u i ≤ factor S a*(source.modes.values.length+1)*2^(2^((9*lam+9)/10)) := by
  let source:=SemiprimeD1ChildOriginalClock.source parent.net parent.ctx a u i
  let q:=SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u*(u-i.val)
  let f:=SemiprimeD1PhysicalSourcePolynomial.sourceFactor
    (SemiprimeD1PhysicalNetworkSourceBudget.inflation S)
  let Z:=fresh parent a u i
  have hc:=original_budget_bound parent lam a u i Z.clock S hw hd hsmall hsize hu huM
    hprecision hreserve hn hF hM ha hp hrank haxes hN hL hD
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
  have hpre : SemiprimeD1ChildPrefactorPolynomial.envelope (scalarCap S) a ≤
      SemiprimeD1ChildPrefactorPolynomial.envelope (scalarCap S) a*(source.modes.values.length+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left
      (SemiprimeD1ChildPrefactorPolynomial.envelope (scalarCap S) a) hlen
  have hinner := Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right hM 1) hsum) hpre
  dsimp only [factor]
  change childBudget parent lam a u i ≤ _
  apply hc.trans
  apply Nat.mul_le_mul_right _
  simpa only [f,source,Nat.add_mul,Nat.mul_assoc] using hinner

end RiemannGaussian.SemiprimeD1PhysicalChildPolynomial
