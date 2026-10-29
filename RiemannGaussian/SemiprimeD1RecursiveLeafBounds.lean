/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallPath
import RiemannGaussian.SemiprimeD1LeafCounterResources

/-! # Actual stopped calls have the original small-leaf scale
Failed native schedule tests and fuel exhaustion at the original root fuel are
both covered. The eager leaf's literal report is bounded using its actual
network, with every stored scope bound derived from canonical well-formed ports.
These are component-report bounds, not a full primitive-machine simulation.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveLeafBounds
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout SemiprimeD1JetAxes
open SemiprimeD1RecursiveCounter SemiprimeD1RecursiveCallTree
open SemiprimeD1Schedule SemiprimeD1LeafRate

/-- No actual active branch exists beyond the original logarithmic fuel cap. -/
theorem activeTest_false_of_depth (s depth M : ℕ)
    (hd : SemiprimeD1PackingReady.logarithm s < depth) :
    activeTest s (SemiprimeD1PackingReady.logarithm s) depth M = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ha
  have hp := active_positive _ _ _ _ ((activeTest_correct _ _ _ _).mp ha)
  exact (Nat.not_le_of_lt hd) (depth_le _ _ hp)

/-- Fuel zero at a state whose remaining fuel covers the original cap implies
the same failed actual schedule test as an ordinary stopped call. -/
theorem zero_fuel_inactive (s depth : ℕ)
    (hf : SemiprimeD1PackingReady.logarithm s+1 ≤ depth+0) (M : ℕ) :
    activeTest s (SemiprimeD1PackingReady.logarithm s) depth M = false :=
  activeTest_false_of_depth s depth M (by omega)

/-- Failure of any literal test gives a genuinely small actual leaf. -/
theorem stopped_edges (s : ℕ) (call : Call)
    (hr : RootReady s (SemiprimeD1PackingReady.logarithm s))
    (hpath : edgeCount call.net*8^call.depth ≤ s)
    (hstop : activeTest s (SemiprimeD1PackingReady.logarithm s)
      call.depth (edgeCount call.net) = false) :
    edgeCount call.net ≤ leafSize s (SemiprimeD1PackingReady.logarithm s) := by
  apply inactive_leaf _ _ _ _ hr hpath
  intro ha
  have ht := (activeTest_correct _ _ _ _).mpr ha
  rw [hstop] at ht
  exact Bool.false_ne_true ht

/-- The actual root fuel suffices to make every executed fuel-zero leaf small;
no size promise about a stopped child is assumed. -/
theorem zero_fuel_edges (s : ℕ) (call : Call)
    (hr : RootReady s (SemiprimeD1PackingReady.logarithm s))
    (hpath : edgeCount call.net*8^call.depth ≤ s)
    (hf : SemiprimeD1PackingReady.logarithm s+1 ≤ call.depth+0) :
    edgeCount call.net ≤ leafSize s (SemiprimeD1PackingReady.logarithm s) :=
  stopped_edges s call hr hpath (zero_fuel_inactive s call.depth hf (edgeCount call.net))

/-- Canonical actual network ports give the full local-scope sum cap. -/
theorem scopeSize_le (net : Network) (hw : WellFormed net) :
    SemiprimeD1LeafCounterBounds.scopeSize (vertices net) ≤
      (vertices net).length*edgeCount net := by
  have hcap : ∀v∈vertices net,v.ports.length ≤ edgeCount net := by
    intro v hv
    exact SemiprimeD1LeafCounterResources.scope_length_of_nodup (edgeCount net) v
      (wellFormed_vertices net hw v hv) (vertex_ports_nodup net hw v hv)
  generalize vertices net = xs at hcap ⊢
  induction xs with
  | nil => simp [SemiprimeD1LeafCounterBounds.scopeSize]
  | cons v vs ih =>
    have hh := hcap v List.mem_cons_self
    have ht := ih (fun w hw => hcap w (List.mem_cons_of_mem v hw))
    simp only [SemiprimeD1LeafCounterBounds.scopeSize] at ht
    simp only [SemiprimeD1LeafCounterBounds.scopeSize,List.map_cons,List.sum_cons,
      List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- A fixed actual-data size suffices for every argument of the leaf polynomial.
The definition contains neither a solved value nor an external work budget. -/
def cofactorSize (ctx : Context) (net : Network) : ℕ :=
  ctx.axes.length+ctx.rank+ctx.precision+edgeCount net+
    (edgeCount net+1)*((vertices net).length+1)+1

/-- The entire eager leaf report has one fixed polynomial cofactor. -/
theorem leaf_clock (ctx : Context) (net : Network) (hw : WellFormed net)
    (hg : Good ctx net) :
    (leaf ctx net).clock ≤ 100000*(cofactorSize ctx net+1)^8*2^edgeCount net := by
  have hscope := scopeSize_le net hw
  have hv : (vertices net).length ≤ (edgeCount net+1)*((vertices net).length+1) := by
    nlinarith
  have hscope' : SemiprimeD1LeafCounterBounds.scopeSize (vertices net) ≤
      (edgeCount net+1)*((vertices net).length+1) := by nlinarith
  apply SemiprimeD1LeafCounterResources.run_clock_polynomial _ _ _ hg (cofactorSize ctx net)
  all_goals unfold cofactorSize;omega

/-- Both failed guards and exhausted original fuel obey the same full eager
report bound, whose exponential part is fixed by the actual original input. -/
theorem stopped_leaf_clock (s : ℕ) (call : Call)
    (hr : RootReady s (SemiprimeD1PackingReady.logarithm s))
    (hpath : edgeCount call.net*8^call.depth ≤ s)
    (hstop : activeTest s (SemiprimeD1PackingReady.logarithm s)
      call.depth (edgeCount call.net) = false)
    (hw : WellFormed call.net) (hg : Good call.ctx call.net) :
    (leaf call.ctx call.net).clock ≤
      100000*(cofactorSize call.ctx call.net+1)^8*
        2^leafSize s (SemiprimeD1PackingReady.logarithm s) := by
  have hm := stopped_edges s call hr hpath hstop
  exact (leaf_clock call.ctx call.net hw hg).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm))

/-- The retained input and global output tables also obey the actual small-leaf
scale. Native address cells are inventory here, not a tape-time claim. -/
theorem stopped_leaf_storage (s : ℕ) (call : Call)
    (hr : RootReady s (SemiprimeD1PackingReady.logarithm s))
    (hpath : edgeCount call.net*8^call.depth ≤ s)
    (hstop : activeTest s (SemiprimeD1PackingReady.logarithm s)
      call.depth (edgeCount call.net) = false)
    (hw : WellFormed call.net) (hg : Good call.ctx call.net) :
    SemiprimeD1LeafCounterResources.retainedStorage (edgeCount call.net) call.ctx (vertices call.net) ≤
      SemiprimeD1LeafCounterBounds.scopeSize (vertices call.net)+
        ((vertices call.net).length+2)*((call.ctx.rank*(3*call.ctx.precision+4)+3)*
          2^leafSize s (SemiprimeD1PackingReady.logarithm s)) := by
  have h := SemiprimeD1LeafCounterResources.retainedStorage_of_wellFormed
    (edgeCount call.net) call.ctx (vertices call.net) hg (wellFormed_vertices call.net hw)
    (vertex_ports_nodup call.net hw)
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (stopped_edges s call hr hpath hstop)
  exact h.trans (by gcongr)

end RiemannGaussian.SemiprimeD1RecursiveLeafBounds
