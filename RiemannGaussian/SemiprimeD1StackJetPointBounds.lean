/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointCorrectness
/-! # Actual convolution-point polynomial transition bounds
Only physical input inventory and original context dimensions enter this bound.
All read lengths, partial sums and included component clocks are derived.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackJetPointBounds
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution SemiprimeD1StackJetPointLoops
open SemiprimeD1StackJetPointTerm SemiprimeD1StackJetPointRead
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Literal physical inventories and original scalar dimensions; no output,
intermediate fit, operation-cost or callback bound occurs in these caps. -/
structure Caps (ctx : Context) (c : Cache) (a b : List (List Bool)) (S : ℕ) : Prop where
  rank : ctx.rank ≤ S
  precision : ctx.precision ≤ S
  axes : ctx.axes.length ≤ S
  width : c.width.length ≤ S
  axisTape : c.axes.length ≤ S
  rankTape : c.rank.length ≤ S
  target : c.target.length ≤ S
  left : (vectorBits a).length ≤ S
  right : (vectorBits b).length ≤ S

/-- Every actual cached coefficient is shorter than its original encoded tape. -/
theorem coefficient_length (words : List (List Bool)) (i : ℕ) :
    ((words[i]?).getD []).length ≤ (vectorBits words).length := by
  induction words generalizing i with
  | nil => simp [vectorBits]
  | cons w ws ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.getD_some,vectorBits,List.length_cons,
        SemiprimeSourceHistogramKeyBits.frame_length]; omega
    | succ i =>
      have hh:=ih i
      simp only [List.getElem?_cons_succ]
      simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega

/-- Pure fixed polynomial monotonicity, separated from all program semantics. -/
theorem pipelineBudget_mono {n m c p N M C P : ℕ} (hn : n ≤ N) (hm : m ≤ M) (hc : c ≤ C) (hp : p ≤ P) :
    pipelineBudget n m c p ≤ pipelineBudget N M C P := by
  unfold pipelineBudget
  gcongr

/-- Uniform explicit cubic bound for one actual physical pair visit. -/
def pairBound (S : ℕ) : ℕ :=
  23*S+25+20000*(S+1)^2*(3*S+1)+(10*S+8)+(60*(2*S+2)+2)+pipelineBudget S S S S

/-- Every possible per-pair intermediate has a derived precision width. -/
theorem pairStep_length (ctx : Context) (a b : List (List Bool)) (k i j : ℕ) (acc : List Bool)
    (ha : acc.length ≤ ctx.precision) :
    (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,j) acc).length ≤ ctx.precision := by
  unfold SemiprimeD1StackJetPointOrder.pairStep
  split_ifs
  · exact SemiprimeD1JetScalarBits.add_length _ _ _
  · exact ha

/-- All literal per-pair calls have the cubic original-inventory cap. -/
theorem pairBudget_le (ctx : Context) (c : Cache) (a b : List (List Bool)) (S i j : ℕ) (acc : List Bool)
    (h : Caps ctx c a b S) (hi : i ≤ S) (hj : j ≤ S) (ha : acc.length ≤ ctx.precision) :
    pairBudget ctx c i j acc a b ≤ pairBound S := by
  have hac : acc.length ≤ S := ha.trans h.precision
  have hl:= (coefficient_length a i).trans h.left
  have hr:= (coefficient_length b j).trans h.right
  have hp:=pipelineTime_le ((a[i]?).getD []) ((b[j]?).getD []) acc c.width
  have hd:=pipelineBudget_mono hl hr hac h.width
  have hpipe:=hp.trans hd
  have hleft:=SemiprimeD1StackJetReadExecution.totalTime_le (unary i) a
  have hright:=SemiprimeD1StackJetReadExecution.totalTime_le (unary j) b
  unfold SemiprimeD1StackJetReadExecution.timeBound at hleft hright
  simp only [unary,List.length_replicate] at hleft hright
  have hread : readPipelineTime c.width (unary i) (unary j) acc a b ≤
      (10*S+8)+(60*(2*S+2)+2)+pipelineBudget S S S S := by
    dsimp only [readPipelineTime]
    simp only [unary,List.length_replicate]
    have hA:=h.left
    have hB:=h.right
    omega
  have hroute : SemiprimeD1StackJetRouteExecution.budget ctx.axes i j ≤
      20000*(S+1)^2*(3*S+1) := by
    unfold SemiprimeD1StackJetRouteExecution.budget
    have hprod : ctx.axes.prod ≤ S := h.rank
    gcongr
    · exact h.axes
    · omega
  have hax:=h.axisTape
  have htarget:=h.target
  unfold pairBudget pairBound
  omega

/-- Every executed inner prefix preserves the derived scalar precision cap. -/
theorem innerValue_length (ctx : Context) (a b : List (List Bool)) (k i n : ℕ) (acc : List Bool)
    (ha : acc.length ≤ ctx.precision) :
    (innerValue ctx a b k i n acc).length ≤ ctx.precision := by
  rw [innerValue_eq]
  exact SemiprimeD1StackJetPointOrder.accumulate_length _ _ _ _ _ _ ha

/-- The actual inner-loop report is linear in its physical iteration count. -/
theorem innerClock_le (ctx : Context) (c : Cache) (a b : List (List Bool)) (S k i n : ℕ) (acc : List Bool)
    (h : Caps ctx c a b S) (hi : i ≤ S) (hn : n ≤ S) (ha : acc.length ≤ ctx.precision) :
    innerClock ctx c a b k i n acc ≤ (n+1)*(pairBound S+2) := by
  induction n generalizing acc with
  | zero => simp only [innerClock,Nat.zero_add,Nat.one_mul]; omega
  | succ n ih =>
    have hn' : n ≤ S := by omega
    have hp:=pairBudget_le ctx c a b S i n acc h hi hn' ha
    have hs:=pairStep_length ctx a b k i n acc ha
    have hc:=ih _ hn' hs
    change 1+pairBudget ctx c i n acc a b+
      innerClock ctx c a b k i n (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,n) acc) ≤ _
    nlinarith

/-- Uniform explicit quartic per-row bound. -/
def rowBound (S : ℕ) : ℕ := (5*S+4)+(S+1)*(pairBound S+2)+2

/-- The actual outer-loop report is linear in its physical row count. -/
theorem outerClock_le (ctx : Context) (c : Cache) (a b : List (List Bool)) (S k rank n : ℕ) (acc : List Bool)
    (h : Caps ctx c a b S) (hr : rank ≤ S) (hn : n ≤ S) (ha : acc.length ≤ ctx.precision) :
    outerClock ctx c a b k rank n acc ≤ (n+1)*rowBound S := by
  induction n generalizing acc with
  | zero => simp only [outerClock,Nat.zero_add,Nat.one_mul]; unfold rowBound; omega
  | succ n ih =>
    have hn' : n ≤ S := by omega
    have hinner:=innerClock_le ctx c a b S k n rank acc h hn' hr ha
    have hscale:=Nat.mul_le_mul_right (pairBound S+2) (Nat.add_le_add_right hr 1)
    have hs:=innerValue_length ctx a b k n rank acc ha
    have hout:=ih _ hn' hs
    have hrt:=h.rankTape
    change 1+(5*c.rank.length+4)+innerClock ctx c a b k n rank acc+
      outerClock ctx c a b k rank n (innerValue ctx a b k n rank acc) ≤ _
    unfold rowBound at *
    nlinarith

/-- Fixed degree-five transition polynomial, without coefficients chosen from data. -/
def budget (S : ℕ) : ℕ := 5*S+5+(S+1)*rowBound S

/-- The whole actual coefficient execution has the fixed polynomial envelope. -/
theorem totalClock_le (ctx : Context) (c : Cache) (a b : List (List Bool)) (S k : ℕ)
    (h : Caps ctx c a b S) :
    SemiprimeD1StackJetPointCorrectness.totalClock ctx c a b k ≤ budget S := by
  have ho:=outerClock_le ctx c a b S k ctx.rank ctx.rank [] h h.rank h.rank (by simp)
  have hr:=h.rankTape
  unfold SemiprimeD1StackJetPointCorrectness.totalClock budget
  have hs:=Nat.mul_le_mul_right (rowBound S) (Nat.add_le_add_right h.rank 1)
  omega

/-- The explicit transition envelope is bounded by one fixed monomial. -/
theorem budget_le_power (S : ℕ) : budget S ≤ 1000000*(S+1)^5 := by
  unfold budget rowBound pairBound pipelineBudget
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4),Nat.zero_le (S^5)]

/-- Actual prepared input inventory and original context dimensions. -/
def inputSize (ctx : Context) (c : Cache) : ℕ :=
  ctx.rank+ctx.precision+ctx.axes.length+c.width.length+c.axes.length+c.rank.length+
    c.target.length+c.a.length+c.b.length+1

/-- Actual encoded inputs discharge all resource caps internally. -/
theorem caps_of_inputs (ctx : Context) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b) : Caps ctx c a b (inputSize ctx c) := by
  constructor
  · unfold inputSize; omega
  · unfold inputSize; omega
  · unfold inputSize; omega
  · unfold inputSize; omega
  · unfold inputSize; omega
  · unfold inputSize; omega
  · unfold inputSize; omega
  · rw [←ha]; unfold inputSize; omega
  · rw [←hb]; unfold inputSize; omega

/-- Closed original-input polynomial time, not a supplied operation-cost cap. -/
theorem source_run_polynomial (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ 1000000*(inputSize ctx c+1)^5,
      SemiprimeD1StackCalls.run program m (initial c.a c.b c.axes c.width c.rank c.target)=
        some (⟨none,none,none,resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits,[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackJetPointCorrectness.source_run ctx hp c a b k ha hb haxes hwidth htarget hrank
  exact ⟨m,hm.trans ((totalClock_le ctx c a b (inputSize ctx c) k (caps_of_inputs ctx c a b ha hb)).trans
    (budget_le_power _)),hr⟩

/-- Genuine compiled finite-machine coefficient execution in a fixed degree-five
polynomial of original inventory, rank, precision and physical target length. -/
noncomputable def machinePointPolynomial (ctx : Context) (hp : ctx.Positive) (c : Cache)
    (a b : List (List Bool)) (k : ℕ) (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c.a c.b c.axes c.width c.rank c.target))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits,[]⟩:
          SemiprimeD1StackCalls.State Stack Label))) (1000000*(inputSize ctx c+1)^5) := by
  let h:=source_run_polynomial ctx hp c a b k ha hb haxes hwidth htarget hrank
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect (aux .a) (aux .acc) Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- Every actual original successful prefix ends no later than the proved halt. -/
theorem prefix_fuel_le (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank)
    (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial c.a c.b c.axes c.width c.rank c.target)=some out) :
    fuel ≤ 1000000*(inputSize ctx c+1)^5 := by
  obtain ⟨m,hm,hstop⟩:=source_run_polynomial ctx hp c a b k ha hb haxes hwidth htarget hrank
  by_contra hn
  have he : fuel=m+(1+(fuel-(m+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : SemiprimeD1StackCalls.run program 1
      (⟨none,none,none,resting c [] [] (SemiprimeD1JetRingBits.mulAt ctx a b k).bits,[]⟩:
        SemiprimeD1StackCalls.State Stack Label)=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Every original physical stack word is initially bounded by input inventory. -/
theorem initial_length (ctx : Context) (c : Cache) (k : Stack) :
    ((initial c.a c.b c.axes c.width c.rank c.target).data k).length ≤ inputSize ctx c := by
  rw [SemiprimeD1StackJetPointCorrectness.initial_data]
  rcases k with k|k
  · simp [resting,inputSize]
  · rcases k with k|k
    · rcases k with k|k
      · simp [resting,inputSize]
      · cases k <;> simp [resting,inputSize]; omega
    · rcases k with k|k
      · simp [resting,inputSize]
      · cases k <;> simp [resting,inputSize] <;> omega

/-- All successful prefixes retain only polynomial Boolean data and real return cells. -/
theorem prefix_cells (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank)
    (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial c.a c.b c.axes c.width c.rank c.target)=some out) :
    (∑s:Stack,(out.data s).length)+out.frames.length ≤
      54*(inputSize ctx c+1000000*(inputSize ctx c+1)^5+1) := by
  have hf:=prefix_fuel_le ctx hp c a b k ha hb haxes hwidth htarget hrank fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize ctx c) _ out
    (initial_length ctx c) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframes
  have hs : (∑s:Stack,(out.data s).length) ≤ 53*(inputSize ctx c+fuel) := by
    calc
      _ ≤ ∑_s:Stack,(inputSize ctx c+fuel) := Finset.sum_le_sum (fun s _=>hd s)
      _ = 53*(inputSize ctx c+fuel) := by
        have hc : Fintype.card Stack=53 := by decide
        simp [hc]
  omega

/-- The same polynomial storage bound applies to every compiled-machine prefix. -/
theorem machine_prefix_cells (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool)) (k : ℕ)
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) (hrank : c.rank=unary ctx.rank)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c.a c.b c.axes c.width c.rank c.target)))=some cfg) :
    (∑s:Stack,(cfg.stk (some s)).length)+(cfg.stk none).length ≤
      54*(inputSize ctx c+1000000*(inputSize ctx c+1)^5+1) := by
  let start:=initial c.a c.b c.axes c.width c.rank c.target
  have he:=SemiprimeD1StackCalls.run_correct (aux .a) (aux .acc) Label.start program fuel start
  change (SemiprimeD1StackCalls.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:SemiprimeD1StackCalls.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells ctx hp c a b k ha hb haxes hwidth htarget hrank fuel out hc

end RiemannGaussian.SemiprimeD1StackJetPointBounds
