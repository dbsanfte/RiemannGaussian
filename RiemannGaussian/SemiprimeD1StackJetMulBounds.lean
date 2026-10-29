/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetMulCorrectness
/-! # Closed polynomial dense-jet multiplication time and prefix storage
Every original coordinate executes the actual point program. The largest target
counter is bounded by the retained physical rank copy; no coefficient, route,
intermediate fit or execution-cost bound is supplied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackJetMulBounds
open SemiprimeD1StackJetMul SemiprimeD1StackJetMulExecution
open SemiprimeD1StackJetPointExecution (Cache)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1JetAxes (Context)

/-- Actual context/input inventory, including the longest physically copied target. -/
def inputSize (ctx : Context) (c : Cache) : ℕ :=
  SemiprimeD1StackJetPointBounds.inputSize ctx (indexed c c.rank)

/-- Each actual target length is bounded by the original retained rank counter. -/
theorem pointSize_le (ctx : Context) (c : Cache) (n : ℕ) (hrank : c.rank=unary ctx.rank) (hn : n ≤ ctx.rank) :
    SemiprimeD1StackJetPointBounds.inputSize ctx (indexed c (unary n)) ≤ inputSize ctx c := by
  have hr : c.rank.length=ctx.rank := by rw [hrank]; simp [unary]
  dsimp only [inputSize,SemiprimeD1StackJetPointBounds.inputSize,indexed]
  simp only [unary,List.length_replicate]
  omega

/-- Uniform original-data bound of one output-index iteration. -/
def roundBound (ctx : Context) (c : Cache) : ℕ :=
  1000000*(inputSize ctx c+1)^5+7*ctx.precision+10

/-- All included point/framing/cleanup work is derived under the actual target bound. -/
theorem bodyBudget_le (ctx : Context) (c : Cache) (n : ℕ) (hrank : c.rank=unary ctx.rank) (hn : n ≤ ctx.rank) :
    1+bodyBudget ctx c n ≤ roundBound ctx c := by
  have hs:=pointSize_le ctx c n hrank hn
  have hm : 1000000*(SemiprimeD1StackJetPointBounds.inputSize ctx (indexed c (unary n))+1)^5 ≤
      1000000*(inputSize ctx c+1)^5 := by gcongr
  unfold bodyBudget roundBound
  omega

/-- The literal original output-index loop has a derived uniform polynomial bound. -/
theorem loopClock_le (ctx : Context) (c : Cache) (n : ℕ) (hrank : c.rank=unary ctx.rank) (hn : n ≤ ctx.rank) :
    loopClock ctx c n ≤ (n+1)*roundBound ctx c := by
  induction n with
  | zero => simp only [loopClock,Nat.zero_add,Nat.one_mul]; unfold roundBound; omega
  | succ n ih =>
    have hn' : n ≤ ctx.rank := by omega
    have hb:=bodyBudget_le ctx c n hrank hn'
    have hi:=ih hn'
    change 1+bodyBudget ctx c n+loopClock ctx c n ≤ _
    nlinarith

/-- Pure fixed degree-six transition polynomial. -/
def polynomial (S : ℕ) : ℕ := 5*S+6+(S+1)*(1000000*(S+1)^5+7*S+10)

/-- A fixed numerical monomial bounds the exact transition polynomial. -/
theorem polynomial_le_power (S : ℕ) : polynomial S ≤ 2000000*(S+1)^6 := by
  unfold polynomial
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4),Nat.zero_le (S^5),Nat.zero_le (S^6)]

/-- Complete original dense multiplication report is genuinely actual transitions. -/
theorem totalClock_le (ctx : Context) (c : Cache) (hrank : c.rank=unary ctx.rank) :
    SemiprimeD1StackJetMulCorrectness.totalClock ctx c ≤ 2000000*(inputSize ctx c+1)^6 := by
  have hl:=loopClock_le ctx c ctx.rank hrank le_rfl
  have hr : c.rank.length ≤ inputSize ctx c := by
    dsimp only [inputSize,SemiprimeD1StackJetPointBounds.inputSize,indexed]
    omega
  have hR : ctx.rank ≤ inputSize ctx c := by
    dsimp only [inputSize,SemiprimeD1StackJetPointBounds.inputSize,indexed]
    omega
  have hp : ctx.precision ≤ inputSize ctx c := by
    dsimp only [inputSize,SemiprimeD1StackJetPointBounds.inputSize,indexed]
    omega
  have hm:=Nat.mul_le_mul_right (roundBound ctx c) (Nat.add_le_add_right hR 1)
  have hs : roundBound ctx c ≤ 1000000*(inputSize ctx c+1)^5+7*inputSize ctx c+10 := by
    unfold roundBound
    omega
  have ht:=Nat.mul_le_mul_left (inputSize ctx c+1) hs
  apply le_trans (b:=polynomial (inputSize ctx c))
  · unfold SemiprimeD1StackJetMulCorrectness.totalClock polynomial
    omega
  · exact polynomial_le_power _

/-- Closed actual original-input polynomial transition certificate. -/
theorem source_run_polynomial (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ 2000000*(inputSize ctx c+1)^6,
      SemiprimeD1StackCalls.run program m (initial c.a c.b c.axes c.width c.rank)=
        some (⟨none,none,none,data c [] [] (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackJetMulCorrectness.source_run ctx hp c a b ha hb haxes hwidth hrank
  exact ⟨m,hm.trans (totalClock_le ctx c hrank),hr⟩

/-- Genuine fixed finite-stack multiplication, all original arrays and context
relations only; no route/coefficient/cost/Fits supplier appears. -/
noncomputable def machineMultiplyPolynomial (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c.a c.b c.axes c.width c.rank))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,data c [] [] (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩:
          SemiprimeD1StackCalls.State Stack Label))) (2000000*(inputSize ctx c+1)^6) := by
  let h:=source_run_polynomial ctx hp c a b ha hb haxes hwidth hrank
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect (.inl (P.aux .a)) output Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- Actual successful prefixes cannot survive beyond the proved physical halt. -/
theorem prefix_fuel_le (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial c.a c.b c.axes c.width c.rank)=some out) :
    fuel ≤ 2000000*(inputSize ctx c+1)^6 := by
  obtain ⟨m,hm,hstop⟩:=source_run_polynomial ctx hp c a b ha hb haxes hwidth hrank
  by_contra hn
  have he : fuel=m+(1+(fuel-(m+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : SemiprimeD1StackCalls.run program 1
      (⟨none,none,none,data c [] [] (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩:
        SemiprimeD1StackCalls.State Stack Label)=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- All physically prepared input words are bounded by original inventory. -/
theorem initial_length (ctx : Context) (c : Cache) (k : Stack) :
    ((initial c.a c.b c.axes c.width c.rank).data k).length ≤ inputSize ctx c := by
  have hz : SemiprimeD1StackJetPointBounds.inputSize ctx (indexed c []) ≤ inputSize ctx c := by
    dsimp only [inputSize,SemiprimeD1StackJetPointBounds.inputSize,indexed]
    simp only [List.length_nil]
    omega
  rcases k with k|k
  · exact (SemiprimeD1StackJetPointBounds.initial_length ctx (indexed c []) k).trans hz
  · cases k <;> simp [initial,inputData]

/-- All successful source prefixes have polynomial Boolean data and return cells. -/
theorem prefix_cells (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial c.a c.b c.axes c.width c.rank)=some out) :
    (∑s:Stack,(out.data s).length)+out.frames.length ≤
      56*(inputSize ctx c+2000000*(inputSize ctx c+1)^6+1) := by
  have hf:=prefix_fuel_le ctx hp c a b ha hb haxes hwidth hrank fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize ctx c) _ out
    (initial_length ctx c) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframes
  have hs : (∑s:Stack,(out.data s).length) ≤ 55*(inputSize ctx c+fuel) := by
    calc
      _ ≤ ∑_s:Stack,(inputSize ctx c+fuel) := Finset.sum_le_sum (fun s _=>hd s)
      _ = 55*(inputSize ctx c+fuel) := by
        have hc : Fintype.card Stack=55 := by decide
        simp [hc]
  omega

/-- The same unconditional physical-cell cap holds for every compiled-machine prefix. -/
theorem machine_prefix_cells (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c.a c.b c.axes c.width c.rank)))=some cfg) :
    (∑s:Stack,(cfg.stk (some s)).length)+(cfg.stk none).length ≤
      56*(inputSize ctx c+2000000*(inputSize ctx c+1)^6+1) := by
  let start:=initial c.a c.b c.axes c.width c.rank
  have he:=SemiprimeD1StackCalls.run_correct (.inl (P.aux .a)) output Label.start program fuel start
  change (SemiprimeD1StackCalls.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:SemiprimeD1StackCalls.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells ctx hp c a b ha hb haxes hwidth hrank fuel out hc

end RiemannGaussian.SemiprimeD1StackJetMulBounds
