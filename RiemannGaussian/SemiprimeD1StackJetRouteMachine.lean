/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteExecution
/-! # Genuine finite-machine route time and every-prefix storage
The input is the explicitly prepared physical axis/index tapes. The fixed
program acquires every suffix and performs every actual digit calculation.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteMachine
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls SemiprimeD1StackJetRouteExecution
open SemiprimeD1StackJetRouteStep (bank_width)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => SemiprimeD1StackJetRoute.control

/-- Literal encoded argument inventory; caller acquisition is not silently free. -/
def inputSize (axes : List ℕ) (i j : ℕ) : ℕ :=
  (vectorBits (axes.map unary)).length+i+j

/-- A true FinTM2 time certificate for the SAME executed fixed instruction table.
Choice selects a proved bounded transition count only inside this proof object;
the executable code and physical path contain no choice or solved-value supplier. -/
noncomputable def routeInTime (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (i j : ℕ) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial ctx.axes i j))
      (some (SemiprimeD1StackCalls.configuration (final ctx.axes i j)))
      (budget ctx.axes i j+1) := by
  let m := Classical.choose (route_run ctx hp i j)
  have h := Classical.choose_spec (route_run ctx hp i j)
  exact SemiprimeD1StackCalls.evalsCorrect Stack.axes Stack.result (ctl .copyLeft) code
    (initial ctx.axes i j) (final ctx.axes i j) (budget ctx.axes i j+1)
    ⟨⟨m,h.2⟩,h.1⟩

/-- Every real source prefix has bounded physical Boolean stacks. -/
theorem prefix_data (axes : List ℕ) (i j fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run code fuel (initial axes i j)=some out) :
    ∀k,(out.data k).length ≤ inputSize axes i j+fuel := by
  have hw := bank_width (vectorBits (axes.map unary)) [] (unary i) (unary j) [] [] [] [] [] [] [] [] []
  simp only [List.length_nil,unary,List.length_replicate,Nat.add_zero] at hw
  exact SemiprimeD1StackReturnLink.run_data_bound code fuel (inputSize axes i j)
    (initial axes i j) out hw hr

/-- The actual finite-label return stack is also bounded at every prefix. -/
theorem prefix_frames (axes : List ℕ) (i j fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run code fuel (initial axes i j)=some out) :
    out.frames.length≤fuel := by
  simpa only [initial,List.length_nil,Nat.zero_add] using
    SemiprimeD1StackCalls.run_frame_bound code fuel (initial axes i j) out hr

/-- Every literal data symbol and return-label symbol is counted. Labels are a
fixed finite alphabet independent of axes, rank, indices and context precision. -/
theorem prefix_cells (axes : List ℕ) (i j fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run code fuel (initial axes i j)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤20*(inputSize axes i j+fuel+1) := by
  have hd := prefix_data axes i j fuel out hr
  have hf := prefix_frames axes i j fuel out hr
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun k _=>hd k)
  have hc : Fintype.card Stack=19 := by decide
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hc] at hs
  omega

/-- All genuinely reached target-machine prefixes satisfy the same physical
payload bound. This includes skipped input, all internal copies and real frames. -/
theorem machine_prefix_cells (axes : List ℕ) (i j fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial axes i j)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      20*(inputSize axes i j+fuel+1) := by
  dsimp only [SemiprimeD1StackJetRoute.machine] at cfg hr ⊢
  have he := SemiprimeD1StackCalls.run_correct Stack.axes Stack.result (ctl .copyLeft) code fuel
    (initial axes i j)
  have hefinal := he.trans hr
  cases hs : SemiprimeD1StackCalls.run code fuel (initial axes i j) with
  | none=>rw [hs] at hefinal; cases hefinal
  | some out=>
    rw [hs] at hefinal
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hefinal
    rw [←hcfg]
    exact prefix_cells axes i j fuel out hs
end RiemannGaussian.SemiprimeD1StackJetRouteMachine
