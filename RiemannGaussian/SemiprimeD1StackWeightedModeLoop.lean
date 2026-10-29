/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeSpec
/-! # Whole actual feasible DFS with real recursive frames and exact tuple order
The proof follows actual successful subtraction and the sole failed test.
The program never executes the mathematical target's range or division.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeLoop
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeActivation SemiprimeD1StackWeightedModeRound
open SemiprimeD1StackWeightedModeOrder SemiprimeD1StackWeightedModeSpec
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
attribute [local irreducible] nodeBudget branchBudget edge values branchValues
/-- Every original positive-weight suffix executes the exact complete feasible recursion,
with only Boolean activation words and the real fixed-label return stack. -/
theorem visit_run (cat width:List Bool) (ws:List Nat) (hw:∀w∈ws,0 < w)
    (P:Nat) (chosen:List Nat) (frames hist out:List Bool) :
    ∃t ≤ nodeBudget ws P (path chosen).length,
      Runs program t (ctl .visit) (store (node cat width ws P (path chosen) frames hist out))
        (ctl .returning) (store (base cat width frames (history (values ws P chosen) hist) out)):=by
  induction ws generalizing P chosen frames hist out with
  | nil=>
    obtain ⟨t,ht,hr⟩:=leaf_visit cat width P chosen frames hist out
    refine ⟨t,?_,?_⟩
    · simpa only [nodeBudget] using ht
    ·
      simpa only [values,SemiprimeD1WeightedTuples.tuples,List.map_cons,List.map_nil,List.append_nil,history_single] using hr
  | cons w ws ih=>
    have hwp:0 < w:=hw w (by simp)
    have hws:∀v∈ws,0 < v:=fun v hv=>hw v (by simp [hv])
    have hLoop:∀R e (chosen:List Nat) (frames hist out:List Bool),
        ∃t ≤ branchBudget w ws R e (path chosen).length,
          Runs program t (ctl (.save 4)) (store (loop cat width w ws R e (path chosen) frames hist out))
            (ctl .returning) (store (base cat width frames (history (branchValues w ws R e chosen) hist) out)):=by
      intro R
      induction R using Nat.strong_induction_on with
      | h R smaller=>
        intro e chosen frames hist out
        let childValues:=values ws R (chosen++[e])
        let childHist:=history childValues hist
        let childFrames:=activation w ws R e (path chosen) frames
        obtain ⟨d,hd,h0⟩:=descend cat width w ws R e (path chosen) frames hist out
        obtain ⟨u,hu,huRun⟩:=ih hws R (chosen++[e]) childFrames hist out
        rw [path_length] at hu
        rw [path_extend] at huRun
        change Runs program u (ctl .visit)
          (store (node cat width ws R (extend e (path chosen)) childFrames hist out))
          (ctl .returning) (store (base cat width childFrames childHist out)) at huRun
        have h1:=recursive_call .child .afterChild _ _ u rfl huRun
        have h2:=restore cat width w ws R e (path chosen) frames childHist out
        have hfirst:=join h0 (join h1 h2)
        by_cases hmore:w ≤ R
        · have hless:R-w < R:=residual_lt R w hwp hmore
          obtain ⟨n,hn,hnRun⟩:=smaller (R-w) hless (e+1) chosen frames childHist out
          have h3:=successor cat width w ws (R-w) e (path chosen) frames childHist out
          have heq:w+(R-w)=R:=by omega
          rw [heq] at h3
          have hall:=join hfirst (join h3 hnRun)
          change Runs program
            (d+((u+2)+(8*mass (loop cat width w ws R e (path chosen) frames childHist out)+41))+
              ((7*w+6)+n)) _ _ _ _ at hall
          refine ⟨d+((u+2)+(8*mass (loop cat width w ws R e (path chosen) frames childHist out)+41))+((7*w+6)+n),?_,?_⟩
          · rw [branchBudget_step w ws R e (path chosen).length hwp hmore]
            simp only [loop_mass] at hd ⊢
            unfold edge
            omega
          · dsimp only [childHist,childValues] at hall
            rw [←history_append,←branchValues_step w ws R e chosen hwp hmore] at hall
            exact hall
        · have hlast:R < w:=by omega
          obtain ⟨n,hn,hnRun⟩:=failed_return cat width w ws R e (path chosen) frames childHist out hlast
          have hall:=join hfirst hnRun
          change Runs program (d+((u+2)+(8*mass (loop cat width w ws R e (path chosen) frames childHist out)+41))+n)
            _ _ _ _ at hall
          refine ⟨d+((u+2)+(8*mass (loop cat width w ws R e (path chosen) frames childHist out)+41))+n,?_,?_⟩
          · rw [branchBudget_last w ws R e (path chosen).length hlast]
            simp only [loop_mass] at hd hn ⊢
            unfold edge
            omega
          · rw [branchValues_last w ws R e chosen hlast]
            exact hall
    obtain ⟨t,ht,hr⟩:=hLoop P 0 chosen frames hist out
    have he:=enter cat width w ws P (path chosen) frames hist out hwp
    have hall:=join he hr
    refine ⟨(8*w+10)+t,?_,?_⟩
    · rw [nodeBudget_cons]
      omega
    · simpa only [branchValues_zero] using hall
end RiemannGaussian.SemiprimeD1StackWeightedModeLoop
