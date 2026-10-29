/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeTreeMachine

/-! # Exact execution of serialized table lookup
No supplied lookup result or tree-height register occurs in the machine. The
induction below verifies the fixed pending-task program on actual serialized data.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeTreeExecution
open Turing Turing.TM2
open SemiprimeD1TensorTapeTreeMachine
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1TensorTables (Table lookup)

/-- The actual scan length of both subtrees, regardless of the selected path. -/
def scanSteps : {n : ℕ} → Table n → ℕ
  | _,.leaf ws => (vectorBits ws).length+3
  | _,.fork low high => 2+scanSteps low+scanSteps high

/-- Pop one physical pending seek/skip bit. -/
theorem task_cons (mode : Bool) (xs tasks path rev out : List Bool) :
    step (cfg (some .task) (none,false) xs (mode::tasks) path rev out)=
      some (cfg (some .node) (some mode,mode) xs tasks path rev out) := by
  simp [SemiprimeD1TensorTapeTreeMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- A literal leaf tag enters the raw vector scanner. -/
theorem node_leaf (mode : Bool) (xs tasks path rev out : List Bool) :
    step (cfg (some .node) (some mode,mode) (false::xs) tasks path rev out)=
      some (cfg (some .marker) (some false,mode) xs tasks path rev out) := by
  simp [SemiprimeD1TensorTapeTreeMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- A completed vector resets only the finite flags and resumes pending tasks. -/
theorem resume_step (mode : Bool) (xs tasks path rev out : List Bool) :
    step (cfg (some .resume) (some false,mode) xs tasks path rev out)=
      some (cfg (some .task) (none,false) xs tasks path rev out) := by rfl

/-- Skipping a fork schedules both actual subtrees without touching the query. -/
theorem node_skip (xs tasks path rev out : List Bool) :
    step (cfg (some .node) (some false,false) (true::xs) tasks path rev out)=
      some (cfg (some .task) (none,false) xs (false::false::tasks) path rev out) := by
  simp [SemiprimeD1TensorTapeTreeMachine.step,program,forkTasks,cfg,contents,TM2.step,TM2.stepAux]

/-- Seeking a fork consumes one query cell; EOF selects the low branch. -/
theorem node_seek (xs tasks path rev out : List Bool) :
    step (cfg (some .node) (some true,true) (true::xs) tasks path rev out)=
      some (cfg (some .task) (none,false) xs
        ((!(path.head?.getD false))::path.head?.getD false::tasks) path.tail rev out) := by
  simp [SemiprimeD1TensorTapeTreeMachine.step,program,forkTasks,cfg,contents,TM2.step,TM2.stepAux]

/-- Each complete tree consumes exactly its encoding, selecting at most one vector. -/
theorem tree_scan {n : ℕ} (table : Table n) (tail tasks path rev out : List Bool) (mode : Bool) :
    Executes (scanSteps table)
      (cfg (some .task) (none,false) (tape table++tail) (mode::tasks) path rev out)
      (cfg (some .task) (none,false) tail tasks (if mode then path.drop n else path)
        (if mode then (vectorBits (lookup table path).words).reverse++rev else rev) out) := by
  induction table generalizing tail tasks path rev mode with
  | leaf ws =>
    have he := Executes.next (task_cons mode _ tasks path rev out)
      (Executes.next (node_leaf mode _ tasks path rev out)
        ((vector_scan ws tail tasks path rev out mode (some false)).trans
          (Executes.next (resume_step mode tail tasks path _ out) (Executes.refl _))))
    convert he using 1 <;> simp [scanSteps,tape,lookup,SemiprimeD1JetAxes.copyVector_value,
      List.cons_append,Nat.add_assoc]
  | @fork n low high ihl ihh =>
    cases mode with
    | false =>
      have hl := ihl (tape high++tail) (false::tasks) path rev false
      have hh := ihh tail tasks path rev false
      have he := Executes.next (task_cons false _ tasks path rev out)
        (Executes.next (node_skip _ tasks path rev out) (hl.trans (by simpa using hh)))
      convert he using 1 <;> simp [scanSteps,tape,List.cons_append,List.append_assoc,Nat.add_assoc]
      all_goals omega
    | true =>
      by_cases hb : path.head?.getD false
      · have hl := ihl (tape high++tail) (true::tasks) path.tail rev false
        have hh := ihh tail tasks path.tail rev true
        have he := Executes.next (task_cons true _ tasks path rev out)
          (Executes.next (node_seek _ tasks path rev out)
            (by simpa only [hb,Bool.not_true,Bool.false_eq_true,ite_false] using
              hl.trans (by simpa using hh)))
        convert he using 1 <;> simp [scanSteps,tape,lookup,hb,List.cons_append,List.append_assoc,
          Nat.add_assoc]
        all_goals omega
      · have hl := ihl (tape high++tail) (false::tasks) path.tail rev true
        have hh := ihh tail tasks (path.tail.drop n)
          ((vectorBits (lookup low path.tail).words).reverse++rev) false
        have he := Executes.next (task_cons true _ tasks path rev out)
          (Executes.next (node_seek _ tasks path rev out)
            (by simpa only [Bool.eq_false_iff.mpr hb,Bool.not_false,Bool.true_eq,ite_true] using
              hl.trans (by simpa using hh)))
        convert he using 1 <;> simp [scanSteps,tape,lookup,hb,List.cons_append,List.append_assoc,
          Nat.add_assoc]
        all_goals omega

/-- Exhausting the physical task stack starts the final reversal. -/
theorem task_nil (xs path rev out : List Bool) :
    step (cfg (some .task) (none,false) xs [] path rev out)=
      some (cfg (some .reverse) (none,false) xs [] path rev out) := by
  simp [SemiprimeD1TensorTapeTreeMachine.step,program,cfg,contents,TM2.step,TM2.stepAux]

/-- Complete lookup has exact literal selected-vector output and exact suffix. -/
theorem lookup_exec {n : ℕ} (table : Table n) (path tail : List Bool) :
    Executes (scanSteps table+(vectorBits (lookup table path).words).length+2)
      (cfg (some .task) (none,false) (tape table++tail) [true] path [] [])
      (cfg none (none,false) tail [] (path.drop n) []
        (vectorBits (lookup table path).words)) := by
  have hs := tree_scan table tail [] path [] [] true
  have ht := Executes.next
    (task_nil tail (path.drop n) ((vectorBits (lookup table path).words).reverse++[]) [])
    (reverse_exec (none,false) tail [] (path.drop n)
      ((vectorBits (lookup table path).words).reverse++[]) [])
  have hh := hs.trans (by simpa using ht)
  simpa [Nat.add_assoc] using hh

/-- Skipping is genuine whole-tree traversal with exact suffix preservation. -/
theorem skip_exec {n : ℕ} (table : Table n) (path tail : List Bool) :
    Executes (scanSteps table+2)
      (cfg (some .task) (none,false) (tape table++tail) [false] path [] [])
      (cfg none (none,false) tail [] path [] []) := by
  have hs := tree_scan table tail [] path [] [] false
  have ht := Executes.next (task_nil tail path [] [])
    (reverse_exec (none,false) tail [] path [] [])
  simpa using hs.trans (by simpa using ht)

end RiemannGaussian.SemiprimeD1TensorTapeTreeExecution
