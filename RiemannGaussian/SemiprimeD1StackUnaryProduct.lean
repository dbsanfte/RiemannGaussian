/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryDivmod
import Mathlib.Tactic.Linarith

/-! # Physical unary product for acquired suffix metadata
Every multiplier token triggers an actual multiplicand drain/restore/copy. The
output is acquired from these loops, never supplied as a product/rank answer.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackUnaryProduct
open Turing Turing.TM2 Turing.TM2.Stmt
open SemiprimeD1StackUnaryDivmod (unary unary_add unary_succ unary_bump)
open SemiprimeD1StackFiniteControlPaths (SourcePath)

/-- Four fixed physical Boolean counter/work stacks. -/
inductive Stack | multiplier | multiplicand | scratch | product deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.multiplier,.multiplicand,.scratch,.product}
  complete := by intro k; cases k <;> simp
/-- Three fixed finite copy-loop phases. -/
inductive PC | loop | drain | restore deriving DecidableEq,Inhabited,Repr
instance : Fintype PC where
  elems := {.loop,.drain,.restore}
  complete := by intro k; cases k <;> simp
/-- Every unbounded symbol is Boolean. -/
abbrev Alphabet (_ : Stack) := Bool

/-- Actual fixed code, including all multiplicand reload work. -/
def program : PC → Stmt Alphabet PC (Option Bool)
  | .loop => .pop .multiplier (fun _ b => b)
      (.branch Option.isSome (.goto (fun _ => .drain)) .halt)
  | .drain => .pop .multiplicand (fun _ b => b)
      (.branch Option.isSome
        (.push .scratch (fun b => b.getD false)
          (.push .product (fun _ => true) (.goto (fun _ => .drain))))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ b => b)
      (.branch Option.isSome
        (.push .multiplicand (fun b => b.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .loop)))

/-- Literal physical counter bank. -/
def contents (multiplier multiplicand scratch product : List Bool) : (k : Stack) → List (Alphabet k)
  | .multiplier => multiplier
  | .multiplicand => multiplicand
  | .scratch => scratch
  | .product => product
/-- Explicit finite-control configurations. -/
def cfg (pc : Option PC) (flag : Option Bool) (multiplier multiplicand scratch product : List Bool) :
    Cfg Alphabet PC (Option Bool) := ⟨pc,flag,contents multiplier multiplicand scratch product⟩
/-- Exact actual execution paths. -/
abbrev Executes := SourcePath program

/-- Literal stack updates introduce no alias or implicit free cell. -/
@[simp] theorem update_contents (multiplier multiplicand scratch product xs : List Bool) (k : Stack) :
    Function.update (contents multiplier multiplicand scratch product) k xs=
      contents (if k=.multiplier then xs else multiplier) (if k=.multiplicand then xs else multiplicand)
        (if k=.scratch then xs else scratch) (if k=.product then xs else product) := by
  funext j
  cases k <;> cases j <;> simp [contents]

/-- Paths concatenate without dropping any acquisition/copy transitions. -/
theorem exec_trans {n m : ℕ} {a b c : Cfg Alphabet PC (Option Bool)}
    (h : Executes n a b) (g : Executes m b c) : Executes (n+m) a c := by
  induction h with
  | refl => simpa using g
  | @next n a d b hs ht ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using SourcePath.next hs (ih g)

/-- Every multiplicand bit is read, saved, and contributes one actual output marker. -/
theorem drain_exec (flag : Option Bool) (m d scratch product : List Bool) :
    Executes (d.length+1) (cfg (some .drain) flag m d scratch product)
      (cfg (some .restore) none m [] (d.reverse++scratch) (unary d.length++product)) := by
  induction d generalizing flag scratch product with
  | nil =>
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,unary,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .drain) flag m (b::bs) scratch product)=
        some (cfg (some .drain) (some b) m bs (b::scratch) (true::product)) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [unary_bump,List.reverse_cons,List.append_assoc] using
      SourcePath.next hs (ih (some b) (b::scratch) (true::product))

/-- Every saved multiplicand cell is physically restored before the next iteration. -/
theorem restore_exec (flag : Option Bool) (m d scratch product : List Bool) :
    Executes (scratch.length+1) (cfg (some .restore) flag m d scratch product)
      (cfg (some .loop) none m (scratch.reverse++d) [] product) := by
  induction scratch generalizing flag d with
  | nil =>
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  | cons b bs ih =>
    have hs : TM2.step program (cfg (some .restore) flag m d (b::bs) product)=
        some (cfg (some .restore) (some b) m (b::d) bs product) := by
      simp [program,cfg,contents,TM2.step,TM2.stepAux]
    simpa [List.reverse_cons,List.append_assoc] using SourcePath.next hs (ih (some b) (b::d))

/-- One complete physical copy; its cost depends on the actual counter length. -/
theorem copy_exec (flag : Option Bool) (m d product : List Bool) :
    Executes (2*d.length+2) (cfg (some .drain) flag m d [] product)
      (cfg (some .loop) none m d [] (unary d.length++product)) := by
  have h := exec_trans (drain_exec flag m d [] product)
    (restore_exec none m [] (d.reverse++[]) (unary d.length++product))
  simp only [List.append_nil,List.length_reverse,List.reverse_reverse] at h
  convert h using 1
  omega

/-- The complete product is physically acquired from original multiplier/multiplicand counters. -/
theorem product_exec (m d : ℕ) (product : List Bool) (flag : Option Bool) :
    Executes (m*(2*d+3)+1) (cfg (some .loop) flag (unary m) (unary d) [] product)
      (cfg none none [] (unary d) [] (unary (m*d)++product)) := by
  induction m generalizing flag product with
  | zero =>
    simp only [Nat.zero_mul,show unary 0=[] from rfl,List.nil_append]
    apply SourcePath.next ?_ (.refl _)
    simp [program,cfg,contents,TM2.step,TM2.stepAux]
  | succ m ih =>
    have hs : TM2.step program (cfg (some .loop) flag (unary (m+1)) (unary d) [] product)=
        some (cfg (some .drain) (some true) (unary m) (unary d) [] product) := by
      simp [program,cfg,contents,unary_succ,TM2.step,TM2.stepAux]
    have hc := copy_exec (some true) (unary m) (unary d) product
    have ht := ih (unary d++product) none
    simp only [unary,List.length_replicate] at hc
    have h := SourcePath.next hs (exec_trans hc ht)
    have he : 2*d+2+(m*(2*d+3)+1)+1=(m+1)*(2*d+3)+1 := by nlinarith
    rw [he] at h
    simpa only [Nat.add_mul,Nat.one_mul,unary_add,List.append_assoc] using h

/-- Actual target labels specialize only finite registers and fixed syntax locations. -/
abbrev Label := SemiprimeD1StackFiniteControl.Label program
/-- Computable actual literal product bytecode. -/
def code := SemiprimeD1StackFiniteControl.code program
/-- Fixed component entry. -/
def entry : Label := SemiprimeD1StackFiniteControl.entry program .loop none

/-- Actual static syntax bound, discharged for every fixed instruction. -/
theorem program_depth (pc : PC) : SemiprimeD1StackFiniteControl.depth (program pc)≤5 := by
  cases pc <;> decide

/-- Exact literal generated-bytecode multiplication, no supplied product or work answer. -/
theorem product_run (m d : ℕ) :
    ∃t≤5*(m*(2*d+3)+1),SemiprimeD1StackBytecode.run code t
      ⟨some entry,none,contents (unary m) (unary d) [] []⟩=
      some ⟨none,none,contents [] (unary d) [] (unary (m*d))⟩ := by
  obtain ⟨t,ht,flag,he⟩ := SemiprimeD1StackFiniteControlPaths.path_refines program 5 program_depth
    (product_exec m d [] none) none
  exact ⟨t,ht,by simpa [List.append_nil,SemiprimeD1StackFiniteControlExecution.destination,cfg,code,entry]
    using SemiprimeD1StackFiniteControlPaths.Executes.iterates he⟩

end RiemannGaussian.SemiprimeD1StackUnaryProduct
