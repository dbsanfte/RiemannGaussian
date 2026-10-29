/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModePrimitives
/-! # Literal word views of weighted-tuple activation and output layouts
Every structure here is proof notation for the seventeen physical Boolean
words. The actual instruction table contains no structure, getter or list value.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedMode
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Bounded natural metadata is encoded as actual unary marker cells. -/
def unary (n:Nat) :List Bool:=List.replicate n true
/-- Actual framed vector of unary weights or exponents; not a primitive encoder instruction. -/
def vector (xs:List Nat) :List Bool:=vectorBits (xs.map unary)
/-- A physical Boolean word at each of the seventeen fixed addresses. -/
structure Words where
  /-- Actual catalogue Boolean tape. -/
  catalogue:List Bool:=[]
  /-- Actual width Boolean tape. -/
  width:List Bool:=[]
  /-- Actual weights Boolean tape. -/
  weights:List Bool:=[]
  /-- Actual budget Boolean tape. -/
  budget:List Bool:=[]
  /-- Actual path Boolean tape. -/
  path:List Bool:=[]
  /-- Actual weight Boolean tape. -/
  weight:List Bool:=[]
  /-- Actual exponent Boolean tape. -/
  exponent:List Bool:=[]
  /-- Actual frames Boolean tape. -/
  frames:List Bool:=[]
  /-- Actual tuple Boolean tape. -/
  tuple:List Bool:=[]
  /-- Actual pathReader Boolean tape. -/
  pathReader:List Bool:=[]
  /-- Actual fieldScratch Boolean tape. -/
  fieldScratch:List Bool:=[]
  /-- Actual valid Boolean tape. -/
  valid:List Bool:=[]
  /-- Actual copyScratch Boolean tape. -/
  copyScratch:List Bool:=[]
  /-- Actual frameScratch Boolean tape. -/
  frameScratch:List Bool:=[]
  /-- Actual subTodo Boolean tape. -/
  subTodo:List Bool:=[]
  /-- Actual history Boolean tape. -/
  history:List Bool:=[]
  /-- Actual output Boolean tape. -/
  output:List Bool:=[]
/-- The literal physical store represented by a proof-side word view. -/
def store (v:Words) :Stack→List Bool
  | .catalogue=>v.catalogue | .width=>v.width | .weights=>v.weights | .budget=>v.budget
  | .path=>v.path | .weight=>v.weight | .exponent=>v.exponent | .frames=>v.frames | .tuple=>v.tuple
  | .pathReader=>v.pathReader | .fieldScratch=>v.fieldScratch | .valid=>v.valid | .copyScratch=>v.copyScratch
  | .frameScratch=>v.frameScratch | .subTodo=>v.subTodo | .history=>v.history | .output=>v.output
/-- One proof-side description of an actual single-word write. -/
def write (v:Words) (k:Stack) (xs:List Bool) :Words:=match k with
  | .catalogue=>{v with catalogue:=xs} | .width=>{v with width:=xs} | .weights=>{v with weights:=xs}
  | .budget=>{v with budget:=xs} | .path=>{v with path:=xs} | .weight=>{v with weight:=xs}
  | .exponent=>{v with exponent:=xs} | .frames=>{v with frames:=xs} | .tuple=>{v with tuple:=xs}
  | .pathReader=>{v with pathReader:=xs} | .fieldScratch=>{v with fieldScratch:=xs} | .valid=>{v with valid:=xs}
  | .copyScratch=>{v with copyScratch:=xs} | .frameScratch=>{v with frameScratch:=xs} | .subTodo=>{v with subTodo:=xs}
  | .history=>{v with history:=xs} | .output=>{v with output:=xs}
/-- Every described write is exactly the physical function update, including all foreign words. -/
theorem store_write (v:Words) (k:Stack) (xs:List Bool) :
    Function.update (store v) k xs=store (write v k xs):=by
  cases k <;> funext j <;> cases j <;> rfl
/-- One real increment adds exactly one metadata cell. -/
theorem unary_succ (n:Nat) :unary (n+1)=true::unary n:=List.replicate_succ
/-- The empty numeric vector still has its actual false terminator. -/
theorem vector_nil :vector []=[false]:=rfl
/-- Each actual coordinate has its true tag, complete unary payload and remaining suffix. -/
theorem vector_cons (x:Nat) (xs:List Nat) :vector (x::xs)=true::frame (unary x) (vector xs):=rfl
/-- Exact metadata word length. -/
theorem unary_length (n:Nat) :(unary n).length=n:=List.length_replicate
/-- Readonly inputs, actual saved caller activations and chronological output remain explicit. -/
def base (cat width frames hist out:List Bool) :Words:=
  {catalogue:=cat,width:=width,frames:=frames,history:=hist,output:=out}
/-- Actual recursively entered suffix, residual budget and reverse-coordinate path. -/
def node (cat width:List Bool) (ws:List Nat) (P:Nat) (path frames hist out:List Bool) :Words:=
  {base cat width frames hist out with weights:=vector ws,budget:=unary P,path:=path}
/-- Actual current feasible exponent branch after reading one positive weight. -/
def loop (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (path frames hist out:List Bool) :Words:=
  {node cat width ws R path frames hist out with weight:=unary w,exponent:=unary e}
/-- Five real framed words precede the untouched activation-stack suffix. -/
def activation (w:Nat) (ws:List Nat) (R e:Nat) (path frames:List Bool) :List Bool:=
  frame (unary w) (frame (vector ws) (frame (unary R) (frame (unary e) (frame path frames))))
/-- Reverse-coordinate path created by the real Frame and true-tag push. -/
def extend (e:Nat) (path:List Bool) :List Bool:=true::frame (unary e) path
/-- Mathematical literal output row, used only to state the reached logger bytes. -/
def row (tuple:List Bool) :List Bool:=true::frame tuple []
/-- Actual chronological reverse log after emitted tuple payloads. -/
def history (tuples:List (List Bool)) (old:List Bool) :List Bool:=
  (tuples.foldr (fun x tail=>row x++tail) []).reverse++old
/-- One emitted tuple extends the literal reverse history in constant per-row work. -/
theorem history_cons (x:List Bool) (xs:List (List Bool)) (old:List Bool) :
    history (x::xs) old=history xs ((row x).reverse++old):=by
  simp only [history,List.foldr_cons,List.reverse_append,List.append_assoc]
/-- Exact successive logged blocks concatenate in their original order. -/
theorem history_append (xs ys:List (List Bool)) (old:List Bool) :
    history (xs++ys) old=history ys (history xs old):=by
  have hf:(xs++ys).foldr (fun x tail=>row x++tail) []=
      xs.foldr (fun x tail=>row x++tail) []++ys.foldr (fun x tail=>row x++tail) []:=by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simp only [List.cons_append,List.foldr_cons,ih,List.append_assoc]
  rw [history,hf,List.reverse_append]
  simp only [history,List.append_assoc]
/-- A reverse-coordinate path represents exactly the prefix already chosen by actual branches. -/
def path (chosen:List Nat) :List Bool:=vector chosen.reverse
/-- Actual recursive path pushes append exactly the chosen original exponent coordinate. -/
theorem path_extend (chosen:List Nat) (e:Nat) :path (chosen++[e])=extend e (path chosen):=by
  simp only [path,List.reverse_append,List.reverse_singleton,List.singleton_append,vector_cons,extend]
end RiemannGaussian.SemiprimeD1StackWeightedModeView
