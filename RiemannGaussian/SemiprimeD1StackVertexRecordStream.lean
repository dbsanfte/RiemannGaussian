/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackVertexProduct

/-! # Literal streaming acquisition of original vertex records
Both original argument fields must already have been physically acquired.
The logger consumes them, prepends their reversed framing to one history,
and performs one final physical reversal after the whole stream.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexRecordStream
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
open SemiprimeSourceHistogramKeyBits (frame)

/-- Four fixed physical Boolean roles. -/
inductive Stack where
  | ports | table | history | output
  deriving DecidableEq
instance : Fintype Stack where
  elems := {.ports,.table,.history,.output}
  complete := by intro k; cases k <;> simp
/-- Fixed finite controls; field=false is ports, field=true is table. -/
inductive Label where
  | initialize | record | read (field : Bool) | tag (field bit : Bool)
  | value (field bit : Bool) | delimiter (field : Bool)
  | reverse | write (bit : Bool) | done
  deriving DecidableEq, Fintype
/-- A physical field register, independent of all mathematical vertex data. -/
def input (field : Bool) : Stack := if field then .table else .ports
/-- The next actual field, or the shared return point. -/
def next (field : Bool) : Label := if field then .done else .read true
/-- Literal logger: no getter, table evaluation, count or clock opcode. -/
def code : Label → B.Instruction Stack Label
  | .initialize => .push .output false .done
  | .record => .push .history true (.read false)
  | .read field => .pop (input field) (.delimiter field) (.tag field false) (.tag field true)
  | .tag field bit => .push .history true (.value field bit)
  | .value field bit => .push .history bit (.read field)
  | .delimiter field => .push .history false (next field)
  | .reverse => .pop .history .done (.write false) (.write true)
  | .write bit => .push .output bit .reverse
  | .done => .halt
/-- Exact four-role store, including arbitrary retained history/output. -/
def data (ports table hist out : List Bool) : Stack → List Bool
  | .ports => ports | .table => table | .history => hist | .output => out
/-- One original record, with no list terminator. This is proof-side byte notation. -/
def row (ports table : List Bool) : List Bool := true :: frame ports (frame table [])
/-- Fixed finite procedure machine with an actual return-cell alphabet. -/
def machine (entry : Label) : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine Stack.ports Stack.output (.inr false)
    (SemiprimeD1StackReturnLink.code entry code)
/-- The source instruction count includes the final literal halt. -/
def recordTime (ports table : List Bool) : Nat := 3 * (ports.length + table.length) + 6
/-- Store description for either field, leaving its sibling intact. -/
def fieldData (field : Bool) (word other hist out : List Bool) : Stack → List Bool :=
  if field then data other word hist out else data word other hist out

/-- Both EOF delimiters and every actual field bit are executed in order. -/
theorem field_run (field : Bool) (word other hist out : List Bool) (flag : Option Bool) :
    B.run code (3 * word.length + 2) ⟨some (.read field),flag,fieldData field word other hist out⟩ =
      some ⟨some (next field),none,fieldData field [] other ((frame word []).reverse ++ hist) out⟩ := by
  induction word generalizing hist flag with
  | nil =>
    cases field <;>
      change some (⟨_,_,_⟩ : B.State Stack Label) = _ <;>
      dsimp [B.execute,code,input,next,fieldData,data] <;>
      congr 2 <;> funext k <;> cases k <;> rfl
  | cons bit word ih =>
    have hfirst : B.run code 3
        ⟨some (.read field),flag,fieldData field (bit::word) other hist out⟩ =
        some ⟨some (.read field),some bit,fieldData field word other (bit::true::hist) out⟩ := by
      cases field <;> cases bit <;>
        change some (⟨_,_,_⟩ : B.State Stack Label) = _ <;>
        dsimp [B.execute,code,input,next,fieldData,data] <;>
      congr 2 <;> funext k <;> cases k <;> rfl
    rw [show 3*(bit::word).length+2=3+(3*word.length+2) by simp;omega,
      SemiprimeD1StackCopy.run_add,hfirst,Option.bind_some,ih]
    simp only [frame,List.reverse_cons,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

/-- Actual initialization writes the terminal tag on output before the final reversal. -/
theorem initialize_run (ports table hist out : List Bool) (flag : Option Bool) :
    B.run code 2 ⟨some .initialize,flag,data ports table hist out⟩ =
      some ⟨none,none,data ports table hist (false::out)⟩ := by
  change some (⟨_,_,_⟩ : B.State Stack Label) = _
  congr 2
  funext k
  cases k <;> rfl

/-- Exact logger trace; both acquired input fields are consumed, old history retained. -/
theorem record_run (ports table hist out : List Bool) (flag : Option Bool) :
    B.run code (recordTime ports table) ⟨some .record,flag,data ports table hist out⟩ =
      some ⟨none,none,data [] [] ((row ports table).reverse ++ hist) out⟩ := by
  have first : B.run code 1 ⟨some .record,flag,data ports table hist out⟩ =
      some ⟨some (.read false),flag,data ports table (true::hist) out⟩ := by
    change some (⟨_,_,_⟩ : B.State Stack Label) = _
    congr 2
    funext k
    cases k <;> rfl
  have hp := field_run false ports table (true::hist) out flag
  have ht := field_run true table [] ((frame ports []).reverse++true::hist) out none
  simp only [fieldData,Bool.false_eq_true,ite_false,ite_true,next] at hp ht
  rw [show recordTime ports table=1+((3*ports.length+2)+((3*table.length+2)+1)) by
    unfold recordTime;omega,SemiprimeD1StackCopy.run_add,first,Option.bind_some,
    SemiprimeD1StackCopy.run_add,hp,Option.bind_some,
    SemiprimeD1StackCopy.run_add,ht,Option.bind_some]
  change some (⟨none,none,_⟩ : B.State Stack Label) = _
  apply congrArg some
  apply congrArg (fun h => (⟨none,none,data [] [] h out⟩ : B.State Stack Label))
  have hf (a b : List Bool) : frame a b=frame a []++b := by
    induction a with
    | nil => rfl
    | cons bit a ih => simp only [frame,ih,List.cons_append]
  simp only [row]
  rw [hf ports (frame table [])]
  simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.cons_append,List.nil_append]

/-- One physical final reversal preserves the two other physical field registers. -/
theorem reverse_run (hist ports table out : List Bool) (flag : Option Bool) :
    B.run code (2*hist.length+2) ⟨some .reverse,flag,data ports table hist out⟩ =
      some ⟨none,none,data ports table [] (hist.reverse++out)⟩ := by
  induction hist generalizing out flag with
  | nil =>
    change some (⟨_,_,_⟩ : B.State Stack Label) = _
    congr 2
    funext k
    cases k <;> rfl
  | cons bit hist ih =>
    have hfirst : B.run code 2 ⟨some .reverse,flag,data ports table (bit::hist) out⟩ =
        some ⟨some .reverse,some bit,data ports table hist (bit::out)⟩ := by
      cases bit <;> change some (⟨_,_,_⟩ : B.State Stack Label) = _ <;>
        congr 2 <;> funext k <;> cases k <;> rfl
    rw [show 2*(bit::hist).length+2=2+(2*hist.length+2) by simp;omega,
      SemiprimeD1StackCopy.run_add,hfirst,Option.bind_some,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

/-- Actual cost is linear in the newly written row, never accumulated history. -/
theorem recordTime_le (ports table : List Bool) : recordTime ports table ≤ 2*(row ports table).length := by
  simp only [recordTime,row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
    List.length_nil]
  omega
/-- Exact bridge to the frozen original product-reader format. -/
theorem row_records (v : SemiprimeD1LeafCounter.Vertex) (rest : List SemiprimeD1LeafCounter.Vertex) :
    row (SemiprimeD1StackVertexReadExecution.portTape v.ports) (SemiprimeD1TensorTapeCodec.tape v.table) ++
      SemiprimeD1StackVertexProduct.records rest = SemiprimeD1StackVertexProduct.records (v::rest) := by
  have hf (a b : List Bool) : frame a b=frame a []++b := by
    induction a with
    | nil => rfl
    | cons bit a ih => simp only [frame,ih,List.cons_append]
  simp only [row,SemiprimeD1StackVertexProduct.records,List.cons_append]
  rw [hf _ (frame _ _),hf _ (SemiprimeD1StackVertexProduct.records rest),hf _ (frame _ [] ++ SemiprimeD1StackVertexProduct.records rest)]
  simp only [List.append_assoc]
end RiemannGaussian.SemiprimeD1StackVertexRecordStream
