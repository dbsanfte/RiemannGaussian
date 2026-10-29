/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityRecipes

/-! # Exact original MacroGraph arity from physically parsed descriptor words
The source header here is a proof-view of actual shared words, not a public
input constructor. The original-N port caller must obtain those words itself.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityOriginal
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityView SemiprimeD1StackVertexArityRecipes
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeMacroGraph
namespace V
export SemiprimeD1EdgeCatalogueEncoding (Record vertex arithmetic bit fields)
end V

/-- Actual tag length in the physical original descriptor. -/
def tagValue {r t digits:ℕ} (v:SubdividedVertex r t digits) : ℕ := (V.vertex v 0).length
/-- Every original descriptor uses one of the fixed eighteen machine tags. -/
theorem tagValue_lt {r t digits:ℕ} (v:SubdividedVertex r t digits) : tagValue v<18 := by
  rcases v with v|v
  · cases v <;> simp [tagValue,V.vertex,V.arithmetic,V.fields,SemiprimeD1VertexCatalogueModes.code]
  · rcases v with ⟨w,b⟩|flag
    · cases w <;> simp [tagValue,V.vertex,V.bit,V.fields,SemiprimeD1VertexCatalogueModes.code]
    · cases flag <;> simp [tagValue,V.vertex,V.bit,V.fields,SemiprimeD1VertexCatalogueModes.code]
/-- Proof-side finite constructor corresponding to the actual pop-counted tag. -/
def tagCode {r t digits:ℕ} (v:SubdividedVertex r t digits) : Fin 18 := ⟨tagValue v,tagValue_lt v⟩
/-- The actual second coordinate cache is the input-index counter in the input case. -/
def indexValue {r t digits:ℕ} (v:SubdividedVertex r t digits) : ℕ := (V.vertex v 2).length
/-- Tag words come from the actual original encoding, not an advised code. -/
theorem tag_word {r t digits:ℕ} (v:SubdividedVertex r t digits) : V.vertex v 0=unary (tagCode v).val := by
  rcases v with v|v
  · cases v <;> simp [tagCode,tagValue,unary,V.vertex,V.arithmetic,V.fields]
  · rcases v with ⟨w,b⟩|flag
    · cases w <;> simp [tagCode,tagValue,unary,V.vertex,V.bit,V.fields]
    · cases flag <;> simp [tagCode,tagValue,unary,V.vertex,V.bit,V.fields]
/-- Coordinate counters are actual unary words in every original descriptor. -/
theorem index_word {r t digits:ℕ} (v:SubdividedVertex r t digits) : V.vertex v 2=unary (indexValue v) := by
  rcases v with v|v
  · cases v <;> simp [indexValue,unary,V.vertex,V.arithmetic,V.fields]
  · rcases v with ⟨w,b⟩|flag
    · cases w <;> simp [indexValue,unary,V.vertex,V.bit,V.fields]
    · cases flag <;> simp [indexValue,unary,V.vertex,V.bit,V.fields]
/-- Actual parsed/source cache words at the internal procedure boundary. -/
def originalHeader {r t digits:ℕ} (v:SubdividedVertex r t digits) : Source→List Bool
  | .tag => V.vertex v 0
  | .index => V.vertex v 2
  | .radiusSucc => unary (r*t+1)
  | .firstAxis => unary r
  | .secondAxis => unary t
  | .digits => unary digits
/-- The generic boundary format is derived from those literal original words. -/
theorem originalHeader_eq {r t digits:ℕ} (v:SubdividedVertex r t digits) :
    originalHeader v=header (tagCode v).val (indexValue v) (r*t+1) r t digits := by
  funext key
  cases key with
  | tag => exact tag_word v
  | index => exact index_word v
  | radiusSucc => rfl
  | firstAxis => rfl
  | secondAxis => rfl
  | digits => rfl
/-- All eighteen physical recipes equal the ORIGINAL arithmetic/equality arity. -/
theorem value_original {r t digits:ℕ} (v:SubdividedVertex r t digits) :
    value (tagCode v) (indexValue v) (r*t+1) r t digits=subdividedArity v := by
  rcases v with v|v
  · cases v <;> simp [value,tagCode,tagValue,indexValue,V.vertex,V.arithmetic,V.fields,
      SemiprimeD1VertexCatalogueModes.code,subdividedArity,SemiprimeMacroGraph.arity] <;> omega
  · rcases v with ⟨w,b⟩|flag
    · cases w <;> simp [value,tagCode,tagValue,V.vertex,V.bit,V.fields,
        SemiprimeD1VertexCatalogueModes.code,subdividedArity]
    · cases flag <;> simp [value,tagCode,tagValue,V.vertex,V.bit,V.fields,
        SemiprimeD1VertexCatalogueModes.code,subdividedArity]
/-- Actual closed arity trace on the ORIGINAL header; no desired arity/Fits/time input. -/
theorem ready_original {r t digits:ℕ} (v:SubdividedVertex r t digits) :
    ∃time≤recipeBudget (indexValue v) (r*t+1) r t digits+107,Runs program time (.inl .main)
      (store (originalHeader v) [] [] [] [] [] []) (.inl .halt)
      (store (originalHeader v) (unary (subdividedArity v)) [] [] [] [] []) := by
  have h:=ready (tagCode v) (indexValue v) (r*t+1) r t digits
  rw [←originalHeader_eq,value_original] at h
  exact h
/-- Internal actual stopped data, including unchanged original source counters. -/
def done {r t digits:ℕ} (v:SubdividedVertex r t digits) : C.State Stack Label :=
  ⟨none,none,none,store (originalHeader v) (unary (subdividedArity v)) [] [] [] [] [],[]⟩
/-- Whole real called procedure with actual halt; the N-only caller will link this trace. -/
theorem source_run {r t digits:ℕ} (v:SubdividedVertex r t digits) :
    ∃time≤recipeBudget (indexValue v) (r*t+1) r t digits+108,
      C.run program time (⟨some (.inl .main),none,none,store (originalHeader v) [] [] [] [] [] [],[]⟩:C.State Stack Label)=some (done v) := by
  obtain ⟨time,ht,he⟩:=ready_original v
  obtain ⟨finish,hr,hout⟩:=he [] (⟨some (.inl .main),none,none,store (originalHeader v) [] [] [] [] [] [],[]⟩:C.State Stack Label) ⟨rfl,rfl,rfl⟩
  refine ⟨time+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done v)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]
end RiemannGaussian.SemiprimeD1StackVertexArityOriginal
