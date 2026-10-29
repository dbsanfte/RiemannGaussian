/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeExecution
import RiemannGaussian.SemiprimeD1StackRootScopeBankBounds
import RiemannGaussian.SemiprimeD1StackOwnerEqualityKeyBounds
/-! # Original-N forward endpoint/owner-ID catalogue source
This literal program runs original Edge13/count/M-bank acquisition once, parses
actual six-field edge records, and consumes ONE actual ascending M-bit ID for
each of the original E wires. Both endpoint keys share that same owner ID.
Arithmetic endpoints execute the complete physical recipe; equality endpoints
execute actual six-field framing and sentinel-copy. No permutation/key/count
answer or native edge enumeration is a runtime input. Execution proofs follow
in separate modules; the program alone is not a completed acquisition theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogue
namespace C
export SemiprimeD1StackCalls (Instruction State run step execute)
end C
namespace S
export SemiprimeD1StackRootScopeBank (Stack Label program input originalInput edgeStack ids)
end S
namespace R
export SemiprimeD1StackPortOwnerRecipe (Input Register Aux Stack Label program)
end R
namespace Q
export SemiprimeD1StackOwnerEqualityKey (Stack Label program)
end Q
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Exactly the47 actual arithmetic caches/scratch/output roles, excluding readonly inputs. -/
abbrev RecipeWork := R.Register⊕R.Aux
/-- Twelve fixed reader, parser, equality-key and output collector roles. -/
inductive Aux where
  | readerEdges | readerIds | copyScratch | fieldScratch | valid | record | equalityKey | equalityScratch
  | frameBuffer | frameScratch | reversed | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.readerEdges,.readerIds,.copyScratch,.fieldScratch,.valid,
  .record,.equalityKey,.equalityScratch,.frameBuffer,.frameScratch,.reversed,.output]
  (by intro k;cases k <;> simp)
/-- Original acquisition plus actual recipe work, seven parsed fields and twelve fresh roles. -/
abbrev Stack := S.Stack⊕(RecipeWork⊕(Fin 7⊕Aux))
/-- Exact original source inclusion, retained across every actual endpoint emission. -/
def source (k:S.Stack) : Stack := .inl k
/-- Private actual recipe work inclusion. -/
def work (k:RecipeWork) : Stack := .inr (.inl k)
/-- The six original edge fields and seventh actual owner-ID field. -/
def cache (part:Fin 7) : Stack := .inr (.inr (.inl part))
/-- Private physical caller work inclusion. -/
def aux (role:Aux) : Stack := .inr (.inr (.inr role))
/-- Original binary N alone. -/
def originalInput : Stack := source S.originalInput
/-- Actual preserved original E-wire record tape. -/
def edgeTape : Stack := source (S.edgeStack (SemiprimeD1StackEdgeCatalogue.aux .output))
/-- Actual preserved acquired M-word bank, where M counts occurrences and not E wires. -/
def idBank : Stack := source S.ids
/-- These are the actual retained unary r/t/digits metadata words of the N-only source. -/
def dimension (role:Fin 3) : Stack :=
  source (S.edgeStack (SemiprimeD1StackEdgeCatalogue.catStack
    (SemiprimeD1StackVertexCatalogue.roleStack
      (if role=0 then .firstAxis else if role=1 then .secondAxis else .digits))))
/-- Arithmetic evaluator inputs alias ONLY actual acquired metadata and actual parsed edge words. -/
def recipeStack : R.Stack→Stack
  | .inl .r=>dimension 0 | .inl .t=>dimension 1 | .inl .digits=>dimension 2
  | .inl .half=>cache 0 | .inl .tag=>cache 1 | .inl .a=>cache 2
  | .inl .b=>cache 3 | .inl .c=>cache 4 | .inl .d=>cache 5
  | .inr k=>work k
/-- Three actual equality-key preserving sentinel-copy operands. -/
def equalityStack (k:Fin 3) : Stack :=
  if k=0 then aux .record else if k=1 then aux .equalityKey else aux .equalityScratch
/-- Whole original record/ID readers are made by actual preserving Copy calls. -/
def copyStack (ids:Bool) (k:Fin 3) : Stack :=
  if k=0 then (if ids then idBank else edgeTape)
  else if k=1 then (if ids then aux .readerIds else aux .readerEdges) else aux .copyScratch
/-- Physical field parser: six edge fields, then one actual ID-vector payload. -/
def fieldStack (part:Fin 7) : F.Stack→Stack
  | .inl .input=>if part=6 then aux .readerIds else aux .readerEdges
  | .inl .scratch=>aux .fieldScratch | .inl .output=>cache part | .inr _=>aux .valid
/-- Equality's exact six-field record is physically assembled from parsed fields, last first. -/
def recordStack (part:Fin 6) (k:Fin 3) : Stack :=
  if k=0 then cache ⟨5-part.val,by omega⟩ else if k=1 then aux .record else aux .frameScratch
/-- The actual newly computed arithmetic key or actually sentinel-copied equality key. -/
def keySource (host:Bool) : Stack := if host then aux .equalityKey else recipeStack (.inr (.inr .output))
/-- Literal two-field map record: computed endpoint key, then the SAME acquired owner ID. -/
def pairStack (host value:Bool) (k:Fin 3) : Stack :=
  if k=0 then (if value then cache 6 else keySource host)
  else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Actual field or whole-map reversal; the final false vector delimiter is physically pushed. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then aux .reversed else aux .frameBuffer)
  else if finish then aux .output else aux .reversed
/-- Fixed complete inventory of recipe registers to physically clear after each wire. -/
def workRole (part:Fin 47) : RecipeWork :=
  if h:part.val<10 then .inl (.mode ⟨part.val,h⟩)
  else match part.val with
    | 10=>.inl .rt
    | 11=>.inl .width
    | 12=>.inl .qa
    | 13=>.inl .ma
    | 14=>.inl .qb
    | 15=>.inl .mb
    | 16=>.inl .tc
    | 17=>.inl .rc
    | 18=>.inl .pbc
    | 19=>.inl .aminus
    | 20=>.inl .bminus
    | 21=>.inl .dminus
    | 22=>.inl .bplus
    | 23=>.inl .slot10
    | 24=>.inl .slot11
    | 25=>.inl .slot12
    | 26=>.inl .wd
    | 27=>.inl .slot13f
    | 28=>.inl .slot13t
    | 29=>.inl .slot14t
    | 30=>.inl .slot14f
    | 31=>.inl .wb
    | 32=>.inl .divInput
    | 33=>.inl .testLeft
    | 34=>.inl .testLimit
    | 35=>.inl .smallA
    | 36=>.inl .ltArt
    | 37=>.inl .ltNext
    | 38=>.inl .tagReader
    | 39=>.inr .copyScratch
    | 40=>.inr .multiplier
    | 41=>.inr .productScratch
    | 42=>.inr .maddScratch
    | 43=>.inr .divCopy
    | 44=>.inr .divScratch
    | 45=>.inr .frameScratch
    | 46=>.inr .output
    | _=>.inr .output
/-- Fixed finite payload-cache cleanup order, preserving both entire original source banks. -/
def clearSource (part:Fin 9) : Stack :=
  if h:part.val<7 then cache ⟨part.val,h⟩ else if part=7 then aux .record else aux .equalityKey
/-- All outer control positions, including actual malformed-input abort branches. -/
inductive Control where
  | main | copyEdges | copyIds | parse | bankTag | arithmetic | equality | emitTag (host:Bool)
  | field (part:Fin 7) | valid (part:Fin 7) | record (part:Fin 6)
  | emitField (host value:Bool) | emitReverse (host value:Bool)
  | clearRecipe (part:Fin 47) | clearCache (part:Fin 9) | finalTag | finalReverse | halt | abort
  deriving Fintype
/-- Every source and every nested arithmetic/equality/parser call has a fixed finite label. -/
inductive Label where
  | local (pc:Control) | source (pc:S.Label) | recipe (pc:R.Label) | equality (pc:Q.Label)
  | copy (ids:Bool) (pc:Fin 9) | field (part:Fin 7) (pc:F.Label)
  | record (part:Fin 6) (pc:Fin 11) | pair (host value:Bool) (pc:Fin 11)
  | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- Actual original-N source, actual E-record/M-ID zipper and both literal endpoint-key paths. -/
def program : Label→C.Instruction Stack Label
  | .source pc=>SemiprimeD1StackValidationLink.instruction source Label.source (S.program pc)
  | .recipe pc=>SemiprimeD1StackValidationLink.instruction recipeStack Label.recipe (R.program pc)
  | .equality pc=>SemiprimeD1StackValidationLink.instruction equalityStack Label.equality (Q.program pc)
  | .copy ids pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack ids) (Label.copy ids) (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .record part pc=>SemiprimeD1StackMultiplierLink.instruction (recordStack part) (Label.record part) (SemiprimeD1StackFrame.code pc)
  | .pair host value pc=>SemiprimeD1StackMultiplierLink.instruction (pairStack host value) (Label.pair host value) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
  | .local .main=>.call (.source (.inl .start)) (.local .copyEdges)
  | .local .copyEdges=>.call (.copy false 0) (.local .copyIds)
  | .local .copyIds=>.call (.copy true 0) (.local .parse)
  | .local .parse=>.base (.peek (aux .readerEdges) (.local .finalTag) (.local (.field 0)) (.local (.field 0)))
  | .local (.field part)=>.call (.field part (F.active .tagPop (none,false))) (.local (.valid part))
  | .local (.valid part)=>
      let next:Label:=if h:part.val<5 then .local (.field ⟨part.val+1,by omega⟩)
        else if part=5 then .local .bankTag else .local (.record 0)
      .base (.pop (aux .valid) (.local .abort) (.local .abort) next)
  | .local .bankTag=>.base (.pop (aux .readerIds) (.local .abort) (.local .abort) (.local (.field 6)))
  | .local (.record part)=>.call (.record part 0)
      (if h:part.val<5 then .local (.record ⟨part.val+1,by omega⟩) else .local .equality)
  | .local .equality=>.call (.equality (.inl 0)) (.local .arithmetic)
  | .local .arithmetic=>.call (.recipe (.local .start)) (.local (.emitTag false))
  | .local (.emitTag host)=>.base (.push (aux .reversed) true (.local (.emitField host false)))
  | .local (.emitField host value)=>.call (.pair host value 0) (.local (.emitReverse host value))
  | .local (.emitReverse host value)=>.call (.reverse false 0)
      (if value then (if host then .local (.clearRecipe 0) else .local (.emitTag true))
        else .local (.emitField host true))
  | .local (.clearRecipe part)=>
      let next:Label:=if h:part.val<46 then .local (.clearRecipe ⟨part.val+1,by omega⟩) else .local (.clearCache 0)
      .base (.pop (work (workRole part)) next (.local (.clearRecipe part)) (.local (.clearRecipe part)))
  | .local (.clearCache part)=>
      let next:Label:=if h:part.val<8 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .parse
      .base (.pop (clearSource part) next (.local (.clearCache part)) (.local (.clearCache part)))
  | .local .finalTag=>.base (.push (aux .reversed) false (.local .finalReverse))
  | .local .finalReverse=>.call (.reverse true 0) (.local .halt)
  | .local .halt | .local .abort=>.base .halt
/-- Original binary N is the only initially present data; every outer/recipe cache starts empty. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (S.input bits) (fun _=>[])
/-- Actual original-N entry of the fixed forward catalogue producer. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.local .main),none,none,input bits,[]⟩
/-- One finite source for original-N forward endpoint/owner-ID acquisition. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .output) (.local .main) program
/-- Every physical data/return alphabet is finite before every original input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput (aux .output) (.local .main) program
end RiemannGaussian.SemiprimeD1StackOwnerCatalogue
