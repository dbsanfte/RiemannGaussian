/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueRow
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMetadata
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalRow
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields SemiprimeD1StackOwnerCatalogueParse
open SemiprimeD1StackOwnerCatalogueRow
open SemiprimeD1StackPortOwnerRecipeSpec (original words)
open SemiprimeD1StackPortOwnerRecipeClassify (originalTag original_tag)
open SemiprimeD1StackPortOwnerRecipeOriginal (original_field)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1StackProcedureTrace (Runs)
/-- Actual original edge fields followed by the next actual bank-ID payload. -/
def fields {r t digits:Nat} (e:SemiprimeMacroGraph.Edge r t digits) (owner:List Bool) : Fin 7→List Bool :=
  ![SemiprimeD1StackEdgeCount.edgeFields e 0,SemiprimeD1StackEdgeCount.edgeFields e 1,
    SemiprimeD1StackEdgeCount.edgeFields e 2,SemiprimeD1StackEdgeCount.edgeFields e 3,
    SemiprimeD1StackEdgeCount.edgeFields e 4,SemiprimeD1StackEdgeCount.edgeFields e 5,owner]
/-- Canonical metadata-store projection; no private outer field is an arithmetic operand. -/
def metaStore (s:S.Stack→List Bool) : Stack→List Bool := data s (fun _=>[]) (fun _=>[]) (fun _=>[])
/-- Proof invariant about the THREE actual acquired unary dimension words. -/
def Metadata (s:S.Stack→List Bool) (r t digits:Nat) : Prop :=
  metaStore s (dimension 0)=unary r ∧ metaStore s (dimension 1)=unary t ∧
    metaStore s (dimension 2)=unary digits
/-- Reading original fields physically reconstructs the existing Edge13 bytes. -/
theorem field_record {r t digits:Nat} (e:SemiprimeMacroGraph.Edge r t digits) (owner tail:List Bool) :
    edgeRest (fields e owner) 0 tail=SemiprimeD1EdgeCatalogueEncoding.edge e tail := rfl
/-- The actual next ID is retained without any endpoint or occurrence arithmetic. -/
theorem field_owner {r t digits:Nat} (e:SemiprimeMacroGraph.Edge r t digits) (owner:List Bool) :
    fields e owner 6=owner := rfl
/-- The arithmetic call receives the ORIGINAL edge's actual acquired unary words. -/
theorem original_inputs {r t digits:Nat} (s:S.Stack→List Bool) (hm:Metadata s r t digits)
    (e:SemiprimeMacroGraph.Edge r t digits) (owner:List Bool) (a:Aux→List Bool) (i:R.Input) :
    data s (fun _=>[]) (fields e owner) a (recipeStack (.inl i))=words (original e) i := by
  cases i with
  | r=>exact hm.1
  | t=>exact hm.2.1
  | digits=>exact hm.2.2
  | half=>exact (original_field e 0).symm
  | tag=>exact (original_field e 1).symm
  | a=>exact (original_field e 2).symm
  | b=>exact (original_field e 3).symm
  | c=>exact (original_field e 4).symm
  | d=>exact (original_field e 5).symm
/-- Both rows are exactly the original endpoints and the SAME acquired owner-ID bytes. -/
theorem original_emitted {r t digits:Nat} (hd:0<digits) (hc:digits≤r*t)
    (e:SemiprimeMacroGraph.Edge r t digits) (owner:List Bool) :
    emitted (fields e owner) (original e) (originalTag e)=
      SemiprimeD1StackOwnerCatalogueEmit.rowBytes
        (SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e false)) owner++
      SemiprimeD1StackOwnerCatalogueEmit.rowBytes
        (SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e true)) owner := by
  unfold emitted
  rw [field_owner]
  have ha:arithmeticBytes (original e) (originalTag e)=
      SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e false):=
    SemiprimeD1StackPortOwnerRecipeExecution.output_original hd hc e
  have he:equalityBytes (fields e owner)=
      SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e true):=by
    unfold equalityBytes
    rw [field_record]
    exact SemiprimeD1StackOwnerEqualityKey.original_key hd hc e
  rw [ha,he]
/-- Full original-edge iteration through the actual parser, arithmetic, copy, emitter and erasers. -/
theorem original_row_run {r t digits:Nat} (hd:0<digits) (s:S.Stack→List Bool)
    (hm:Metadata s r t digits) (e:SemiprimeMacroGraph.Edge r t digits)
    (owner edges ids collector:List Bool) :
    ∃time≤budget (fields e owner) (original e) (originalTag e),Runs program time (.local .parse)
      (data s (fun _=>[]) (fun _=>[])
        (rowAux (SemiprimeD1EdgeCatalogueEncoding.edge e edges) (true::SemiprimeSourceHistogramKeyBits.frame owner ids) collector))
      (.local .parse) (data s (fun _=>[]) (fun _=>[])
        (rowAux edges ids ((emitted (fields e owner) (original e) (originalTag e)).reverse++collector))) := by
  obtain ⟨time,ht,hr⟩:=row_run s (fields e owner) (original e) (originalTag e) (original_tag e) hd
    edges ids collector (original_inputs s hm e owner _)
  refine ⟨time,ht,?_⟩
  have hp:parsed (fields e owner) 0=fun _=>[]:=by funext i;exact ite_eq_right (Nat.not_lt_zero _)
  have ha:parseAux (fields e owner) 0 edges ids collector=
      rowAux (SemiprimeD1EdgeCatalogueEncoding.edge e edges)
        (true::SemiprimeSourceHistogramKeyBits.frame owner ids) collector:=by
    funext k;cases k <;> simp only [parseAux,rowAux,field_record,field_owner]
  simpa only [hp,ha] using hr
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalRow
