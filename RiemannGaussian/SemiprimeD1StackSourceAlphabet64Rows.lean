/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64ColourLoop
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Calls
/-! # One actual full compact-ID/base64-row catalogue write with all cleanup charged -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Rows
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackSourceAlphabet64Calls
open SemiprimeD1StackSourceAlphabet64ColourLoop SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- The actual twelve row-local/cursor/history fields; every other physical word is retained. -/
def view (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist:List Bool) :Stack→List Bool
  | .inr .reader=>reader | .inr .raw=>raw | .inr .bits=>bits | .inr .bitsReverse=>rev
  | .inr .trimScratch=>tr | .inr .id=>ident | .inr .colourRaw=>rawcol | .inr .colour=>col
  | .inr .rowHistory=>rowhist | .inr .row=>rowword | .inr .frameBuffer=>buf | .inr .history=>hist
  | k=>base k
/-- One actual reader write retains every other physical role. -/
theorem update_reader (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .reader) next=view base next raw bits rev tr ident rawcol col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual raw write retains every other physical role. -/
theorem update_raw (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .raw) next=view base reader next bits rev tr ident rawcol col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual bits write retains every other physical role. -/
theorem update_bits (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .bits) next=view base reader raw next rev tr ident rawcol col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual bitsReverse write retains every other physical role. -/
theorem update_rev (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .bitsReverse) next=view base reader raw bits next tr ident rawcol col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual trimScratch write retains every other physical role. -/
theorem update_tr (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .trimScratch) next=view base reader raw bits rev next ident rawcol col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual id write retains every other physical role. -/
theorem update_ident (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .id) next=view base reader raw bits rev tr next rawcol col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual colourRaw write retains every other physical role. -/
theorem update_rawcol (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .colourRaw) next=view base reader raw bits rev tr ident next col rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual colour write retains every other physical role. -/
theorem update_col (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .colour) next=view base reader raw bits rev tr ident rawcol next rowhist rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual rowHistory write retains every other physical role. -/
theorem update_rowhist (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .rowHistory) next=view base reader raw bits rev tr ident rawcol col next rowword buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual row write retains every other physical role. -/
theorem update_rowword (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .row) next=view base reader raw bits rev tr ident rawcol col rowhist next buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual frameBuffer write retains every other physical role. -/
theorem update_buf (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .frameBuffer) next=view base reader raw bits rev tr ident rawcol col rowhist rowword next hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One actual history write retains every other physical role. -/
theorem update_hist (base:Stack→List Bool) (reader raw bits rev tr ident rawcol col rowhist rowword buf hist next:List Bool) :
    Function.update (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist) (aux .history) next=view base reader raw bits rev tr ident rawcol col rowhist rowword buf next :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- The real colour-loop view touches exactly its six actual row-local fields. -/
theorem colour_view (base:Stack→List Bool)
    (reader raw bits rev tr ident rawcol col rowhist rowword buf hist rev' rawcol' tr' col' buf' rowhist':List Bool) :
    SemiprimeD1StackSourceAlphabet64Colours.view (view base reader raw bits rev tr ident rawcol col rowhist rowword buf hist)
      rev' rawcol' tr' col' buf' rowhist'=
      view base reader raw bits rev' tr' ident rawcol' col' rowhist' rowword buf' hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One exact dictionary row is its actual tag and TWO actual framed fields. -/
def chunk (a:Nat) (word:List Bool) :List Bool :=true::frame (compact word) (frame (row a word) [])
/-- One real saveWord path consumes the actual raw fixed-width assignment and
writes its canonical-ID/full-row pair while clearing every row-local work word. -/
theorem word_run (base:Stack→List Bool) (a:Nat) (word reader hist:List Bool) (hlen:word.length=6*a)
    (hc:base (aux .copyScratch)=[]) (hl:base (aux .trimLeft)=[]) (hr:base (aux .trimRight)=[])
    (hs:base (aux .frameScratch)=[]) :
    ∃q ≤ 1000*(a+1),Runs program q .saveWord
      (view base reader word [] [] [] [] [] [] [] [] [] hist) .header
      (view base reader [] [] [] [] [] [] [] [] [] [] ((chunk a word).reverse++hist)) :=by
  let ident:=compact word
  let rowword:=row a word
  have h0:=copy_call .word .saveWord .reverseID rfl (view base reader word [] [] [] [] [] [] [] [] [] hist) rfl hc
  change Runs program (5*word.length+4) .saveWord _ .reverseID
    (Function.update (view base reader word [] [] [] [] [] [] [] [] [] hist) (aux .bits) word) at h0
  rw [update_bits] at h0
  change Runs program (5*word.length+4) .saveWord _ .reverseID (view base reader word word [] [] [] [] [] [] [] [] hist) at h0
  have h1:=reverse_call .id .reverseID (.normalize .id) rfl (view base reader word word [] [] [] [] [] [] [] [] hist)
  change Runs program (2*word.length+3) .reverseID _ (.normalize .id)
    (Function.update (Function.update (view base reader word word [] [] [] [] [] [] [] [] hist) (aux .raw) [])
      (aux .trimScratch) (word.reverse++[])) at h1
  rw [update_raw,update_tr,List.append_nil] at h1
  have h2:=trim_call .id (view base reader [] word [] word.reverse [] [] [] [] [] [] hist) hl hr
  change Runs program (SemiprimeD1StackReduceExecution.trimTime word.reverse+1) (.normalize .id) _ .reverseBits
    (Function.update (Function.update (view base reader [] word [] word.reverse [] [] [] [] [] [] hist) (aux .trimScratch) [])
      (aux .id) (SemiprimeD1StackReduceExecution.trimReverse word.reverse++[])) at h2
  rw [update_tr,update_ident,List.append_nil,trim_reverse] at h2
  have h3:=reverse_call .bits .reverseBits .colourStart rfl (view base reader [] word [] [] ident [] [] [] [] [] hist)
  change Runs program (2*word.length+3) .reverseBits _ .colourStart
    (Function.update (Function.update (view base reader [] word [] [] ident [] [] [] [] [] hist) (aux .bits) [])
      (aux .bitsReverse) (word.reverse++[])) at h3
  rw [update_bits,update_rev,List.append_nil] at h3
  obtain ⟨c,hcBound,h4⟩:=colours_run (view base reader [] [] [] [] ident [] [] [] [] [] hist) a word.reverse []
    (by rw [List.length_reverse];exact hlen) hl hr hs
  rw [colour_view,colour_view,List.append_nil] at h4
  change Runs program c .colourStart _ .reverseRow
    (view base reader [] [] [] [] ident [] [] (fields (colours a word.reverse)).reverse [] [] hist) at h4
  have h5:=reverse_call .row .reverseRow .frameRow rfl
    (view base reader [] [] [] [] ident [] [] rowword.reverse [] [] hist)
  change Runs program (2*rowword.reverse.length+3) .reverseRow _ .frameRow
    (Function.update (Function.update (view base reader [] [] [] [] ident [] [] rowword.reverse [] [] hist) (aux .rowHistory) [])
      (aux .row) (rowword.reverse.reverse++[])) at h5
  rw [update_rowhist,update_rowword,List.reverse_reverse,List.append_nil] at h5
  have h6:=frame_call .row .frameRow .frameID rfl (view base reader [] [] [] [] ident [] [] [] rowword [] hist) hs
  change Runs program (6*rowword.length+5) .frameRow _ .frameID
    (Function.update (view base reader [] [] [] [] ident [] [] [] rowword [] hist) (aux .frameBuffer) (frame rowword [])) at h6
  rw [update_buf] at h6
  have h7:=frame_call .id .frameID .pairTag rfl (view base reader [] [] [] [] ident [] [] [] rowword (frame rowword []) hist) hs
  change Runs program (6*ident.length+5) .frameID _ .pairTag
    (Function.update (view base reader [] [] [] [] ident [] [] [] rowword (frame rowword []) hist) (aux .frameBuffer)
      (frame ident (frame rowword []))) at h7
  rw [update_buf] at h7
  have h8:Runs program 1 .pairTag (view base reader [] [] [] [] ident [] [] [] rowword (frame ident (frame rowword [])) hist)
      .reversePair (view base reader [] [] [] [] ident [] [] [] rowword (chunk a word) hist):=by
    apply one_base program _ _ (.push (aux .frameBuffer) true .reversePair) _ _ rfl
    · rfl
    · exact update_buf _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h9:=reverse_call .pair .reversePair .clearID rfl
    (view base reader [] [] [] [] ident [] [] [] rowword (chunk a word) hist)
  change Runs program (2*(chunk a word).length+3) .reversePair _ .clearID
    (Function.update (Function.update (view base reader [] [] [] [] ident [] [] [] rowword (chunk a word) hist) (aux .frameBuffer) [])
      (aux .history) ((chunk a word).reverse++hist)) at h9
  rw [update_buf,update_hist] at h9
  have h10:=SemiprimeD1StackPhysicalLoops.drain program .clearID .clearRow (aux .id) rfl
    (view base reader [] [] [] [] ident [] [] [] rowword [] ((chunk a word).reverse++hist)) ident
  rw [update_ident,update_ident] at h10
  have h11:=SemiprimeD1StackPhysicalLoops.drain program .clearRow .header (aux .row) rfl
    (view base reader [] [] [] [] [] [] [] [] rowword [] ((chunk a word).reverse++hist)) rowword
  rw [update_rowword,update_rowword] at h11
  have hall:=compose (compose (compose (compose (compose (compose (compose (compose (compose (compose (compose h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  refine ⟨_,?_,hall⟩
  have hi:ident.length ≤ word.length:=SemiprimeSourceCompactBits.trim_length word
  have hrow:rowword.length ≤ 13*a:=row_length a word
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le word.reverse
  have hchunk:(chunk a word).length=2*ident.length+2*rowword.length+3:=by
    change (true::frame ident (frame rowword [])).length=_
    simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
  rw [List.length_reverse,hlen] at ht
  rw [List.length_reverse,hchunk]
  omega
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Rows
