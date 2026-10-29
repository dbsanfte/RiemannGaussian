/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidth
import RiemannGaussian.SemiprimeD1StackRecoveryWidthPolynomial
/-! # Complete72-word physical boundary interpretation and topological gate prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidth
open SemiprimeD1StackUnaryDivmod (unary)
namespace V
export SemiprimeD1StackRecoveryWidthPolynomial (value sourceValue envelope)
end V
/-- Every actual register and auxiliary word, with no omitted work or alias shadow. -/
structure Words where
  /-- All64 actual arithmetic registers. -/
  registers:W.Gate→List Bool:=fun _=>[]
  /-- Actual a word. -/
  a:List Bool:=[]
  /-- Actual m word. -/
  m:List Bool:=[]
  /-- Actual grid word. -/
  grid:List Bool:=[]
  /-- Actual todo word. -/
  todo:List Bool:=[]
  /-- Actual multiplier word. -/
  multiplier:List Bool:=[]
  /-- Actual productScratch word. -/
  productScratch:List Bool:=[]
  /-- Actual copyScratch word. -/
  copyScratch:List Bool:=[]
  /-- Actual output word. -/
  output:List Bool:=[]
/-- Literal complete physical bank. -/
def bank (w:Words) :Stack→List Bool:=Sum.elim w.registers (fun k=>match k with
  | .a=>w.a | .m=>w.m | .grid=>w.grid | .todo=>w.todo | .multiplier=>w.multiplier
  | .productScratch=>w.productScratch | .copyScratch=>w.copyScratch | .output=>w.output)
/-- One real register update leaves all71 other words unchanged. -/
theorem update_reg (w:Words) (g:W.Gate) (xs:List Bool) :
    Function.update (bank w) (reg g) xs=bank {w with registers:=Function.update w.registers g xs}:=by
  funext k;rcases k with k|k
  · simp only [bank,reg,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- A literal a write preserves every other actual register/auxiliary word. -/
theorem update_a (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .a) xs=bank {w with a:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal m write preserves every other actual register/auxiliary word. -/
theorem update_m (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .m) xs=bank {w with m:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal grid write preserves every other actual register/auxiliary word. -/
theorem update_grid (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .grid) xs=bank {w with grid:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal todo write preserves every other actual register/auxiliary word. -/
theorem update_todo (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .todo) xs=bank {w with todo:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal multiplier write preserves every other actual register/auxiliary word. -/
theorem update_multiplier (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .multiplier) xs=bank {w with multiplier:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal productScratch write preserves every other actual register/auxiliary word. -/
theorem update_productScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .productScratch) xs=bank {w with productScratch:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal copyScratch write preserves every other actual register/auxiliary word. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .copyScratch) xs=bank {w with copyScratch:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- A literal output write preserves every other actual register/auxiliary word. -/
theorem update_output (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .output) xs=bank {w with output:=xs}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Exactly the static earlier gate prefix has already been physically acquired. -/
def registers (stage a M N:Nat) (g:W.Gate) :List Bool:=
  if g.val<stage then unary (V.value g a M N) else []
/-- Original unary metadata and physically acquired grid size are retained at every gate boundary. -/
def atGate (stage a M N:Nat) :Words:=
  {registers:=registers stage a M N,a:=unary a,m:=unary M,grid:=unary N}
/-- A fresh actual gate output is physically empty. -/
theorem fresh (g:W.Gate) (a M N:Nat) :bank (atGate g.val a M N) (reg g)=[]:=by
  change (if g.val<g.val then _ else _)=_
  rw [ite_eq_right (Nat.lt_irrefl _)]
/-- Both original/cache wires and every earlier actual gate have their physically acquired marker words. -/
theorem source_ready (g:W.Gate) (s:W.Source) (hs:W.Earlier g s) (a M N:Nat) :
    bank (atGate g.val a M N) (sourceStack s)=unary (V.sourceValue a M N s):=by
  cases s with
  | a=>rfl
  | m=>rfl
  | n=>rfl
  | reg j=>
    change (if j.val<g.val then _ else _)=_
    exact ite_eq_left hs
/-- Completing an actual gate writes only its fresh register and advances the exact prefix by one. -/
theorem registers_write (g:W.Gate) (a M N:Nat) :
    Function.update (registers g.val a M N) g (unary (V.value g a M N))=registers (g.val+1) a M N:=by
  funext j
  by_cases hj:j=g
  · subst j
    simp only [Function.update_self,registers,ite_eq_left (Nat.lt_succ_self _)]
  · rw [Function.update_of_ne hj]
    have hv:j.val≠g.val:=fun h=>hj (Fin.ext h)
    by_cases he:j.val<g.val
    · simp only [registers,ite_eq_left he,ite_eq_left (by omega:j.val<g.val+1)]
    · simp only [registers,ite_eq_right he,ite_eq_right (by omega:¬j.val<g.val+1)]
/-- Complete physical bank after the same actual gate instruction, with all original/cache/work words retained. -/
theorem gate_write (g:W.Gate) (a M N:Nat) :
    Function.update (bank (atGate g.val a M N)) (reg g) (unary (V.value g a M N))=
      bank (atGate (g.val+1) a M N):=by
  rw [update_reg]
  change bank {atGate g.val a M N with registers:=Function.update (registers g.val a M N) g (unary (V.value g a M N))}=_
  rw [registers_write]
  rfl
/-- The zero-gate boundary contains no precomputed polynomial output. -/
theorem zero_registers (a M N:Nat) :registers 0 a M N=fun _=>[]:=by
  funext g;exact ite_eq_right (Nat.not_lt_zero _)
/-- All64 actual gates are present before physical output conversion. -/
theorem complete_registers (a M N:Nat) :registers 64 a M N=fun g=>unary (V.value g a M N):=by
  funext g;exact ite_eq_left g.isLt
/-- Exact initial bank has ONLY the two acquired unary metadata inputs. -/
theorem initial_bank (a m:List Bool) :input a m=bank {a:=a,m:=m}:=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Physically acquired grid size is exponential in unary exponent VALUE and is explicitly retained/paid. -/
def gridSize (a:Nat) :Nat:=2^(a+1)
/-- Exactly the original unary inputs, acquired grid count and physically emitted false template remain at return. -/
def result (a M:Nat) :Stack→List Bool:=bank {a:=unary a,m:=unary M,grid:=unary (gridSize a), output:=List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false}
/-- Actual clean final halt, including flags and every real return cell. -/
def done (a M:Nat) :C.State Stack Label:=⟨none,none,none,result a M,[]⟩
/-- Paid original-dimension resource includes the actual acquired grid size by VALUE. -/
def inputEnvelope (a M:Nat) :Nat:=V.envelope a M (gridSize a)
/-- Proof-side boundary selector follows exactly the fixed static next-gate control. -/
def gateLabel (n:Nat) :Label:=if h:n<64 then .gate ⟨n,h⟩ else .fill
/-- The real finite source advances its fixed instruction position, never an input-supplied counter. -/
theorem next_gate (g:W.Gate) :nextGate g=gateLabel (g.val+1):=rfl
/-- Proof-side cleanup selector names the literal sequence of64 real EOF-drains. -/
def cleanLabel (n:Nat) :Label:=if h:n<64 then .clean ⟨n,h⟩ else .done
/-- Cleanup instruction positions are fixed before all inputs. -/
theorem next_clean (g:W.Gate) :nextClean g=cleanLabel (g.val+1):=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWidthEncoding
