/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueRow
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueNumeric
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueParse
open SemiprimeD1StackOwnerCatalogueRecord SemiprimeD1StackOwnerCatalogueRow
open SemiprimeD1StackOwnerCatalogueClear SemiprimeD1StackOwnerCatalogueCacheClear
open SemiprimeSourceHistogramKeyBits (frame_length)
namespace Rn
export SemiprimeD1StackPortOwnerRecipeNumeric (cap volume input_length_le)
end Rn
/-- Derived bound on all actually computed arithmetic words, including the emitted key. -/
def recipeCap (v:Nat) : Nat := 50002*((v+1)^2+1)^2
/-- Fixed degree-four majorant for one COMPLETE actual row iteration. -/
def rowCap (v:Nat) : Nat :=1000000*(v+recipeCap v+1)
/-- Each actual halted recipe word is bounded by the SAME real execution, including all scratch. -/
theorem recipe_word_bound (c:P.Counters) (tag:P.Tag) (ht:c.tag=(P.tagCode tag).val) (hd:0<c.digits)
    (v:Nat) (hv:Rn.volume c≤v) (k:RecipeWork) : (recipeWork c tag k).length≤recipeCap v := by
  obtain ⟨t,htime,hr⟩:=SemiprimeD1StackPortOwnerRecipeExecution.source_run c tag ht hd
  have hw:=SemiprimeD1StackReturnLink.run_data_bound SemiprimeD1StackPortOwnerRecipe.program t
    (2*(Rn.cap c+1)^2) _ _ (by
      intro i;rcases i with i|i
      · exact Rn.input_length_le c i
      · exact Nat.zero_le _) hr (.inr k)
  have hb:=SemiprimeD1StackPortOwnerRecipeBounds.budget_cap c tag
  have hc:Rn.cap c≤(v+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have hp:(Rn.cap c+1)^2≤((v+1)^2+1)^2:=Nat.pow_le_pow_left (by omega) 2
  change (recipeWork c tag k).length≤_ at hw
  unfold recipeCap
  omega
/-- Every physically framed record suffix has its actual linear field-byte length. -/
theorem recordTail_bound (p:Fin 7→List Bool) (v n:Nat) (hn:n≤6) (hp:∀i,(p i).length≤v) :
    (recordTail p n).length≤n*(2*v+1) := by
  induction n with
  | zero=>rw [recordTail_zero];simp
  | succ n ih=>
    have hlt:n<6:=by omega
    rw [←recordTail_step p n hlt,frame_length]
    have h:=hp ⟨5-n,by omega⟩
    have hi:=ih (by omega)
    nlinarith
/-- The actual six-field record cannot exceed the sum of its actual field-byte bounds. -/
theorem record_bound (p:Fin 7→List Bool) (v:Nat) (hp:∀i,(p i).length≤v) :
    (edgeRest p 0 []).length≤12*v+6 := by
  have h:=recordTail_bound p v 6 (by omega) hp
  rw [recordTail_six] at h
  omega
/-- All 47 real drain clocks are bounded by the ACTUAL halted work words. -/
theorem workTime_bound (w:RecipeWork→List Bool) (v n:Nat) (hw:∀k,(w k).length≤v) :
    workTime w n≤n*(v+1) := by
  induction n with
  | zero=>simp only [workTime,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=hw (workRole ⟨n%47,Nat.mod_lt _ (by omega)⟩)
    simp only [workTime]
    nlinarith
/-- All nine real row-payload erasure clocks count their actual bytes and EOF pops. -/
theorem cacheTime_bound (p:Packet) (v n:Nat) (hp:∀i,(p i).length≤v) :
    cacheTime p n≤n*(v+1) := by
  induction n with
  | zero=>simp only [cacheTime,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=hp ⟨n%9,Nat.mod_lt _ (by omega)⟩
    simp only [cacheTime]
    nlinarith
/-- COMPLETE same-source row budget is polynomial in acquired operand/ID-byte bounds. -/
theorem row_budget_bound (p:Fin 7→List Bool) (c:P.Counters) (tag:P.Tag)
    (ht:c.tag=(P.tagCode tag).val) (hd:0<c.digits) (v:Nat)
    (hp:∀i,(p i).length≤v) (hv:Rn.volume c≤v) :
    SemiprimeD1StackOwnerCatalogueRow.budget p c tag≤rowCap v := by
  have hparse:=row_read_bound p v hp
  have hrecord:=recordTime_bound p v 6 hp
  have hr:=record_bound p v hp
  have he:(equalityBytes p).length≤12*v+7:=by simpa only [equalityBytes,List.length_append,List.length_cons,List.length_nil] using Nat.add_le_add_right hr 1
  have hwords:=recipe_word_bound c tag ht hd v hv
  have ha:(arithmeticBytes c tag).length≤recipeCap v:=hwords (.inr .output)
  have hwork:=workTime_bound (recipeWork c tag) (recipeCap v) 47 hwords
  have hpacket:∀i,(rowPacket p i).length≤12*v+7:=by
    intro i;unfold rowPacket
    split
    · have h:=hp ⟨i.val,by omega⟩;omega
    · split
      · exact hr.trans (by omega)
      · exact he
  have hcache:=cacheTime_bound (rowPacket p) (12*v+7) 9 hpacket
  have hb:=SemiprimeD1StackPortOwnerRecipeBounds.budget_cap c tag
  have hc:Rn.cap c≤(v+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have hpow:(Rn.cap c+1)^2≤((v+1)^2+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have hb':SemiprimeD1StackPortOwnerRecipeExecution.budget c tag≤recipeCap v:=by
    unfold recipeCap;omega
  have hid:=hp 6
  unfold SemiprimeD1StackOwnerCatalogueRow.budget rowCap
  omega
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueNumeric
