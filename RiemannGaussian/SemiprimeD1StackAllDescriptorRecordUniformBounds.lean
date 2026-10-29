/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordClock

/-! # Uniform bounds for the actual eighteen-family descriptor source
All bounds below concern the frozen executing source's own clock. Byte and
arity bounds are proof-side estimates of its real acquired input, never
additional runtime operands or supplied execution times.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordUniformBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace D
export SemiprimeD1StackDescriptorRecord (Stack initial)
export SemiprimeD1StackDescriptorRecordExecution (prepareBound)
end D
namespace Clock
export SemiprimeD1StackAllDescriptorRecordClock (componentBound runBound)
end Clock
/-- Complete physical input byte measure, including numerical conversion capacity. -/
def inventory (raw:Fin 6→List Bool) (words:List (List Bool)) (M:Nat) (hist out:List Bool) : Nat :=
  (∑i:Fin 6,(raw i).length)+(vectorBits words).length+M+hist.length+out.length+10
/-- Every actual source word is bounded by the full physical byte measure. -/
theorem raw_length_le (raw:Fin 6→List Bool) (words:List (List Bool)) (M:Nat) (hist out:List Bool) (i:Fin 6) :
    (raw i).length ≤ inventory raw words M hist out := by
  have h:=Finset.single_le_sum (f:=fun j:Fin 6=>(raw j).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  unfold inventory
  omega
/-- An abstract clean descriptor loader has no uncharged physical initial word. -/
theorem loader_cell_bound {K L:Type} (s:SemiprimeD1StackStaticTable.Static K L)
    (fields:Fin 6→List Bool) (bank hist out:List Bool) (J:Nat)
    (hfields:∀i,(fields i).length ≤ J) (hb:bank.length ≤ J) (hh:hist.length ≤ J) (ho:out.length ≤ J)
    (k:D.Stack K) : ((D.initial s (fun _=>[]) fields bank hist out).data k).length ≤ J := by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · exact Nat.zero_le _
      · rcases k with k|k
        · exact Nat.zero_le _
        · rcases k with k|k
          · cases k <;> first | exact hb | exact Nat.zero_le _
          · cases k <;> exact Nat.zero_le _
    · rcases k with k|k
      · cases k <;> exact Nat.zero_le _
      · cases k <;> first | exact hh | exact ho | exact Nat.zero_le _
  · rcases k with k|k
    · exact hfields k
    · exact Nat.zero_le _
/-- The real template drain/copy clock is uniformly linear in the input word bound. -/
theorem prepare_bound {K L:Type} [Fintype K]
    (s:SemiprimeD1StackStaticTable.Static K L) (fields:Fin 6→List Bool) (bank hist out:List Bool) (J:Nat)
    (hJ:1 ≤ J) (hK:Fintype.card K ≤ 204) (hs:s.roles.length ≤ 204)
    (hfields:∀i,(fields i).length ≤ J) (hb:bank.length ≤ J) (hh:hist.length ≤ J) (ho:out.length ≤ J) :
    D.prepareBound s (fun _=>[]) fields bank hist out ≤ 1000000*J := by
  have hc:=loader_cell_bound s fields bank hist out J hfields hb hh ho
  have hi:SemiprimeD1StackDescriptorRecordLoadView.inventory
      (D.initial s (fun _=>[]) fields bank hist out).data ≤ 443*J := by
    unfold SemiprimeD1StackDescriptorRecordLoadView.inventory
    calc
      _ ≤ ∑_k:D.Stack K,J:=Finset.sum_le_sum (fun k _=>hc k)
      _=Fintype.card (D.Stack K)*J:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
      _ ≤ 443*J:=Nat.mul_le_mul_right J (by rw [SemiprimeD1StackDescriptorRecord.stack_card];omega)
  have hr:=Nat.mul_le_mul_right
    (SemiprimeD1StackDescriptorRecordLoad.loadUnit (D.initial s (fun _=>[]) fields bank hist out).data) hs
  unfold SemiprimeD1StackDescriptorRecordLoad.loadUnit at hr
  unfold SemiprimeD1StackDescriptorRecordExecution.prepareBound SemiprimeD1StackDescriptorRecordLoad.loadUnit
  omega
/-- The selector's two physical singleton words stay within the same byte cap. -/
theorem selected_fields_bound (raw:Fin 6→List Bool) (second inverse:Bool) (J:Nat) (hJ:1 ≤ J)
    (hraw:∀i,(raw i).length ≤ J) :
    ∀i,(SemiprimeD1StackSelectedDescriptorRecord.fields raw [second] [inverse] i).length ≤ J := by
  intro i
  unfold SemiprimeD1StackSelectedDescriptorRecord.fields
  split_ifs <;> first | exact hJ | exact hraw i
/-- One fixed polynomial capacity for every scalar checker used by the dispatcher. -/
def envelope (I B:Nat) : Nat :=10^120*((I+1)^18*2^B)
/-- Simple lower powers fit the fixed checker polynomial at every input size. -/
theorem lower_power (I n:Nat) (hn:n ≤ 18) : (I+1)^n ≤ (I+1)^18 :=
  Nat.pow_le_pow_right (by omega) hn
/-- Raising a bounded physical inventory preserves the explicit fixed coefficient. -/
theorem inventory_power (x I n:Nat) (hx:x ≤ 4*(I+1)) (hn:n ≤ 18) : x^n ≤ 4^18*(I+1)^18 := by
  calc
    _ ≤ (4*(I+1))^n:=Nat.pow_le_pow_left hx n
    _=4^n*(I+1)^n:=mul_pow _ _ _
    _ ≤ 4^18*(I+1)^18:=Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hn) (lower_power I n hn)
/-- Every concrete fixed monomial is charged in the same common envelope. -/
theorem monomial_cap (c x I n e B:Nat) (hx:x ≤ 4*(I+1)) (hn:n ≤ 18) (he:e ≤ B) :
    c*x^n*2^e ≤ c*4^18*((I+1)^18*2^B) := by
  have hp:=Nat.mul_le_mul (inventory_power x I n hx hn)
    (Nat.pow_le_pow_right (by decide:1 ≤ (2:Nat)) he)
  calc
    _=c*(x^n*2^e):=by ring
    _ ≤ c*((4^18*(I+1)^18)*2^B):=Nat.mul_le_mul_left c hp
    _= _:=by ring
/-- Every family, including both transforms and all Boolean tags, obeys one
fixed actual-clock bound with explicit physical-word and arity estimates. -/
theorem component_bound (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool))
    (M:Nat) (hist out:List Bool) (I B:Nat)
    (hraw:∀i,(raw i).length ≤ I) (hb:(vectorBits words).length ≤ I)
    (hh:hist.length ≤ I) (ho:out.length ≤ I) (hM:M ≤ I)
    (hs:words.length ≤ B)
    (hp:SemiprimeD1StackProductTableSpec.arity (raw 0) ≤ B)
    (hz:(SemiprimeD1StackZeroBoundaryTable.cached (raw 0)).length ≤ B) :
    Clock.componentBound code raw words M hist out ≤ envelope I B := by
  let Q:=(I+1)^18*2^B
  have hone:1 ≤ (2:Nat)^B:=Nat.pow_pos (by decide)
  have hpoly:1 ≤ (I+1)^18:=Nat.pow_pos (by omega)
  have hQ:1 ≤ Q:=Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by decide))
  have hJ:I+1 ≤ Q:=by
    have h0: I+1 ≤ (I+1)^18:=by simpa only [pow_one] using lower_power I 1 (by decide)
    exact h0.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((I+1)^18) hone)
  have hJ2:(I+1)^2 ≤ Q:=
    (lower_power I 2 (by decide)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((I+1)^18) hone)
  have hc:words.length ≤ I:=(SemiprimeD1StackStaticTableBounds.scope_count_le words).trans hb
  have hconv:110*(words.length+1)*(M+1) ≤ 110*Q:=by
    have h0:=Nat.mul_le_mul (show words.length+1 ≤ I+1 by omega) (show M+1 ≤ I+1 by omega)
    have h1:(words.length+1)*(M+1) ≤ Q:=h0.trans (by simpa only [pow_two] using hJ2)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 110 h1
  have hexp (e:Nat) (he:e ≤ B) : (2:Nat)^e ≤ Q:=by
    have h0:=Nat.pow_le_pow_right (by decide:1 ≤ (2:Nat)) he
    exact h0.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^B) hpoly)
  have hscope:=hexp words.length hs
  have hprod:=hexp (SemiprimeD1StackProductTableSpec.arity (raw 0)) hp
  have hzero:=hexp (SemiprimeD1StackZeroBoundaryTable.cached (raw 0)).length hz
  have hf:∀i,(raw i).length ≤ I+1:=fun i=>(hraw i).trans (Nat.le_succ I)
  have hbf:(vectorBits words).length ≤ I+1:=hb.trans (Nat.le_succ I)
  have hhf:hist.length ≤ I+1:=hh.trans (Nat.le_succ I)
  have hof:out.length ≤ I+1:=ho.trans (Nat.le_succ I)
  have hprepareI:=prepare_bound SemiprimeD1StackPublicInputTable.static raw (vectorBits words) hist out (I+1)
    (by omega) (by exact SemiprimeD1StackPublicInput.stack_card.le.trans (by decide))
    (by change SemiprimeD1StackPublicInputTable.roles.length ≤ 204;exact SemiprimeD1StackPublicInputTable.roles_length.le.trans (by decide)) hf hbf hhf hof
  have hprepareC:=prepare_bound SemiprimeD1StackPublicCarryTable.static raw (vectorBits words) hist out (I+1)
    (by omega) (by exact SemiprimeD1StackPublicCarry.stack_card.le.trans (by decide))
    (by change SemiprimeD1StackPublicCarryTable.roles.length ≤ 204;exact SemiprimeD1StackPublicCarryTable.roles_length.le.trans (by decide)) hf hbf hhf hof
  have hprepareS:=prepare_bound SemiprimeD1StackPublicScaleTable.static
    (SemiprimeD1StackSelectedDescriptorRecord.fields raw [false] [((raw 2).length==2)])
    (vectorBits words) hist out (I+1) (by omega)
    (by exact SemiprimeD1StackPublicScale.stack_card.le.trans (by decide))
    (by change SemiprimeD1StackPublicScaleTable.roles.length ≤ 204;exact SemiprimeD1StackPublicScaleTable.roles_length.le.trans (by decide))
    (selected_fields_bound raw false _ (I+1) (by omega) hf) hbf hhf hof
  have hprepareT:=prepare_bound SemiprimeD1StackPublicTransformTable.static
    (SemiprimeD1StackSelectedDescriptorRecord.fields raw [code.val==3] [((raw 2).length==2)])
    (vectorBits words) hist out (I+1) (by omega)
    (by exact SemiprimeD1StackPublicTransform.stack_card.le.trans (by decide))
    (by change SemiprimeD1StackPublicTransformTable.roles.length ≤ 204;exact SemiprimeD1StackPublicTransformTable.roles_length.le.trans (by decide))
    (selected_fields_bound raw _ _ (I+1) (by omega) hf) hbf hhf hof
  have hinput:SemiprimeD1StackPublicInputTableBounds.runBound (raw 0) (raw 3) words ≤ 10^20*4^18*Q:=by
    have h:=monomial_cap (10^20) (SemiprimeD1StackPublicInputTableBounds.inventory (raw 0) (raw 3) words)
      I 2 words.length B (by
        unfold SemiprimeD1StackPublicInputTableBounds.inventory
        have h0:=hraw 0;have h3:=hraw 3
        omega) (by decide) hs
    unfold SemiprimeD1StackPublicInputTableBounds.runBound
    norm_num only at h ⊢
    exact h
  have hcarry:SemiprimeD1StackPublicCarryTableBounds.runBound (raw 0) (raw 2) words ≤ 10^20*4^18*Q:=by
    have h:=monomial_cap (10^20) (SemiprimeD1StackPublicCarryTableBounds.inventory (raw 0) (raw 2) words)
      I 2 words.length B (by
        unfold SemiprimeD1StackPublicCarryTableBounds.inventory
        have h0:=hraw 0;have h2:=hraw 2
        omega) (by decide) hs
    unfold SemiprimeD1StackPublicCarryTableBounds.runBound
    norm_num only at h ⊢
    exact h
  have hscale:SemiprimeD1StackPublicScaleTableBounds.runBound (raw 0) (raw 3) (raw 4) words ≤ 10^80*4^18*Q:=by
    exact monomial_cap (10^80) (SemiprimeD1StackPublicScaleTableBounds.inventory (raw 0) (raw 3) (raw 4) words)
      I 16 words.length B (by
        unfold SemiprimeD1StackPublicScaleTableBounds.inventory
        have h0:=hraw 0;have h3:=hraw 3;have h4:=hraw 4
        omega) (by decide) hs
  have htransform:SemiprimeD1StackPublicTransformTableBounds.runBound (raw 0) words ≤ 10^100*4^18*Q:=by
    exact monomial_cap (10^100) (SemiprimeD1StackPublicTransformTableBounds.inventory (raw 0) words)
      I 18 words.length B (by
        unfold SemiprimeD1StackPublicTransformTableBounds.inventory
        have h0:=hraw 0
        omega) (by decide) hs
  have hproduct:SemiprimeD1StackProductTableBounds.runBound (raw 0) ≤ 10^30*4^18*Q:=by
    have h:=monomial_cap (10^30) ((raw 0).length+1) I 3
      (SemiprimeD1StackProductTableSpec.arity (raw 0)) B (by have h0:=hraw 0;omega) (by decide) hp
    unfold SemiprimeD1StackProductTableBounds.runBound
    norm_num only at h ⊢
    exact h
  have hpublic:SemiprimeD1BinaryPublicAcquisitionExecution.timeBound (raw 0) ≤ 800000*Q:=by
    have h0:=Nat.pow_le_pow_left (show (raw 0).length+1 ≤ I+1 by have h:=hraw 0;omega) 2
    unfold SemiprimeD1BinaryPublicAcquisitionExecution.timeBound
    exact Nat.mul_le_mul_left _ (h0.trans hJ2)
  have hselector:SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) [] [] ≤ 27*(I+1):=by
    have h1:=hraw 1;have h2:=hraw 2
    unfold SemiprimeD1StackTransformSelectorsExecution.timeBound
    simp only [List.length_nil]
    omega
  unfold SemiprimeD1StackAllDescriptorRecordClock.componentBound
  cases h:SemiprimeD1StackAllDescriptorRecordSpec.family code with
  | input=>
    dsimp only
    unfold SemiprimeD1StackInputDescriptorRecordBounds.runBound SemiprimeD1StackPublicInputRecordClock.runBound
    generalize heq : SemiprimeD1StackDescriptorRecordExecution.prepareBound
      SemiprimeD1StackPublicInputTable.static (fun _=>[]) raw (vectorBits words) hist out=prepTime
    have hprep:prepTime ≤ 1000000*(I+1):=by
      rw [←heq]
      exact hprepareI
    change _ ≤ 10^120*Q
    norm_num only [Nat.add_assoc]
    omega
  | carry=>
    dsimp only
    unfold SemiprimeD1StackCarryDescriptorRecordBounds.runBound SemiprimeD1StackPublicCarryRecordClock.runBound
    generalize heq : SemiprimeD1StackDescriptorRecordExecution.prepareBound
      SemiprimeD1StackPublicCarryTable.static (fun _=>[]) raw (vectorBits words) hist out=prepTime
    have hprep:prepTime ≤ 1000000*(I+1):=by
      rw [←heq]
      exact hprepareC
    change _ ≤ 10^120*Q
    norm_num only [Nat.add_assoc]
    omega
  | scale=>
    dsimp only
    unfold SemiprimeD1StackScaleDescriptorRecord.runBound SemiprimeD1StackPublicScaleRecordClock.runBound
    generalize heq : SemiprimeD1StackDescriptorRecordExecution.prepareBound
      SemiprimeD1StackPublicScaleTable.static (fun _=>[]) (SemiprimeD1StackSelectedDescriptorRecord.fields raw [false] [(raw 2).length==2]) (vectorBits words) hist out=prepTime
    have hprep:prepTime ≤ 1000000*(I+1):=by
      rw [←heq]
      exact hprepareS
    change _ ≤ 10^120*Q
    norm_num only [Nat.add_assoc]
    omega
  | transform=>
    dsimp only
    unfold SemiprimeD1StackTransformDescriptorRecord.runBound SemiprimeD1StackPublicTransformRecordClock.runBound
    generalize heq : SemiprimeD1StackDescriptorRecordExecution.prepareBound
      SemiprimeD1StackPublicTransformTable.static (fun _=>[]) (SemiprimeD1StackSelectedDescriptorRecord.fields raw [code.val==3] [(raw 2).length==2]) (vectorBits words) hist out=prepTime
    have hprep:prepTime ≤ 1000000*(I+1):=by
      rw [←heq]
      exact hprepareT
    change _ ≤ 10^120*Q
    norm_num only [Nat.add_assoc]
    omega
  | product=>dsimp only;change _ ≤ 10^120*Q;norm_num only [Nat.add_assoc];omega
  | boundary=>dsimp only;change _ ≤ 10^120*Q;norm_num only [Nat.add_assoc];omega
  | boolean mode=>dsimp only;change _ ≤ 10^120*Q;norm_num only [Nat.add_assoc];omega
/-- Every allocated initial role, including all dormant private shadows, is charged. -/
theorem mass_clean_bound (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) (I:Nat)
    (hraw:∀i,(raw i).length ≤ I) (hb:(vectorBits words).length ≤ I)
    (hh:hist.length ≤ I) (ho:out.length ≤ I) :
    SemiprimeD1StackAllDescriptorRecordCleanup.mass
      (SemiprimeD1StackAllDescriptorRecord.cleanData raw (vectorBits words) hist out) ≤ 1263*I := by
  have hcell (k:SemiprimeD1StackAllDescriptorRecord.Stack) :
      (SemiprimeD1StackAllDescriptorRecord.cleanData raw (vectorBits words) hist out k).length ≤ I := by
    cases k with
    | inl k=>cases k with
      | source i=>exact hraw i
      | bank=>exact hb
      | history=>exact hh
      | output=>exact ho
      | tagReader=>exact Nat.zero_le _
      | copyScratch=>exact Nat.zero_le _
    | inr k=>exact Nat.zero_le _
  unfold SemiprimeD1StackAllDescriptorRecordCleanup.mass
  calc
    _ ≤ ∑_k:SemiprimeD1StackAllDescriptorRecord.Stack,I:=Finset.sum_le_sum (fun k _=>hcell k)
    _=1263*I:=by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackAllDescriptorRecord.stack_card,smul_eq_mul]
/-- Same complete source clock, including all1252 private drains, under one fixed envelope. -/
theorem run_bound (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool))
    (M:Nat) (hist out:List Bool) (I B:Nat)
    (hraw:∀i,(raw i).length ≤ I) (hb:(vectorBits words).length ≤ I)
    (hh:hist.length ≤ I) (ho:out.length ≤ I) (hM:M ≤ I)
    (hs:words.length ≤ B)
    (hp:SemiprimeD1StackProductTableSpec.arity (raw 0) ≤ B)
    (hz:(SemiprimeD1StackZeroBoundaryTable.cached (raw 0)).length ≤ B) :
    Clock.runBound code raw words M hist out ≤ 10^130*((I+1)^18*2^B) := by
  let Q:=(I+1)^18*2^B
  have h0:=component_bound code raw words M hist out I B hraw hb hh ho hM hs hp hz
  change Clock.componentBound code raw words M hist out ≤ 10^120*Q at h0
  have hm:=mass_clean_bound raw words hist out I hraw hb hh ho
  have hone:1 ≤ (2:Nat)^B:=Nat.pow_pos (by decide)
  have hpoly: I+1 ≤ (I+1)^18:=by simpa only [pow_one] using lower_power I 1 (by decide)
  have hQ:I+1 ≤ Q:=hpoly.trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((I+1)^18) hone)
  unfold SemiprimeD1StackAllDescriptorRecordClock.runBound
  change _ ≤ 10^130*Q
  omega
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordUniformBounds
