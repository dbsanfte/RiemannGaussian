/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordPacketCoefficientClock
import RiemannGaussian.SemiprimeD1PacketSourceClock

/-! # Whole actual packet entry report from original finite input bounds
The exact real endpoints, acquired mode descriptors and global exponent tuple
are executed. Every row/column/coefficient/source callback and prefix is paid.
The affine requested-coefficient factor `(K+1)^rows` remains explicit; no
polynomial-in-K claim hides that finite recursion.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordPacketEntryClock
open SemiprimeD1JetAxes SemiprimeD1JetAffineCoefficient SemiprimeD1JetAffineCoefficientBounds
open SemiprimeD1JetWordPacketEntryBits SemiprimeD1PacketEntryInputs SemiprimeD1WordPacketArithmeticClock
open SemiprimeD1PacketEntryBits (borrow multiply sourceProduct)
open SemiprimeD1WordPacketCoefficientClock SemiprimeD1PacketSourceClock

/-- Physical endpoint word copies plus original native slot-value control. -/
def wireClock (a E : ℕ) : ℕ := 4*a+3*E+2*2^a+10

/-- Slot bounds are actual original orientation-word lengths, not desired outputs. -/
theorem wire_clock {V : ℕ} (a : ℕ) (endpoint : SemiprimeD1ChildGraph.Endpoint V) (bit : Bool)
    (E : ℕ) (hs : endpoint.slot.length ≤ a) (he : endpoint.edge.length ≤ E) :
    (wire a endpoint bit).2 ≤ wireClock a E := by
  have hp := SemiprimeBitArithmetic.bitValue_lt_width endpoint.slot
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hs
  have hv : SemiprimeBitArithmetic.bitValue endpoint.slot ≤ 2^a := hp.le.trans hpow
  simp only [wire,SemiprimeSourceCompactBits.copy_clock,SemiprimeSourceCompactBits.copy_bits]
  unfold wireClock
  omega

/-- Complete local side split and every endpoint-word callback. -/
def gatherClock (a A E : ℕ) : ℕ := A*(wireClock a E+6)+2

/-- Actual local gather has a fixed polynomial report in original endpoint bounds. -/
theorem gather_clock {V : ℕ} (a : ℕ) (endpoints : List (SemiprimeD1ChildGraph.Endpoint V))
    (bits : List Bool) (E : ℕ) (hs : ∀e∈endpoints,e.slot.length ≤ a)
    (he : ∀e∈endpoints,e.edge.length ≤ E) :
    (gather a endpoints bits).clock ≤ gatherClock a endpoints.length E := by
  induction endpoints generalizing bits with
  | nil => simp only [gather,gatherClock,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons endpoint endpoints ih =>
    have hh := wire_clock a endpoint (bits.head?.getD false) E
      (hs _ List.mem_cons_self) (he _ List.mem_cons_self)
    have ht := ih bits.tail (fun e hm => hs e (List.mem_cons_of_mem _ hm))
      (fun e hm => he e (List.mem_cons_of_mem _ hm))
    dsimp only [gather]
    split <;> dsimp only <;> unfold gatherClock at ht ⊢ <;>
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

/-- Every actual target mask entry performs one original global-beta read. -/
theorem restrictFrom_work (beta : List ℕ) (items : List SemiprimeD1PacketModeMask.Item) (index : ℕ) :
    (SemiprimeD1PacketModeMask.restrictFrom beta items index).work ≤
      items.length*(3*beta.length+6)+1 := by
  induction items generalizing index with
  | nil => simp only [SemiprimeD1PacketModeMask.restrictFrom,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons item items ih =>
    have hh := SemiprimeD1AffineCoefficientBounds.read_work 0 beta index
    have ht := ih (index+1)
    change (SemiprimeD1AffineCoefficient.read 0 beta index).2+
      (SemiprimeD1PacketModeMask.restrictFrom beta items (index+1)).work+5 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Actual requested-coefficient budget is monotone in real-row count. -/
theorem affine_rows_mono (ctx : Context) (K L A T W C : ℕ) (h : L ≤ A) :
    budget ctx K L T W C ≤ budget ctx K A T W C := by
  unfold budget
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)
  · exact Nat.pow_le_pow_right (by omega) h

/-- Real-row acquisition grows linearly with actual column count. -/
theorem recipe_columns_mono (ctx : Context) (a C A K P T : ℕ) (h : C ≤ A) :
    recipeClock ctx a C K P T ≤ recipeClock ctx a A K P T := by
  unfold recipeClock rowBaseClock
  gcongr

/-- Original source-factor acquisition grows linearly with actual column count. -/
theorem source_columns_mono (ctx : Context) (a C A P B T : ℕ) (h : C ≤ A) :
    sourceFactorClock ctx a C P B T ≤ sourceFactorClock ctx a A P B T := by
  unfold sourceFactorClock
  gcongr

/-- Explicit complete actual entry budget. The only non-polynomial factor is
its literal requested-coefficient row recursion, with at most A real rows. -/
def entryClock (ctx : Context) (a A K P T B L E : ℕ) : ℕ :=
  gatherClock a A E+(K*(3*L+6)+1)+
    (A*(recipeClock ctx a A K P T+4)+1)+
    budget ctx K A K ctx.precision K+
    (K*(sourceFactorClock ctx a A P B L+mulClock ctx+3)+oneClock ctx)+
    mulClock ctx+3+L+10

/-- Whole executed packet entry clock from acquired original dimensional bounds.
Every intermediate physical width/shape is derived from the concrete routines.
No requested coefficient, source-factor value or intermediate clock is supplied. -/
theorem evaluate_clock {V : ℕ} (ctx : Context) (z : JetRun) (hz : Good ctx z.words)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (items : SemiprimeD1PacketModeMask.Cache) (endpoints : List (SemiprimeD1ChildGraph.Endpoint V))
    (beta : List ℕ) (bits : List Bool) (P T B E : ℕ)
    (hmode : ∀item∈items.items,item.mode.order ≤ P) (htile : ∀item∈items.items,item.tile ≤ T)
    (hbeta : ∀b∈beta,b ≤ B) (hslot : ∀e∈endpoints,e.slot.length ≤ a)
    (hedge : ∀e∈endpoints,e.edge.length ≤ E) :
    (evaluate ctx z a i t items endpoints beta bits).clock ≤
      entryClock ctx a endpoints.length items.items.length P T B beta.length E := by
  let input := gather a endpoints bits
  let restricted := SemiprimeD1PacketModeMask.restrict items beta
  let rows := recipes ctx (borrow z) a i t input.columns items.items input.rows
  let target := SemiprimeD1JetAffineCoefficient.evaluate ctx items.items.length rows.value restricted.value
  let source := sourceProduct ctx a i input.columns beta items.items 0
  have hcount := gather_count a endpoints bits
  have hR : input.rows.length ≤ endpoints.length := by
    exact (Nat.le_add_right input.rows.length input.columns.length).trans hcount.le
  have hC : input.columns.length ≤ endpoints.length := by
    exact (Nat.le_add_left input.columns.length input.rows.length).trans hcount.le
  have hinput := gather_clock a endpoints bits E hslot hedge
  have hrestricted := restrictFrom_work beta items.items 0
  have hrestrictedLength : restricted.value.length=items.items.length :=
    SemiprimeD1PacketModeMask.restrictFrom_length _ _ _
  have hrows := recipes_clock ctx (borrow z) hz a i t input.columns items.items input.rows P T hmode htile
  have hrecipes := recipe_columns_mono ctx a input.columns.length endpoints.length items.items.length P T hC
  have hrowsBound : rows.work ≤ endpoints.length*(recipeClock ctx a endpoints.length items.items.length P T+4)+1 := by
    have hh := Nat.mul_le_mul hR (Nat.add_le_add_right hrecipes 4)
    exact hrows.trans (Nat.add_le_add_right hh 1)
  have hrowLength : rows.value.length=input.rows.length := by
    rw [recipes_payload,List.length_map]
  have hsourceRows : ∀row∈rows.value, Source ctx ctx.precision items.items.length row := by
    intro row hrow
    change row ∈ (recipes ctx (borrow z) a i t input.columns items.items input.rows).value at hrow
    rw [recipes_payload] at hrow
    obtain ⟨realRow,_,rfl⟩ := List.mem_map.mp hrow
    exact recipe_source ctx (borrow z) a i t realRow input.columns items.items
  have htarget := SemiprimeD1JetAffineCoefficientBounds.evaluate_clock ctx items.items.length rows.value restricted.value
    ctx.precision items.items.length le_rfl hsourceRows
  rw [hrowLength,hrestrictedLength] at htarget
  have htargetBound : target.clock ≤ budget ctx items.items.length endpoints.length items.items.length ctx.precision items.items.length :=
    htarget.trans (affine_rows_mono ctx _ _ _ _ _ _ hR)
  have hsource := sourceProduct_clock ctx a i input.columns beta items.items 0 P B hmode hbeta
  have hsourceMono := source_columns_mono ctx a input.columns.length endpoints.length P B beta.length hC
  have hsourceBound : source.clock ≤ items.items.length*(sourceFactorClock ctx a endpoints.length P B beta.length+mulClock ctx+3)+oneClock ctx :=
    hsource.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.add_le_add_right hsourceMono (mulClock ctx)) 3)) (oneClock ctx))
  have hout := multiply_clock ctx target source (SemiprimeD1JetAffineCoefficientBounds.evaluate_good ctx _ _ _)
    (sourceProduct_good ctx a i input.columns beta items.items 0)
  change input.clock+restricted.work+rows.work+(multiply ctx target source).clock+beta.length+10 ≤ _
  have hrestricted' : restricted.work ≤ items.items.length*(3*beta.length+6)+1 := hrestricted
  have hinput' : input.clock ≤ gatherClock a endpoints.length E := hinput
  have hmul := hout.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add htargetBound hsourceBound) (mulClock ctx)) 3)
  calc
    _ ≤ gatherClock a endpoints.length E+(items.items.length*(3*beta.length+6)+1)+
        (endpoints.length*(recipeClock ctx a endpoints.length items.items.length P T+4)+1)+
        (budget ctx items.items.length endpoints.length items.items.length ctx.precision items.items.length+
          (items.items.length*(sourceFactorClock ctx a endpoints.length P B beta.length+mulClock ctx+3)+oneClock ctx)+mulClock ctx+3)+beta.length+10 := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add hinput' hrestricted') hrowsBound) hmul) (le_refl beta.length)) (le_refl 10)
    _ = _ := by unfold entryClock;ring

/-- All entry stages except the explicit finite coefficient recursion. -/
def nonAffineClock (ctx : Context) (a A K P T B L E : ℕ) : ℕ :=
  gatherClock a A E+(K*(3*L+6)+1)+(A*(recipeClock ctx a A K P T+4)+1)+
    (K*(sourceFactorClock ctx a A P B L+mulClock ctx+3)+oneClock ctx)+
    mulClock ctx+3+L+10

/-- Fixed arithmetic polynomial prefactor, before the literal (K+1)^A recurrence. -/
def entryPolynomial (ctx : Context) (a A K P T B L E : ℕ) : ℕ :=
  nonAffineClock ctx a A K P T B L E+(A+1)*stageConstant ctx K K ctx.precision K

/-- Exact separation of the finite coefficient-recursion stage. -/
theorem entryClock_eq (ctx : Context) (a A K P T B L E : ℕ) :
    entryClock ctx a A K P T B L E = nonAffineClock ctx a A K P T B L E+
      budget ctx K A K ctx.precision K := by
  unfold entryClock nonAffineClock
  ring

/-- A fixed nonnegative overhead is absorbed without changing the recursion exponent. -/
theorem add_mul_le (X Y q : ℕ) (hq : 1 ≤ q) : X+Y*q ≤ (X+Y)*q := by
  have hx : X ≤ X*q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left X hq
  calc
    _ ≤ X*q+Y*q := Nat.add_le_add_right hx _
    _ = _ := by ring

/-- Whole entry cost is an explicit original-dimension polynomial times the
literal naive coefficient recursion. It does not hide a dynamic-programming shortcut. -/
theorem entryClock_factor (ctx : Context) (a A K P T B L E : ℕ) :
    entryClock ctx a A K P T B L E ≤ entryPolynomial ctx a A K P T B L E*(K+1)^A := by
  rw [entryClock_eq]
  unfold budget entryPolynomial
  exact add_mul_le _ _ _ (Nat.one_le_pow _ _ (by omega))

/-- Uniform table acquisition uses the actual packet arity, including zero-port cases. -/
theorem entryClock_mono_arity (ctx : Context) (a A A' K P T B L E : ℕ) (h : A ≤ A') :
    entryClock ctx a A K P T B L E ≤ entryClock ctx a A' K P T B L E := by
  unfold entryClock gatherClock recipeClock rowBaseClock sourceFactorClock budget
  gcongr

end RiemannGaussian.SemiprimeD1WordPacketEntryClock
