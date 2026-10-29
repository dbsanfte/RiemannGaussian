/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceChoiceOrder

/-! # Actual acquired-menu invariants for the existing Boolean-ID controller
Correctness and work contracts are required only for IDs in the acquired menu
and prefixes made from that menu. This avoids assuming resource bounds on
arbitrary external bit strings. The executed controller is unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceWordIdControl
open SemiprimeRationalBits SemiprimeMaterializedWords SemiprimeSourceChoiceBits

/-- Every ID of a stored physical prefix belongs to the actual acquired menu. -/
def InMenu (menu xs : List (List Bool)) : Prop := ∀ x∈xs,x∈menu

/-- Extending a prefix by one acquired ID preserves its concrete menu invariant. -/
theorem inMenu_cons (menu xs : List (List Bool)) (x : List Bool)
    (hx : x∈menu) (hxs : InMenu menu xs) : InMenu menu (x::xs) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hxs y hy

/-- Physical choice returns an actual menu entry, regardless of score values. -/
theorem choose_inMenu (menu : List (List Bool)) (physical : List Bool → RationalReport)
    (a : List Bool) (tail : List (List Bool)) (h : InMenu menu (a::tail)) :
    (SemiprimeSourceChoiceBits.choose physical a tail).value∈menu :=
  h _ (choose_mem physical a tail)

/-- Every stored output ID is either originally fixed or physically selected from the menu. -/
theorem assign_inMenu (menu : List (List Bool)) (a : List Bool) (tail : List (List Bool))
    (physical : List Bool → List (List Bool) → RationalReport)
    (tokens : List Bool) (fixed : List (List Bool))
    (hc : InMenu menu (a::tail)) (hf : InMenu menu fixed) :
    InMenu menu (SemiprimeSourceChoiceBits.assign a tail physical tokens fixed).value := by
  induction tokens generalizing fixed with
  | nil => simpa only [SemiprimeSourceChoiceBits.assign,copyIDs_value] using hf
  | cons t tokens ih =>
    simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value]
    exact ih _ (inMenu_cons menu fixed _ (choose_inMenu menu _ a tail hc) hf)

/-- Order refinement is needed only for actual acquired candidate IDs. -/
theorem choose_decode {A : Type} (menu : List (List Bool)) (decode : List Bool → A)
    (physical : List Bool → RationalReport) (source : A → Run ℚ)
    (hv : ∀ w∈menu,(physical w).word.Valid)
    (ho : ∀ v∈menu,∀ w∈menu,(physical v).word.value ≤ (physical w).word.value ↔
      (source (decode v)).value ≤ (source (decode w)).value)
    (a : List Bool) (tail : List (List Bool)) (hc : InMenu menu (a::tail)) :
    decode (SemiprimeSourceChoiceBits.choose physical a tail).value=
      (SemiprimeMaterializedWords.choose source (decode a) (tail.map decode)).value := by
  induction tail generalizing a with
  | nil => simp only [SemiprimeSourceChoiceBits.choose,copyID_value,List.map_nil,
      SemiprimeMaterializedWords.choose]
  | cons b bs ih =>
    have ht : InMenu menu (b::bs) := fun w hw => hc w (List.mem_cons_of_mem a hw)
    have ha := hc a List.mem_cons_self
    have hn := choose_inMenu menu physical b bs ht
    have hh := ho a ha (SemiprimeSourceChoiceBits.choose physical b bs).value hn
    simp only [SemiprimeSourceChoiceBits.choose,copyID_value,List.map_cons,
      SemiprimeMaterializedWords.choose]
    rw [SemiprimeSourceComparisonBits.compare_branch _ _ (hv a ha) (hv _ hn)]
    simp only [apply_ite,hh,ih b ht]
    split <;> simp_all

/-- Exact original assignment from concrete valid-menu prefix score refinement. -/
theorem assign_decode {A : Type} (menu : List (List Bool)) (decode : List Bool → A)
    (a : List Bool) (tail : List (List Bool))
    (physical : List Bool → List (List Bool) → RationalReport)
    (source : ℕ → List A → Run ℚ)
    (hv : ∀ ts xs,InMenu menu xs → (physical ts xs).word.Valid)
    (ho : ∀ ts xs,InMenu menu xs → ∀ v∈menu,∀ w∈menu,
      (physical ts (v::xs)).word.value ≤ (physical ts (w::xs)).word.value ↔
        (source ts.length (decode v::xs.map decode)).value ≤
          (source ts.length (decode w::xs.map decode)).value)
    (tokens : List Bool) (fixed : List (List Bool))
    (hc : InMenu menu (a::tail)) (hf : InMenu menu fixed) :
    (SemiprimeSourceChoiceBits.assign a tail physical tokens fixed).value.map decode=
      (SemiprimeMaterializedWords.assign (decode a) (tail.map decode) source tokens.length
        (fixed.map decode)).value := by
  induction tokens generalizing fixed with
  | nil => simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value,List.length_nil,
      SemiprimeMaterializedWords.assign]
  | cons t tokens ih =>
    have hnext := choose_inMenu menu (fun w => physical tokens (w::fixed)) a tail hc
    have hc' := choose_decode menu decode (fun w => physical tokens (w::fixed))
      (fun w => source tokens.length (w::fixed.map decode))
      (fun w hw => hv tokens (w::fixed) (inMenu_cons menu fixed w hw hf))
      (ho tokens fixed hf) a tail hc
    have ht := ih _ (inMenu_cons menu fixed _ hnext hf)
    simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value,ht,List.map_cons,hc',
      List.length_cons,SemiprimeMaterializedWords.assign]

/-- The acquired unary-token wrapper preserves exact labels under reachable-menu contracts. -/
theorem run_decode {A : Type} (menu : List (List Bool)) (decode : List Bool → A)
    (a : List Bool) (tail : List (List Bool))
    (physical : List Bool → List (List Bool) → RationalReport)
    (source : ℕ → List A → Run ℚ)
    (hv : ∀ ts xs,InMenu menu xs → (physical ts xs).word.Valid)
    (ho : ∀ ts xs,InMenu menu xs → ∀ v∈menu,∀ w∈menu,
      (physical ts (v::xs)).word.value ≤ (physical ts (w::xs)).word.value ↔
        (source ts.length (decode v::xs.map decode)).value ≤
          (source ts.length (decode w::xs.map decode)).value)
    (n : ℕ) (fixed : List (List Bool)) (hc : InMenu menu (a::tail)) (hf : InMenu menu fixed) :
    (SemiprimeSourceChoiceBits.run a tail physical n fixed).value.map decode=
      (SemiprimeMaterializedWords.assign (decode a) (tail.map decode) source n (fixed.map decode)).value := by
  simpa only [SemiprimeSourceChoiceBits.run,acquireTokens_value,List.length_replicate] using
    assign_decode menu decode a tail physical source hv ho (List.replicate n false) fixed hc hf

/-- Actual prefix contracts suffice for the controller's full scan/copy/comparison report. -/
theorem assign_work (menu : List (List Bool)) (a : List Bool) (tail : List (List Bool))
    (physical : List Bool → List (List Bool) → RationalReport)
    (tokens : List Bool) (fixed : List (List Bool)) (F W B N : ℕ)
    (hm : ∀ x∈menu,x.length ≤ B) (hc : InMenu menu (a::tail)) (hf : InMenu menu fixed)
    (hs : ∀ ts xs,ts.length+xs.length ≤ N → InMenu menu xs →
      (physical ts xs).clock ≤ F ∧ Width (physical ts xs).word W)
    (hlen : tokens.length+fixed.length ≤ N) :
    (SemiprimeSourceChoiceBits.assign a tail physical tokens fixed).work ≤
      tokens.length*(tail.length*(2*F+200*(W+1)^2+4*B+5)+4*B+2+N*(4*B+4)+4)+
        N*(4*B+4)+1 := by
  induction tokens generalizing fixed with
  | nil =>
    have hh := copyIDs_work fixed B (fun x hx => hm x (hf x hx))
    have hN : fixed.length ≤ N := by simpa using hlen
    simpa only [SemiprimeSourceChoiceBits.assign,List.length_nil,Nat.zero_mul,Nat.zero_add] using
      hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (4*B+4) hN) 1)
  | cons t tokens ih =>
    have hn := choose_inMenu menu (fun w => physical tokens (w::fixed)) a tail hc
    have hnew := inMenu_cons menu fixed _ hn hf
    have hchoose := SemiprimeSourceChoiceBits.choose_work (fun w => physical tokens (w::fixed)) a tail F W B
      (fun w hw => hs tokens (w::fixed)
        (by simp only [List.length_cons] at hlen ⊢;omega)
        (inMenu_cons menu fixed w (hc w hw) hf))
      (fun w hw => hm w (hc w hw))
    have hp := copyIDs_work ((SemiprimeSourceChoiceBits.choose (fun w => physical tokens (w::fixed)) a tail).value::fixed)
      B (fun w hw => hm w (hnew w hw))
    have ht := ih _ hnew (by simp only [List.length_cons] at hlen ⊢;omega)
    have hfix : fixed.length+1 ≤ N := by simp only [List.length_cons] at hlen;omega
    have hmul := Nat.mul_le_mul_right (4*B+4) hfix
    simp only [SemiprimeSourceChoiceBits.assign,copyIDs_value,List.length_cons] at ⊢ hp
    nlinarith

/-- Token acquisition is included before executing the bounded actual-menu controller. -/
theorem run_work (menu : List (List Bool)) (a : List Bool) (tail : List (List Bool))
    (physical : List Bool → List (List Bool) → RationalReport)
    (n : ℕ) (fixed : List (List Bool)) (F W B N : ℕ)
    (hm : ∀ x∈menu,x.length ≤ B) (hc : InMenu menu (a::tail)) (hf : InMenu menu fixed)
    (hs : ∀ ts xs,ts.length+xs.length ≤ N → InMenu menu xs →
      (physical ts xs).clock ≤ F ∧ Width (physical ts xs).word W)
    (hlen : n+fixed.length ≤ N) :
    (SemiprimeSourceChoiceBits.run a tail physical n fixed).work ≤
      2*n+3+n*(tail.length*(2*F+200*(W+1)^2+4*B+5)+4*B+2+N*(4*B+4)+4)+
        N*(4*B+4)+1 := by
  have h := assign_work menu a tail physical (List.replicate n false) fixed F W B N hm hc hf hs
    (by simpa only [List.length_replicate] using hlen)
  simp only [SemiprimeSourceChoiceBits.run,acquireTokens_value,acquireTokens_work]
  simp only [List.length_replicate] at h
  omega

end RiemannGaussian.SemiprimeSourceWordIdControl
