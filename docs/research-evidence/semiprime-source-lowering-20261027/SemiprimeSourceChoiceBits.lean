/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceComparisonBits
import RiemannGaussian.SemiprimeMaterializedWords

/-! # Physical candidate selection and finite assignment control
Candidate IDs are Boolean words. Every selection copies its returned ID and
compares actual produced score words, retaining both producer clocks. Assignment
consumes a physical unary token list and copies its current prefix at every step.
The score compiler remains an explicit interface; the control does not acquire
scores by interpreting rational values or enumerate possible branch paths.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceChoiceBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitProductSort
open SemiprimeRationalBits SemiprimeMaterializedWords

/-- Copy every physical candidate ID cell, retaining its primitive work. -/
def copyID (x : List Bool) : Run (List Bool) :=
  let out := fitBits x x
  ⟨out.bits,bitCost out+1⟩

/-- Exact copied payload, including padding. -/
theorem copyID_value (x : List Bool) : (copyID x).value = x := fitBits_self x

/-- Physical ID copying is linear in its supplied width. -/
theorem copyID_work (x : List Bool) : (copyID x).work ≤ 4*x.length+2 := by
  have h := fitBits_cost x x
  dsimp only [copyID]
  omega

/-- Execute the original tail-first candidate search using only physical score order. -/
def choose (score : List Bool → RationalReport) (a : List Bool) : List (List Bool) → Run (List Bool)
  | [] => copyID a
  | b::bs =>
    let next := choose score b bs
    let left := score a
    let right := score next.value
    let order := SemiprimeSourceComparisonBits.compare left.word right.word
    let out := copyID (if order.order.le = true then a else next.value)
    ⟨out.value,next.work+left.clock+right.clock+order.clock+out.work+3⟩

/-- A selected ID always comes from the actual supplied candidate list. -/
theorem choose_mem (score : List Bool → RationalReport) (a : List Bool) (tail : List (List Bool)) :
    (choose score a tail).value ∈ a::tail := by
  induction tail generalizing a with
  | nil => simp [choose,copyID_value]
  | cons b bs ih =>
    simp only [choose,copyID_value]
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih b)

/-- Exact refinement of the original choice, including its left-on-equality rule. -/
theorem choose_refines (score : List Bool → RationalReport) (a : List Bool) (tail : List (List Bool))
    (hv : ∀ x, (score x).word.Valid) :
    (choose score a tail).value =
      (SemiprimeMaterializedWords.choose (fun x => ⟨(score x).word.value,(score x).clock⟩) a tail).value := by
  induction tail generalizing a with
  | nil => exact copyID_value a
  | cons b bs ih =>
    simp only [choose,copyID_value,SemiprimeMaterializedWords.choose]
    rw [SemiprimeSourceComparisonBits.compare_branch _ _ (hv a) (hv _),ih b]

/-- Every executed candidate score, comparison and returned-ID copy stays paid. -/
theorem choose_work (score : List Bool → RationalReport) (a : List Bool) (tail : List (List Bool))
    (F W B : ℕ) (hs : ∀ x∈a::tail, (score x).clock ≤ F ∧ Width (score x).word W)
    (hb : ∀ x∈a::tail, x.length ≤ B) :
    (choose score a tail).work ≤ tail.length*(2*F+200*(W+1)^2+4*B+5)+4*B+2 := by
  induction tail generalizing a with
  | nil => exact (copyID_work a).trans (by simpa using Nat.add_le_add_right (Nat.mul_le_mul_left 4 (hb a List.mem_cons_self)) 2)
  | cons b bs ih =>
    have ht := ih b (fun x hx => hs x (List.mem_cons_of_mem a hx))
      (fun x hx => hb x (List.mem_cons_of_mem a hx))
    have hn := List.mem_cons_of_mem a (choose_mem score b bs)
    have hl := hs a List.mem_cons_self
    have hr := hs _ hn
    have hc := SemiprimeSourceComparisonBits.compare_clock _ _ W hl.2 hr.2
    have hchoice : (if (SemiprimeSourceComparisonBits.compare (score a).word
        (score (choose score b bs).value).word).order.le = true then a else (choose score b bs).value).length ≤ B := by
      split
      · exact hb a List.mem_cons_self
      · exact hb _ hn
    have hp := copyID_work (if (SemiprimeSourceComparisonBits.compare (score a).word
      (score (choose score b bs).value).word).order.le = true then a else (choose score b bs).value)
    simp only [choose,List.length_cons]
    nlinarith

/-- Copy an entire current assignment, preserving every candidate ID bit. -/
def copyIDs : List (List Bool) → Run (List (List Bool))
  | [] => ⟨[],1⟩
  | a::as =>
    let first := copyID a
    let rest := copyIDs as
    ⟨first.value::rest.value,first.work+rest.work+2⟩

/-- Physical prefix copying preserves the literal candidate list. -/
theorem copyIDs_value (xs : List (List Bool)) : (copyIDs xs).value = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [copyIDs,copyID_value,ih]

/-- Every prefix ID and list cell is charged. -/
theorem copyIDs_work (xs : List (List Bool)) (B : ℕ) (hx : ∀ x∈xs,x.length ≤ B) :
    (copyIDs xs).work ≤ xs.length*(4*B+4)+1 := by
  induction xs with
  | nil => simp [copyIDs]
  | cons x xs ih =>
    have hh := hx x List.mem_cons_self
    have ht := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
    have hc := copyID_work x
    simp only [copyIDs,List.length_cons]
    nlinarith

/-- Consume physical unary loop tokens and execute only the selected search branch.
No numeric counter value is decoded by the control path. -/
def assign (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport) :
    List Bool → List (List Bool) → Run (List (List Bool))
  | [],fixed => copyIDs fixed
  | _::tokens,fixed =>
    let next := choose (fun w => score tokens (w::fixed)) a tail
    let saved := copyIDs (next.value::fixed)
    let rest := assign a tail score tokens saved.value
    ⟨rest.value,next.work+saved.work+rest.work+3⟩

/-- Every loop adds precisely one selected physical ID. -/
theorem assign_length (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (tokens : List Bool) (fixed : List (List Bool)) :
    (assign a tail score tokens fixed).value.length = fixed.length+tokens.length := by
  induction tokens generalizing fixed with
  | nil => simp [assign,copyIDs_value]
  | cons t tokens ih => simp only [assign,copyIDs_value,ih,List.length_cons];omega

/-- The unary-controlled loop reproduces the original finite assignment exactly. -/
theorem assign_refines (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (hv : ∀ tokens fixed, (score tokens fixed).word.Valid)
    (n : ℕ) (fixed : List (List Bool)) :
    (assign a tail score (List.replicate n false) fixed).value =
      (SemiprimeMaterializedWords.assign a tail
        (fun n xs => ⟨(score (List.replicate n false) xs).word.value,
          (score (List.replicate n false) xs).clock⟩) n fixed).value := by
  induction n generalizing fixed with
  | zero => exact copyIDs_value fixed
  | succ n ih =>
    simp only [List.replicate_succ,assign,copyIDs_value,ih,SemiprimeMaterializedWords.assign]
    rw [choose_refines _ a tail (fun w => hv _ (w::fixed))]

/-- All selected IDs retain the original finite width, independent of score values. -/
theorem assign_width (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (tokens : List Bool) (fixed : List (List Bool)) (B : ℕ)
    (ha : ∀ x∈a::tail,x.length ≤ B) (hf : ∀ x∈fixed,x.length ≤ B) :
    ∀ x∈(assign a tail score tokens fixed).value,x.length ≤ B := by
  induction tokens generalizing fixed with
  | nil => simpa only [assign,copyIDs_value] using hf
  | cons t tokens ih =>
    simp only [assign,copyIDs_value]
    apply ih
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha _ (choose_mem _ a tail)
    · exact hf x hx

/-- The executed dynamic loop has linear iteration count and candidate count.
Its producer envelope is needed only on reachable prefix lengths. -/
theorem assign_work (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (tokens : List Bool) (fixed : List (List Bool)) (F W B N : ℕ)
    (ha : ∀ x∈a::tail,x.length ≤ B) (hf : ∀ x∈fixed,x.length ≤ B)
    (hs : ∀ ts xs, ts.length+xs.length ≤ N →
      (score ts xs).clock ≤ F ∧ Width (score ts xs).word W)
    (hlen : tokens.length+fixed.length ≤ N) :
    (assign a tail score tokens fixed).work ≤
      tokens.length*(tail.length*(2*F+200*(W+1)^2+4*B+5)+4*B+2+N*(4*B+4)+4)+
        N*(4*B+4)+1 := by
  induction tokens generalizing fixed with
  | nil =>
    have h := copyIDs_work fixed B hf
    have hm := Nat.mul_le_mul_right (4*B+4) (show fixed.length ≤ N by simpa using hlen)
    simpa only [assign,List.length_nil,Nat.zero_mul,Nat.zero_add] using
      h.trans (Nat.add_le_add_right hm 1)
  | cons t tokens ih =>
    have hnext : ∀ x∈(choose (fun w => score tokens (w::fixed)) a tail).value::fixed,
        x.length ≤ B := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha _ (choose_mem _ a tail)
      · exact hf x hx
    have hc := choose_work (fun w => score tokens (w::fixed)) a tail F W B
      (fun w _ => hs tokens (w::fixed) (by simp only [List.length_cons] at hlen ⊢; omega)) ha
    have hp := copyIDs_work ((choose (fun w => score tokens (w::fixed)) a tail).value::fixed) B hnext
    have ht := ih ((choose (fun w => score tokens (w::fixed)) a tail).value::fixed) hnext
      (by simp only [List.length_cons] at hlen ⊢;omega)
    have hfN : fixed.length+1 ≤ N := by simp only [List.length_cons] at hlen;omega
    have hm := Nat.mul_le_mul_right (4*B+4) hfN
    simp only [assign,copyIDs_value,List.length_cons] at ⊢ hp
    nlinarith

/-- Build the physical loop tokens by an explicit constructor traversal. -/
def acquireTokens : ℕ → Run (List Bool)
  | 0 => ⟨[],1⟩
  | n+1 =>
    let rest := acquireTokens n
    ⟨false::rest.value,rest.work+2⟩

/-- The token producer supplies exactly the finite source iteration count. -/
theorem acquireTokens_value (n : ℕ) : (acquireTokens n).value = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [acquireTokens,ih,List.replicate_succ]

/-- Token acquisition pays every constructor and recursion step. -/
theorem acquireTokens_work (n : ℕ) : (acquireTokens n).work = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [acquireTokens,ih];omega

/-- Acquire the finite iteration tokens before executing dynamic assignment. -/
def run (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (n : ℕ) (fixed : List (List Bool)) : Run (List (List Bool)) :=
  let tokens := acquireTokens n
  let result := assign a tail score tokens.value fixed
  ⟨result.value,tokens.work+result.work+2⟩

/-- The actual token acquisition joins the exact original assignment refinement. -/
theorem run_refines (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (hv : ∀ tokens fixed, (score tokens fixed).word.Valid)
    (n : ℕ) (fixed : List (List Bool)) :
    (run a tail score n fixed).value =
      (SemiprimeMaterializedWords.assign a tail
        (fun n xs => ⟨(score (List.replicate n false) xs).word.value,
          (score (List.replicate n false) xs).clock⟩) n fixed).value := by
  simp only [run,acquireTokens_value,assign_refines a tail score hv]

/-- Both token construction and the executed dynamic search have derived work. -/
theorem run_work (a : List Bool) (tail : List (List Bool))
    (score : List Bool → List (List Bool) → RationalReport)
    (n : ℕ) (fixed : List (List Bool)) (F W B N : ℕ)
    (ha : ∀ x∈a::tail,x.length ≤ B) (hf : ∀ x∈fixed,x.length ≤ B)
    (hs : ∀ ts xs, ts.length+xs.length ≤ N →
      (score ts xs).clock ≤ F ∧ Width (score ts xs).word W)
    (hlen : n+fixed.length ≤ N) :
    (run a tail score n fixed).work ≤
      2*n+3+n*(tail.length*(2*F+200*(W+1)^2+4*B+5)+4*B+2+N*(4*B+4)+4)+
        N*(4*B+4)+1 := by
  have h := assign_work a tail score (List.replicate n false) fixed F W B N ha hf hs
    (by simpa only [List.length_replicate] using hlen)
  simp only [run,acquireTokens_value,acquireTokens_work]
  simp only [List.length_replicate] at h
  omega

end RiemannGaussian.SemiprimeSourceChoiceBits
