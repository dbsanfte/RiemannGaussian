/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRingBits

/-! # Concrete eager local tensor tables
Subexponential space permits complete local tables. They contain literal
coefficient words; there are no entry recipes or requested-value suppliers in
an acquired table. Building from an actual producer retains every leaf report.
Bit/cell reports below are separate from whole-controller tape simulation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1TensorTables
open SemiprimeD1JetAxes (Context)
open SemiprimeSourceCompactBits (Compact)

/-- Concrete canonical data for every assignment to an ordered local port list. -/
inductive Table : ℕ→Type
  | leaf (words : List (List Bool)) : Table 0
  | fork {n : ℕ} (low high : Table n) : Table (n+1)
  deriving Repr

/-- An acquired finite table with its complete retained producer/cell report. -/
structure Acquired (n : ℕ) where
  /-- Entire literal truth table, with no evaluator closure. -/
  table : Table n
  /-- Original producer work and every table allocation. -/
  clock : ℕ

/-- Intrinsic current-context word shape at each actual stored tensor entry. -/
def GoodWords (ctx : Context) (words : List (List Bool)) : Prop :=
  words.length=ctx.rank ∧ ∀w∈words,Compact w ∧ w.length≤ctx.precision

/-- Every stored entry is canonical in the CURRENT context and precision. -/
def Good (ctx : Context) : {n : ℕ}→Table n→Prop
  | _,.leaf words => GoodWords ctx words
  | _,.fork low high => Good ctx low ∧ Good ctx high

/-- Physical read, following actual assignment bits and copying the final vector. -/
def lookup : {n : ℕ}→Table n→List Bool→SemiprimeD1JetRingBits.Run
  | _,.leaf words,_ =>
    let out := SemiprimeD1JetAxes.copyVector words
    ⟨out.1,out.2⟩
  | _,.fork low high,bits =>
    let next := if bits.head?.getD false then lookup high bits.tail else lookup low bits.tail
    ⟨next.words,next.clock+4⟩

/-- Mathematical local tensor value; only the acquired table is inspected. -/
def valueAt : {n : ℕ}→Table n→(Fin n→Bool)→List (List Bool)
  | _,.leaf words,_ => words
  | _,.fork low high,bits => if bits 0 then valueAt high (fun i => bits i.succ) else valueAt low (fun i => bits i.succ)

/-- Lookup recovers the exact local tensor value, rather than a supplied entry answer. -/
theorem lookup_value {n : ℕ} (table : Table n) (bits : List Bool) (hlen : bits.length=n) :
    (lookup table bits).words=valueAt table (fun i => bits[i.val]'(by omega)) := by
  induction table generalizing bits with
  | leaf words => exact SemiprimeD1JetAxes.copyVector_value words
  | @fork n low high ihlow ihhigh =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have ht : bits.length=n := by simpa only [List.length_cons] using Nat.succ.inj hlen
      cases bit
      · simpa only [lookup,valueAt,List.head?_cons,Option.getD_some,Bool.false_eq_true,
          ite_false,List.tail_cons,Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,List.getElem_cons_succ] using ihlow bits ht
      · simpa only [lookup,valueAt,List.head?_cons,Option.getD_some,ite_true,List.tail_cons,
          Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,List.getElem_cons_succ] using ihhigh bits ht

/-- Every reached leaf inherits actual canonical shape, not an output Fits premise. -/
theorem lookup_good (ctx : Context) {n : ℕ} (table : Table n) (ht : Good ctx table) (bits : List Bool) :
    GoodWords ctx (lookup table bits).words := by
  induction table generalizing bits with
  | leaf words => simpa only [lookup,SemiprimeD1JetAxes.copyVector_value,Good] using ht
  | fork low high ihlow ihhigh =>
    change GoodWords ctx (if bits.head?.getD false then lookup high bits.tail else lookup low bits.tail).words
    split_ifs
    · exact ihhigh ht.2 _
    · exact ihlow ht.1 _

/-- Physical entry reads pay every traversed branch and every copied coefficient bit. -/
theorem lookup_clock (ctx : Context) {n : ℕ} (table : Table n) (ht : Good ctx table) (bits : List Bool) :
    (lookup table bits).clock≤ctx.rank*(3*ctx.precision+4)+1+4*n := by
  induction table generalizing bits with
  | leaf words =>
    have h := SemiprimeD1JetAxes.copyVector_clock_le words ctx.precision (fun w hw => (ht.2 w hw).2)
    simpa only [lookup,ht.1,Nat.mul_zero,Nat.add_zero] using h
  | @fork n low high ihlow ihhigh =>
    have hl := ihlow ht.1 bits.tail
    have hh := ihhigh ht.2 bits.tail
    change (if bits.head?.getD false then lookup high bits.tail else lookup low bits.tail).clock+4≤_
    split_ifs <;> omega

/-- Materialize every actual local assignment, caching both children once. -/
def build : (n : ℕ)→(List Bool→SemiprimeD1JetRingBits.Run)→Acquired n
  | 0,producer =>
    let entry := producer []
    ⟨.leaf entry.words,entry.clock+2⟩
  | n+1,producer =>
    let low := build n (fun bits => producer (false::bits))
    let high := build n (fun bits => producer (true::bits))
    ⟨.fork low.table high.table,low.clock+high.clock+5⟩

/-- Every entry of the materialized table is the actual producer result. -/
theorem build_value (n : ℕ) (producer : List Bool→SemiprimeD1JetRingBits.Run)
    (bits : List Bool) (hlen : bits.length=n) :
    (lookup (build n producer).table bits).words=(producer bits).words := by
  induction n generalizing producer bits with
  | zero =>
    have hb : bits=[] := List.eq_nil_of_length_eq_zero hlen
    subst bits
    exact SemiprimeD1JetAxes.copyVector_value _
  | succ n ih =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have ht : bits.length=n := by
        simp only [List.length_cons] at hlen
        omega
      cases bit <;> simp only [build,lookup,List.head?_cons,Option.getD_some,
        Bool.false_eq_true,ite_false,ite_true,List.tail_cons] <;> exact ih _ bits ht

/-- Canonical producer outputs give canonical full tables, from actual assignment shape alone. -/
theorem build_good (ctx : Context) (n : ℕ) (producer : List Bool→SemiprimeD1JetRingBits.Run)
    (hp : ∀bits,bits.length=n→GoodWords ctx (producer bits).words) : Good ctx (build n producer).table := by
  induction n generalizing producer with
  | zero => exact hp [] rfl
  | succ n ih =>
    exact ⟨ih _ (fun bits hb => hp (false::bits) (by simp only [List.length_cons,hb])),
      ih _ (fun bits hb => hp (true::bits) (by simp only [List.length_cons,hb]))⟩

/-- ALL actual producer reports and table cells have the exact eager exponential scale. -/
theorem build_clock (n B : ℕ) (producer : List Bool→SemiprimeD1JetRingBits.Run)
    (hp : ∀bits,bits.length=n→(producer bits).clock≤B) :
    (build n producer).clock+5≤(B+7)*2^n := by
  induction n generalizing producer with
  | zero =>
    have h := hp [] rfl
    change (producer []).clock+2+5≤_
    simpa only [pow_zero,Nat.mul_one] using Nat.add_le_add_right h 7
  | succ n ih =>
    have hl := ih _ (fun bits hb => hp (false::bits) (by simp only [List.length_cons,hb]))
    have hh := ih _ (fun bits hb => hp (true::bits) (by simp only [List.length_cons,hb]))
    change (build n (fun bits => producer (false::bits))).clock+
      (build n (fun bits => producer (true::bits))).clock+5+5≤_
    rw [pow_succ,←Nat.mul_assoc]
    omega

/-- A direct encoding inventory, counting copied bits/cells and each table tag. -/
def storage : {n : ℕ}→Table n→ℕ
  | _,.leaf words => (SemiprimeD1JetAxes.copyVector words).2+1
  | _,.fork low high => storage low+storage high+1

/-- Complete canonical table memory is bounded uniformly over EVERY assignment. -/
theorem storage_bound (ctx : Context) {n : ℕ} (table : Table n) (ht : Good ctx table) :
    storage table+1≤(ctx.rank*(3*ctx.precision+4)+3)*2^n := by
  induction table with
  | leaf words =>
    have h := SemiprimeD1JetAxes.copyVector_clock_le words ctx.precision (fun w hw => (ht.2 w hw).2)
    simpa only [storage,ht.1,pow_zero,Nat.mul_one,Nat.add_assoc] using Nat.add_le_add_right h 2
  | @fork n low high ihlow ihhigh =>
    have hl := ihlow ht.1
    have hh := ihhigh ht.2
    change storage low+storage high+1+1≤_
    rw [pow_succ,←Nat.mul_assoc]
    omega

end RiemannGaussian.SemiprimeD1TensorTables
