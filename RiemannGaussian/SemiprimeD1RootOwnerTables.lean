/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTables
import RiemannGaussian.SemiprimeD1JetPolynomialBits
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Actual owner-copy tables, including isolated variables
Each table sums the two allowed Boolean values. Empty degree therefore retains
multiplicity two when unfixed, rather than replacing it by an all-equal Boolean.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1RootOwnerTables
open SemiprimeBitArithmetic SemiprimeD1JetAxes SemiprimeMacroEntryBitPrimitives
open SemiprimeD1TensorTables

/-- Original semiprime root coefficients modulo four, with no nilpotent axes. -/
def rootContext : Context:=⟨[],2⟩

/-- Actual Boolean equality circuit. -/
def equalBit (x y : Bool) : Bool:=!(Bool.xor x y)

/-- Physical equality is exact for the two literal Boolean values. -/
theorem equalBit_correct (x y : Bool) : equalBit x y=decide (x=y) := by
  cases x <;> cases y <;> rfl

/-- Scan every current prefix record, retaining duplicates and conflicting records. -/
def prefixRun {n : ℕ} (v : Fin n) (b : Bool) : List (Fin n×Bool)→CheckRun
  | [] => ⟨true,1⟩
  | x::xs =>
    let tail:=prefixRun v b xs
    let allowed:=if x.1=v then equalBit x.2 b else true
    ⟨allowed&&tail.accepted,tail.clock+8⟩

/-- Literal current-prefix compatibility, without an allowed-value answer input. -/
def allowed {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (b : Bool) : Bool:=
  fixed.all (fun x=>decide (x.1≠v ∨ x.2=b))

/-- The actual prefix scan computes precisely all original records. -/
theorem prefixRun_value {n : ℕ} (v : Fin n) (b : Bool) (fixed : List (Fin n×Bool)) :
    (prefixRun v b fixed).accepted=allowed fixed v b := by
  induction fixed with
  | nil => rfl
  | cons x xs ih =>
    simp only [prefixRun,allowed,List.all_cons,ih,equalBit_correct]
    by_cases h : x.1=v <;> simp [h]

/-- Every actual prefix record, equality and Boolean conjunction is paid. -/
theorem prefixRun_clock {n : ℕ} (v : Fin n) (b : Bool) (fixed : List (Fin n×Bool)) :
    (prefixRun v b fixed).clock=8*fixed.length+1 := by
  induction fixed with
  | nil => rfl
  | cons x xs ih => simp only [prefixRun,List.length_cons,ih];omega

/-- Scan every actual incident-copy bit for one proposed variable value. -/
def sameRun (b : Bool) : List Bool→CheckRun
  | [] => ⟨true,1⟩
  | x::xs => let tail:=sameRun b xs;⟨equalBit x b&&tail.accepted,tail.clock+5⟩

/-- Every incident copy must be exactly the proposed Boolean value. -/
theorem sameRun_value (b : Bool) (bits : List Bool) :
    (sameRun b bits).accepted=bits.all (fun x=>decide (x=b)) := by
  induction bits with
  | nil => rfl
  | cons x xs ih => simp only [sameRun,List.all_cons,ih,equalBit_correct]

/-- All actual owner-copy reads and equality circuits are retained. -/
theorem sameRun_clock (b : Bool) (bits : List Bool) :
    (sameRun b bits).clock=5*bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons x xs ih => simp only [sameRun,List.length_cons,ih];omega

/-- Actual root owner tensor entry: sum both allowed constant-copy assignments physically. -/
def producer {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (bits : List Bool) :
    SemiprimeD1JetRingBits.Run :=
  let p0:=prefixRun v false fixed
  let p1:=prefixRun v true fixed
  let s0:=sameRun false bits
  let s1:=sameRun true bits
  let low:=p0.accepted&&s0.accepted
  let high:=p1.accepted&&s1.accepted
  let out:=SemiprimeD1JetScalarBits.add 2 [low] [high]
  ⟨[out.bits],p0.clock+p1.clock+s0.clock+s1.clock+out.clock+12⟩

/-- Exact original sum over the two possible owner-variable values. -/
def weight {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (bits : List Bool) : ℕ:=
  bitNat (allowed fixed v false&&bits.all (fun x=>decide (x=false)))+
  bitNat (allowed fixed v true&&bits.all (fun x=>decide (x=true)))

/-- The physical owner entry is the original two-value sum modulo four. -/
theorem producer_value {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (bits : List Bool) :
    SemiprimeD1JetRingBits.coefficient rootContext (producer fixed v bits).words 0=
      (weight fixed v bits:ZMod 4) := by
  change (bitValue (SemiprimeD1JetScalarBits.add 2
    [(prefixRun v false fixed).accepted&&(sameRun false bits).accepted]
    [(prefixRun v true fixed).accepted&&(sameRun true bits).accepted]).bits:ZMod 4)=_
  rw [SemiprimeD1JetScalarBits.add_zmod,prefixRun_value,prefixRun_value,sameRun_value,sameRun_value]
  simp only [bitValue,Nat.mul_zero,Nat.add_zero,weight,Nat.cast_add]

/-- Every actual owner table entry is canonical at the root precision, without Fits advice. -/
theorem producer_good {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (bits : List Bool) :
    GoodWords rootContext (producer fixed v bits).words := by
  refine ⟨rfl,?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl|h
  · exact ⟨SemiprimeD1JetScalarBits.add_compact _ _ _,SemiprimeD1JetScalarBits.add_length _ _ _⟩
  · cases h

/-- Actual prefix and all-copy scans have linear report, with the physical adder paid. -/
theorem producer_clock {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (bits : List Bool) :
    (producer fixed v bits).clock ≤ 16*fixed.length+10*bits.length+60 := by
  have hp0:=prefixRun_clock v false fixed
  have hp1:=prefixRun_clock v true fixed
  have hs0:=sameRun_clock false bits
  have hs1:=sameRun_clock true bits
  have ha:=SemiprimeD1JetScalarBits.add_clock 2
    [(prefixRun v false fixed).accepted&&(sameRun false bits).accepted]
    [(prefixRun v true fixed).accepted&&(sameRun true bits).accepted]
  simp only [List.length_cons,List.length_nil,max_self] at ha
  change (prefixRun v false fixed).clock+(prefixRun v true fixed).clock+
    (sameRun false bits).clock+(sameRun true bits).clock+
    (SemiprimeD1JetScalarBits.add 2
      [(prefixRun v false fixed).accepted&&(sameRun false bits).accepted]
      [(prefixRun v true fixed).accepted&&(sameRun true bits).accepted]).clock+12 ≤ _
  omega

/-- Materialize every owner-copy assignment from actual fixed records. -/
def acquire {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (degree : ℕ) : Acquired degree :=
  build degree (producer fixed v)

/-- Every materialized owner entry is exactly the real producer, not a verdict oracle. -/
theorem acquire_value {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (degree : ℕ)
    (bits : List Bool) (hb : bits.length=degree) :
    (lookup (acquire fixed v degree).table bits).words=(producer fixed v bits).words :=
  build_value degree (producer fixed v) bits hb

/-- All eager owner tables satisfy the intrinsic root context invariant. -/
theorem acquire_good {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (degree : ℕ) :
    Good rootContext (acquire fixed v degree).table :=
  build_good rootContext degree (producer fixed v) (fun bits _=>producer_good fixed v bits)

/-- Every original owner assignment and producer callback is paid at the eager scope rate. -/
theorem acquire_clock {n : ℕ} (fixed : List (Fin n×Bool)) (v : Fin n) (degree : ℕ) :
    (acquire fixed v degree).clock+5 ≤ (16*fixed.length+10*degree+67)*2^degree :=
  build_clock degree (16*fixed.length+10*degree+60) (producer fixed v)
    (fun bits hb=>by simpa only [hb] using producer_clock fixed v bits)

/-- Isolated unfixed variables contribute TWO, as the original variable sum requires. -/
theorem empty_unfixed {n : ℕ} (v : Fin n) : weight [] v []=2 := by
  norm_num [weight,allowed,bitNat]

/-- An isolated fixed variable contributes one, rather than disappearing. -/
theorem empty_fixed {n : ℕ} (v : Fin n) (b : Bool) : weight [(v,b)] v []=1 := by
  cases b <;> norm_num [weight,allowed,bitNat]

end RiemannGaussian.SemiprimeD1RootOwnerTables
