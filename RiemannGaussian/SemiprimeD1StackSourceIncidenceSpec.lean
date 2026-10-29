/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceIncidenceCountFormula
import RiemannGaussian.SemiprimeSourceHistogramPrefix
import RiemannGaussian.SemiprimeBitArithmetic

/-! # Proof interpretation of the literal incidence-only classifier
Words, lists and numeric reads here specify the physical program. They are not
operands, callbacks, flags or instructions of that program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSpec
open SemiprimeBitArithmetic (bitValue addBits)
/-- Three fixed classifier outcomes, carried solely by finite instruction labels. -/
inductive Status where
  | reject | stable | free
  deriving DecidableEq,Repr
instance :Fintype Status :=Fintype.ofList [.reject,.stable,.free] (by intro k;cases k <;> simp)
/-- The exact physical normalized ID returned by the acquired prefix dictionary. -/
def readID (ids:List (List Bool)) (key:List Bool) :List Bool :=
  SemiprimeSourceHistogramPrefix.expected ids (bitValue key)
/-- Byte-read specification of one endpoint equality. Presence is separate from ID zero. -/
def edge (ids:List (List Bool)) (left right:List Bool) :Status :=
  if bitValue left=bitValue right then .stable
  else if ids.length ≤ bitValue left ∨ ids.length ≤ bitValue right then .free
  else if bitValue (readID ids left)=bitValue (readID ids right) then .stable else .reject
/-- Literal selection among three actual retained binary payloads, or the empty zero word. -/
def payload (square cube fourth:List Bool) :Status→Status→List Bool
  | .reject,_|_,.reject=>[]
  | .free,.free=>square
  | .free,.stable|.stable,.free=>cube
  | .stable,.stable=>fourth
/-- Mathematical possible projection of the three physically computed outcomes. -/
def possible :Status→Bool | .reject=>false | .stable|.free=>true
/-- Mathematical free-degree projection; a loop never consumes a free degree. -/
def drop :Status→Bool | .free=>true | .reject|.stable=>false
/-- Under the actual valid-key/prefix-range invariant, absence means precisely a free endpoint. -/
theorem free_range (k N i:Nat) (hk:k ≤ N) (hi:i < N) :
    i∈List.range' k (N-k) ↔ k ≤ i :=by
  constructor
  · intro h
    have h0:=List.mem_range'.mp h
    omega
  · intro h
    apply List.mem_range'.mpr
    exact ⟨i-k,by omega,by omega⟩
/-- The three physical outcome branches are the exact separated-edge predicates.
The environment below is solely the proof interpretation of already acquired prefix bytes. -/
theorem edge_predicates (ids:List (List Bool)) (left right:List Bool) (N:Nat)
    (hk:ids.length ≤ N) (hl:bitValue left < N) (hr:bitValue right < N) :
    possible (edge ids left right)=decide (SemiprimeSourceIncidenceCountFormula.pairOK
      (List.range' ids.length (N-ids.length))
      (fun i=>bitValue (SemiprimeSourceHistogramPrefix.expected ids i)) (bitValue left) (bitValue right)) ∧
    drop (edge ids left right)=decide (SemiprimeSourceIncidenceCountFormula.pairActive
      (List.range' ids.length (N-ids.length)) (bitValue left) (bitValue right)) :=by
  have ha:=free_range ids.length N (bitValue left) hk hl
  have hb:=free_range ids.length N (bitValue right) hk hr
  by_cases h:bitValue left=bitValue right
  · simp [edge,h,possible,drop,SemiprimeSourceIncidenceCountFormula.pairOK,
      SemiprimeSourceIncidenceCountFormula.pairActive]
  · by_cases hf:ids.length ≤ bitValue left ∨ ids.length ≤ bitValue right
    · simp [edge,h,hf,possible,drop,SemiprimeSourceIncidenceCountFormula.pairOK,
        SemiprimeSourceIncidenceCountFormula.pairActive,ha,hb]
      exact hf.elim Or.inl (fun h=>Or.inr (Or.inl h))
    · have hl0:¬ids.length ≤ bitValue left:=fun h=>hf (Or.inl h)
      have hr0:¬ids.length ≤ bitValue right:=fun h=>hf (Or.inr h)
      by_cases hv:bitValue (readID ids left)=bitValue (readID ids right)
      · simp only [readID] at hv
        simp [edge,h,possible,drop,SemiprimeSourceIncidenceCountFormula.pairOK,
          SemiprimeSourceIncidenceCountFormula.pairActive,ha,hb,hl0,hr0,readID,hv]
      · simp only [readID] at hv
        simp [edge,h,possible,drop,SemiprimeSourceIncidenceCountFormula.pairOK,
          SemiprimeSourceIncidenceCountFormula.pairActive,ha,hb,hl0,hr0,readID,hv]
/-- Only the actual copied cached power bytes determine a term's integer value. -/
theorem payload_value (L:Nat) (square cube fourth:List Bool)
    (hs:bitValue square=L^2) (hc:bitValue cube=L^3) (hf:bitValue fourth=L^4)
    (a b:Status) :bitValue (payload square cube fourth a b)=
      if possible a && possible b then
        if drop a && drop b then L^2 else if drop a || drop b then L^3 else L^4 else 0 :=by
  cases a <;> cases b <;> simp only [payload,possible,drop,Bool.and_false,Bool.and_true,Bool.or_false,Bool.or_true,
    Bool.false_eq_true,ite_false,ite_true,bitValue,hs,hc,hf]
/-- Actual two-edge term for two physically parsed owner/factor descriptors. -/
def term (ids:List (List Bool)) (square cube fourth:List Bool)
    (left right:List Bool×List Bool) :List Bool :=
  payload square cube fourth (edge ids left.1 right.1) (edge ids left.2 right.2)
/-- Both physically computed edge branches select the exact separated incidence count lane. -/
theorem term_formula (ids:List (List Bool)) (L N:Nat) (square cube fourth:List Bool)
    (hs:bitValue square=L^2) (hc:bitValue cube=L^3) (hf:bitValue fourth=L^4)
    (left right:List Bool×List Bool) (hk:ids.length ≤ N)
    (hl:bitValue left.1 < N ∧ bitValue left.2 < N)
    (hr:bitValue right.1 < N ∧ bitValue right.2 < N) :
    bitValue (term ids square cube fourth left right)=
      SemiprimeSourceIncidenceCountFormula.classifiedCount L (List.range' ids.length (N-ids.length))
        (fun i=>bitValue (SemiprimeSourceHistogramPrefix.expected ids i))
        (bitValue left.1) (bitValue left.2) (bitValue right.1) (bitValue right.2) :=by
  have h0:=edge_predicates ids left.1 right.1 N hk hl.1 hr.1
  have h1:=edge_predicates ids left.2 right.2 N hk hl.2 hr.2
  rw [term,payload_value L square cube fourth hs hc hf,h0.1,h0.2,h1.1,h1.2]
  simp only [SemiprimeSourceIncidenceCountFormula.classifiedCount,
    Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
/-- Complete ordered inner scan, retaining every duplicate incidence and its order. -/
def inner (ids:List (List Bool)) (square cube fourth:List Bool)
    (left:List Bool×List Bool) (right:List (List Bool×List Bool)) (acc:List Bool) :List Bool :=
  right.foldl (fun sum row=>(addBits sum (term ids square cube fourth left row) false).bits) acc
/-- Complete factor-major/local-slot outer scan of the same actual descriptor stream. -/
def total (ids:List (List Bool)) (square cube fourth:List Bool)
    (rows:List (List Bool×List Bool)) :List Bool :=
  rows.foldl (fun sum row=>inner ids square cube fourth row rows sum) []
/-- Actual binary addition computes the ordered inner integer sum, including every repeated row. -/
theorem inner_value (ids:List (List Bool)) (square cube fourth:List Bool)
    (left:List Bool×List Bool) (rows:List (List Bool×List Bool)) (acc:List Bool) :
    bitValue (inner ids square cube fourth left rows acc)=
      bitValue acc+(rows.map (fun right=>bitValue (term ids square cube fourth left right))).sum :=by
  induction rows generalizing acc with
  | nil=>simp only [inner,List.foldl_nil,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons row rows ih=>
    change bitValue (inner ids square cube fourth left rows
      (addBits acc (term ids square cube fourth left row) false).bits)=_
    rw [ih,SemiprimeBitArithmetic.addBits_correct]
    simp only [SemiprimeBitArithmetic.bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,
      List.map_cons,List.sum_cons,Nat.add_assoc]
/-- Complete exact M² incidence sum; this is not a permutation or distinct-pair approximation. -/
theorem total_value (ids:List (List Bool)) (square cube fourth:List Bool)
    (rows:List (List Bool×List Bool)) :
    bitValue (total ids square cube fourth rows)=
      (rows.map (fun left=>(rows.map (fun right=>bitValue (term ids square cube fourth left right))).sum)).sum :=by
  have h:∀(todo:List (List Bool×List Bool)) (acc:List Bool),
      bitValue (todo.foldl (fun sum row=>inner ids square cube fourth row rows sum) acc)=
        bitValue acc+(todo.map (fun left=>(rows.map (fun right=>bitValue (term ids square cube fourth left right))).sum)).sum:=by
    intro todo
    induction todo with
    | nil=>intro acc;simp only [List.foldl_nil,List.map_nil,List.sum_nil,Nat.add_zero]
    | cons row todo ih=>
      intro acc
      rw [List.foldl_cons,ih,inner_value]
      simp only [List.map_cons,List.sum_cons,Nat.add_assoc]
  simpa only [total,bitValue,Nat.zero_add] using h rows []
/-- The branch never obtains a larger physical term than one actually retained power word. -/
theorem payload_length (square cube fourth:List Bool) (a b:Status) :
    (payload square cube fourth a b).length ≤ square.length+cube.length+fourth.length :=by
  cases a <;> cases b <;> simp only [payload,List.length_nil] <;> omega
/-- Each physical ripple addition grows by at most its actual term width plus one. -/
theorem add_length (left right:List Bool) :
    (addBits left right false).bits.length ≤ left.length+right.length+1 :=by
  have h:=(SemiprimeBitArithmetic.addBits_counts left right false).2.2.2.2
  have hm:max left.length right.length ≤ left.length+right.length:=max_le (by omega) (by omega)
  omega
/-- All inner accumulator bytes have a direct bound in actual input word widths and scanned rows. -/
theorem inner_length (ids:List (List Bool)) (square cube fourth:List Bool)
    (left:List Bool×List Bool) (right:List (List Bool×List Bool)) (acc:List Bool) :
    (inner ids square cube fourth left right acc).length ≤
      acc.length+right.length*(square.length+cube.length+fourth.length+1) :=by
  induction right generalizing acc with
  | nil=>simpa only [inner,List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero] using (Nat.le_refl acc.length)
  | cons row rows ih=>
    have h0:=add_length acc (term ids square cube fourth left row)
    have h1:=payload_length square cube fourth (edge ids left.1 row.1) (edge ids left.2 row.2)
    have h2:=ih (addBits acc (term ids square cube fourth left row) false).bits
    change (inner ids square cube fourth left rows (addBits acc (term ids square cube fourth left row) false).bits).length ≤ _
    change (term ids square cube fourth left row).length ≤ _ at h1
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- All ordered M² terms remain counted, with no truth matrix or score oracle. -/
theorem total_length (ids:List (List Bool)) (square cube fourth:List Bool)
    (rows:List (List Bool×List Bool)) :
    (total ids square cube fourth rows).length ≤
      rows.length*rows.length*(square.length+cube.length+fourth.length+1) :=by
  have h:∀(todo:List (List Bool×List Bool)) (acc:List Bool),(todo.foldl (fun sum row=>inner ids square cube fourth row rows sum) acc).length ≤
      acc.length+todo.length*rows.length*(square.length+cube.length+fourth.length+1):=by
    intro todo
    induction todo with
    | nil=>intro acc;simpa only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero] using (Nat.le_refl acc.length)
    | cons row todo ih=>
      intro acc
      have h0:=inner_length ids square cube fourth row rows acc
      have h1:=ih (inner ids square cube fourth row rows acc)
      simp only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa only [total,List.length_nil,Nat.zero_add] using h rows []
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSpec
