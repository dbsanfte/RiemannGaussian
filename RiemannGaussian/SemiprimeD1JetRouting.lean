/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetScalarBits

/-! # Acquired native mixed-radix routes for truncated multijet multiplication
Only context dimensions and coordinate indices control routes; no coefficient
word is decoded. Native quotient/index operations are a scoped metadata ledger.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetRouting

/-- Actual acquired truncated-product destination and metadata/control report. -/
structure Run where
  /-- None means a nilpotent exponent overflow, not a coefficient test. -/
  value : Option ℕ
  /-- Native index arithmetic, dimension scans and branch control. -/
  clock : ℕ

/-- Outermost-first exponent vector of a native dense coordinate index. -/
def digits : List ℕ→ℕ→List ℕ
  | [],_ => []
  | _q::qs,i => i/qs.prod::digits qs (i%qs.prod)

/-- Independent bounded-exponent predicate for a product of two basis monomials. -/
def admissible : List ℕ→ℕ→ℕ→Prop
  | [],i,j => i=0 ∧ j=0
  | q::qs,i,j => i/qs.prod+j/qs.prod<q ∧ admissible qs (i%qs.prod) (j%qs.prod)

instance admissibleDecidable (axes : List ℕ) (i j : ℕ) : Decidable (admissible axes i j) := by
  induction axes generalizing i j with
  | nil => unfold admissible;infer_instance
  | cons q qs ih => unfold admissible;exact instDecidableAnd

/-- Native radix encoding of the componentwise exponent sum. -/
def sumIndex : List ℕ→ℕ→ℕ→ℕ
  | [],_,_ => 0
  | _q::qs,i,j => (i/qs.prod+j/qs.prod)*qs.prod+sumIndex qs (i%qs.prod) (j%qs.prod)

/-- Execute context-derived routing, discarding only actual exponent overflow. -/
def route : List ℕ→ℕ→ℕ→Run
  | [],i,j => ⟨if i=0 ∧ j=0 then some 0 else none,3⟩
  | q::qs,i,j =>
    let radix:=qs.prod
    let high:=i/radix+j/radix
    if high<q then
      let tail:=route qs (i%radix) (j%radix)
      ⟨tail.value.map (fun k => high*radix+k),tail.clock+qs.length+12⟩
    else ⟨none,qs.length+8⟩

/-- Acquired routing agrees exactly with native exponent compatibility and encoding. -/
theorem route_value (axes : List ℕ) (i j : ℕ) :
    (route axes i j).value=if admissible axes i j then some (sumIndex axes i j) else none := by
  induction axes generalizing i j with
  | nil => rfl
  | cons q qs ih =>
    simp only [route,admissible,sumIndex]
    by_cases hh : i/qs.prod+j/qs.prod<q
    · simp only [hh,ite_true,true_and,ih]
      split_ifs <;> rfl
    · simp only [hh,ite_false,false_and]

/-- All exponent routes have a finite quadratic context-scan ledger. -/
theorem route_clock (axes : List ℕ) (i j : ℕ) :
    (route axes i j).clock≤20*(axes.length+1)^2 := by
  induction axes generalizing i j with
  | nil => simp [route]
  | cons q qs ih =>
    have ht:=ih (i%qs.prod) (j%qs.prod)
    simp only [route,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

/-- Every admitted exponent sum is inside the actual dense target shape. -/
theorem sumIndex_lt (axes : List ℕ) (i j : ℕ)
    (hpos : ∀q∈axes,0<q) (ha : admissible axes i j) : sumIndex axes i j<axes.prod := by
  induction axes generalizing i j with
  | nil => simp [sumIndex]
  | cons q qs ih =>
    have hq:=hpos q List.mem_cons_self
    have htail : ∀x∈qs,0<x := fun x hx => hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos htail
    have ht:=ih _ _ htail ha.2
    have hh:=ha.1
    simp only [sumIndex,List.prod_cons]
    nlinarith

/-- Accepted routes preserve the exact sum of ALL old/new exponent coordinates. -/
theorem digits_sumIndex (axes : List ℕ) (i j : ℕ)
    (hpos : ∀q∈axes,0<q) (ha : admissible axes i j) :
    digits axes (sumIndex axes i j)=List.zipWith (·+·) (digits axes i) (digits axes j) := by
  induction axes generalizing i j with
  | nil => rfl
  | cons q qs ih =>
    have htail : ∀x∈qs,0<x := fun x hx => hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos htail
    have ht:=sumIndex_lt qs _ _ htail ha.2
    simp only [digits,sumIndex,List.zipWith_cons_cons]
    have hd : ((i/qs.prod+j/qs.prod)*qs.prod+sumIndex qs (i%qs.prod) (j%qs.prod))/qs.prod=
        i/qs.prod+j/qs.prod := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt ht,Nat.zero_add]
    have hm : ((i/qs.prod+j/qs.prod)*qs.prod+sumIndex qs (i%qs.prod) (j%qs.prod))%qs.prod=
        sumIndex qs (i%qs.prod) (j%qs.prod) := by
      rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt ht]
    rw [hd,hm]
    exact congrArg (List.cons (i/qs.prod+j/qs.prod)) (ih _ _ htail ha.2)

/-- Independent componentwise exponent bound for a dense monomial. -/
def fits : List ℕ→List ℕ→Prop
  | [],[] => True
  | q::qs,e::es => e<q ∧ fits qs es
  | _,_ => False

/-- For actual in-range inputs, routing accepts EXACTLY the componentwise
nilpotent exponent bounds, so no legitimate monomial is silently discarded. -/
theorem admissible_iff_fits (axes : List ℕ) (i j : ℕ)
    (hpos : ∀q∈axes,0<q) (hi : i<axes.prod) (hj : j<axes.prod) :
    admissible axes i j ↔ fits axes (List.zipWith (·+·) (digits axes i) (digits axes j)) := by
  induction axes generalizing i j with
  | nil =>
    have hi0 : i=0 := by simpa using hi
    have hj0 : j=0 := by simpa using hj
    simp [admissible,digits,fits,hi0,hj0]
  | cons q qs ih =>
    have htail : ∀x∈qs,0<x := fun x hx => hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos htail
    simp only [admissible,digits,List.zipWith_cons_cons,fits]
    exact and_congr Iff.rfl (ih _ _ htail (Nat.mod_lt _ hp) (Nat.mod_lt _ hp))

end RiemannGaussian.SemiprimeD1JetRouting
