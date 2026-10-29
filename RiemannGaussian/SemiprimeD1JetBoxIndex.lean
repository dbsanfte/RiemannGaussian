/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetAlgebra
import RiemannGaussian.SemiprimeD1JetRouting

/-! # Native mixed-radix indices and the actual rectangular exponent box
No exponent table or inverse-index oracle is assumed. New axes are outermost.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetBoxIndex
open SemiprimeD1JetAlgebra (InBox)

/-- Actual finite dimension function of the original axis list. -/
def dims (axes : List ℕ) (i : Fin axes.length) : ℕ := axes[i.val]

/-- Original native mixed-radix coordinate function. -/
def digitFn : (axes : List ℕ)→ℕ→Fin axes.length→ℕ
  | [],_ => Fin.elim0
  | _::qs,i => Fin.cases (i/qs.prod) (fun j => digitFn qs (i%qs.prod) j)

/-- Native radix encoding of a finite exponent function. -/
def encode : (axes : List ℕ)→(Fin axes.length→ℕ)→ℕ
  | [],_ => 0
  | _::qs,e => e 0*qs.prod+encode qs (fun j => e j.succ)

/-- Native finite-function digits are exactly the executed routing's list digits. -/
theorem digitFn_list (axes : List ℕ) (i : ℕ) (j : Fin axes.length) :
    digitFn axes i j=(SemiprimeD1JetRouting.digits axes i).getD j.val 0 := by
  induction axes generalizing i with
  | nil => exact Fin.elim0 j
  | cons q qs ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simpa only [digitFn,Fin.cases_succ,SemiprimeD1JetRouting.digits,
        Fin.val_succ,List.getD_cons_succ] using ih (i%qs.prod) j

/-- Every actual dense index yields bounded exponents in every axis. -/
theorem digitFn_bound (axes : List ℕ) (i : ℕ)
    (hpos : ∀q∈axes,0<q) (hi : i<axes.prod) : ∀j,digitFn axes i j<dims axes j := by
  induction axes generalizing i with
  | nil => intro j;exact Fin.elim0 j
  | cons q qs ih =>
    have ht : ∀x∈qs,0<x := fun x hx=>hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos ht
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change i/qs.prod<q
      exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [List.prod_cons,Nat.mul_comm] using hi)
    · exact ih (i%qs.prod) ht (Nat.mod_lt _ hp) j

/-- Encoding a bounded exponent vector lies inside the actual dense shape. -/
theorem encode_bound (axes : List ℕ) (e : Fin axes.length→ℕ)
    (hpos : ∀q∈axes,0<q) (he : ∀j,e j<dims axes j) : encode axes e<axes.prod := by
  induction axes with
  | nil => simp [encode]
  | cons q qs ih =>
    have ht : ∀x∈qs,0<x := fun x hx=>hpos x (List.mem_cons_of_mem q hx)
    have hef : ∀j,e j.succ<dims qs j := fun j=>he j.succ
    have hb:=ih (fun j=>e j.succ) ht hef
    have hh : e 0<q := he 0
    have hp : 0<qs.prod := List.prod_pos ht
    simp only [encode,List.prod_cons]
    nlinarith

/-- No old coordinate is lost by the native encode/decode round trip. -/
theorem encode_digitFn (axes : List ℕ) (i : ℕ)
    (hpos : ∀q∈axes,0<q) (hi : i<axes.prod) : encode axes (digitFn axes i)=i := by
  induction axes generalizing i with
  | nil => simp only [List.prod_nil] at hi;simp only [encode];omega
  | cons q qs ih =>
    have ht : ∀x∈qs,0<x := fun x hx=>hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos ht
    simp only [encode,digitFn,Fin.cases_zero,Fin.cases_succ]
    rw [ih (i%qs.prod) ht (Nat.mod_lt _ hp)]
    simpa only [Nat.mul_comm] using Nat.div_add_mod i qs.prod

/-- Every actual bounded exponent vector is recovered coordinatewise. -/
theorem digitFn_encode (axes : List ℕ) (e : Fin axes.length→ℕ)
    (hpos : ∀q∈axes,0<q) (he : ∀j,e j<dims axes j) : digitFn axes (encode axes e)=e := by
  induction axes with
  | nil => funext j;exact Fin.elim0 j
  | cons q qs ih =>
    have ht : ∀x∈qs,0<x := fun x hx=>hpos x (List.mem_cons_of_mem q hx)
    have hef : ∀j,e j.succ<dims qs j := fun j=>he j.succ
    have hp : 0<qs.prod := List.prod_pos ht
    have hb:=encode_bound qs (fun j=>e j.succ) ht hef
    have hd : (e 0*qs.prod+encode qs (fun j=>e j.succ))/qs.prod=e 0 := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hb,Nat.zero_add]
    have hm : (e 0*qs.prod+encode qs (fun j=>e j.succ))%qs.prod=encode qs (fun j=>e j.succ) := by
      rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [digitFn,encode,Fin.cases_zero] using hd
    · simp only [digitFn,encode,Fin.cases_succ,hm]
      exact congrFun (ih (fun j=>e j.succ) ht hef) j

/-- Proof-side finite exponent interpretation of the ACTUAL native digit function. -/
noncomputable def exponent (axes : List ℕ) (i : ℕ) : Fin axes.length→₀ℕ :=
  Finsupp.equivFunOnFinite.symm (digitFn axes i)

/-- No hidden exponent lookup controls interpretation. -/
theorem exponent_apply (axes : List ℕ) (i : ℕ) (j : Fin axes.length) :
    exponent axes i j=digitFn axes i j := rfl

/-- The native index exponent is an actual element of the quotient's rectangle. -/
theorem exponent_inBox (axes : List ℕ) (i : ℕ)
    (hpos : ∀q∈axes,0<q) (hi : i<axes.prod) : InBox (dims axes) (exponent axes i) :=
  digitFn_bound axes i hpos hi

/-- Concrete dense-index/box-exponent equivalence, not a cardinality hypothesis. -/
noncomputable def boxEquiv (axes : List ℕ) (hpos : ∀q∈axes,0<q) :
    Fin axes.prod ≃ {e : Fin axes.length→₀ℕ // InBox (dims axes) e} where
  toFun i := ⟨exponent axes i.val,exponent_inBox axes i.val hpos i.isLt⟩
  invFun e := ⟨encode axes e.val,encode_bound axes e.val hpos e.property⟩
  left_inv i := Fin.ext (encode_digitFn axes i.val hpos i.isLt)
  right_inv e := Subtype.ext (by
    ext j
    exact congrFun (digitFn_encode axes e.val hpos e.property) j)

/-- Native routing accepts exactly when the sum of actual quotient exponents
lies in the concrete rectangular ideal's retained box. -/
theorem admissible_iff_inBox_sum (axes : List ℕ) (i j : ℕ)
    (hpos : ∀q∈axes,0<q) (hi : i<axes.prod) (hj : j<axes.prod) :
    SemiprimeD1JetRouting.admissible axes i j ↔
      InBox (dims axes) (exponent axes i+exponent axes j) := by
  change SemiprimeD1JetRouting.admissible axes i j ↔
    ∀k,digitFn axes i k+digitFn axes j k<dims axes k
  induction axes generalizing i j with
  | nil =>
    have hi0 : i=0 := by simpa using hi
    have hj0 : j=0 := by simpa using hj
    simp [SemiprimeD1JetRouting.admissible,hi0,hj0]
  | cons q qs ih =>
    have ht : ∀x∈qs,0<x := fun x hx=>hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos ht
    change SemiprimeD1JetRouting.admissible (q::qs) i j ↔
      ∀k : Fin (qs.length+1),digitFn (q::qs) i k+digitFn (q::qs) j k<dims (q::qs) k
    rw [Fin.forall_fin_succ]
    change (i/qs.prod+j/qs.prod<q ∧ SemiprimeD1JetRouting.admissible qs (i%qs.prod) (j%qs.prod)) ↔
      (i/qs.prod+j/qs.prod<q ∧ ∀k,digitFn qs (i%qs.prod) k+digitFn qs (j%qs.prod) k<dims qs k)
    exact and_congr Iff.rfl (ih _ _ ht (Nat.mod_lt _ hp) (Nat.mod_lt _ hp))

/-- An accepted target exponent is exactly the finite-function exponent sum. -/
theorem exponent_sumIndex (axes : List ℕ) (i j : ℕ)
    (hpos : ∀q∈axes,0<q) (ha : SemiprimeD1JetRouting.admissible axes i j) :
    exponent axes (SemiprimeD1JetRouting.sumIndex axes i j)=exponent axes i+exponent axes j := by
  ext k
  change digitFn axes (SemiprimeD1JetRouting.sumIndex axes i j) k=digitFn axes i k+digitFn axes j k
  induction axes generalizing i j with
  | nil => exact Fin.elim0 k
  | cons q qs ih =>
    have ht : ∀x∈qs,0<x := fun x hx=>hpos x (List.mem_cons_of_mem q hx)
    have hp : 0<qs.prod := List.prod_pos ht
    have hb:=SemiprimeD1JetRouting.sumIndex_lt qs _ _ ht ha.2
    have hd : ((i/qs.prod+j/qs.prod)*qs.prod+SemiprimeD1JetRouting.sumIndex qs (i%qs.prod) (j%qs.prod))/qs.prod=
        i/qs.prod+j/qs.prod := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hb,Nat.zero_add]
    have hm : ((i/qs.prod+j/qs.prod)*qs.prod+SemiprimeD1JetRouting.sumIndex qs (i%qs.prod) (j%qs.prod))%qs.prod=
        SemiprimeD1JetRouting.sumIndex qs (i%qs.prod) (j%qs.prod) := by
      rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa only [digitFn,Fin.cases_zero,SemiprimeD1JetRouting.sumIndex] using hd
    · simp only [digitFn,Fin.cases_succ,SemiprimeD1JetRouting.sumIndex,hm]
      exact ih _ _ ht ha.2 k

end RiemannGaussian.SemiprimeD1JetBoxIndex
