/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRouting
import RiemannGaussian.SemiprimeD1StackUnaryDivmod
import Mathlib.Tactic.Linarith

/-! # Original mixed-radix routing specification for physical metadata loops
These lemmas remove weighted output reconstruction and derive actual suffix
counter bounds from original positive axes. They are not a second evaluator.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackRouteArithmetic
open SemiprimeD1JetRouting (admissible sumIndex route)

/-- On an admitted product the original dense destination is the ordinary sum.
No positivity or independently supplied sum-index answer is needed. -/
theorem sumIndex_eq_add (axes : List ℕ) (i j : ℕ) (ha : admissible axes i j) :
    sumIndex axes i j=i+j := by
  induction axes generalizing i j with
  | nil =>
    change i=0 ∧ j=0 at ha
    simp [sumIndex,ha.1,ha.2]
  | cons q qs ih =>
    change i/qs.prod+j/qs.prod<q ∧ admissible qs (i%qs.prod) (j%qs.prod) at ha
    simp only [sumIndex,ih _ _ ha.2]
    have hi := Nat.div_add_mod i qs.prod
    have hj := Nat.div_add_mod j qs.prod
    nlinarith

/-- The frozen original route is represented by compatibility plus physical unary addition. -/
theorem route_eq_add (axes : List ℕ) (i j : ℕ) :
    (route axes i j).value=if admissible axes i j then some (i+j) else none := by
  rw [SemiprimeD1JetRouting.route_value]
  by_cases ha : admissible axes i j
  · simp [ha,sumIndex_eq_add axes i j ha]
  · simp [ha]

/-- Exact original suffix records to be acquired physically, outermost first. -/
def records : List ℕ → List (ℕ×ℕ)
  | [] => []
  | q::qs => (q,qs.prod)::records qs

/-- Compatibility of the actual suffix records, as a proof specification only. -/
def compatible : List (ℕ×ℕ) → ℕ → ℕ → Bool
  | [],i,j => decide (i=0 ∧ j=0)
  | (q,d)::rest,i,j => decide (i/d+j/d<q) && compatible rest (i%d) (j%d)

/-- Original record traversal agrees with the original route predicate on ALL prefixes. -/
theorem compatible_records (axes : List ℕ) (i j : ℕ) :
    compatible (records axes) i j=decide (admissible axes i j) := by
  induction axes generalizing i j with
  | nil => rfl
  | cons q qs ih =>
    simp only [records,compatible,ih]
    by_cases hh : i/qs.prod+j/qs.prod<q <;>
      by_cases ht : admissible qs (i%qs.prod) (j%qs.prod) <;> simp [admissible,hh,ht]

/-- Positivity of the actual rank comes solely from original axes. -/
theorem rank_pos (axes : List ℕ) (hp : ∀q∈axes,0<q) : 0<axes.prod := List.prod_pos hp

/-- Every actually required divisor/axis counter is original-positive and rank-bounded. -/
theorem record_bounds (axes : List ℕ) (hp : ∀q∈axes,0<q)
    (q d : ℕ) (h : (q,d)∈records axes) :
    0<q ∧ 0<d ∧ q≤axes.prod ∧ d≤axes.prod ∧ q*d≤axes.prod := by
  induction axes with
  | nil => simp [records] at h
  | cons x xs ih =>
    have hx := hp x (by simp)
    have ht : ∀q∈xs,0<q := fun q hq => hp q (by simp [hq])
    have hr := rank_pos xs ht
    simp only [records,List.mem_cons] at h
    simp only [List.prod_cons]
    rcases h with he|he
    · cases he
      exact ⟨hx,hr,by nlinarith,by nlinarith,le_rfl⟩
    · obtain ⟨hq,hd,hqr,hdr,hpqd⟩ := ih ht he
      exact ⟨hq,hd,by nlinarith,by nlinarith,by nlinarith⟩

/-- Original context wrapper, without a supplied suffix/route/height premise. -/
theorem context_record_bounds (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (q d : ℕ) (h : (q,d)∈records ctx.axes) :
    0<q ∧ 0<d ∧ q≤ctx.rank ∧ d≤ctx.rank ∧ q*d≤ctx.rank :=
  record_bounds ctx.axes hp q d h

end RiemannGaussian.SemiprimeD1StackRouteArithmetic
