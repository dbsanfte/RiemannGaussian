/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTernaryPublicFactor
import OAI.Algorithms.SubexponentialSAT.GlobalPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel

/-! # Original-OAI Boolean factor-system and exact ring-count bridge
This leaf deliberately imports the pinned original OAI branch, never the vendor
layout branch. Replacement rows are explicit premises, not acquired data.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace RiemannGaussian.SemiprimeBooleanRingFactor
open scoped BigOperators
open SemiprimeTernaryPublicFactor SemiprimeSubdividedEntry SemiprimeMacroGraph
open OAI.Algorithms.SubexponentialSAT

/-- Actual original variables occurring at the ordered ports of a public factor. -/
def scope (N : ℕ) (hN : 0<N) (e : Factors N hN) : Finset (Variables N hN) :=
  Finset.univ.image (coordinate N hN e)

/-- The original paid Boolean checker, on its genuine scope subtype. -/
def system (N : ℕ) (hN : 0<N) : Factor.System (Variables N hN) (Factors N hN) Bool where
  scope := scope N hN
  table e a := (publicSubdividedEntry N hN e (fun i =>
    a ⟨coordinate N hN e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)).accepted

/-- The subtype table reconstructs exactly the original ordered entry. -/
theorem evalFactor_eq (N : ℕ) (hN : 0<N) (e : Factors N hN) (x : Variables N hN → Bool) :
    Factor.evalFactor (system N hN) e x=
      (publicSubdividedEntry N hN e (fun i => x (coordinate N hN e i))).accepted := rfl

/-- Genuine scopes have at most the original number of ordered ports. -/
theorem scope_card_le (N : ℕ) (hN : 0<N) (e : Factors N hN) :
    ((system N hN).scope e).card ≤ subdividedArity e := by
  exact (Finset.card_image_le).trans_eq (by simp)

/-- Original incidence two also bounds the number of distinct incident factors. -/
theorem incidence_le_two (N : ℕ) (hN : 0<N) (a : Variables N hN) :
    (Finset.univ.filter (fun e => a∈(system N hN).scope e)).card ≤ 2 := by
  classical
  have hp := occurrence_two N hN a
  have hh : ∀ e : Factors N hN,
      (if a∈(system N hN).scope e then (1 : ℕ) else 0) ≤
      ∑ i : Fin (subdividedArity e), if coordinate N hN e i=a then (1 : ℕ) else 0 := by
    intro e
    split_ifs with h
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      calc
        1 = (if coordinate N hN e i=a then (1 : ℕ) else 0) := by simp [hi]
        _ ≤ ∑ k : Fin (subdividedArity e), if coordinate N hN e k=a then 1 else 0 :=
          Finset.single_le_sum (f := fun k : Fin (subdividedArity e) =>
            if coordinate N hN e k=a then (1 : ℕ) else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    · exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun e (_ : e∈Finset.univ) => hh e)
  rw [hp] at hs
  simpa only [Finset.sum_boole,Nat.cast_id] using hs

/-- Exact original public factor count, not a supplied global correctness promise. -/
theorem count_eq_factors (N : ℕ) (hN : 0<N) :
    Factor.count (system N hN)=Fintype.card (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  change (∑ x : Variables N hN → Bool, ∏ e : Factors N hN,
    if Factor.evalFactor (system N hN) e x=true then (1 : ℕ) else 0)=_
  simp_rw [evalFactor_eq]
  exact SemiprimeTernaryFactor.boolean_count_tensor _ _ _ |>.symm.trans (boolean_factor_count N hN)

/-- Literal Boolean embedding in any coefficient ring. -/
def liftBool {C : Type*} [CommRing C] : Bool → C | false => 0 | true => 1

/-- Boolean interpolation requires only unit differences 1 and -1. -/
theorem liftBool_units {C : Type*} [CommRing C] :
    TableInterpolation.UnitDifferences (liftBool (C:=C)) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [liftBool]

/-- Restoring polynomial rows recover the true integer factor count in every commutative ring. -/
theorem restoring_rows_count {C : Type*} [CommRing C] (N : ℕ) (hN : 0<N)
    (row : (e : Factors N hN) → {v // v∈(system N hN).scope e} →
      Variables N hN → Polynomial C)
    (hrow : ∀ e v w, (row e v w).eval 0=if w=v.1 then 1 else 0) :
    (GlobalPolynomial.interpolatedGlobalPolynomial (system N hN) liftBool liftBool_units row).eval 0=
      (Fintype.card (SemiprimePublicFactorCount.OrdinaryFactors N) : C) := by
  rw [GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial _ _ _ _ hrow,count_eq_factors]

/-- Count capacity follows from the actual Boolean variable space. -/
theorem count_capacity (N : ℕ) (hN : 0<N) :
    Factor.count (system N hN)<3^(Fintype.card (Variables N hN)+1) := by
  have hc := Factor.count_le_pow (system N hN)
  simp only [Fintype.card_bool] at hc
  have hp : 2^Fintype.card (Variables N hN) ≤ 3^Fintype.card (Variables N hN) :=
    Nat.pow_le_pow_left (by decide) _
  have hpos : 0<3^Fintype.card (Variables N hN) := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

/-- The supplied irreducible ring model decodes the restoring-row answer exactly. -/
theorem decode_restoring_rows {d : ℕ} (model : SqrtLog.RingModel.Data d) (hd : d≠0)
    (N : ℕ) (hN : 0<N) (t : ℕ) (ht : t=Fintype.card (Variables N hN)+1)
    (row : (e : Factors N hN) → {v // v∈(system N hN).scope e} → Variables N hN →
      Polynomial (model.O t))
    (hrow : ∀ e v w, (row e v w).eval 0=if w=v.1 then 1 else 0) :
    model.decodeCount t (by omega) ((GlobalPolynomial.interpolatedGlobalPolynomial
      (system N hN) liftBool liftBool_units row).eval 0)=
      Fintype.card (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial _ _ _ _ hrow]
  have hc : Factor.count (system N hN)<3^t := by rw [ht]; exact count_capacity N hN
  rw [model.decodeCount_natCast t (by omega) hd _ hc]
  exact count_eq_factors N hN

end RiemannGaussian.SemiprimeBooleanRingFactor
