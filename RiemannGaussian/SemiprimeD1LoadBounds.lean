/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CollisionVariance

/-! # Exact finite-family variance and maximum-load bounds
Every load is the literal occurrence multiplicity. No histogram/mass answer
is an input to the original-list corollary.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1LoadBounds
open scoped BigOperators
open SemiprimeSourceHistogramGrouping

/-- Literal rational load of one label. -/
def load {I K : Type*} [DecidableEq K] (xs : List I) (key : I→K) (k : K) : ℚ :=
  multiplicity key xs k

/-- Every actual list occurrence contributes exactly once to the complete family. -/
theorem total_load {I K : Type*} [Fintype K] [DecidableEq K]
    (xs : List I) (key : I→K) : ∑ k,load xs key k=(xs.length:ℚ) := by
  induction xs with
  | nil => simp [load,SemiprimeSourceHistogramGrouping.multiplicity]
  | cons i xs ih =>
    simp only [load,SemiprimeSourceHistogramGrouping.multiplicity,List.countP_cons,Nat.cast_add] at *
    simp_rw [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [Finset.sum_add_distrib,ih]
    simp

/-- Collision mass of the literal label loads. -/
def collision {I K : Type*} [Fintype K] [DecidableEq K]
    (xs : List I) (key : I→K) : ℚ := ∑ k,(load xs key k)^2

/-- Complete-family grouping includes every absent label with load zero. -/
theorem collision_pairs {I K : Type*} [Fintype K] [DecidableEq K]
    (xs : List I) (key : I→K) :
    collision xs key=pairs xs (fun i j => if key i=key j then (1:ℚ) else 0) := by
  have h := weighted_pair_grouping key xs (fun _ => (1:ℚ))
  have hb (k : K) : bucket key xs (fun _ => (1:ℚ)) k=load xs key k := by
    have hi:=indicator_sum key xs k
    unfold bucket load
    dsimp only
    have hc := congrArg (fun z : ℕ => (z:ℚ)) hi
    push_cast at hc
    simpa only [List.map_map,Function.comp_def,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using hc
  change pairs xs (fun i j => if key i=key j then (1:ℚ)*(1:ℚ) else 0)=_ at h
  simp only [mul_one,hb] at h
  rw [h]
  unfold collision
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hz : load xs key k=0 := by
    unfold load SemiprimeSourceHistogramGrouping.multiplicity
    apply Nat.cast_eq_zero.mpr
    apply List.countP_eq_zero.mpr
    intro i hi he
    exact hk (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,of_decide_eq_true he⟩))
  simp only [hz,zero_pow (by decide : 2≠0)]

/-- The finite scaled-variance identity uses only the actual total mass. -/
theorem scaled_variance {I K : Type*} [Fintype K] [DecidableEq K]
    (xs : List I) (key : I→K) :
    (∑ k,((Fintype.card K:ℚ)*load xs key k-xs.length)^2)=
      (Fintype.card K:ℚ)^2*collision xs key-(Fintype.card K:ℚ)*(xs.length:ℚ)^2 := by
  have ht:=total_load xs key
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    mul_pow,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (Fintype.card K:ℚ)^2*collision xs key-
      (∑ k,2*((Fintype.card K:ℚ)*load xs key k)*(xs.length:ℚ))+
      (Fintype.card K:ℚ)*(xs.length:ℚ)^2=_
  have he : (∑ k,2*((Fintype.card K:ℚ)*load xs key k)*(xs.length:ℚ))=
      2*(Fintype.card K:ℚ)*(xs.length:ℚ)^2 := by
    calc
      _ = (2*(Fintype.card K:ℚ)*(xs.length:ℚ))*(∑ k,load xs key k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [ht];ring
  rw [he]
  ring

/-- Original collision variance controls EVERY family load, including absent bins. -/
theorem load_le_twice {I K : Type*} [Fintype K] [DecidableEq K]
    (xs : List I) (key : I→K) (Δ : ℕ)
    (hc : (Fintype.card K:ℚ)*collision xs key≤
      (xs.length:ℚ)^2+2*xs.length*Δ*Fintype.card K)
    (hsmall : 2*(Fintype.card K)^2*Δ≤xs.length) (k : K) :
    (Fintype.card K:ℚ)*load xs key k≤2*xs.length := by
  have hd : 0≤(Fintype.card K:ℚ) := by positivity
  have hm : 0≤(xs.length:ℚ) := by positivity
  have hs : (2:ℚ)*(Fintype.card K:ℚ)^2*Δ≤xs.length := by exact_mod_cast hsmall
  have hvar := scaled_variance xs key
  have hv : (∑ j,((Fintype.card K:ℚ)*load xs key j-xs.length)^2)≤(xs.length:ℚ)^2 := by
    have h1:=mul_le_mul_of_nonneg_left hc hd
    have h2:=mul_le_mul_of_nonneg_left hs hm
    nlinarith
  have hk : ((Fintype.card K:ℚ)*load xs key k-xs.length)^2≤
      ∑ j,((Fintype.card K:ℚ)*load xs key j-xs.length)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((Fintype.card K:ℚ)*load xs key j-xs.length)) (Finset.mem_univ k)
  have hn : 0≤load xs key k := by unfold load;positivity
  nlinarith

end RiemannGaussian.SemiprimeD1LoadBounds
