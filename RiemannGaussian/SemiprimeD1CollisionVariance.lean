/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceIncidenceHistogram

/-! # Original occurrence-list collision bound for D.1 packing
Parallel ports remain separate list occurrences. Degree bounds are bounds on
literal original owner/factor fibres, not on a supplied collision answer.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CollisionVariance
open scoped BigOperators
open SemiprimeSourceHistogramGrouping

/-- Literal ordered occurrence-pair sum. -/
def pairSum {I R : Type*} [AddCommMonoid R] (xs : List I) (f : I → I → R) : R :=
  (xs.map (fun i => (xs.map (f i)).sum)).sum

/-- A uniform per-occurrence bound pays every actual list entry. -/
theorem sum_map_le {I : Type*} (xs : List I) (f : I → ℚ) (C : ℚ)
    (h : ∀ i∈xs, f i≤C) : (xs.map f).sum≤(xs.length:ℚ)*C := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi:=h i List.mem_cons_self
    have ht:=ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- Exact equality-pair count is the sum of the actual fibre loads. -/
theorem equal_pairs {I K : Type*} [DecidableEq K] (xs : List I) (key : I→K) :
    pairSum xs (fun i j => if key i=key j then (1:ℕ) else 0)=
      (xs.map (fun i => multiplicity key xs (key i))).sum := by
  unfold pairSum
  congr 1
  apply List.map_congr_left
  intro i _
  simpa only [eq_comm] using indicator_sum key xs (key i)

/-- Shared endpoints are an original finite predicate, not a collision oracle. -/
def sharedCount {I V E : Type*} [DecidableEq V] [DecidableEq E]
    (xs : List I) (owner : I→V) (factor : I→E) : ℕ :=
  pairSum xs (fun i j => if owner i=owner j ∨ factor i=factor j then 1 else 0)

/-- The union of two endpoint equalities has at most two fibre-load budgets. -/
theorem shared_count_le {I V E : Type*} [DecidableEq V] [DecidableEq E]
    (xs : List I) (owner : I→V) (factor : I→E) (Δ : ℕ)
    (ho : ∀ i∈xs,multiplicity owner xs (owner i)≤Δ)
    (hf : ∀ i∈xs,multiplicity factor xs (factor i)≤Δ) :
    sharedCount xs owner factor≤2*xs.length*Δ := by
  have hrow (i : I) (hi : i∈xs) :
      (xs.map (fun j => if owner i=owner j ∨ factor i=factor j then 1 else 0)).sum≤2*Δ := by
    calc
      _ ≤ (xs.map (fun j => (if owner i=owner j then 1 else 0)+
            (if factor i=factor j then 1 else 0))).sum := by
        apply List.sum_le_sum
        intro j _
        by_cases ho : owner i=owner j <;> by_cases hf : factor i=factor j <;> simp [ho,hf]
      _ = multiplicity owner xs (owner i)+multiplicity factor xs (factor i) := by
        rw [List.sum_map_add]
        rw [show (xs.map (fun j => if owner i=owner j then 1 else 0)).sum=
          multiplicity owner xs (owner i) by simpa only [eq_comm] using indicator_sum owner xs (owner i)]
        rw [show (xs.map (fun j => if factor i=factor j then 1 else 0)).sum=
          multiplicity factor xs (factor i) by simpa only [eq_comm] using indicator_sum factor xs (factor i)]
      _ ≤ 2*Δ := by have:=ho i hi;have:=hf i hi;omega
  unfold sharedCount pairSum
  calc
    _ ≤ (xs.map (fun _ => 2*Δ)).sum := by
      apply List.sum_le_sum
      exact hrow
    _ = 2*xs.length*Δ := by simp [Nat.mul_comm,Nat.mul_left_comm]

/-- The original all-free equality probability for one endpoint namespace. -/
def freePotential {K : Type*} [DecidableEq K] (L : ℚ) (a b : K) : ℚ :=
  if a=b then 1 else 1/L

/-- Away from pairs sharing an endpoint the two equalities cost exactly L². -/
theorem free_product_le {V E : Type*} [DecidableEq V] [DecidableEq E]
    (L : ℚ) (hL : 1≤L) (a c : V) (b d : E) :
    freePotential L a c*freePotential L b d≤
      1/L^2+(if a=c ∨ b=d then 1 else 0) := by
  have hp : 0<L := by linarith
  have hinv : 0≤1/L := by positivity
  have hle : 1/L≤1 := (div_le_one hp).mpr hL
  have hs : 0≤1/L^2 := by positivity
  by_cases ha : a=c <;> by_cases hb : b=d <;>
    simp only [freePotential,ha,hb,ite_true,ite_false,or_self,or_true,or_false,one_mul,mul_one]
  all_goals first | nlinarith | (field_simp;norm_num)

/-- All-free expected collision mass, computed from actual original ports. -/
def initialCollision {I V E : Type*} [DecidableEq V] [DecidableEq E]
    (xs : List I) (owner : I→V) (factor : I→E) (L : ℚ) : ℚ :=
  pairSum xs (fun i j => freePotential L (owner i) (owner j)*
    freePotential L (factor i) (factor j))

/-- Initial D.3 collision bound, including parallel ports and empty graphs. -/
theorem initial_collision_le {I V E : Type*} [DecidableEq V] [DecidableEq E]
    (xs : List I) (owner : I→V) (factor : I→E) (Δ : ℕ) (L : ℚ) (hL : 1≤L)
    (ho : ∀ i∈xs,multiplicity owner xs (owner i)≤Δ)
    (hf : ∀ i∈xs,multiplicity factor xs (factor i)≤Δ) :
    initialCollision xs owner factor L≤(xs.length:ℚ)^2/L^2+2*xs.length*Δ := by
  have hshared : (sharedCount xs owner factor:ℚ)≤2*xs.length*Δ := by
    exact_mod_cast shared_count_le xs owner factor Δ ho hf
  have he : initialCollision xs owner factor L≤
      (xs.length:ℚ)^2/L^2+(sharedCount xs owner factor:ℚ) := by
    unfold initialCollision sharedCount pairSum
    push_cast
    calc
      _ ≤ (xs.map (fun i => (xs.map (fun j => 1/L^2+
          (if owner i=owner j ∨ factor i=factor j then (1:ℚ) else 0))).sum)).sum := by
        apply List.sum_le_sum
        intro i _
        apply List.sum_le_sum
        intro j _
        exact free_product_le L hL _ _ _ _
      _ = _ := by simp [List.sum_map_add,pow_two,Function.comp_def,List.map_map];ring
  linarith

/-- Literal scaled equality kernel at an all-free key. -/
theorem kernel_free {W : Type*} [DecidableEq W] (L : ℚ) (hL : L≠0)
    (remaining : List ℕ) (ω : ℕ→W) (a c : ℕ) (ha : a∈remaining) :
    SemiprimeSourceIncidenceHistogram.kernel L remaining ω a c=
      L*freePotential L a c := by
  by_cases h : a=c <;> simp [SemiprimeSourceIncidenceHistogram.kernel,freePotential,h,ha,hL]

/-- The actual all-free sixteen-feature scalar equals L² times the expected load. -/
theorem histogram_initial {I W : Type*} [DecidableEq W] (xs : List I)
    (owner factor : I→ℕ) (remaining : List ℕ) (ω : ℕ→W) (L : ℚ) (hL : L≠0)
    (ho : ∀ i∈xs,owner i∈remaining) (hf : ∀ i∈xs,factor i∈remaining) :
    SemiprimeSourceIncidenceHistogram.histogramSum L xs remaining ω owner factor=
      L^2*initialCollision xs owner factor L := by
  rw [← SemiprimeSourceIncidenceHistogram.kernel_pairs]
  change pairSum xs _=L^2*pairSum xs _
  rw [← show pairSum xs (fun i j => L^2*(freePotential L (owner i) (owner j)*
      freePotential L (factor i) (factor j)))=L^2*pairSum xs (fun i j =>
      freePotential L (owner i) (owner j)*freePotential L (factor i) (factor j)) by
    simp only [pairSum,List.sum_map_mul_left]]
  unfold pairSum
  congr 1
  apply List.map_congr_left
  intro i hi
  congr 1
  apply List.map_congr_left
  intro j _
  dsimp only
  rw [kernel_free L hL remaining ω _ _ (ho i hi),kernel_free L hL remaining ω _ _ (hf i hi)]
  ring

/-- The actual initial padded incidence scalar has the original D.3 bound. -/
theorem padded_initial_le {I W : Type*} [DecidableEq W] (xs : List I)
    (owner factor : I→ℕ) (remaining : List ℕ) (ω : ℕ→W) (Δ : ℕ)
    (L : ℚ) (hL : 1≤L)
    (hao : ∀ i∈xs,owner i∈remaining) (haf : ∀ i∈xs,factor i∈remaining)
    (ho : ∀ i∈xs,multiplicity owner xs (owner i)≤Δ)
    (hf : ∀ i∈xs,multiplicity factor xs (factor i)≤Δ) :
    L^2*SemiprimeSourceIncidenceHistogram.histogramSum L xs remaining ω owner factor≤
      L^2*(xs.length:ℚ)^2+2*xs.length*Δ*L^4 := by
  have hp : 0<L := by linarith
  rw [histogram_initial xs owner factor remaining ω L (ne_of_gt hp) hao haf]
  have h:=mul_le_mul_of_nonneg_left (initial_collision_le xs owner factor Δ L hL ho hf)
    (show 0≤L^4 by positivity)
  have he : L^4*((xs.length:ℚ)^2/L^2+2*xs.length*Δ)=
      L^2*(xs.length:ℚ)^2+2*xs.length*Δ*L^4 := by field_simp
  rw [he] at h
  nlinarith [sq_nonneg L]

/-- At completion no free keys remain: equality is purely the actual label pair. -/
theorem histogram_terminal {I W : Type*} [DecidableEq W] (xs : List I)
    (owner factor : I→ℕ) (ω : ℕ→W) (L : ℚ) :
    L^2*SemiprimeSourceIncidenceHistogram.histogramSum L xs [] ω owner factor=
      L^4*pairs xs (fun i j => if ω (owner i)=ω (owner j) ∧
        ω (factor i)=ω (factor j) then (1:ℚ) else 0) := by
  rw [← SemiprimeSourceIncidenceHistogram.kernel_pairs,← pairs_scale,← pairs_scale]
  unfold pairs
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  apply List.map_congr_left
  intro j _
  dsimp only
  by_cases ho : owner i=owner j <;> by_cases hf : factor i=factor j <;>
    by_cases hv : ω (owner i)=ω (owner j) <;> by_cases he : ω (factor i)=ω (factor j) <;>
    simp_all [SemiprimeSourceIncidenceHistogram.kernel] <;> ring

end RiemannGaussian.SemiprimeD1CollisionVariance
