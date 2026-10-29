/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeafLoad

/-! # Polynomial retained report for actual deterministic partition acquisition -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryPlanBudget
open SemiprimeD1BoundaryPlan

/-- Sum a uniform per-element work allowance without a product of catalogues. -/
theorem sum_map_le {α : Type} (xs : List α) (f : α → Nat) (B : Nat)
    (h : ∀x∈xs,f x≤ B) : (xs.map f).sum≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hx,ht]

/-- The acquired local colour sample count is exactly its finite power. -/
theorem colourWords_length (k n : Nat) : (colourWords k n).length=k^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [colourWords,List.length_flatMap,ih,pow_succ,Nat.mul_comm]

/-- Duplicate removal never increases a literal finite inventory. -/
theorem eraseDups_length (xs : List Nat) : xs.eraseDups.length≤ xs.length := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [List.eraseDups_cons,List.length_cons]
      have hf:=List.length_filter_le (fun b => !(b==x)) xs
      have ht:=ih (xs.filter (fun b => !(b==x))).length
        (by simp only [List.length_cons] at hn;omega) _ rfl
      simp only [List.length_cons] at hn
      omega

/-- One or two original edge factors have at most four unknown endpoints. -/
theorem endpoints_length (es : List (Nat × Nat)) : (endpoints es).length≤2*es.length := by
  apply (eraseDups_length _).trans_eq
  have h : (es.flatMap (fun e => [e.1,e.2])).length=2*es.length := by
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih];omega
  exact h

/-- Fixed-degree local conditional-expectation work polynomial. -/
def localBudget (k F : Nat) : Nat := (k^4+1)*(F+k+13)^4

theorem local_clock (scale k : Nat) (fixed : List Nat) (load : Load)
    (es : List (Nat × Nat)) (hk : 1≤ k) (hs : scale≤4) (he : es.length≤2) :
    (localExpectation scale k fixed load es).clock≤ localBudget k fixed.length := by
  have hv:=endpoints_length es
  have hu:=List.length_filter_le (fun v => !(v<fixed.length)) (endpoints es)
  have hpow : k^((endpoints es).filter (fun v => !(v<fixed.length))).length≤ k^4 :=
    Nat.pow_le_pow_right hk (by omega)
  simp only [localExpectation,colourWords_length]
  unfold localBudget
  apply Nat.mul_le_mul (Nat.add_le_add_right hpow 1)
  apply Nat.pow_le_pow_left
  omega

/-- Sum a finite flattened report list exactly once. -/
theorem flat_sum {α : Type} (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum=(xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

/-- Every measured load needs at most M squared local reports. -/
def potentialBudget (M k F : Nat) : Nat :=
  2*k*(M*M*localBudget k F+M*localBudget k F+(M+k+F+2)^4)+2*k+1

theorem potential_clock (g : Graph) (k : Nat) (fixed : List Nat) (hk : 1≤ k) :
    (potential g k fixed).clock≤ potentialBudget g.edges.length k fixed.length := by
  let reports:=(loads k).map (fun load =>
    let single:=g.edges.map (fun e => localExpectation 2 k fixed load [e])
    let pairs:=g.edges.flatMap (fun e => g.edges.map (fun f => localExpectation 4 k fixed load [e,f]))
    (((pairs.map (fun r => r.value)).sum:Int)-2*(meanNumerator g.edges.length k load:Int)*
      ((single.map (fun r => r.value)).sum:Int)+(meanNumerator g.edges.length k load:Int)^2,
      (pairs.map (fun r => r.clock)).sum+(single.map (fun r => r.clock)).sum+(g.edges.length+k+fixed.length+2)^4))
  have hloads : (loads k).length≤2*k := by simp only [loads,List.length_append,List.length_map,List.length_range];omega
  have hr : ∀r∈reports,r.2≤ g.edges.length*g.edges.length*localBudget k fixed.length+
      g.edges.length*localBudget k fixed.length+(g.edges.length+k+fixed.length+2)^4 := by
    intro r hr
    obtain ⟨load,_,rfl⟩:=List.mem_map.mp hr
    have hs:=sum_map_le g.edges (fun e => (localExpectation 2 k fixed load [e]).clock)
      (localBudget k fixed.length) (fun e _ => local_clock 2 k fixed load [e] hk (by omega) (by simp))
    have hp:=sum_map_le g.edges (fun e =>
      ((g.edges.map (fun f => localExpectation 4 k fixed load [e,f])).map Work.clock).sum)
      (g.edges.length*localBudget k fixed.length) (fun e _ => by
        simpa only [List.map_map,Function.comp_def] using sum_map_le g.edges
          (fun f => (localExpectation 4 k fixed load [e,f]).clock) (localBudget k fixed.length)
          (fun f _ => local_clock 4 k fixed load [e,f] hk (by omega) (by simp)))
    simp only [List.map_flatMap,flat_sum,List.map_map,Function.comp_def] at hp ⊢
    nlinarith only [hs,hp]
  have ht:=sum_map_le reports Prod.snd _ hr
  have hlen : reports.length=(loads k).length := List.length_map _
  change (reports.map Prod.snd).sum+reports.length+1≤_
  unfold potentialBudget
  rw [hlen] at ht ⊢
  exact (Nat.add_le_add_right (Nat.add_le_add ht hloads) 1).trans (by gcongr)

/-- Fixed-degree local budget monotonicity. -/
theorem local_mono (k l F G : Nat) (hk : k≤ l) (hF : F≤ G) : localBudget k F≤ localBudget l G := by
  unfold localBudget
  gcongr

/-- Fixed-degree potential budget monotonicity. -/
theorem potential_mono (M N k l F G : Nat) (hM : M≤ N) (hk : k≤ l) (hF : F≤ G) :
    potentialBudget M k F≤ potentialBudget N l G := by
  have hlocal:=local_mono k l F G hk hF
  unfold potentialBudget
  gcongr

/-- All actual candidate potentials and deterministic tie-policy bookkeeping. -/
def candidateBudget (M k F : Nat) : Nat :=
  k*potentialBudget M k (F+1)+(k+1)*(F+M+k+2)^3

theorem candidate_mono (M N k l F G : Nat) (hM : M≤ N) (hk : k≤ l) (hF : F≤ G) :
    candidateBudget M k F≤ candidateBudget N l G := by
  have hp:=potential_mono M N k l (F+1) (G+1) hM hk (Nat.add_le_add_right hF 1)
  unfold candidateBudget
  gcongr

/-- Actual candidate acquisition evaluates precisely k fixed-degree potentials. -/
theorem candidate_clock (g : Graph) (k : Nat) (fixed : List Nat) (hk : 1≤ k) :
    (leastCandidate g k fixed).clock≤ candidateBudget g.edges.length k fixed.length := by
  have hs:=sum_map_le (List.range k)
    (fun c => (potential g k (fixed++[c])).clock) (potentialBudget g.edges.length k (fixed.length+1))
    (fun c _ => by simpa only [List.length_append,List.length_singleton] using potential_clock g k (fixed++[c]) hk)
  rw [List.length_range] at hs
  simp only [leastCandidate,List.map_map,List.length_map,List.length_range,Function.comp_def]
  unfold candidateBudget
  exact Nat.add_le_add_right hs _

/-- Every extension step pays one real candidate acquisition. -/
theorem extend_clock (g : Graph) (k n V : Nat) (fixed : List Nat) (hk : 1≤ k)
    (hsize : fixed.length+n≤ V) :
    (extend g k n fixed).clock≤ n*(candidateBudget g.edges.length k V+V+3)+V+1 := by
  induction n generalizing fixed with
  | zero => simp only [extend,Nat.zero_mul,Nat.zero_add]; omega
  | succ n ih =>
    have hfixed : fixed.length≤ V := by omega
    have hc:=(candidate_clock g k fixed hk).trans
      (candidate_mono _ _ k k fixed.length V (by rfl) (by rfl) hfixed)
    have ht:=ih (fixed++[(leastCandidate g k fixed).value])
      (by simp only [List.length_append,List.length_singleton];omega)
    simp only [extend]
    nlinarith only [hc,ht,hfixed]

/-- Fixed polynomial in the graph's original vertex/edge inventory. -/
def acquisitionBudget (V M : Nat) : Nat :=
  V*(candidateBudget M (M+2) V+V+3)+V+1+(V+M+(M+2)+2)^6

/-- The actual closed deterministic partition report is polynomial in its
original graph. All k^4 local sample catalogues and edge-pair traversals are paid. -/
theorem acquire_clock (g : Graph) : (acquire g).clock≤ acquisitionBudget g.vertices g.edges.length := by
  have hk:=SemiprimeD1BoundaryChoice.chooseK_bounds g
  have he:=extend_clock g (chooseK g) g.vertices g.vertices [] (by omega) (by simp)
  have hc:=candidate_mono g.edges.length g.edges.length (chooseK g) (g.edges.length+2)
    g.vertices g.vertices (by rfl) hk.2 (by rfl)
  simp only [acquire]
  unfold acquisitionBudget
  apply Nat.add_le_add
  · exact he.trans (by gcongr)
  · gcongr
    exact hk.2

end RiemannGaussian.SemiprimeD1BoundaryPlanBudget
