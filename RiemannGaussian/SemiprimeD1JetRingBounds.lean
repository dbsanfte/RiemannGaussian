/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRingBits

/-! # Original-input bounds for the executed dense multijet backend
No intermediate/output Fits or coefficient truth is a premise. Rank, precision,
input shape and input physical word widths determine a fixed polynomial report.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1JetRingBounds
open SemiprimeD1JetRingBits SemiprimeD1JetAxes

/-- Actual cached reads preserve original word caps or return literal zero. -/
theorem read_length (ws : List (List Bool)) (i W : ℕ)
    (hw : ∀w∈ws,w.length≤W) : (read ws i).bits.length≤W := by
  induction ws generalizing i with
  | nil => exact Nat.zero_le _
  | cons w ws ih =>
    cases i with
    | zero => exact hw w List.mem_cons_self
    | succ i => exact ih i (fun v hv => hw v (List.mem_cons_of_mem w hv))

/-- Every routed product or zero term has target width. -/
theorem term_length (ctx : Context) (a b : List (List Bool)) (k : ℕ) (ij : ℕ×ℕ) :
    (term ctx a b k ij).bits.length≤ctx.precision := by
  unfold term
  dsimp only
  split_ifs
  · exact SemiprimeD1JetScalarBits.mul_length _ _ _
  · exact Nat.zero_le _

/-- One term pays its actual route, two source reads and physical product. -/
def termBudget (axes N W p : ℕ) : ℕ :=
  20*(axes+1)^2+6*N+12*W*(2*W+2)+9*p+20

/-- The term bound follows only original source dimensions/widths. -/
theorem term_clock (ctx : Context) (a b : List (List Bool)) (k : ℕ) (ij : ℕ×ℕ)
    (N W : ℕ) (ha : a.length≤N) (hb : b.length≤N)
    (hwa : ∀w∈a,w.length≤W) (hwb : ∀w∈b,w.length≤W) :
    (term ctx a b k ij).clock≤termBudget ctx.axes.length N W ctx.precision := by
  have hr:=SemiprimeD1JetRouting.route_clock ctx.axes ij.1 ij.2
  have hla:=read_clock a ij.1
  have hlb:=read_clock b ij.2
  have hwa':=read_length a ij.1 W hwa
  have hwb':=read_length b ij.2 W hwb
  have hm:=SemiprimeD1JetScalarBits.mul_clock ctx.precision (read a ij.1).bits (read b ij.2).bits
  have hp : 12*(read a ij.1).bits.length*((read a ij.1).bits.length+(read b ij.2).bits.length+2)≤
      12*W*(2*W+2) := by
    have hsum : (read a ij.1).bits.length+(read b ij.2).bits.length+2≤2*W+2 := by omega
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 12 (Nat.mul_le_mul hwa' hsum)
  unfold term termBudget
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- All plan pairs are actual finite coordinates, including zero rank. -/
theorem plan_length (N : ℕ) : (plan N).length=N*N := by
  simp [plan,List.length_flatMap]

/-- A finite report list retains the sum of all actual callback costs. -/
theorem sum_clocks_le (rs : List Scalar) (B : ℕ) (h : ∀r∈rs,r.clock≤B) :
    (rs.map (fun r => r.clock)).sum≤rs.length*B := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hh:=h r List.mem_cons_self
    have ht:=ih (fun s hs => h s (List.mem_cons_of_mem r hs))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Actual output-coordinate polynomial cost, allowing deliberately naive reads. -/
def mulAtBudget (axes N W p : ℕ) : ℕ :=
  N*N*(termBudget axes N W p+20*p+35)+N+11

/-- Pure scalar aggregation isolates executable report projections from arithmetic. -/
theorem accumulator_budget (s t N K p : ℕ)
    (hs : s≤t+N*N*(20*p+15)+1) (ht : t≤N*N*K) :
    s+20*(N*N)+N+10≤N*N*(K+20*p+35)+N+11 := by
  calc
    _ ≤ (t+N*N*(20*p+15)+1)+20*(N*N)+N+10 := by omega
    _ ≤ (N*N*K+N*N*(20*p+15)+1)+20*(N*N)+N+10 := by omega
    _ = _ := by ring

/-- All source term calls, accumulator prefixes, pair-plan cells and control are paid. -/
theorem mulAt_clock (ctx : Context) (a b : List (List Bool)) (k W : ℕ)
    (ha : a.length≤ctx.rank) (hb : b.length≤ctx.rank)
    (hwa : ∀w∈a,w.length≤W) (hwb : ∀w∈b,w.length≤W) :
    (mulAt ctx a b k).clock≤mulAtBudget ctx.axes.length ctx.rank W ctx.precision := by
  let terms:=(plan ctx.rank).map (term ctx a b k)
  have hlen : terms.length=ctx.rank*ctx.rank := by simp only [terms,List.length_map,plan_length]
  have hw : ∀r∈terms,r.bits.length≤ctx.precision := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨ij,_,rfl⟩
    exact term_length _ _ _ _ _
  have hs:=sumReports_clock ctx.precision terms hw
  have ht:=sum_clocks_le terms (termBudget ctx.axes.length ctx.rank W ctx.precision) (by
    intro r hr
    rcases List.mem_map.mp hr with ⟨ij,_,rfl⟩
    exact term_clock _ _ _ _ _ _ _ ha hb hwa hwb)
  rw [hlen] at hs ht
  change (sumReports ctx.precision terms).clock+20*(plan ctx.rank).length+ctx.rank+10≤_
  rw [plan_length]
  exact accumulator_budget _ _ _ _ _ hs ht

/-- Whole dense product cost is fixed polynomial in rank, precision, axis count and width. -/
def mulBudget (axes N W p : ℕ) : ℕ := N*mulAtBudget axes N W p+10*N+5

/-- Actual whole product retains EVERY acquired output and source report. -/
theorem mul_clock (ctx : Context) (a b : List (List Bool)) (W : ℕ)
    (ha : a.length≤ctx.rank) (hb : b.length≤ctx.rank)
    (hwa : ∀w∈a,w.length≤W) (hwb : ∀w∈b,w.length≤W) :
    (mul ctx a b).clock≤mulBudget ctx.axes.length ctx.rank W ctx.precision := by
  have h:=sum_clocks_le ((List.range ctx.rank).map (mulAt ctx a b))
    (mulAtBudget ctx.axes.length ctx.rank W ctx.precision) (by
      intro r hr
      rcases List.mem_map.mp hr with ⟨k,_,rfl⟩
      exact mulAt_clock _ _ _ _ _ ha hb hwa hwb)
  simp only [List.length_map,List.length_range] at h
  exact Nat.add_le_add_right h (10*ctx.rank+5)

/-- Actual input source reads and physical coordinate addition have a linear budget. -/
theorem addAt_clock (ctx : Context) (a b : List (List Bool)) (i W : ℕ)
    (ha : a.length≤ctx.rank) (hb : b.length≤ctx.rank)
    (hwa : ∀w∈a,w.length≤W) (hwb : ∀w∈b,w.length≤W) :
    (addAt ctx a b i).clock≤6*ctx.rank+11*W+9*ctx.precision+17 := by
  have hla:=read_clock a i
  have hlb:=read_clock b i
  have hwa':=read_length a i W hwa
  have hwb':=read_length b i W hwb
  have hm:=SemiprimeD1JetScalarBits.add_clock ctx.precision (read a i).bits (read b i).bits
  have hmax:=max_le hwa' hwb'
  simp only [addAt]
  omega

/-- Whole dense addition cost, including all output report-list scans. -/
theorem add_clock (ctx : Context) (a b : List (List Bool)) (W : ℕ)
    (ha : a.length≤ctx.rank) (hb : b.length≤ctx.rank)
    (hwa : ∀w∈a,w.length≤W) (hwb : ∀w∈b,w.length≤W) :
    (add ctx a b).clock≤ctx.rank*(6*ctx.rank+11*W+9*ctx.precision+17)+10*ctx.rank+5 := by
  have h:=sum_clocks_le ((List.range ctx.rank).map (addAt ctx a b))
    (6*ctx.rank+11*W+9*ctx.precision+17) (by
      intro r hr
      rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
      exact addAt_clock _ _ _ _ _ ha hb hwa hwb)
  simp only [List.length_map,List.length_range] at h
  exact Nat.add_le_add_right h (10*ctx.rank+5)

end RiemannGaussian.SemiprimeD1JetRingBounds
