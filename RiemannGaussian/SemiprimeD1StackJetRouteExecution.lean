/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRouteLoop
/-! # Closed original-context physical mixed-radix execution -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteExecution
open SemiprimeD1StackJetRoute SemiprimeD1StackJetRouteCalls SemiprimeD1StackJetRouteStep
open SemiprimeD1StackJetRouteControl SemiprimeD1StackJetRouteBase SemiprimeD1StackJetRouteLoop
open SemiprimeD1StackJetRouteRecords (tape acquired_tape original_tape_length)
open SemiprimeD1StackJetRouteFailure (compose)
open SemiprimeD1StackUnaryDivmod (unary unary_add)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => SemiprimeD1StackJetRoute.control

/-- Polynomial transition envelope in actual rank, axis count and original unary indices. -/
def budget (axes : List ℕ) (i j : ℕ) : ℕ :=
  20000*(axes.length+1)^2*(axes.prod+i+j+1)

/-- Literal original-context inputs: axes and indices are physical tapes;
no suffix, route, compatibility or rank answer is provided. -/
def initial (axes : List ℕ) (i j : ℕ) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨some (ctl .copyLeft),none,none,
    bank (vectorBits (axes.map unary)) [] (unary i) (unary j) [] [] [] [] [] [] [] [] [],[]⟩

/-- Exact bytes at the original mixed-radix route boundary. -/
def final (axes : List ℕ) (i j : ℕ) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨none,none,none,answer (decide (SemiprimeD1JetRouting.admissible axes i j)) (unary (i+j)),[]⟩

/-- Original axes internally acquire every suffix product before the actual
record loop. The destination is a cached physical sum, retained only on success. -/
theorem route_trace (axes : List ℕ) (hp : ∀q∈axes,0<q) (i j : ℕ) :
    ∃m≤budget axes i j,Trace.Runs code m (ctl .copyLeft) (initial axes i j).data
      (ctl .halt) (final axes i j).data := by
  have h1 := copy_left (vectorBits (axes.map unary)) (unary i) (unary j)
  have h2 := copy_right (vectorBits (axes.map unary)) (unary i) (unary j) (unary i)
  rw [←unary_add j i,Nat.add_comm j i] at h2
  obtain ⟨a,ha,h3⟩ := suffix_call axes hp (unary i) (unary j) (unary (i+j))
  rw [acquired_tape] at h3
  have h4 := flag_true (ctl .suffixDone) (ctl .clearRank) rfl []
    (tape (SemiprimeD1StackRouteArithmetic.records axes)) (unary i) (unary j) (unary (i+j))
    (unary axes.prod) [] [] [] [] [] []
  have h5 := clear_rank (tape (SemiprimeD1StackRouteArithmetic.records axes))
    (unary i) (unary j) (unary (i+j)) (unary axes.prod)
  obtain ⟨b,hb,h6⟩ := loop (SemiprimeD1StackRouteArithmetic.records axes) i j (unary (i+j))
  rw [SemiprimeD1StackRouteArithmetic.compatible_records] at h6
  have h := compose h1 (compose h2 (compose h3 (compose h4 (compose h5 h6))))
  refine ⟨_,?_,h⟩
  have hlen : (SemiprimeD1StackRouteArithmetic.records axes).length=axes.length := by
    clear hp ha hb h h1 h2 h3 h4 h5 h6
    induction axes with
    | nil=>rfl
    | cons q qs ih=>simp [SemiprimeD1StackRouteArithmetic.records,ih]
  rw [hlen] at hb
  have ht := original_tape_length axes hp
  simp only [unary,List.length_replicate] at hb ⊢
  have hlinear : (tape (SemiprimeD1StackRouteArithmetic.records axes)).length+i+j+(i+j)+1≤
      4*(axes.length+1)*(axes.prod+i+j+1) := by
    ring_nf at ht ⊢
    omega
  have hscaled := Nat.mul_le_mul_left (4000*(axes.length+1)) hlinear
  unfold budget
  ring_nf at ha hb hscaled ⊢
  omega

/-- Closed literal clean-halt execution with the final halt transition paid. -/
theorem route_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (i j : ℕ) :
    ∃m≤budget ctx.axes i j+1,
      SemiprimeD1StackCalls.run code m (initial ctx.axes i j)=some (final ctx.axes i j) := by
  obtain ⟨m,hm,ht⟩ := route_trace ctx.axes hp i j
  obtain ⟨out,hr,ho⟩ := ht [] (initial ctx.axes i j) ⟨rfl,rfl,rfl⟩
  have hh := SemiprimeD1StackProcedureTrace.halt_run code (ctl .halt) rfl
    (final ctx.axes i j).data [] out ho
  refine ⟨m+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh

/-- The sole physical output Boolean and unary destination specify exactly the
frozen original route, including all rejected/out-of-range indices. -/
theorem final_value (axes : List ℕ) (i j : ℕ) :
    (if (final axes i j).data .valid=[true] then
      some ((final axes i j).data .result).length else none)=
      (SemiprimeD1JetRouting.route axes i j).value := by
  rw [SemiprimeD1StackRouteArithmetic.route_eq_add]
  by_cases ha : SemiprimeD1JetRouting.admissible axes i j <;>
    simp [final,answer,bank,ha,unary]
end RiemannGaussian.SemiprimeD1StackJetRouteExecution
