/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffixStep
/-! # Full executed reverse suffix-product scan -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetSuffixScan
open SemiprimeD1StackJetSuffix SemiprimeD1StackJetSuffixCalls
open SemiprimeD1StackJetSuffixPass SemiprimeD1StackJetSuffixStep
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackJetSuffix.control

/-- Literal field encoding; this is a specification, not an input catalogue. -/
def fields : List ℕ → List Bool
  | [] => []
  | q::qs => frame (unary q) (fields qs)

/-- Exact arithmetic specification of the actual scan's retained record tape. -/
def result : List ℕ → ℕ → List Bool → ℕ × List Bool
  | [],d,acc => (d,acc)
  | q::qs,d,acc => result qs (q*d) (frame (unary q) (frame (unary d) acc))

/-- The bound charges every executed call, traversal and replacement. -/
def scanBudget : List ℕ → ℕ → ℕ
  | [],_ => 1
  | q::qs,d => 12*(q*d)+29*q+7*d+27+scanBudget qs (q*d)

/-- The complete reverse scan uses the acquired product of each preceding suffix. -/
theorem scan (xs : List ℕ) (d : ℕ) (acc : List Bool) :
    ∃m≤scanBudget xs d,Trace.Runs code m (ctl .suffixPeek)
      (data [] (fields xs) [] (unary d) [] acc [] [])
      (ctl .success) (data [] [] [] (unary (result xs d acc).1) [] (result xs d acc).2 [] []) := by
  induction xs generalizing d acc with
  | nil =>
    refine ⟨1,by simp [scanBudget],?_⟩
    apply Trace.one_base code (ctl .suffixPeek) (ctl .success)
      (.peek .reverseAxes (ctl .success) (ctl .readReverse) (ctl .readReverse)) _ _ rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,fields]
    · rfl
  | cons q qs ih =>
    obtain ⟨m,hm,hs⟩ := one_suffix q d (fields qs) acc
    obtain ⟨n,hn,ht⟩ := ih (q*d) (frame (unary q) (frame (unary d) acc))
    refine ⟨m+n,by simp only [scanBudget]; omega,?_⟩
    exact compose hs ht

/-- Scalar scan budget is polynomial in the genuine maximum suffix-product value. -/
theorem scanBudget_le (xs : List ℕ) (d cap : ℕ)
    (hp : ∀q∈xs,0<q) (hd : 0<d) (hc : d*xs.prod≤cap) :
    scanBudget xs d≤(48*cap+28)*xs.length+1 := by
  induction xs generalizing d with
  | nil => simp [scanBudget]
  | cons q qs ih =>
    have hq : 0<q := hp q (by simp)
    have hqs : ∀v∈qs,0<v := fun v hv => hp v (by simp [hv])
    have hprod : 0<qs.prod := SemiprimeD1StackRouteArithmetic.rank_pos qs hqs
    have hqd : q*d≤cap := by simp only [List.prod_cons] at hc; nlinarith
    have hqcap : q≤cap := by nlinarith
    have hdcap : d≤cap := by nlinarith
    have htail : q*d*qs.prod≤cap := by simpa only [List.prod_cons,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hc
    have hi := ih (q*d) hqs (by positivity) htail
    simp only [scanBudget,List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeD1StackJetSuffixScan
