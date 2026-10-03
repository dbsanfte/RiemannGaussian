/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeKernelResidual

/-!
# Complete public kernel descent with retained factor transport

Reuse each actual child route rather than routing that input again.
Every kernel residual is below half its parent. Public logarithmic fuel
therefore ends at a proper factor or a projected-long certificate. The
entire chain retains its original and active units and prime lists;
factor recovery is a named downstream view. Source-width and prefix-query
envelopes charge all levels. Projected-long extraction and bit costs remain
open, so this is not a complete one-sixth factorizer.
-/

namespace RiemannGaussian.SemiprimeKernelDescent

open SemiprimeGroupSelection SemiprimeKernelResidual

/-- Rich descent carrier, retaining every parent unit and actual child route. -/
inductive Trace : ℕ → Type where
  | factor {N : ℕ} (d : ℕ) : Trace N
  | longBase {N : ℕ} (k : ℕ) : Trace N
  | child {N : ℕ} (R : ℕ) (original active : (ZMod N)ˣ) (primes : List ℕ)
      (route : SemiprimeLocalOrderRouting.Route) (trace : Trace R) : Trace N
  | unresolved {N : ℕ} : Trace N

/-- Certificates attach the literal semiprime and transport facts at every
level, without replacing the richer trace by its final factor option. -/
inductive Certified : {N : ℕ} → Trace N → Prop where
  | factor {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
      (hd : ProperDivisor (p*q) d) : Certified (.factor d : Trace (p*q))
  | longBase {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
      (hgood : SemiprimeLocalOrderRouting.GoodRoute p q
        (SemiprimeLehmanCoverage.sixthWidth (p*q)) (.longBase k)) :
      Certified (.longBase k : Trace (p*q))
  | child {p q R : ℕ} {g h : (ZMod (p*q))ˣ} {primes : List ℕ}
      {route : SemiprimeLocalOrderRouting.Route} {trace : Trace R}
      (hp : p.Prime) (hq : q.Prime)
      (hgood : GoodKernel p q (.residual R g h primes route))
      (hchild : Certified trace) : Certified (.child R g h primes route trace)

/-- Consume the existing child route at each kernel descent. Fuel and all
input-specific kernel handling are part of the public procedure. -/
noncomputable def descend : (fuel N : ℕ) → SemiprimeLocalOrderRouting.Route → Trace N
  | 0, _, _ => .unresolved
  | fuel+1, N, route =>
    match route with
    | .factor d => .factor d
    | .longBase k => .longBase k
    | .unresolved => .unresolved
    | .kernelBase k =>
      if hc : k.Coprime N then
        match kernelRoute (ZMod.unitOfCoprime k hc) (SemiprimeLehmanCoverage.sixthWidth N) with
        | .factor d => .factor d
        | .residual R g h primes child => .child R g h primes child (descend fuel R child)
        | .unresolved => .unresolved
      else .unresolved

/-- Every nonzero input has positive sixth-root width. -/
theorem sixthWidth_pos {N : ℕ} (hN : 0<N) :
    0<SemiprimeLehmanCoverage.sixthWidth N := by
  have hb := SemiprimeLehmanCoverage.sixthWidth_upper N
  by_contra hn
  have he : SemiprimeLehmanCoverage.sixthWidth N=0 := by omega
  rw [he] at hb
  norm_num at hb
  omega

/-- Each retained half-input fits the remaining public logarithmic fuel. -/
theorem half_fuel {N R fuel : ℕ} (hhalf : 2*R<N) (hpay : N<2^(fuel+1)) :
    R<2^fuel := by
  rw [pow_succ] at hpay
  omega

/-- A certified semiprime route is completely stripped of kernel leaves
within the public fuel. No order or smaller-input solver is assumed. -/
theorem descend_certified {p q fuel : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpay : p*q<2^fuel) (route : SemiprimeLocalOrderRouting.Route)
    (hroute : SemiprimeLocalOrderRouting.GoodRoute p q
      (SemiprimeLehmanCoverage.sixthWidth (p*q)) route) :
    Certified (descend fuel (p*q) route) := by
  induction fuel generalizing p q route with
  | zero =>
    have hpos := Nat.mul_pos hp.pos hq.pos
    norm_num only [pow_zero] at hpay
    omega
  | succ fuel ih =>
    cases route with
    | factor d => exact .factor hp hq hroute
    | longBase k => exact .longBase hp hq hroute
    | unresolved => exact False.elim hroute
    | kernelBase k =>
      obtain ⟨hc,hdata⟩ := hroute
      have hkernel := kernelRoute_semiprime hp hq
        (sixthWidth_pos (Nat.mul_pos hp.pos hq.pos))
        (SemiprimeLehmanCoverage.sixthWidth_upper (p*q))
        (ZMod.unitOfCoprime k hc) hdata
      unfold descend
      dsimp only
      rw [dif_pos hc]
      cases hk : kernelRoute (ZMod.unitOfCoprime k hc)
          (SemiprimeLehmanCoverage.sixthWidth (p*q)) with
      | factor d =>
        rw [hk] at hkernel
        exact .factor hp hq hkernel
      | residual R g h primes child =>
        rw [hk] at hkernel
        obtain ⟨u,v,hu,hv,hR,hchild⟩ := hkernel.2.2.1
        have hfuel := half_fuel hkernel.1 hpay
        subst R
        exact .child hp hq hkernel (ih hu hv hfuel child hchild)
      | unresolved =>
        rw [hk] at hkernel
        exact False.elim hkernel

/-- Full N-only trace with one initial public route and logarithmic fuel. -/
noncomputable def publicTrace (N : ℕ) : Trace N :=
  descend (Nat.clog 2 (N+1)) N (SemiprimeLocalOrderRouting.publicRoute N)

/-- Every semiprime produces a complete certified factor-or-long trace. -/
theorem publicTrace_certified {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Certified (publicTrace (p*q)) := by
  exact descend_certified hp hq
    (lt_of_lt_of_le (Nat.lt_succ_self (p*q)) (Nat.le_pow_clog (by decide) (p*q+1)))
    _ (SemiprimeLocalOrderRouting.publicRoute_semiprime hp hq)

/-- Recover a factor through the retained active units without discarding
the richer trace. Each child edge pays its own order test and candidate. -/
noncomputable def recoveredFactor {N : ℕ} : Trace N → Option ℕ
  | .factor d => some d
  | .longBase _ => none
  | .unresolved => none
  | .child R _ h _ _ trace =>
    match recoveredFactor trace with
    | some d => recoverResidual h R d
    | none => none

/-- The downstream recovered option is always a proper divisor when present. -/
theorem recoveredFactor_sound {N d : ℕ} {trace : Trace N}
    (hc : Certified trace) (hd : recoveredFactor trace=some d) : ProperDivisor N d := by
  cases hc with
  | factor hp hq hproper =>
    have he : _=d := Option.some.inj hd
    exact he ▸ hproper
  | longBase hp hq hgood => contradiction
  | @child p q R g h primes route trace hp hq hgood hchild =>
    dsimp only [recoveredFactor] at hd
    cases hs : recoveredFactor trace with
    | none => rw [hs] at hd; contradiction
    | some f =>
      rw [hs] at hd
      exact recoverResidual_sound _ hd

/-- The terminal input remains available as a separate trace view. -/
def leafInput {N : ℕ} : Trace N → ℕ
  | .child _ _ _ _ _ trace => leafInput trace
  | _ => N

/-- The terminal public branch is retained, including its base label. -/
def leafRoute {N : ℕ} : Trace N → SemiprimeLocalOrderRouting.Route
  | .factor d => .factor d
  | .longBase k => .longBase k
  | .unresolved => .unresolved
  | .child _ _ _ _ _ trace => leafRoute trace

/-- Exhaustive result: an actual recovered original factor, or a certified
projected-long leaf at a no-larger semiprime, with all parents retained. -/
theorem certified_cases {N : ℕ} {trace : Trace N} (hc : Certified trace) :
    (∃ d, recoveredFactor trace=some d ∧ ProperDivisor N d) ∨
    (recoveredFactor trace=none ∧
      ∃ u v k, u.Prime ∧ v.Prime ∧ leafInput trace=u*v ∧ u*v≤N ∧
        leafRoute trace=.longBase k ∧
        SemiprimeLocalOrderRouting.GoodRoute u v
          (SemiprimeLehmanCoverage.sixthWidth (u*v)) (.longBase k)) := by
  induction hc with
  | factor hp hq hproper => exact Or.inl ⟨_,rfl,hproper⟩
  | longBase hp hq hgood =>
    exact Or.inr ⟨rfl,_,_,_,hp,hq,rfl,le_rfl,rfl,hgood⟩
  | @child p q R g h primes route trace hp hq hgood hchild ih =>
    rcases ih with ⟨d,hd,hproper⟩ | ⟨hnone,u,v,k,hu,hv,hinput,hbound,hroute,hlong⟩
    · obtain ⟨f,hf,hfproper⟩ := residual_transport hp hq g h primes route hgood hproper
      apply Or.inl
      refine ⟨f,?_,hfproper⟩
      simp only [recoveredFactor,hd,hf]
    · apply Or.inr
      refine ⟨?_,u,v,k,hu,hv,hinput,?_,hroute,hlong⟩
      · simp only [recoveredFactor,hnone]
      · have hhalf := hgood.1
        omega

/-- Universal N-only factor-or-retained-projected-long result. This
discharges all kernel descent, not the remaining long extractor. -/
theorem publicTrace_cases {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∃ d, recoveredFactor (publicTrace (p*q))=some d ∧ ProperDivisor (p*q) d) ∨
    (recoveredFactor (publicTrace (p*q))=none ∧
      ∃ u v k, u.Prime ∧ v.Prime ∧ leafInput (publicTrace (p*q))=u*v ∧ u*v≤p*q ∧
        leafRoute (publicTrace (p*q))=.longBase k ∧
        SemiprimeLocalOrderRouting.GoodRoute u v
          (SemiprimeLehmanCoverage.sixthWidth (u*v)) (.longBase k)) :=
  certified_cases (publicTrace_certified hp hq)

/-- Number of charged nonempty input levels in a trace. -/
def depth {N : ℕ} : Trace N → ℕ
  | .unresolved => 0
  | .child _ _ _ _ _ trace => depth trace+1
  | _ => 1

/-- Public fuel bounds every level, including the terminal input. -/
theorem depth_descend_le (fuel N : ℕ) (route : SemiprimeLocalOrderRouting.Route) :
    depth (descend fuel N route)≤fuel := by
  induction fuel generalizing N route with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    cases route with
    | factor d => exact Nat.le_add_left 1 fuel
    | longBase k => exact Nat.le_add_left 1 fuel
    | unresolved => exact Nat.zero_le _
    | kernelBase k =>
      unfold descend
      dsimp only
      split_ifs with hc
      · cases hk : kernelRoute (ZMod.unitOfCoprime k hc)
          (SemiprimeLehmanCoverage.sixthWidth N) with
        | factor d => exact Nat.le_add_left 1 fuel
        | residual R g h primes child =>
          exact Nat.add_le_add_right (ih R child) 1
        | unresolved => exact Nat.zero_le _
      · exact Nat.zero_le _

/-- Sixth-root source width is monotone in the public input. -/
theorem sixthWidth_mono {R N : ℕ} (hRN : R≤N) :
    SemiprimeLehmanCoverage.sixthWidth R≤SemiprimeLehmanCoverage.sixthWidth N := by
  unfold SemiprimeLehmanCoverage.sixthWidth
  exact Nat.find_min' _ (hRN.trans (SemiprimeLehmanCoverage.sixthWidth_upper N))

/-- Even an immediately successful child route inside the kernel handler
has width no larger than its parent's. Such a call is still charged. -/
theorem kernel_child_width_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ)
    (hdata : SemiprimeLocalOrderRouting.KernelData g
      (SemiprimeLehmanCoverage.sixthWidth (p*q))) :
    SemiprimeLehmanCoverage.sixthWidth
      (splitSmall (p*q-1) (SemiprimeLehmanCoverage.sixthWidth (p*q))).1≤
      SemiprimeLehmanCoverage.sixthWidth (p*q) := by
  have hN : 4≤p*q := by nlinarith [hp.two_le,hq.two_le]
  have hB := sixthWidth_pos (Nat.mul_pos hp.pos hq.pos)
  have hB2 : 2≤SemiprimeLehmanCoverage.sixthWidth (p*q) := by
    have hbudget := SemiprimeLehmanCoverage.sixthWidth_upper (p*q)
    by_contra hn
    have he : SemiprimeLehmanCoverage.sixthWidth (p*q)=1 := by omega
    rw [he] at hbudget
    norm_num at hbudget
    omega
  have hhalf := splitSmall_half_bound (show 2<p*q by omega)
    (kernel_even_exponent hp hq hB g hdata) hB2
  exact sixthWidth_mono (by omega)

/-- Charge source widths at every level rather than only at the root. -/
def widthCharge {N : ℕ} : Trace N → ℕ
  | .unresolved => 0
  | .child _ _ _ _ _ trace => SemiprimeLehmanCoverage.sixthWidth N+widthCharge trace
  | _ => SemiprimeLehmanCoverage.sixthWidth N

/-- Every certified level has width bounded by its original input's width. -/
theorem widthCharge_le {N : ℕ} {trace : Trace N} (hc : Certified trace) :
    widthCharge trace≤depth trace*SemiprimeLehmanCoverage.sixthWidth N := by
  induction hc with
  | factor hp hq hproper => simp only [widthCharge,depth,one_mul,le_refl]
  | longBase hp hq hgood => simp only [widthCharge,depth,one_mul,le_refl]
  | @child p q R g h primes route trace hp hq hgood hchild ih =>
    have hRN : R≤p*q := by have hhalf := hgood.1; omega
    have hw := sixthWidth_mono hRN
    have hm := Nat.mul_le_mul_left (depth trace) hw
    dsimp only [widthCharge,depth]
    rw [Nat.add_mul,one_mul]
    omega

/-- The entire public chain charges at most B times logarithmic fuel in
source width. This is not a complete polynomial or bit-cost theorem. -/
theorem publicTrace_width_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    widthCharge (publicTrace (p*q))≤
      Nat.clog 2 (p*q+1)*SemiprimeLehmanCoverage.sixthWidth (p*q) := by
  exact (widthCharge_le (publicTrace_certified hp hq)).trans
    (Nat.mul_le_mul_right _ (depth_descend_le _ _ _))

/-- Three width slots per level reserve its local route, cached kernel
source, and optional child local route, including immediate child success. -/
def routingWidthCharge {N : ℕ} (trace : Trace N) : ℕ := 3*widthCharge trace

/-- Reserving every source slot preserves the B times logarithmic width
envelope. Polynomial operation and bit bounds remain separate obligations. -/
theorem publicTrace_routing_width_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    routingWidthCharge (publicTrace (p*q))≤
      3*(Nat.clog 2 (p*q+1)*SemiprimeLehmanCoverage.sixthWidth (p*q)) :=
  Nat.mul_le_mul_left 3 (publicTrace_width_budget hp hq)

/-- Per-input small-prime query allowance, including all logarithmic stages. -/
def prefixAllowance (N : ℕ) : ℕ :=
  (2*SemiprimeLehmanCoverage.sixthWidth N+1)*Nat.clog 2 (N+1)

/-- The literal cached split's GCD count is covered by this allowance. -/
theorem split_queries_le (N : ℕ) :
    smallPrimeLoopGcdCount (SemiprimeLehmanCoverage.sixthWidth N)
      (SemiprimeStrassenPrefix.blockColumns (N-1) (SemiprimeLehmanCoverage.sixthWidth N))
      (Nat.clog 2 N) (N-1)≤prefixAllowance N := by
  exact (smallPrimeLoopGcdCount_le _ _ _ _).trans
    (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 (Nat.le_succ N)))

/-- A smaller input has no larger prefix-query allowance. -/
theorem prefixAllowance_mono {R N : ℕ} (hRN : R≤N) :
    prefixAllowance R≤prefixAllowance N := by
  have hw := sixthWidth_mono hRN
  apply Nat.mul_le_mul
  · omega
  · exact Nat.clog_mono_right 2 (Nat.add_le_add_right hRN 1)

/-- Charge the small-prime allowance at every input, including a harmless
overcharge at a terminal route that did not need a kernel split. -/
def prefixCharge {N : ℕ} : Trace N → ℕ
  | .unresolved => 0
  | .child _ _ _ _ _ trace => prefixAllowance N+prefixCharge trace
  | _ => prefixAllowance N

/-- The sum of cached-prefix query allowances pays every descent level. -/
theorem prefixCharge_le {N : ℕ} {trace : Trace N} (hc : Certified trace) :
    prefixCharge trace≤depth trace*prefixAllowance N := by
  induction hc with
  | factor hp hq hproper => simp only [prefixCharge,depth,one_mul,le_refl]
  | longBase hp hq hgood => simp only [prefixCharge,depth,one_mul,le_refl]
  | @child p q R g h primes route trace hp hq hgood hchild ih =>
    have hRN : R≤p*q := by have hhalf := hgood.1; omega
    have hm := Nat.mul_le_mul_left (depth trace) (prefixAllowance_mono hRN)
    dsimp only [prefixCharge,depth]
    rw [Nat.add_mul,one_mul]
    omega

/-- All cached small-prime GCD work in the chain has a B log-squared
allowance. Seed routing, polynomial arithmetic and bit costs are separate. -/
theorem publicTrace_prefix_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    prefixCharge (publicTrace (p*q))≤
      Nat.clog 2 (p*q+1)*prefixAllowance (p*q) := by
  exact (prefixCharge_le (publicTrace_certified hp hq)).trans
    (Nat.mul_le_mul_right _ (depth_descend_le _ _ _))

/-- Count downstream trace-recovery calls, each containing one order
test, one quadratic candidate and its checked GCD. -/
noncomputable def recoveryCount {N : ℕ} : Trace N → ℕ
  | .child _ _ _ _ _ trace => recoveryCount trace+
      match recoveredFactor trace with
      | some _ => 1
      | none => 0
  | _ => 0

/-- Each retained child edge can cause at most one factor-recovery call. -/
theorem recoveryCount_le {N : ℕ} (trace : Trace N) : recoveryCount trace≤depth trace := by
  induction trace with
  | factor d => exact Nat.zero_le _
  | longBase k => exact Nat.zero_le _
  | unresolved => exact Nat.zero_le _
  | child R g h primes route trace ih =>
    dsimp only [recoveryCount,depth]
    cases recoveredFactor trace <;> simp only <;> omega

end RiemannGaussian.SemiprimeKernelDescent
