/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHeadSharedCancellation

/-!
# The ordinary-prime boundary after shared-owner completion

The all-count nonowner cancellation does not remove the ordinary-prime
cofactor boundary. On every original head pair, completing at its smaller
prime gives the exact response `L-log q`, at least `3N/8`. This boundary
and the SAME existing head have the same phase and sign. They reinforce
on identical labels, even with the original factorial allocation retained.

This is a local go/no-go audit, not a bound for the sum across labels.
It forbids paying this boundary with the squarefree counting error or
claiming that completion automatically cancels the original correction.
-/

set_option autoImplicit false
noncomputable section
open Real
open scoped Classical BigOperators
namespace RiemannGaussian.ZetaRieszOwnerCompletionAudit
open ZetaRieszPrimeHeadTransport ZetaRieszPrimeHeadPolePayment
open ZetaRieszSmallTagNativeFloor (owners owners_data)
open ZetaRieszOwnerMaximal (ownerWeight ownerWeight_bounds)

/-- The literal integer upper endpoint, not a frozen radial slice. -/
theorem pair_cofactor_log_upper {u : ℝ} {N p q : ℕ}
    (hp : p∈owners u N) (hq : q∈pairInterval N p) (hqp : q.Prime) :
    log q≤(101/100 : ℝ)*N := by
  have hd := owners_data hp
  have hqX := (Finset.mem_Ioc.mp hq).2
  have hf := Nat.floor_le (exp_pos ((203/100 : ℝ)*N-log p)).le
  have hle : (q : ℝ)≤exp ((203/100 : ℝ)*N-log p) :=
    (by exact_mod_cast hqX : (q : ℝ)≤
      ZetaRieszOwnerLatticePhase.coreFloor N (log p) (203/100)).trans hf
  have hl := log_le_log (by exact_mod_cast hqp.pos : (0 : ℝ)<q) hle
  rw [log_exp] at hl
  linarith only [hl,hd.2.2.1]

/-- Completion at the smaller prime has a positive response of linear
size on EVERY original native head pair. No zero or phase hypothesis. -/
theorem pair_completion_response_bounds {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) :
    (3/8 : ℝ)*N≤SquarefreeVaughanLogSource.length u N-log q ∧
    SquarefreeVaughanLogSource.length u N-log q<log p ∧
    (27/200 : ℝ)*N≤SquarefreeVaughanLogSource.length u N-log p := by
  have hd := owners_data hp
  have hlogs := head_prime_logs hp hq
  have hqhi := pair_cofactor_log_upper hp hq hqp
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN
    (by linarith : 0<u) hU
  have hhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [hlo,hhi,hlogs.1,hlogs.2,hqhi,hd.2.2.2,hn]

/-- The count-one cofactor is NOT a vanished joined marked weight.
Its literal truncated divisor response is exactly the positive cutoff. -/
theorem ordinary_prime_boundary_eq {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) :
    VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-log q) p=
      SquarefreeVaughanLogSource.length u N-log q := by
  have h := pair_completion_response_bounds hu hU hN hp hq hqp
  have hb : 0≤SquarefreeVaughanLogSource.length u N-log q :=
    (by positivity : (0 : ℝ)≤(3/8 : ℝ)*N).trans h.1
  rw [VaughanLogAverage.riesz,(owners_data hp).1.sum_divisors]
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,Nat.cast_one,log_one,sub_zero,
    one_mul,ArithmeticFunction.moebius_apply_prime (owners_data hp).1,
    Int.cast_neg,neg_mul]
  rw [max_eq_right hb,max_eq_left (by linarith only [h.2.1])]
  ring

theorem ordinary_prime_boundary_positive {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) :
    0<VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-log q) p := by
  rw [ordinary_prime_boundary_eq hu hU hN hp hq hqp]
  exact (by positivity : (0 : ℝ)<(3/8 : ℝ)*N).trans_le
    (pair_completion_response_bounds hu hU hN hp hq hqp).1

/-- The original allocation is kept exactly. The new boundary amplitude
is at least the old head amplitude, before their common product phase. -/
theorem allocated_head_le_boundary {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) :
    0≤(SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q)) ∧
    (SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q))≤
      VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-log q) p := by
  have hb := pair_completion_response_bounds hu hU hN hp hq hqp
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  obtain ⟨hlp,hlq⟩ := head_prime_logs hp hq
  have hp0 : 0<log p := by linarith only [hlp,hn]
  have hq0 : 0<log q := by linarith only [hlq,hn]
  have hw := ownerWeight_bounds N
    (div_nonneg hq0.le (add_pos hp0 hq0).le)
    ((div_le_one (add_pos hp0 hq0)).mpr (by linarith))
  have hb0 : 0≤SquarefreeVaughanLogSource.length u N-log p :=
    (by positivity : (0 : ℝ)≤(27/200 : ℝ)*N).trans hb.2.2
  refine ⟨mul_nonneg hb0 hw.1,?_⟩
  rw [ordinary_prime_boundary_eq hu hU hN hp hq hqp]
  have hm := mul_le_mul_of_nonneg_left hw.2 hb0
  have hlo := log_le_log (by exact_mod_cast hqp.pos : (0 : ℝ)<q)
    (by exact_mod_cast (pair_cofactor_lt_owner (by omega : 64≤N) hp hq).le :
      (q : ℝ)≤p)
  linarith only [hm,hlo]

/-- Identical-label boundaries REINFORCE in the full complex phase.
This says nothing about cancellation between DIFFERENT prime pairs. -/
theorem same_label_boundary_norm_add {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (y : ℝ) (p q : ℕ) :
    ‖(a : ℂ)*character y p q+(b : ℂ)*character y p q‖=a+b := by
  rw [← add_mul,← Complex.ofReal_add,norm_mul,norm_character,mul_one,
    Complex.norm_real,Real.norm_of_nonneg (add_nonneg ha hb)]

/-- Apply the exact norm equality to the actual coefficient/allocation
of every original head pair, multiplied by any common nonnegative kernel.
It is impossible to cancel these two SAME-label channels against each
other. The original signed sum across labels is still the open target. -/
theorem native_boundary_reinforces_head {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) {w : ℝ} (hw : 0≤w) (y : ℝ) :
    ‖((w*VaughanLogAverage.riesz
        (SquarefreeVaughanLogSource.length u N-log q) p : ℝ) : ℂ)*character y p q+
      ((w*(SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q)) : ℝ) : ℂ)*character y p q‖=
    w*(VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-log q) p+
      (SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q))) := by
  have hb := ordinary_prime_boundary_positive hu hU hN hp hq hqp
  have hh := (allocated_head_le_boundary hu hU hN hp hq hqp).1
  have he := same_label_boundary_norm_add (mul_nonneg hw hb.le)
    (show 0≤w*(SquarefreeVaughanLogSource.length u N-log p)*
      ownerWeight N (log q/(log p+log q)) by simpa only [mul_assoc] using mul_nonneg hw hh)
    y p q
  exact he.trans (by ring)

/-- The same statement directly for `originalPair`, including its full
physical phase, factorial kernel, exact allocation and literal sieve.
The ordinary-prime completion boundary has no allocation factor. Nothing
is completed or bounded across different labels in this theorem. -/
theorem originalPair_boundary_norm_add {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) (y : ℝ) :
    let L := SquarefreeVaughanLogSource.length u N
    let w := u^(N+1)/(L*p)*
      (ZetaRieszSmoothOwnerDiscrepancy.radial N (log p+log q)/(q : ℝ)*
        ZetaRieszUnsignedDivisorError.sieve (ZetaRieszSmallTagNativeFloor.smallPrimes N) q)
    ‖((w*VaughanLogAverage.riesz (L-log q) p : ℝ) : ℂ)*character y p q+
      originalPair u y N p q‖=
      w*(VaughanLogAverage.riesz (L-log q) p+
        (L-log p)*ownerWeight N (log q/(log p+log q))) := by
  let L := SquarefreeVaughanLogSource.length u N
  let w := u^(N+1)/(L*p)*
    (ZetaRieszSmoothOwnerDiscrepancy.radial N (log p+log q)/(q : ℝ)*
      ZetaRieszUnsignedDivisorError.sieve (ZetaRieszSmallTagNativeFloor.smallPrimes N) q)
  change ‖((w*VaughanLogAverage.riesz (L-log q) p : ℝ) : ℂ)*character y p q+
      originalPair u y N p q‖=w*_
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hL : 0<L := (by positivity : (0 : ℝ)<(277/200 : ℝ)*N).trans_le
    (ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU)
  obtain ⟨hlp,hlq⟩ := head_prime_logs hp hq
  have hrad := (ZetaRieszSmoothOwnerDiscrepancy.radial_bounds N
    (by linarith only [hlp,hlq,hn] : 0≤log p+log q)).1
  have hu0 : 0≤u := by linarith only [hu]
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (owners_data hp).1.pos
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hqp.pos
  have hw : 0≤w := by
    unfold w ZetaRieszUnsignedDivisorError.sieve
    split_ifs <;> positivity
  have hr : rawAmount u N p q=w*(L-log p) := by
    unfold rawAmount w
    rw [if_pos hqp]
    ring
  have he := native_boundary_reinforces_head hu hU hN hp hq hqp hw y
  rw [originalPair,hr]
  rw [show ((w*(L-log p) : ℝ) : ℂ)*character y p q*
      (ownerWeight N (log q/(log p+log q)) : ℂ)=
      ((w*(L-log p)*ownerWeight N (log q/(log p+log q)) : ℝ) : ℂ)*
        character y p q by simp only [Complex.ofReal_mul]; ring]
  exact he

end RiemannGaussian.ZetaRieszOwnerCompletionAudit
