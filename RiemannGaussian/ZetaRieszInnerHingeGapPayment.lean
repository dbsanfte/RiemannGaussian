/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerPairFloor
import RiemannGaussian.ZetaRieszSmoothOwnerDiscrepancy

/-!
# Total source cost of literal close inner-hinge pairs

The original unallocated opposite-parity atoms are joined first. Their
remaining difference is controlled by the actual total-log gap, with no
divisor-count allowance. The whole finite matching has a geometric cost
if its literal gaps are exponentially small. Neither native partner
existence nor a bound on signed unmatched/funding terms is assumed proved.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszInnerHingeGapPayment
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszJointAllocation
open ZetaRieszPrimeEndpoint ZetaRieszInnerHingeTransport ZetaRieszPairMatching

private def feature (y T : ℝ) : ℂ :=
  Complex.exp (-((1 : ℂ)+Complex.I*y)*(T : ℂ))

private theorem norm_feature (y T : ℝ) : ‖feature y T‖=exp (-T) := by
  simp [feature,Complex.norm_exp]

private theorem feature_deriv (y T : ℝ) :
    HasDerivAt (feature y) (-((1 : ℂ)+Complex.I*y)*feature y T) T := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := T)).const_mul (-((1 : ℂ)+Complex.I*y))).cexp
  change HasDerivAt (fun t : ℝ => Complex.exp (-((1 : ℂ)+Complex.I*y)*(t : ℂ)))
    (-((1 : ℂ)+Complex.I*y)*Complex.exp (-((1 : ℂ)+Complex.I*y)*(T : ℂ))) T
  simpa [Complex.ofRealCLM_apply,mul_comm] using h

private theorem feature_lipschitz (y T U : ℝ) :
    ‖feature y T-feature y U‖ ≤ (1+|y|)*exp (-min T U)*|T-U| := by
  have hc : ‖(1 : ℂ)+Complex.I*y‖ ≤ 1+|y| := by
    have h := norm_add_le (1 : ℂ) (Complex.I*y)
    simpa only [norm_one,norm_mul,Complex.norm_I,Complex.norm_real,
      Real.norm_eq_abs,one_mul] using h
  have hb v (hv : v ∈ Set.Icc (min T U) (max T U)) :
      ‖-((1 : ℂ)+Complex.I*y)*feature y v‖ ≤ (1+|y|)*exp (-min T U) := by
    rw [norm_mul,norm_neg,norm_feature]
    exact mul_le_mul hc (exp_le_exp.mpr (by linarith [hv.1]))
      (exp_pos _).le (by positivity)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v _ => (feature_deriv y v).hasDerivWithinAt) hb
      (convex_Icc (min T U) (max T U))
      (show U ∈ Set.Icc (min T U) (max T U) from ⟨min_le_right _ _,le_max_right _ _⟩)
      (show T ∈ Set.Icc (min T U) (max T U) from ⟨min_le_left _ _,le_max_left _ _⟩)

private def innerKernel (N : ℕ) (L c y T : ℝ) : ℂ :=
  (((T-c)*radial N T/L : ℝ) : ℂ)*feature y T

/-- The literal linear hinge and factorial radial mass have a coupled
gap bound. The full complex phase is retained until after subtraction. -/
theorem inner_kernel_gap (N : ℕ) {L c T U H : ℝ} (hL : 1 ≤ L)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hH : 0 ≤ H)
    (hτ' : |U-c| ≤ H) (y : ℝ) :
    ‖innerKernel N L c y T-innerKernel N L c y U‖ ≤
      radialCap N*(1+H*(2+|y|))*exp (-min T U)*|T-U| := by
  have hL0 : 0 < L := by linarith
  have hrT := radial_bounds N hT
  have hrU := radial_bounds N hU
  have hr0 := radialCap_nonneg N
  have hrd := radial_lipschitz N hT hU
  have ha : |(T-c)*radial N T/L-(U-c)*radial N U/L| ≤
      radialCap N*(1+H)*|T-U| := by
    have hh : |(T-c)*radial N T-(U-c)*radial N U| ≤
        radialCap N*(1+H)*|T-U| := by
      calc
        _ = |(T-U)*radial N T+(U-c)*(radial N T-radial N U)| := by congr 1; ring
        _ ≤ |T-U| * radialCap N+H*(radialCap N*|T-U|) := by
          apply (abs_add_le _ _).trans
          rw [abs_mul,abs_mul,abs_of_nonneg hrT.1]
          exact add_le_add (mul_le_mul_of_nonneg_left hrT.2 (abs_nonneg _))
            (mul_le_mul hτ' hrd (abs_nonneg _) hH)
        _ = _ := by ring
    rw [← sub_div,abs_div,abs_of_pos hL0]
    exact (div_le_div_of_nonneg_right hh hL0.le).trans
      ((div_le_self (by positivity) hL).trans_eq (by rfl))
  have hau : |(U-c)*radial N U/L| ≤ H*radialCap N := by
    rw [abs_div,abs_of_pos hL0,abs_mul,abs_of_nonneg hrU.1]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul hτ' hrU.2 hrU.1 hH) hL0.le).trans (div_le_self (by positivity) hL)
  have he : innerKernel N L c y T-innerKernel N L c y U =
      ((((T-c)*radial N T/L-(U-c)*radial N U/L : ℝ) : ℂ)*feature y T)+
      (((U-c)*radial N U/L : ℝ) : ℂ)*(feature y T-feature y U) := by
    unfold innerKernel
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,norm_feature]
  have hmin : exp (-T) ≤ exp (-min T U) := exp_le_exp.mpr (by linarith [min_le_left T U])
  have hfirst := mul_le_mul ha hmin (exp_pos _).le (by positivity)
  have hsecond := mul_le_mul hau (feature_lipschitz y T U) (norm_nonneg _) (by positivity)
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

/-- On the native radial range a unit-size log gap has a count-free
price against ONE original reciprocal label, before source scaling. -/
theorem inner_kernel_unit_gap (N : ℕ) {L c T U : ℝ} (hL : 1 ≤ L)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hc : 0 ≤ c)
    (hUc : c ≤ U) (hUH : U ≤ 3*((N : ℝ)+1))
    (hgap : |T-U| ≤ 1) (y : ℝ) :
    ‖innerKernel N L c y T-innerKernel N L c y U‖ ≤
      21*(1+|y|)*((N : ℝ)+1)*radialCap N*exp (-T)*|T-U| := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hr0 := radialCap_nonneg N
  have hh := inner_kernel_gap N hL hT hU (by positivity : 0 ≤ 3*((N : ℝ)+1))
    (by rw [abs_of_nonneg (sub_nonneg.mpr hUc)]; linarith) y
  have hcoef : 1+3*((N : ℝ)+1)*(2+|y|) ≤ 7*(1+|y|)*((N : ℝ)+1) := by
    nlinarith [abs_nonneg y,mul_nonneg hn (abs_nonneg y)]
  have hexp : exp (-min T U) ≤ 3*exp (-T) := by
    have hmin : T-1 ≤ min T U := le_min (by linarith) (by
      have ht := (abs_le.mp hgap).2
      linarith)
    calc
      _ ≤ exp (1-T) := exp_le_exp.mpr (by linarith)
      _ = exp 1*exp (-T) := by rw [← exp_add]; congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_right exp_one_lt_three.le (exp_pos _).le
  apply hh.trans
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left hcoef (radialCap_nonneg N)) hexp
    (exp_pos _).le (by positivity)
  exact (mul_le_mul_of_nonneg_right h (abs_nonneg _)).trans_eq (by ring)

private theorem boundedShare_empty (N n : ℕ) : boundedShare ∅ N n=0 := by
  simp [boundedShare,allocationShare,assignedAmplitude]

private theorem kernel_eq_phase (N : ℕ) (L y : ℝ) {p q b : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hb : 0 < b) :
    innerKernel N L (L+log q) y (log (p*(q*b) : ℕ)) =
      ((log (p*b : ℕ)-L : ℝ) : ℂ)*
        ZetaRieszSignedConvolution.phaseWeight ∅ L N y (q*b) p := by
  let T := log (p*(q*b) : ℕ)
  have hpb : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  have hqb : log (q*b : ℕ)=log q+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast hb.ne')]
  have hpqb : T=log p+log (q*b : ℕ) := by
    dsimp [T]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne')
      (by exact_mod_cast (mul_pos hq hb).ne')]
  have hlog : log (p*b : ℕ)-L=T-(L+log q) := by
    rw [hpb,hpqb,hqb]
    ring
  have he : ((exp (-T/2) : ℝ) : ℂ)*feature y T =
      zetaPrimeFeature (3/2+Complex.I*y) (p*(q*b)) := by
    rw [Complex.ofReal_exp,feature,zetaPrimeFeature,← Complex.exp_add]
    congr 1
    dsimp [T]
    push_cast
    ring
  change innerKernel N L (L+log q) y T = _
  rw [ZetaRieszSignedConvolution.phaseWeight,boundedShare_empty]
  simp only [sub_zero,one_mul]
  rw [zetaPrimeLogKernel,← he,hlog]
  unfold innerKernel
  simp only [radial]
  dsimp [T]
  push_cast
  rw [pow_succ]
  ring

/-- Exact ordinary unallocated atom on the ORIGINAL integer label.
This is used only to pay a joined close-pair difference, never a completion. -/
theorem unallocated_inner_atom {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : Squarefree b) (hc : 2 ≤ b.primeFactors.card)
    (hqb : ¬q ∣ b) (hpqb : ¬p ∣ q*b) {L : ℝ}
    (hi : InnerHinge L p q b) (N : ℕ) (y : ℝ) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*b))*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b)) =
        (μ b : ℂ)*innerKernel N L (L+log q) y (log (p*(q*b) : ℕ)) := by
  have h := literal_inner_atom hp hq hb hc hqb hpqb hi ∅ N y
  rw [kernel_eq_phase N L y hp.pos hq.pos (Nat.pos_of_ne_zero hb.ne_zero)]
  simpa only [residualCoefficient,boundedShare_empty,sub_zero,
    Complex.ofReal_one,one_mul,mul_assoc] using h

/-- Every opposite-parity pair on the same exact inner hinge has the
same count-free log-gap price, including replacements inside the cofactor.
All integer labels and both complex phases remain literal. -/
theorem opposite_inner_pair_gap {p p' q b b' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hq : q.Prime) (hb : Squarefree b) (hb' : Squarefree b')
    (hc : 2 ≤ b.primeFactors.card) (hc' : 2 ≤ b'.primeFactors.card)
    (hqb : ¬q ∣ b) (hqb' : ¬q ∣ b')
    (hpqb : ¬p ∣ q*b) (hp'qb' : ¬p' ∣ q*b') (hparity : μ b'= -(μ b))
    {L : ℝ} (hL : 1 ≤ L) (hi : InnerHinge L p q b) (hi' : InnerHinge L p' q b')
    (N : ℕ) (y : ℝ)
    (hU : log (p'*(q*b') : ℕ) ≤ 3*((N : ℝ)+1))
    (hgap : |log (p*(q*b) : ℕ)-log (p'*(q*b') : ℕ)| ≤ 1) :
    ‖SquarefreeVaughanLogSource.coefficient L (p*(q*b))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b))+
      SquarefreeVaughanLogSource.coefficient L (p'*(q*b'))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*(q*b'))‖ ≤
      21*(1+|y|)*((N : ℝ)+1)*radialCap N*((p*(q*b) : ℕ) : ℝ)⁻¹*
        |log (p*(q*b) : ℕ)-log (p'*(q*b') : ℕ)| := by
  rw [unallocated_inner_atom hp hq hb hc hqb hpqb hi,
    unallocated_inner_atom hp' hq hb' hc' hqb' hp'qb' hi',
    hparity]
  have he : (μ b : ℂ)*innerKernel N L (L+log q) y (log (p*(q*b) : ℕ))+
      ((-(μ b) : ℤ) : ℂ)*innerKernel N L (L+log q) y (log (p'*(q*b') : ℕ)) =
      (μ b : ℂ)*(innerKernel N L (L+log q) y (log (p*(q*b) : ℕ))-
        innerKernel N L (L+log q) y (log (p'*(q*b') : ℕ))) := by push_cast; ring
  rw [he,norm_mul]
  have hm : ‖(μ b : ℂ)‖ ≤ 1 := by
    have ht : |(μ b : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
    simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using ht
  apply (mul_le_of_le_one_left (norm_nonneg _) hm).trans
  have hlog (p : ℕ) (hp : p.Prime) (b : ℕ) (hb : b ≠ 0) :
      log (p*b : ℕ)-L=log (p*(q*b) : ℕ)-(L+log q) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hb),
      Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
        (by exact_mod_cast (mul_ne_zero hq.ne_zero hb)),
      Nat.cast_mul,log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hb)]
    ring
  have hiU : L+log q ≤ log (p'*(q*b') : ℕ) := by
    have ht := hi'.2.2.1
    rw [hlog p' hp' b' hb'.ne_zero] at ht
    linarith
  have hh := inner_kernel_unit_gap N hL (log_natCast_nonneg _) (log_natCast_nonneg _)
    (by linarith [log_natCast_nonneg q] : 0 ≤ L+log q) hiU hU hgap y
  have hn0 : (0 : ℝ)<(p*(q*b) : ℕ) := by exact_mod_cast mul_pos hp.pos (mul_pos hq.pos (Nat.pos_of_ne_zero hb.ne_zero))
  rw [exp_neg,exp_log hn0] at hh
  exact hh

/-- The original owner-shrinking / cofactor-insertion edge is one
instance of the same literal opposite-parity inequality. -/
theorem literal_pair_gap {p p' q r b : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hq : q.Prime) (hr : r.Prime) (hb : Squarefree b)
    (hc : 2 ≤ b.primeFactors.card) (hrb : ¬r ∣ b)
    (hqb : ¬q ∣ b) (hqr : ¬q ∣ r*b)
    (hpqb : ¬p ∣ q*b) (hp'qr : ¬p' ∣ q*(r*b))
    {L : ℝ} (hL : 1 ≤ L) (hi : InnerHinge L p q b) (hi' : InnerHinge L p' q (r*b))
    (N : ℕ) (y : ℝ)
    (hU : log (p'*(q*(r*b)) : ℕ) ≤ 3*((N : ℝ)+1))
    (hgap : |log (p*(q*b) : ℕ)-log (p'*(q*(r*b)) : ℕ)| ≤ 1) :
    ‖SquarefreeVaughanLogSource.coefficient L (p*(q*b))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b))+
      SquarefreeVaughanLogSource.coefficient L (p'*(q*(r*b)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*(q*(r*b)))‖ ≤
      21*(1+|y|)*((N : ℝ)+1)*radialCap N*((p*(q*b) : ℕ) : ℝ)⁻¹*
        |log (p*(q*b) : ℕ)-log (p'*(q*(r*b)) : ℕ)| := by
  have hsf : Squarefree (r*b) := Nat.squarefree_mul_iff.mpr
    ⟨hr.coprime_iff_not_dvd.mpr hrb,hr.squarefree,hb⟩
  have hcount : 2 ≤ (r*b).primeFactors.card := hc.trans
    (Finset.card_le_card (Nat.primeFactors_mono (dvd_mul_left b r) (mul_ne_zero hr.ne_zero hb.ne_zero)))
  exact opposite_inner_pair_gap hp hp' hq hb hsf hc hcount hqb hqr hpqb hp'qr
    (by rw [moebius_prime_mul_eq_not_dvd hr,if_neg hrb]) hL hi hi' N y hU hgap

/-- Replacing one genuine cofactor prime by two gives the same parity
flip, even when the common cofactor already contains the prime2. -/
theorem cofactor_split_parity {v r r' b : ℕ} (hv : v.Prime) (hr : r.Prime)
    (hr' : r'.Prime) (hvb : ¬v ∣ b) (hr'b : ¬r' ∣ b) (hrr'b : ¬r ∣ r'*b) :
    μ (r*(r'*b))= -(μ (v*b)) := by
  rw [moebius_prime_mul_eq_not_dvd hr,if_neg hrr'b,
    moebius_prime_mul_eq_not_dvd hr',if_neg hr'b,
    moebius_prime_mul_eq_not_dvd hv,if_neg hvb]

/-- The needed gap rate beats source growth at the unchanged radius.
This does not assert existence of any prime replacement or matching. -/
theorem small_gap_source_rate {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*2^(N+1)*exp (-(N : ℝ)/1000) ≤
      2*ZetaRieszWideOwnerAudit.radiusCeiling*exp (-(N : ℝ)/1250) := by
  have hb : 2*u ≤ exp (1/10000 : ℝ) := by
    have h := add_one_le_exp (1/10000 : ℝ)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) hb N
  rw [← exp_nat_mul] at hp
  have hr := mul_le_mul_of_nonneg_right hp (exp_pos (-(N : ℝ)/1000)).le
  rw [← exp_add] at hr
  have he : exp ((N : ℝ)*(1/10000)+(-(N : ℝ)/1000)) ≤ exp (-(N : ℝ)/1250) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ = 2*u*((2*u)^N*exp (-(N : ℝ)/1000)) := by rw [← mul_pow,pow_succ]; ring
    _ ≤ 2*u*exp (-(N : ℝ)/1250) := mul_le_mul_of_nonneg_left (hr.trans he) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le

/-- Sum all literal close pairs before pricing. The output has a strict
geometric saving at the original radius. Native matching existence and
same-funded membership remain explicit obligations, not analytic premises. -/
theorem global_literal_gap_cost (E : Finset (ℕ×ℕ)) (hE : separatedPairs E)
    (Q N : ℕ) (hQ : matchedVertices E ⊆ Finset.Icc 1 Q)
    (hlogQ : log Q ≤ 3*((N : ℝ)+1)) {L u B : ℝ} (hL : 1 ≤ L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hB : 0 ≤ B)
    (y : ℝ) (w : ℕ → ℂ) (hw : ∀ n ∈ matchedVertices E, ‖w n‖ ≤ B)
    (hfund : ∀ e ∈ E, w e.1=w e.2)
    (hgap : ∀ e ∈ E, |log e.1-log e.2| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ e ∈ E, ∃ p p' q b b' : ℕ,
      p.Prime ∧ p'.Prime ∧ q.Prime ∧ Squarefree b ∧ Squarefree b' ∧
      2 ≤ b.primeFactors.card ∧ 2 ≤ b'.primeFactors.card ∧ ¬q ∣ b ∧ ¬q ∣ b' ∧
      ¬p ∣ q*b ∧ ¬p' ∣ q*b' ∧ μ b'= -(μ b) ∧ e.1=p*(q*b) ∧ e.2=p'*(q*b') ∧
      InnerHinge L p q b ∧ InnerHinge L p' q b') :
    u^(N+1)*(∑ e ∈ E,
      ‖w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
        w e.2*SquarefreeVaughanLogSource.coefficient L e.2*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.2‖) ≤
      168*ZetaRieszWideOwnerAudit.radiusCeiling*B*(1+|y|)*((N : ℝ)+1)^3*
        exp (-(N : ℝ)/1250) := by
  let C := 21*B*(1+|y|)*((N : ℝ)+1)*radialCap N*exp (-(N : ℝ)/1000)
  have hr0 := radialCap_nonneg N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hv (e : ℕ×ℕ) (he : e ∈ E) : e.1 ∈ matchedVertices E ∧ e.2 ∈ matchedVertices E := by
    constructor <;> apply Finset.mem_biUnion.mpr <;>
      exact ⟨e,he,by simp [pairVertices]⟩
  have hη : exp (-(N : ℝ)/1000) ≤ 1 := exp_le_one_iff.mpr (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have hp e (he : e ∈ E) :
      ‖w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
        w e.2*SquarefreeVaughanLogSource.coefficient L e.2*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.2‖ ≤
        C*((e.1 : ℝ)⁻¹+(e.2 : ℝ)⁻¹) := by
    obtain ⟨p,p',q,b,b',hp,hp',hq,hb,hb',hc,hc',hqb,hqb',hpqb,hp'qb',hparity,he1,he2,hi,hi'⟩ := hgeom e he
    have hlogU : log e.2 ≤ 3*((N : ℝ)+1) := by
      have hn := (Finset.mem_Icc.mp (hQ (hv e he).2)).2
      exact (log_le_log (by
        have hn1 := (Finset.mem_Icc.mp (hQ (hv e he).2)).1
        exact_mod_cast hn1) (by exact_mod_cast hn)).trans hlogQ
    have hg := hgap e he
    have ht := opposite_inner_pair_gap hp hp' hq hb hb' hc hc' hqb hqb' hpqb hp'qb' hparity hL hi hi' N y
      (by simpa only [← he2] using hlogU) (by simpa only [← he1,← he2] using hg.trans hη)
    rw [← he1,← he2] at ht
    rw [← hfund e he,show w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
        zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
      w e.1*SquarefreeVaughanLogSource.coefficient L e.2*
        zetaPrimeLogKernel N (3/2+Complex.I*y) e.2 =
        w e.1*(SquarefreeVaughanLogSource.coefficient L e.1*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
          SquarefreeVaughanLogSource.coefficient L e.2*
            zetaPrimeLogKernel N (3/2+Complex.I*y) e.2) by ring,norm_mul]
    have hh := mul_le_mul (hw e.1 (hv e he).1) ht
      (norm_nonneg _) hB
    apply hh.trans
    calc
      _ ≤ B*(21*(1+|y|)*((N : ℝ)+1)*radialCap N*(e.1 : ℝ)⁻¹*
          exp (-(N : ℝ)/1000)) := by gcongr
      _ = C*(e.1 : ℝ)⁻¹ := by dsimp [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg e.2))) hC
  have hcost : (∑ e ∈ E,
      ‖w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
        w e.2*SquarefreeVaughanLogSource.coefficient L e.2*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.2‖) ≤ C*(1+log Q) := by
    calc
      _ ≤ ∑ e ∈ E, C*((e.1 : ℝ)⁻¹+(e.2 : ℝ)⁻¹) := Finset.sum_le_sum hp
      _ = C*∑ n ∈ matchedVertices E, (n : ℝ)⁻¹ := by
        rw [← Finset.mul_sum,sum_matchedVertices E hE]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg hQ (by intros; positivity)).trans
          (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
            using harmonic_le_one_add_log Q)) hC
  have hb := mul_le_mul_of_nonneg_left hcost (pow_nonneg hu (N+1))
  have hcap : 1+log Q ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have ht := mul_le_mul_of_nonneg_left hcap (mul_nonneg (pow_nonneg hu (N+1)) hC)
  calc
    _ ≤ u^(N+1)*C*(4*((N : ℝ)+1)) := hb.trans (by convert ht using 1; ring)
    _ = (84*B*(1+|y|)*((N : ℝ)+1)^3)*
        (u^(N+1)*2^(N+1)*exp (-(N : ℝ)/1000)) := by
      dsimp [C,radialCap]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (small_gap_source_rate hu hU N)
        (by positivity : 0 ≤ 84*B*(1+|y|)*((N : ℝ)+1)^3)
      exact hh.trans_eq (by ring)

/-- The total close-pair price is source-o(1), with fixed original height
and funding bound. This pays neither missing pairs nor their signed rest. -/
theorem tendsto_gap_price (C : ℝ) :
    Tendsto (fun N : ℕ => C*((N : ℝ)+1)^3*exp (-(N : ℝ)/1250)) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (exp_pos (-(1/1250 : ℝ)))
    (exp_lt_one_iff.mpr (by norm_num : -(1/1250 : ℝ) < 0))
  have hh := ht.const_mul C
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    rw [← exp_nat_mul]
    have he : exp ((N : ℝ)*(-(1/1250 : ℝ)))=exp (-(N : ℝ)/1250) := by
      congr 1
      ring
    rw [he]
    ring)

/-- A literal prime-replacement interval gives the exact required log
gap. This is an implication about actual partners, not a prime-gap theorem. -/
theorem replacement_interval_log_gap {p p' q r b : ℕ}
    (hp : 0 < p) (hp' : 0 < p') (hq : 0 < q) (hr : 0 < r) (hb : 0 < b)
    {η : ℝ} (hlo : (p : ℝ) ≤ (p' : ℝ)*r)
    (hhi : (p' : ℝ)*r ≤ (p : ℝ)*(1+η)) :
    |log (p*(q*b) : ℕ)-log (p'*(q*(r*b)) : ℕ)| ≤ η := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h0' : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hd : 1 ≤ ((p' : ℝ)*r)/p := (le_div_iff₀ h0).mpr (by simpa using hlo)
  have hu : ((p' : ℝ)*r)/p ≤ 1+η := (div_le_iff₀ h0).mpr (by simpa [mul_comm] using hhi)
  have he : log (p'*(q*(r*b)) : ℕ)-log (p*(q*b) : ℕ) =
      log (((p' : ℝ)*r)/p) := by
    simp only [Nat.cast_mul]
    rw [log_div (mul_pos h0' hr0).ne' h0.ne',log_mul h0'.ne' hr0.ne',
      log_mul h0'.ne' (mul_pos hq0 (mul_pos hr0 hb0)).ne',
      log_mul hq0.ne' (mul_pos hr0 hb0).ne',log_mul hr0.ne' hb0.ne',
      log_mul h0.ne' (mul_pos hq0 hb0).ne',log_mul hq0.ne' hb0.ne']
    ring
  have hnon : 0 ≤ log (((p' : ℝ)*r)/p) := log_nonneg hd
  have hlog := log_le_sub_one_of_pos (div_pos (mul_pos h0' hr0) h0)
  rw [abs_sub_comm,abs_of_nonneg (he ▸ hnon),he]
  linarith

private theorem ordered_integer_log_gap {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    (b : ℝ)⁻¹ ≤ log b-log a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast ha.trans hab
  have hs : (a : ℝ)+1 ≤ b := by exact_mod_cast Nat.add_one_le_iff.mpr hab
  have ht := one_sub_inv_le_log_of_pos (div_pos hb0 ha0)
  rw [inv_div,log_div hb0.ne' ha0.ne'] at ht
  have hd : (b : ℝ)⁻¹ ≤ 1-(a : ℝ)/b := by
    calc
      _ = 1/(b : ℝ) := by simp only [one_div]
      _ ≤ ((b : ℝ)-a)/b := div_le_div_of_nonneg_right (by linarith) hb0.le
      _ = _ := by field_simp
  exact hd.trans ht

/-- A distinct local integer replacement has a real granularity cost.
Bin occupancy cannot remove the spacing of the replaced integer factors. -/
theorem integer_log_gap_lower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    (max (a : ℝ) b)⁻¹ ≤ |log a-log b| := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hmax : max (a : ℝ) b=b := max_eq_right (by exact_mod_cast hab.le)
    rw [hmax]
    exact (ordered_integer_log_gap ha hab).trans (by
      simpa only [abs_sub_comm] using le_abs_self (log b-log a))
  · have hmax : max (a : ℝ) b=a := max_eq_left (by exact_mod_cast hba.le)
    rw [hmax]
    exact (ordered_integer_log_gap hb hba).trans (le_abs_self (log a-log b))

/-- The explicit geometric gap target requires a linearly large local
logarithmic factor. This is a necessity, not an existence or capacity result. -/
theorem small_gap_forces_large_local_factor {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (N : ℕ) (hgap : |log a-log b| ≤ exp (-(N : ℝ)/1000)) :
    (N : ℝ)/1000 ≤ log (max (a : ℝ) b) := by
  have hm : (0 : ℝ) < max (a : ℝ) b :=
    (by exact_mod_cast ha : (0 : ℝ) < a).trans_le (le_max_left _ _)
  have hlog := log_le_log (inv_pos.mpr hm)
    ((integer_log_gap_lower ha hb hne).trans hgap)
  rw [log_inv,log_exp] at hlog
  linarith

/-- A whole ORIGINAL-carrier floor with all close-pair costs paid by
explicit geometric rates. The original unmatched/funding contribution stays
signed. Coverage, equal funding and actual prime partners are not supplied
by this theorem or by the many-bin condition. -/
theorem matching_original_floor_of_small_gaps (A S : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : separatedPairs E) (hS : E ⊆ S ×ˢ S)
    {N : ℕ} (hN : 32 ≤ N) (Q : ℕ)
    (hQ : matchedVertices E ⊆ Finset.Icc 1 Q)
    (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u B : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hB : 0 < B)
    (y : ℝ) (w : ℕ → ℂ) (hw : ∀ n ∈ matchedVertices E, ‖w n‖ ≤ B)
    (hD : matchedVertices E ⊆ literalWindow N)
    (hdata : ∀ n ∈ matchedVertices E,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hx : ∀ e ∈ E,
      (3/8 : ℝ) ≤ log (e.1/largestPrime e.1 : ℕ)/log e.1 ∧
      log (e.1/largestPrime e.1 : ℕ)/log e.1 ≤
        log (e.2/largestPrime e.2 : ℕ)/log e.2 ∧
      log (e.2/largestPrime e.2 : ℕ)/log e.2 ≤ 1)
    (hF : ∀ e ∈ E, (w e.1*SquarefreeVaughanLogSource.coefficient L e.1*
      zetaPrimeLogKernel N (3/2+Complex.I*y) e.1).re ≤ 0)
    (hfund : ∀ e ∈ E, w e.1=w e.2)
    (hgap : ∀ e ∈ E, |log e.1-log e.2| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ e ∈ E, ∃ p p' q b b' : ℕ,
      p.Prime ∧ p'.Prime ∧ q.Prime ∧ Squarefree b ∧ Squarefree b' ∧
      2 ≤ b.primeFactors.card ∧ 2 ≤ b'.primeFactors.card ∧ ¬q ∣ b ∧ ¬q ∣ b' ∧
      ¬p ∣ q*b ∧ ¬p' ∣ q*b' ∧ μ b'= -(μ b) ∧ e.1=p*(q*b) ∧ e.2=p'*(q*b') ∧
      InnerHinge L p q b ∧ InnerHinge L p' q b') :
    u^(N+1)*(∑ n ∈ S\matchedVertices E,
      w n*residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      168*ZetaRieszWideOwnerAudit.radiusCeiling*B*(1+|y|)*((N : ℝ)+1)^3*
        exp (-(N : ℝ)/1250)-
      (2*ZetaRieszWideOwnerAudit.radiusCeiling*B*exp (-(N : ℝ)/50))*
        zetaMoebiusLogMajorantMass (1+1/262144)-
      B*((4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) ≤
      u^(N+1)*(∑ n ∈ S, w n*residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hf := ZetaRieszOwnerPairFloor.matching_original_floor A S E hE hS hN
    (by linarith : 0 < L) hu hU hB y w hw hD hdata hx hF
  have hg := global_literal_gap_cost E hE Q N hQ hlogQ hL hu hU hB.le y w hw
    hfund hgap hgeom
  linarith only [hf,hg]

end RiemannGaussian.ZetaRieszInnerHingeGapPayment
