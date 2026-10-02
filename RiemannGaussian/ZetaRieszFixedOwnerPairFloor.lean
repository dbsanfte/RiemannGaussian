/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszInnerHingeGapPayment

/-!
# Join fixed-owner parity pairs without an ordering boundary

On a fixed actual largest prime, the literal owner allocation varies by
the total-log gap. Its whole matching price is geometrically small when
the paired gaps have the proved required rate. No negative-first or
ordered-share hypothesis is needed. Partner capacity, original funding
equality and the signed unmatched population remain arithmetic obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszFixedOwnerPairFloor
open ZetaRieszJointAllocation ZetaRieszOwnerMaximal ZetaRieszPrimeEndpoint
open ZetaRieszPairMatching ZetaRieszInnerHingeGapPayment ZetaRieszWideOwnerAudit
open ZetaRieszInnerHingeTransport

private theorem mass_le_one (n k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    mass n k x ≤ 1 := by
  have hs : mass n k x ≤ lowerMass n k x :=
    Finset.single_le_sum (fun j _ => mass_nonneg n j hx hx1)
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  exact hs.trans (lowerMass_bounds n k hx hx1).2

private theorem lowerMass_lipschitz (n k : ℕ) {x x' : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hx' : x' ∈ Set.Icc (0 : ℝ) 1) :
    |lowerMass n k x-lowerMass n k x'| ≤ (n : ℝ)*|x-x'| := by
  have hb v (hv : v ∈ Set.Icc (0 : ℝ) 1) :
      ‖-(n : ℝ)*mass (n-1) k v‖ ≤ n := by
    rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg n),
      abs_of_nonneg (mass_nonneg (n-1) k hv.1 hv.2)]
    exact (mul_le_mul_of_nonneg_left (mass_le_one (n-1) k hv.1 hv.2)
      (Nat.cast_nonneg n)).trans_eq (by ring)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v _ => (hasDerivAt_lowerMass n k v).hasDerivWithinAt) hb
      (convex_Icc (0 : ℝ) 1) hx' hx

/-- The exact original owner allocation is uniformly Lipschitz on its
entire share range, including both endpoints and every factorial order. -/
theorem ownerWeight_lipschitz {N : ℕ} (hN : 32 ≤ N) {x x' : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hx' : x' ∈ Set.Icc (0 : ℝ) 1) :
    |ownerWeight N x-ownerWeight N x'| ≤ 2*((N : ℝ)+1)*|x-x'| := by
  have he : ownerWeight N x-ownerWeight N x' =
      -(lowerMass (N+1) (13*N/32) x-lowerMass (N+1) (13*N/32) x')+
      (lowerMass (N+1) (N/5+1) x-lowerMass (N+1) (N/5+1) x') := by
    rw [ownerWeight,ownerWeight,ownerMass_eq_difference hN,ownerMass_eq_difference hN]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_neg]
  exact (add_le_add (lowerMass_lipschitz (N+1) (13*N/32) hx hx')
    (lowerMass_lipschitz (N+1) (N/5+1) hx hx')).trans_eq (by push_cast; ring)

/-- With an unchanged largest-prime logarithm, the owner share moves
only by the actual total-log gap. No order of the two labels is required. -/
theorem fixed_owner_share_gap {a T U : ℝ} (ha : 0 ≤ a)
    (hT : 1 ≤ T) (hU : 1 ≤ U) (haT : a ≤ T) :
    |(1-a/T)-(1-a/U)| ≤ |T-U| := by
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := by linarith
  have hprod : 0 < T*U := mul_pos hT0 hU0
  have he : (1-a/T)-(1-a/U)=(a/(T*U))*(T-U) := by
    field_simp
    ring
  have hb : a/(T*U) ≤ 1 := (div_le_one hprod).mpr (by
    nlinarith [mul_le_mul_of_nonneg_left hU hT0.le])
  rw [he,abs_mul,abs_of_nonneg (div_nonneg ha hprod.le)]
  exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans_eq (by ring)

/-- Keep both phases in the joined unallocated pair. Only the small
allocation DIFFERENCE is priced; no direction or sign is imposed. -/
theorem fixed_owner_pair_norm {N : ℕ} (hN : 32 ≤ N) {a T U : ℝ}
    (ha : 0 ≤ a) (hT : 1 ≤ T) (hU : 1 ≤ U) (haT : a ≤ T) (haU : a ≤ U)
    (F G : ℂ) :
    ‖(ownerWeight N (1-a/T) : ℂ)*F+(ownerWeight N (1-a/U) : ℂ)*G‖ ≤
      ‖F+G‖+2*((N : ℝ)+1)*|T-U| * ‖G‖ := by
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := by linarith
  have hx : 1-a/T ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [(div_le_one hT0).mpr haT],by linarith [div_nonneg ha hT0.le]⟩
  have hx' : 1-a/U ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [(div_le_one hU0).mpr haU],by linarith [div_nonneg ha hU0.le]⟩
  have hb := ownerWeight_bounds N hx.1 hx.2
  have hd := (ownerWeight_lipschitz hN hx hx').trans
    (mul_le_mul_of_nonneg_left (fixed_owner_share_gap ha hT hU haT) (by positivity))
  have he : (ownerWeight N (1-a/T) : ℂ)*F+(ownerWeight N (1-a/U) : ℂ)*G =
      (ownerWeight N (1-a/T) : ℂ)*(F+G)+
      ((ownerWeight N (1-a/U)-ownerWeight N (1-a/T) : ℝ) : ℂ)*G := by
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_nonneg hb.1,abs_sub_comm]
  exact add_le_add ((mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)).trans_eq (by ring))
    (mul_le_mul_of_nonneg_right hd (norm_nonneg _))

/-- The exact factorial majorant still has a strict gap after the
actual exp(-N/1000) allocation variation is included. -/
theorem owner_gap_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    u^(N+1)*exp (-(N : ℝ)/1000)*(131071/262144 : ℝ)⁻¹^N ≤
      radiusCeiling*exp (-(N : ℝ)/1250) := by
  have hb : radiusCeiling*(131071/262144 : ℝ)⁻¹ ≤ exp (1/8000 : ℝ) := by
    have h := add_one_le_exp (1/8000 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num [radiusCeiling] :
    (0 : ℝ) ≤ radiusCeiling*(131071/262144 : ℝ)⁻¹) hb N
  rw [← exp_nat_mul] at hp
  have hm := mul_le_mul_of_nonneg_right hp (exp_pos (-(N : ℝ)/1000)).le
  rw [← exp_add] at hm
  have hr : exp ((N : ℝ)*(1/8000)+(-(N : ℝ)/1000)) ≤ exp (-(N : ℝ)/1250) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ ≤ radiusCeiling^(N+1)*exp (-(N : ℝ)/1000)*(131071/262144 : ℝ)⁻¹^N := by gcongr
    _ = radiusCeiling*((radiusCeiling*(131071/262144 : ℝ)⁻¹)^N*
        exp (-(N : ℝ)/1000)) := by rw [mul_pow,pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm.trans hr) (by norm_num [radiusCeiling])

/-- Sum the small fixed-owner allocation difference over EVERY matched
label. This is an absolute geometric source payment, not a relative debit. -/
theorem total_owner_gap_variation (D : Finset ℕ) (w : ℕ → ℂ) {B L u : ℝ}
    (hB : 0 ≤ B) (hw : ∀ n ∈ D, ‖w n‖ ≤ B) (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) (y : ℝ) :
    u^(N+1)*(2*((N : ℝ)+1)*exp (-(N : ℝ)/1000))*
      (∑ n ∈ D, ‖w n*SquarefreeVaughanLogSource.coefficient L n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      2*radiusCeiling*B*((N : ℝ)+1)*exp (-(N : ℝ)/1250)*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have hs : (∑ n ∈ D, ‖w n*SquarefreeVaughanLogSource.coefficient L n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      B*(131071/262144 : ℝ)⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144) := by
    calc
      _ ≤ ∑ n ∈ D, B*(131071/262144 : ℝ)⁻¹^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
            (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
          convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
            (by norm_num : (0 : ℝ) < 131071/262144) using 1
          norm_num
        rw [norm_mul,norm_mul]
        have hc := mul_le_mul (hw n hn) (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
          (norm_nonneg _) hB
        exact (mul_le_mul hc hk (norm_nonneg _)
          (mul_nonneg hB (zetaMoebiusLogMajorant_nonneg n))).trans_eq (by ring)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (Summable.sum_le_tsum D (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
            (exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
          (mul_nonneg hB (by positivity))
  have hm : 0 ≤ zetaMoebiusLogMajorantMass (1+1/262144) :=
    tsum_nonneg (fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  calc
    _ ≤ u^(N+1)*(2*((N : ℝ)+1)*exp (-(N : ℝ)/1000))*
        (B*(131071/262144 : ℝ)⁻¹^N*zetaMoebiusLogMajorantMass (1+1/262144)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (u^(N+1)*exp (-(N : ℝ)/1000)*(131071/262144 : ℝ)⁻¹^N)*
        (2*((N : ℝ)+1)*B*zetaMoebiusLogMajorantMass (1+1/262144)) := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (owner_gap_source_rate hu hU N)
        (by positivity : 0 ≤ 2*((N : ℝ)+1)*B*zetaMoebiusLogMajorantMass (1+1/262144))
      exact h.trans_eq (by ring)

private theorem owner_log_bounds {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) :
    0 ≤ log (largestPrime n) ∧ log (largestPrime n) ≤ log n := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  exact ⟨log_natCast_nonneg _,log_le_log (by exact_mod_cast hprime.pos)
    (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hd)⟩

private theorem literal_owner_share {n : ℕ} (hs : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hln : 0 < log n) :
    log (n/largestPrime n : ℕ)/log n=1-log (largestPrime n)/log n := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.cast_div hd (by exact_mod_cast hprime.ne_zero),
    log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hprime.ne_zero),
    sub_div,div_self hln.ne']

private theorem owner_atom_eq (A : Finset ℕ) (N n : ℕ) (L y : ℝ) (w : ℕ → ℂ)
    (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card) (hA : largestPrime n ∈ A)
    (hln : 0 < log n) :
    w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      (ownerWeight N (1-log (largestPrime n)/log n) : ℂ)*
        (w n*SquarefreeVaughanLogSource.coefficient L n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hb := ZetaRieszOwnerVariation.single_prime_share A N hs hc hp hA
  have hw : ownerWeight N (log (n/largestPrime n : ℕ)/log n)=
      1-boundedShare (A ∩ {largestPrime n}) N n := by
    rw [hb]
    rfl
  rw [literal_owner_share hs hc hln] at hw
  rw [hw]
  simp only [residualCoefficient]
  push_cast
  ring

/-- The TOTAL original unique-owner pair cost is geometrically paid,
without ordered shares or negative-first orientation. Every pair retains
the same actual canonical owner and original funding coefficient. Native
existence/coverage and the original signed unmatched term remain open. -/
theorem global_fixed_owner_cost (A : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : separatedPairs E) {N : ℕ} (hN : 32 ≤ N) (Q : ℕ)
    (hQ : matchedVertices E ⊆ Finset.Icc 1 Q) (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u B : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hB : 0 ≤ B)
    (y : ℝ) (w : ℕ → ℂ) (hw : ∀ n ∈ matchedVertices E, ‖w n‖ ≤ B)
    (hD : matchedVertices E ⊆ literalWindow N)
    (hdata : ∀ n ∈ matchedVertices E,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hfix : ∀ e ∈ E, largestPrime e.1=largestPrime e.2)
    (hfund : ∀ e ∈ E, w e.1=w e.2)
    (hgap : ∀ e ∈ E, |log e.1-log e.2| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ e ∈ E, ∃ p p' q b b' : ℕ,
      p.Prime ∧ p'.Prime ∧ q.Prime ∧ Squarefree b ∧ Squarefree b' ∧
      2 ≤ b.primeFactors.card ∧ 2 ≤ b'.primeFactors.card ∧ ¬q ∣ b ∧ ¬q ∣ b' ∧
      ¬p ∣ q*b ∧ ¬p' ∣ q*b' ∧ μ b'= -(μ b) ∧ e.1=p*(q*b) ∧ e.2=p'*(q*b') ∧
      InnerHinge L p q b ∧ InnerHinge L p' q b') :
    u^(N+1)*(∑ e ∈ E,
      ‖w e.1*residualCoefficient (A ∩ {largestPrime e.1}) L N e.1*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.1+
        w e.2*residualCoefficient (A ∩ {largestPrime e.2}) L N e.2*
          zetaPrimeLogKernel N (3/2+Complex.I*y) e.2‖) ≤
      (168*radiusCeiling*B*(1+|y|)+
        2*radiusCeiling*B*zetaMoebiusLogMajorantMass (1+1/262144))*
          ((N : ℝ)+1)^3*exp (-(N : ℝ)/1250) := by
  let D := matchedVertices E
  let F := fun n => w n*SquarefreeVaughanLogSource.coefficient L n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let O := fun n => w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let δ := 2*((N : ℝ)+1)*exp (-(N : ℝ)/1000)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hv e (he : e ∈ E) : e.1 ∈ D ∧ e.2 ∈ D := by
    constructor <;> apply Finset.mem_biUnion.mpr <;>
      exact ⟨e,he,by simp [pairVertices]⟩
  have hlow n (hn : n ∈ D) : 1 ≤ log n := by
    have ht := (mem_literalWindow N n).mp (hD hn)
    have hNr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have ho n (hn : n ∈ D) :
      O n=(ownerWeight N (1-log (largestPrime n)/log n) : ℂ)*F n := by
    have hs := hdata n hn
    exact owner_atom_eq A N n L y w hs.1 hs.2.1 hs.2.2 (by linarith [hlow n hn])
  have hp e (he : e ∈ E) : ‖O e.1+O e.2‖ ≤ ‖F e.1+F e.2‖+δ*‖F e.2‖ := by
    have hs1 := hdata e.1 (hv e he).1
    have hs2 := hdata e.2 (hv e he).2
    have hb1 := owner_log_bounds hs1.1 hs1.2.1
    have hb2 := owner_log_bounds hs2.1 hs2.2.1
    have howner := hfix e he
    have ht := fixed_owner_pair_norm hN hb1.1 (hlow e.1 (hv e he).1)
      (hlow e.2 (hv e he).2) hb1.2 (by simpa only [howner] using hb2.2)
      (F e.1) (F e.2)
    rw [ho e.1 (hv e he).1,ho e.2 (hv e he).2,← howner]
    exact ht.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgap e he) (by positivity : 0 ≤ 2*((N : ℝ)+1)))
        (norm_nonneg (F e.2))))
  have hFsum : (∑ e ∈ E, ‖F e.2‖) ≤ ∑ n ∈ D, ‖F n‖ := by
    rw [sum_matchedVertices E hE]
    apply Finset.sum_le_sum
    intro e _
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hcost : (∑ e ∈ E, ‖O e.1+O e.2‖) ≤
      (∑ e ∈ E, ‖F e.1+F e.2‖)+δ*(∑ n ∈ D, ‖F n‖) := by
    calc
      _ ≤ ∑ e ∈ E, (‖F e.1+F e.2‖+δ*‖F e.2‖) := Finset.sum_le_sum hp
      _ = (∑ e ∈ E, ‖F e.1+F e.2‖)+δ*(∑ e ∈ E, ‖F e.2‖) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hFsum hδ)
  have hs := mul_le_mul_of_nonneg_left hcost (pow_nonneg hu (N+1))
  have hraw := global_literal_gap_cost E hE Q N hQ hlogQ hL hu hU hB y w hw
    hfund hgap hgeom
  have hvar := total_owner_gap_variation D w hB hw (by linarith : 0 < L) hu hU N y
  change u^(N+1)*(∑ e ∈ E, ‖F e.1+F e.2‖) ≤ _ at hraw
  change u^(N+1)*δ*(∑ n ∈ D, ‖F n‖) ≤ _ at hvar
  have hm : 0 ≤ zetaMoebiusLogMajorantMass (1+1/262144) :=
    tsum_nonneg (fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (exp_pos _).le)
  have hr : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  have hcub : ((N : ℝ)+1) ≤ ((N : ℝ)+1)^3 := by
    have hh : 0 ≤ (N : ℝ)*((N : ℝ)+1)*((N : ℝ)+2) := by positivity
    nlinarith only [hh]
  have hvarcap := mul_le_mul_of_nonneg_right hcub
    (by positivity : 0 ≤ 2*radiusCeiling*B*exp (-(N : ℝ)/1250)*
      zetaMoebiusLogMajorantMass (1+1/262144))
  change u^(N+1)*(∑ e ∈ E, ‖O e.1+O e.2‖) ≤ _
  rw [mul_add,← mul_assoc] at hs
  calc
    _ ≤ 168*radiusCeiling*B*(1+|y|)*((N : ℝ)+1)^3*exp (-(N : ℝ)/1250)+
        2*radiusCeiling*B*((N : ℝ)+1)*exp (-(N : ℝ)/1250)*
          zetaMoebiusLogMajorantMass (1+1/262144) := by linarith only [hs,hraw,hvar]
    _ ≤ _ := by nlinarith only [hvarcap]

/-- Remove a whole admissible fixed-owner matching from the ORIGINAL
signed carrier at geometric source cost. Both floor and ceiling inherit
this estimate. The unchanged unmatched term includes every original
allocation, funding and mask; no native coverage is asserted. -/
theorem matching_original_signed_error (A S : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : separatedPairs E) (hS : E ⊆ S ×ˢ S) {N : ℕ} (hN : 32 ≤ N) (Q : ℕ)
    (hQ : matchedVertices E ⊆ Finset.Icc 1 Q) (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u B : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hB : 0 < B)
    (y : ℝ) (w : ℕ → ℂ) (hw : ∀ n ∈ matchedVertices E, ‖w n‖ ≤ B)
    (hD : matchedVertices E ⊆ literalWindow N)
    (hdata : ∀ n ∈ matchedVertices E,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ largestPrime n ∈ A)
    (hfix : ∀ e ∈ E, largestPrime e.1=largestPrime e.2)
    (hfund : ∀ e ∈ E, w e.1=w e.2)
    (hgap : ∀ e ∈ E, |log e.1-log e.2| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ e ∈ E, ∃ p p' q b b' : ℕ,
      p.Prime ∧ p'.Prime ∧ q.Prime ∧ Squarefree b ∧ Squarefree b' ∧
      2 ≤ b.primeFactors.card ∧ 2 ≤ b'.primeFactors.card ∧ ¬q ∣ b ∧ ¬q ∣ b' ∧
      ¬p ∣ q*b ∧ ¬p' ∣ q*b' ∧ μ b'= -(μ b) ∧ e.1=p*(q*b) ∧ e.2=p'*(q*b') ∧
      InnerHinge L p q b ∧ InnerHinge L p' q b') :
    ‖(u : ℂ)^(N+1)*((∑ n ∈ S, w n*residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      ∑ n ∈ S\matchedVertices E, w n*residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
      (168*radiusCeiling*B*(1+|y|)+
        2*radiusCeiling*B*zetaMoebiusLogMajorantMass (1+1/262144))*
          ((N : ℝ)+1)^3*exp (-(N : ℝ)/1250)+
      B*((4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) := by
  let D := matchedVertices E
  let F := fun n => w n*residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let O := fun n => w n*residualCoefficient (A ∩ {largestPrime n}) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hDS : D ⊆ S := matchedVertices_subset hS
  have he : (∑ n ∈ S, F n)-(∑ n ∈ S\D, F n)=∑ n ∈ D, F n := by
    have hs := Finset.sum_sdiff (f := F) hDS
    rw [← hs]
    ring
  change ‖(u : ℂ)^(N+1)*((∑ n ∈ S, F n)-(∑ n ∈ S\D, F n))‖ ≤ _
  rw [he]
  have howner : ‖(u : ℂ)^(N+1)*∑ n ∈ D, O n‖ ≤
      u^(N+1)*(∑ e ∈ E, ‖O e.1+O e.2‖) := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu,sum_matchedVertices E hE]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hu (N+1))
  have hcost := global_fixed_owner_cost A E hE hN Q hQ hlogQ hL hu hU hB.le y w hw
    hD hdata hfix hfund hgap hgeom
  change u^(N+1)*(∑ e ∈ E, ‖O e.1+O e.2‖) ≤ _ at hcost
  have hnonowner := ZetaRieszOwnerPairFloor.weighted_nonowner_error A D w hB hw
    (by linarith : 0 < L) N hD y hu hU
  have heq : (u : ℂ)^(N+1)*∑ n ∈ D, F n =
      (u : ℂ)^(N+1)*∑ n ∈ D, O n+
      (u : ℂ)^(N+1)*∑ n ∈ D, w n*
        (residualCoefficient A L N n-residualCoefficient (A ∩ {largestPrime n}) L N n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    simp only [F,O,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (howner.trans hcost) hnonowner)

end RiemannGaussian.ZetaRieszFixedOwnerPairFloor
