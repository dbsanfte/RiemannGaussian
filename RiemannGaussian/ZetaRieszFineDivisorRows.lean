/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointOwnerEnvelope

/-!
# Signed full-window rows down to the fine unsigned-divisor threshold

A tighter summable outer tilt pays the ORIGINAL squarefree counting error
on unsigned legs above exp(N/1000). The exact owner allocation and physical
phase are retained. The resulting signed full-window row payment is for
literal incidences, not a prime-density completion or a numerical floor.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszFineDivisorRows
open ZetaRieszUnsignedDivisorError ZetaRieszSignedConvolution
open ZetaRieszSaturatedRowFloor ZetaRieszOwnerMaximal ZetaRieszFreeRadialRows
open ZetaRieszPrimeCountFrequency

/-- The finer literal unsigned-divisor threshold. -/
def unsignedSlope : ℝ := 1/1000

/-- A summable all-count tilt small enough to leave a strict source saving. -/
def sigma : ℝ := 65537/65536

/-- The explicit comparison and lattice saving, after source normalization. -/
def comparisonRate : ℝ := exp (-(1/10000 : ℝ))

theorem comparisonRate_bounds : 0 < comparisonRate ∧ comparisonRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

private theorem fine_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {M X : ℕ} (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (N : ℕ) (hlarge : exp ((N : ℝ)/1000) ≤ M)
    (a : ℕ → ℝ) (y c A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ d ∈ Finset.Ioc M X, |a d| ≤ A) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X a y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCost*3^S.card*exp (-(N : ℝ)/4000)*
          ((3+|y|)*A+∑ d ∈ Finset.Ico (M+1) X, |a d-a (d+1)|) := by
  have hC := countingCost_pos.le
  dsimp only
  have hactive k (_ : k ∈ Finset.Icc 1 X)
      (hz : ZetaRieszCofactorDiscrepancy.shellWeight M X a y c k ≠
        ZetaRieszCofactorDiscrepancy.shellWeight M X a y c (k+1)) : M ≤ k := by
    by_contra hn
    have hkM : k < M := lt_of_not_ge hn
    simp [ZetaRieszCofactorDiscrepancy.shellWeight,show ¬M<k by omega,
      show ¬M<k+1 by omega] at hz
  have hb := weighted_error_exponential S hS X N
    (ZetaRieszCofactorDiscrepancy.shellWeight M X a y c) (1/1000)
    (by simp [ZetaRieszCofactorDiscrepancy.shellWeight])
    (fun k hk hz => by
      have hMk : (M : ℝ) ≤ k := by exact_mod_cast hactive k hk hz
      simpa only [div_mul_eq_mul_div,one_mul] using hlarge.trans hMk)
  have he : -((1/1000 : ℝ)*N)/4=-(N : ℝ)/4000 := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (ZetaRieszCofactorDiscrepancy.shellWeight_variation hM hMX hXM a y c A hA ha)
    (by positivity : 0 ≤ countingCost*3^S.card*exp (-(N : ℝ)/4000)))

private theorem fine_owned_shell_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {N M X : ℕ} (hN : 32 ≤ N) (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/1000) ≤ M) {P c : ℝ} (hP : 0 ≤ P)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ c+log d)
    (hPT : ∀ d ∈ Finset.Icc (M+1) X, P ≤ c+log d) (y : ℝ) :
    let w := ZetaRieszCofactorDiscrepancy.shellWeight M X (ownedAmplitude N P c) y c
    |(∑ d ∈ Finset.Icc 1 X, w d*sieve S d)-
      density S*(∑ d ∈ Finset.Icc 1 X, w d)| ≤
        countingCost*3^S.card*exp (-(N : ℝ)/4000)*
          (((N : ℝ)+7+|y|)*radialEnvelope N) := by
  have hb := fine_shell_error S hS hM hMX hXM N hlarge (ownedAmplitude N P c) y c
    (radialEnvelope N) (radialEnvelope_pos N).le
    (fun d hd => ownedAmplitude_bound N hP
      (hT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩))
      (hPT d (Finset.mem_Icc.mpr ⟨by have := Finset.mem_Ioc.mp hd; omega,(Finset.mem_Ioc.mp hd).2⟩)))
  apply hb.trans
  have hC := countingCost_pos.le
  have ht := ownedAmplitude_variation hN hM hMX hXM hP hT hPT
  calc
    _ ≤ countingCost*3^S.card*exp (-(N : ℝ)/4000)*
        ((3+|y|)*radialEnvelope N+((N : ℝ)+4)*radialEnvelope N) :=
      mul_le_mul_of_nonneg_left (add_le_add_right ht ((3+|y|)*radialEnvelope N))
        (by positivity)
    _ = _ := by ring

private theorem fine_discrepancy_bound {N M X p b : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hlarge : exp ((N : ℝ)/1000) ≤ M) {L : ℝ} (hL : 0 < L)
    (hp : 0 < p) (hb : 0 < b) (hPL : log p ≤ L)
    (hT : ∀ d ∈ Finset.Icc (M+1) X, 1 ≤ log (p*b : ℕ)+log d)
    (y : ℝ) :
    |ownedShellDiscrepancy N L y p b M X| ≤
      (countingCost*exp (-(N : ℝ)/4000)*
        (((N : ℝ)+7+|y|)*radialEnvelope N))*
          (3^(p*b).primeFactors.card/(p*b : ℕ)) := by
  have hpb : (0 : ℝ)<(p*b : ℕ) := by exact_mod_cast Nat.mul_pos hp hb
  have hlog : log (p*b : ℕ) = log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hb.ne')]
  have hPT d (_ : d ∈ Finset.Icc (M+1) X) : log p ≤ log (p*b : ℕ)+log d := by
    rw [hlog]
    linarith [log_natCast_nonneg b,log_natCast_nonneg d]
  have he := fine_owned_shell_error (p*b).primeFactors
    (fun _ h => Nat.prime_of_mem_primeFactors h) hN hM hMX hXM hlarge
    (log_natCast_nonneg p) hT hPT y
  have hh := pairHinge_bounds L p b
  have hm : |(μ b : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
  have hc : |(μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ))| ≤ 1/(p*b : ℕ) := by
    rw [abs_div,abs_mul,abs_of_nonneg hh.1,abs_of_pos (mul_pos hL hpb)]
    apply (div_le_iff₀ (mul_pos hL hpb)).mpr
    have hx := mul_le_mul_of_nonneg_right hm hh.1
    have heq : 1/(p*b : ℕ)*(L*(p*b : ℕ))=L := by field_simp
    rw [heq]
    exact hx.trans (by simpa using hh.2.trans hPL)
  rw [ownedShellDiscrepancy,abs_mul]
  exact (mul_le_mul hc he (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem fine_outer_cost_bound (B : Finset (ℕ×ℕ)) (N : ℕ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N) :
    (∑ pb ∈ B, (3 : ℝ)^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) ≤
      3*exp ((203/6553600 : ℝ)*N)*
        ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) := by
  let σ : ℝ := 65537/65536
  let P := B.image Prod.fst
  let Q := B.image Prod.snd
  have hs : 1 < σ := by norm_num [σ]
  have hQ : ∀ b ∈ Q, Squarefree b := by
    intro b hb
    obtain ⟨pb,hpb,rfl⟩ := Finset.mem_image.mp hb
    exact (hB pb hpb).2.1
  have hBP : B ⊆ P.product Q := by
    intro pb hpb
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨pb,hpb,rfl⟩,
      Finset.mem_image.mpr ⟨pb,hpb,rfl⟩⟩
  have hterm pb (hpb : pb ∈ B) :
      (3 : ℝ)^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ) ≤
        3*exp ((203/6553600 : ℝ)*N)*
          (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))) := by
    obtain ⟨hp,hb,hpd⟩ := hB pb hpb
    have hpn : pb.1 ∉ pb.2.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
    have hc : (pb.1*pb.2).primeFactors.card = pb.2.primeFactors.card+1 := by
      rw [Nat.primeFactors_mul hp.ne_zero hb.ne_zero,hp.primeFactors,
        Finset.singleton_union,Finset.card_insert_of_notMem hpn]
    have hpn0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by
      exact_mod_cast Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hb.ne_zero)
    have hl : log (pb.1*pb.2 : ℕ) = log pb.1+log pb.2 := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hb.ne_zero)]
    have he : exp ((1/65536 : ℝ)*log (pb.1*pb.2 : ℕ))*
        (exp (-σ*log pb.1)*exp (-σ*log pb.2))=((pb.1*pb.2 : ℕ) : ℝ)⁻¹ := by
      rw [← exp_add,← exp_add,hl]
      have hx : (1/65536 : ℝ)*(log pb.1+log pb.2)+(-σ*log pb.1+-σ*log pb.2) =
          -(log pb.1+log pb.2) := by dsimp [σ]; ring
      rw [hx,← hl,exp_neg,exp_log hpn0]
    have hle : exp ((1/65536 : ℝ)*log (pb.1*pb.2 : ℕ)) ≤
        exp ((203/6553600 : ℝ)*N) := by
      apply exp_le_exp.mpr
      linarith [hlog pb hpb]
    rw [hc,pow_succ,div_eq_mul_inv,← he]
    nlinarith [mul_le_mul_of_nonneg_left hle
      (by positivity : 0 ≤ (3 : ℝ)^pb.2.primeFactors.card*
        (exp (-σ*log pb.1)*exp (-σ*log pb.2)))]
  calc
    _ ≤ ∑ pb ∈ B, 3*exp ((203/6553600 : ℝ)*N)*
        (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ pb ∈ P.product Q, 3*exp ((203/6553600 : ℝ)*N)*
        (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBP (by intros; positivity)
    _ = 3*exp ((203/6553600 : ℝ)*N)*
        ((∑ p ∈ P, exp (-σ*log p))*(∑ b ∈ Q, (3 : ℝ)^b.primeFactors.card*exp (-σ*log b))) := by
      rw [Finset.product_eq_sprod,Finset.sum_product P Q (fun pb => 3*exp ((203/6553600 : ℝ)*N)*
        (exp (-σ*log pb.1)*((3 : ℝ)^pb.2.primeFactors.card*exp (-σ*log pb.2))))]
      simp only [Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ _ := by
      have hp := (summable_zetaPrimeExpWeight hs).sum_le_tsum P
        (fun _ _ => (exp_pos _).le)
      have hq := ZetaRieszPrimeCountMass.squarefree_count_mass_le_exp Q hQ hs
        (by norm_num : (0 : ℝ)≤3)
      calc
        _ ≤ 3*exp ((203/6553600 : ℝ)*N)*
            (ZetaRieszPrimeCountMass.countMass σ*exp (3*ZetaRieszPrimeCountMass.countMass σ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hp hq (Finset.sum_nonneg (by intros; positivity))
              (ZetaRieszPrimeCountMass.countMass_nonneg σ))
            (by positivity : 0 ≤ 3*exp ((203/6553600 : ℝ)*N))
        _ = _ := by ring



private def fineRate (u : ℝ) : ℝ := 2*u*exp (-(7177/32768000 : ℝ))

private theorem fineRate_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    0 ≤ fineRate u ∧ fineRate u ≤ comparisonRate := by
  refine ⟨by unfold fineRate; positivity,?_⟩
  have hlog : log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ≤ 1/10000 := by
    have h := log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ)<2*ZetaRieszWideOwnerAudit.radiusCeiling)
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h
  calc
    fineRate u ≤ 2*ZetaRieszWideOwnerAudit.radiusCeiling*exp (-(7177/32768000 : ℝ)) := by
      unfold fineRate; gcongr
    _ = exp (log (2*ZetaRieszWideOwnerAudit.radiusCeiling)-(7177/32768000 : ℝ)) := by
      rw [exp_sub,exp_log (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]),exp_neg]
      ring
    _ ≤ comparisonRate := by unfold comparisonRate; apply exp_le_exp.mpr; linarith

/-- Every original prime-count intersection is included in this finite
constant; it does not depend on order, owner, height or count cutoff. -/
def fineErrorConstant : ℝ :=
  6*ZetaRieszWideOwnerAudit.radiusCeiling*countingCost*
    ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))

theorem fineErrorConstant_nonneg : 0 ≤ fineErrorConstant := by
  have hc := countingCost_pos.le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)
  unfold fineErrorConstant ZetaRieszWideOwnerAudit.radiusCeiling
  positivity

theorem source_scaled_fine_shell_error (B : Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ℕ×ℕ → ℕ) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hB : ∀ pb ∈ B, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ pb ∈ B, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ pb ∈ B, 0 < M pb)
    (hMX : ∀ pb ∈ B, M pb < X pb)
    (hXM : ∀ pb ∈ B, X pb ≤ 2*M pb)
    (hlarge : ∀ pb ∈ B, exp ((N : ℝ)/1000) ≤ M pb)
    (hPL : ∀ pb ∈ B, log pb.1 ≤ L)
    (hT : ∀ pb ∈ B, ∀ d ∈ Finset.Icc (M pb+1) (X pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      fineErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*comparisonRate^N := by
  have hc := countingCost_pos.le
  have hm := ZetaRieszPrimeCountMass.countMass_nonneg (65537/65536)
  let H := countingCost*exp (-(N : ℝ)/4000)*(((N : ℝ)+7+|y|)*radialEnvelope N)
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_pos N]
  have he : |∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      H*(3*exp ((203/6553600 : ℝ)*N)*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536))) := by
    calc
      _ ≤ ∑ pb ∈ B, |ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pb ∈ B, H*(3^(pb.1*pb.2).primeFactors.card/(pb.1*pb.2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro pb hpb
        exact fine_discrepancy_bound hN (hM pb hpb) (hMX pb hpb) (hXM pb hpb)
          (hlarge pb hpb) hL (hB pb hpb).1.pos
          (Nat.pos_of_ne_zero (hB pb hpb).2.1.ne_zero) (hPL pb hpb) (hT pb hpb) y
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (fine_outer_cost_bound B N hB hlog) hH
  have hex : exp (-(N : ℝ)/4000)*exp ((203/6553600 : ℝ)*N) =
      exp (-(7177/32768000 : ℝ))^N := by
    rw [← exp_add,← exp_nat_mul]
    congr 1
    ring
  have hnorm : |u^(N+1)*∑ pb ∈ B, ownedShellDiscrepancy N L y pb.1 pb.2 (M pb) (X pb)| ≤
      (6*u*countingCost*ZetaRieszPrimeCountMass.countMass (65537/65536)*
        exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(fineRate u)^N := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
    apply (mul_le_mul_of_nonneg_left he (pow_nonneg hu _)).trans_eq
    dsimp [H,radialEnvelope,fineRate]
    rw [mul_pow,mul_pow,pow_succ,pow_succ]
    have heq := hex
    calc
      _ = (6*u*countingCost*ZetaRieszPrimeCountMass.countMass (65537/65536)*
          exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)))*
          ((N : ℝ)+1)*((N : ℝ)+7+|y|)*(2^N*u^N)*
            (exp (-(N : ℝ)/4000)*exp ((203/6553600 : ℝ)*N)) := by ring
      _ = _ := by rw [heq]; ring
  apply hnorm.trans
  have hr := fineRate_bounds hu hU
  have hconst : 6*u*countingCost*ZetaRieszPrimeCountMass.countMass (65537/65536)*
      exp (3*ZetaRieszPrimeCountMass.countMass (65537/65536)) ≤ fineErrorConstant := by
    unfold fineErrorConstant
    gcongr
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
    (pow_le_pow_left₀ hr.1 hr.2 N) (pow_nonneg hr.1 N)
    (by positivity [fineErrorConstant_nonneg,comparisonRate_bounds.1])

/-- All radial shells may be joined before taking the signed comparison
error. A polynomial number of shells leaves the strict geometric saving.
The masks selecting each outer pair and each shell remain arbitrary. -/
theorem source_scaled_fine_shells_error {ι : Type*} (I : Finset ι)
    (B : ι → Finset (ℕ×ℕ)) {N : ℕ} (hN : 32 ≤ N)
    (M X : ι → ℕ×ℕ → ℕ) {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hI : I.card ≤ N+1)
    (hB : ∀ i ∈ I, ∀ pb ∈ B i, pb.1.Prime ∧ Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2)
    (hlog : ∀ i ∈ I, ∀ pb ∈ B i, log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N)
    (hM : ∀ i ∈ I, ∀ pb ∈ B i, 0 < M i pb)
    (hMX : ∀ i ∈ I, ∀ pb ∈ B i, M i pb < X i pb)
    (hXM : ∀ i ∈ I, ∀ pb ∈ B i, X i pb ≤ 2*M i pb)
    (hlarge : ∀ i ∈ I, ∀ pb ∈ B i, exp ((N : ℝ)/1000) ≤ M i pb)
    (hPL : ∀ i ∈ I, ∀ pb ∈ B i, log pb.1 ≤ L)
    (hT : ∀ i ∈ I, ∀ pb ∈ B i, ∀ d ∈ Finset.Icc (M i pb+1) (X i pb),
      1 ≤ log (pb.1*pb.2 : ℕ)+log d) :
    |u^(N+1)*∑ i ∈ I, ∑ pb ∈ B i,
      ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| ≤
      fineErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N := by
  let C := fineErrorConstant*((N : ℝ)+1)*((N : ℝ)+7+|y|)*comparisonRate^N
  have hC : 0 ≤ C := by
    dsimp [C]; positivity [fineErrorConstant_nonneg,comparisonRate_bounds.1]
  calc
    _ ≤ ∑ i ∈ I, |u^(N+1)*∑ pb ∈ B i,
        ownedShellDiscrepancy N L y pb.1 pb.2 (M i pb) (X i pb)| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, C := Finset.sum_le_sum (fun i hi =>
      source_scaled_fine_shell_error (B i) hN (M i) (X i) hL hu hU y
        (hB i hi) (hlog i hi) (hM i hi) (hMX i hi) (hXM i hi)
        (hlarge i hi) (hPL i hi) (hT i hi))
    _ = (I.card : ℝ)*C := by simp
    _ ≤ ((N : ℝ)+1)*C := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hC
    _ ≤ _ := by
      have hp : (N : ℝ)+7+|y| ≤ (8+|y|)*((N : ℝ)+1) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
      have hh := mul_le_mul_of_nonneg_left hp
        (by positivity [fineErrorConstant_nonneg,comparisonRate_bounds.1] :
          0 ≤ fineErrorConstant*((N : ℝ)+1)^2*comparisonRate^N)
      dsimp [C]
      nlinarith only [hh]



/-- A full original radial interval, before either boundary is clipped.
The outer cutoff 1949/1000 replaces the previous 37/20 eligibility. -/
def lower (N p b : ℕ) : ℕ :=
  ⌈exp ((39/20 : ℝ)*N-log (p*b : ℕ))⌉₊

/-- The rounded original upper core-window endpoint. -/
def upper (N p b : ℕ) : ℕ :=
  ⌊exp ((203/100 : ℝ)*N-log (p*b : ℕ))⌋₊

/-- All physical outer rows eligible for the fine-threshold signed
payment. Additional masks are not approximated or completed. -/
def fineRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  ((ZetaRieszAnnulusJoint.intermediatePrimes u N).product
    (Finset.Icc 2 ⌊exp ((203/100 : ℝ)*N)⌋₊)).filter fun pb =>
      Squarefree pb.2 ∧ ¬pb.1 ∣ pb.2 ∧
      (∀ q ∈ pb.2.primeFactors, q < pb.1) ∧
      pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≠ 0 ∧
      log (pb.1*pb.2 : ℕ) ≤ (1949/1000 : ℝ)*N ∧
      log pb.1 < (243/200 : ℝ)*N ∧
      (203/100 : ℝ)*N ≤ log pb.1+SquarefreeVaughanLogSource.length u N ∧
      lower N pb.1 pb.2 ≤ upper N pb.1 pb.2

private theorem lower_pos (N p b : ℕ) : 0 < lower N p b :=
  Nat.ceil_pos.mpr (exp_pos _)

/-- The exact unsigned-log lower threshold is a consequence of the
full-window eligibility, not an assumption on a completed row. -/
theorem fine_row_large {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (h : pb ∈ fineRows u N) :
    exp ((N : ℝ)/1000) ≤ lower N pb.1 pb.2 := by
  have hc := (Finset.mem_filter.mp h).2.2.2.2.2.1
  apply (exp_le_exp.mpr ?_).trans (Nat.le_ceil _)
  linarith

/-- Every fine row retains the literal saturation, owner, core-window
and physical-prime geometry. -/
theorem fine_row_geometry {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (h : pb ∈ fineRows u N) :
    RowGeometry N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
      (lower N pb.1 pb.2) (upper N pb.1 pb.2) := by
  obtain ⟨hprod,hs,hpd,hmax,ha,hc,hP,hsat,hlu⟩ := Finset.mem_filter.mp h
  obtain ⟨hp,hb⟩ := Finset.mem_product.mp hprod
  have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp
  have hp0 : (0 : ℝ)<pb.1 := by exact_mod_cast hp'.1.pos
  have hb0 : (0 : ℝ)<pb.2 := by
    have hbpos : 0 < pb.2 := by have := (Finset.mem_Icc.mp hb).1; omega
    exact_mod_cast hbpos
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul hp0.ne' hb0.ne']
  have hM := lower_pos N pb.1 pb.2
  have hX := hM.trans_le hlu
  have hlo : (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ) ≤ log (lower N pb.1 pb.2) := by
    simpa only [log_exp,lower] using log_le_log (exp_pos _)
      (Nat.le_ceil (exp ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))))
  have hhi : log (upper N pb.1 pb.2) ≤ (203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ) := by
    simpa only [log_exp,upper] using log_le_log
      (by exact_mod_cast hX : (0 : ℝ)<upper N pb.1 pb.2)
      (Nat.floor_le (exp_pos ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))).le)
  refine ⟨hp'.1,by have := (Finset.mem_Icc.mp hb).1; omega,hs,hpd,hmax,ha,hM,
    by linarith,by linarith,?_,?_⟩
  · rw [hlog] at hhi
    linarith
  · have hn := Nat.cast_nonneg (α := ℝ) N
    nlinarith

/-- The selected owners are the ORIGINAL finite physical primes. -/
theorem fine_row_owner_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (h : pb ∈ fineRows u N) :
    pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N :=
  (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1

private theorem physical_bound (N : ℕ) {P T : ℝ} (hP : 0 ≤ P)
    (hT : 1 ≤ T) (hPT : P ≤ T) (y : ℝ) :
    |physicalWeight N P y T| ≤ radialEnvelope N := by
  have ht0 : 0 < T := by linarith
  have hx : 0 ≤ 1-P/T ∧ 1-P/T ≤ 1 := by
    constructor
    · have := (div_le_one ht0).mpr hPT; linarith
    · have := div_nonneg hP ht0.le; linarith
  have ho := ownerWeight_bounds N hx.1 hx.2
  rw [physicalWeight,abs_mul,abs_mul,abs_of_nonneg ho.1,
    abs_of_nonneg (radialMoment_nonneg N ht0.le)]
  calc
    _ ≤ radialMoment N T := mul_le_of_le_one_right
      (mul_nonneg ho.1 (radialMoment_nonneg N ht0.le)) (abs_cos_le_one _)
        |>.trans (mul_le_of_le_one_left (radialMoment_nonneg N ht0.le) ho.2)
    _ ≤ _ := radialMoment_le N ht0.le

private theorem physical_continuous (N : ℕ) (P y : ℝ) {T : ℝ} (hT : T ≠ 0) :
    ContinuousAt (physicalWeight N P y) T := by
  unfold physicalWeight
  have hmass : Continuous (ownerWeight N) := by
    unfold ownerWeight ZetaRieszJointAllocation.mass
    fun_prop
  exact ((hmass.continuousAt.comp
    (continuousAt_const.sub (continuousAt_const.div continuousAt_id hT))).mul
      (by unfold radialMoment; fun_prop)).mul (by fun_prop)

private theorem log_ceil_gap (v : ℝ) :
    0 ≤ log (⌈exp v⌉₊ : ℝ)-v ∧ log (⌈exp v⌉₊ : ℝ)-v ≤ exp (-v) := by
  have hm : (0 : ℝ)<⌈exp v⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (exp_pos v)
  have hlo := log_le_log (exp_pos v) (Nat.le_ceil (exp v))
  have hhi := (Nat.ceil_lt_add_one (exp_pos v).le).le
  have hl := log_le_sub_one_of_pos (div_pos hm (exp_pos v))
  rw [log_div hm.ne' (exp_pos v).ne',log_exp] at hl
  refine ⟨by simpa using sub_nonneg.mpr hlo,hl.trans ?_⟩
  rw [show (⌈exp v⌉₊ : ℝ)/exp v-1=((⌈exp v⌉₊ : ℝ)-exp v)/exp v by field_simp,
    exp_neg,← one_div]
  exact div_le_div_of_nonneg_right (by linarith) (exp_pos v).le

private theorem log_floor_gap {v : ℝ} (h : 0 < ⌊exp v⌋₊) :
    0 ≤ v-log (⌊exp v⌋₊ : ℝ) ∧ v-log (⌊exp v⌋₊ : ℝ) ≤ (⌊exp v⌋₊ : ℝ)⁻¹ := by
  have hx : (0 : ℝ)<⌊exp v⌋₊ := by exact_mod_cast h
  have hlo := log_le_log hx (Nat.floor_le (exp_pos v).le)
  have hhi := (Nat.lt_floor_add_one (exp v)).le
  have hl := log_le_sub_one_of_pos (div_pos (exp_pos v) hx)
  rw [log_div (exp_pos v).ne' hx.ne',log_exp] at hl
  refine ⟨by simpa using sub_nonneg.mpr hlo,hl.trans ?_⟩
  rw [show exp v/(⌊exp v⌋₊ : ℝ)-1=(exp v-(⌊exp v⌋₊ : ℝ))/(⌊exp v⌋₊ : ℝ) by
      field_simp,← one_div]
  exact div_le_div_of_nonneg_right (by linarith) hx.le


/-- The full unsigned-log window estimate needs only radial endpoint
geometry. Cofactor saturation plays no role in the signed Fourier payment. -/
theorem full_window_integer_error_of_gap {N : ℕ} (hN : 32 ≤ N) (β : ℝ) {pb : ℕ×ℕ}
    (hOuter : log (pb.1*pb.2 : ℕ) ≤ ((39/20 : ℝ)-β)*N)
    (hP : log pb.1 < (243/200 : ℝ)*N)
    (hLU : lower N pb.1 pb.2 ≤ upper N pb.1 pb.2) (y : ℝ) :
    |(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T| ≤
      (6*(N : ℝ)+12+2*|y|)*radialEnvelope N*exp (-β*N) := by
  have hM := lower_pos N pb.1 pb.2
  have hMX := hLU
  have hlo : (39/20 : ℝ)*N ≤ log (pb.1*pb.2 : ℕ)+log (lower N pb.1 pb.2) := by
    have h := log_le_log (exp_pos _) (Nat.le_ceil
      (exp ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))))
    simp only [log_exp,lower] at h ⊢
    nlinarith
  have hhi : log (pb.1*pb.2 : ℕ)+log (upper N pb.1 pb.2) ≤ (203/100 : ℝ)*N := by
    have h := log_le_log (by exact_mod_cast hM.trans_le hMX : (0 : ℝ)<upper N pb.1 pb.2)
      (Nat.floor_le (exp_pos ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))).le)
    simp only [log_exp,upper] at h ⊢
    nlinarith
  have hX : 0 < upper N pb.1 pb.2 := hM.trans_le hMX
  let P := log pb.1
  let c := log (pb.1*pb.2 : ℕ)
  let a := (39/20 : ℝ)*N
  let b := (203/100 : ℝ)*N
  let M := lower N pb.1 pb.2
  let X := upper N pb.1 pb.2
  have hPl : P ≤ a := by dsimp [P,a]; nlinarith
  have hP0 : 0 ≤ P := log_natCast_nonneg pb.1
  have ha1 : 1 ≤ a := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    dsimp [a]
    nlinarith
  have hl : a ≤ c+log M := hlo
  have hh : c+log X ≤ b := hhi
  have hlog : c+log M ≤ c+log X :=
    add_le_add_right (log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMX)) c
  have heM : (M : ℝ)⁻¹ ≤ exp (-β*N) := by
    rw [neg_mul,exp_neg]
    exact inv_anti₀ (exp_pos _) (show exp (β*N) ≤ lower N pb.1 pb.2 from
      (exp_le_exp.mpr (by nlinarith : β*N ≤
        (39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ))).trans (Nat.le_ceil _))
  have hleft : c+log M-a ≤ exp (-β*N) := by
    have hv := (log_ceil_gap (((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ)))).2
    change log (M : ℝ)-((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ)) ≤ _ at hv
    have hrlo : β*N ≤ ((39/20 : ℝ)*N-log (pb.1*pb.2 : ℕ)) := by
      nlinarith
    exact (by dsimp [a,c]; nlinarith [hv] : c+log M-a ≤ exp (-(a-c))).trans
      (exp_le_exp.mpr (by dsimp [a,c]; nlinarith))
  have hright : b-(c+log X) ≤ exp (-β*N) := by
    have hv := (log_floor_gap (v := ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))) hX).2
    change ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ))-log X ≤ (X : ℝ)⁻¹ at hv
    have hi : (X : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast hMX)
    exact (by dsimp [b,c]; nlinarith [hv] : b-(c+log X) ≤ (X : ℝ)⁻¹).trans (hi.trans heM)
  have hc : ContinuousOn (physicalWeight N P y) (Icc a b) := by
    intro T hT
    exact (physical_continuous N P y (by nlinarith [hT.1])).continuousWithinAt
  have hI (v w : ℝ) (hv : a ≤ v) (hw : w ≤ b) (hvw : v ≤ w) :
      IntervalIntegrable (physicalWeight N P y) volume v w := by
    apply (hc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hvw]
    exact Icc_subset_Icc hv hw
  have hwb := (fun T (ht : T ∈ Icc a b) => physical_bound N hP0
    (by nlinarith [ht.1]) (hPl.trans ht.1) y)
  have hli : |∫ T : ℝ in a..(c+log M), physicalWeight N P y T| ≤
      radialEnvelope N*exp (-β*N) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := c+log M) (C := radialEnvelope N) (f := physicalWeight N P y) (by
        rw [uIoc_of_le hl]
        intro T hT
        exact hwb T ⟨hT.1.le,hT.2.trans (hlog.trans hh)⟩)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hl)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hleft (radialEnvelope_pos N).le)
  have hri : |∫ T : ℝ in (c+log X)..b, physicalWeight N P y T| ≤
      radialEnvelope N*exp (-β*N) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c+log X) (b := b) (C := radialEnvelope N) (f := physicalWeight N P y) (by
        rw [uIoc_of_le hh]
        intro T hT
        exact hwb T ⟨(hl.trans hlog).trans hT.1.le,hT.2⟩)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hh)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hright (radialEnvelope_pos N).le)
  have he : (∫ T : ℝ in a..b, physicalWeight N P y T)=
      (∫ T : ℝ in a..(c+log M), physicalWeight N P y T)+
      (∫ T : ℝ in (c+log M)..(c+log X), physicalWeight N P y T)+
      (∫ T : ℝ in (c+log X)..b, physicalWeight N P y T) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hI a _ le_rfl (hlog.trans hh) hl) (hI _ _ hl hh hlog),
      intervalIntegral.integral_add_adjacent_intervals
        (hI a _ le_rfl hh (hl.trans hlog)) (hI _ b (hl.trans hlog) le_rfl hh)]
  have hq := integer_weight_error hN hM hMX hP0 (ha1.trans hl) (hPl.trans hl) y
  have hq' := (mul_le_mul_of_nonneg_left heM
    (by positivity [radialEnvelope_pos N] : 0 ≤ 2*(3*(N : ℝ)+5+|y|)*radialEnvelope N))
  rw [← div_eq_mul_inv] at hq'
  have hq'' := hq.trans hq'
  change |_-∫ T : ℝ in a..b, physicalWeight N P y T| ≤ _
  rw [he]
  calc
    _ = |((∑ d ∈ Finset.Ioc M X, physicalWeight N P y (c+log d)/(d : ℝ))-
        ∫ T : ℝ in (c+log M)..(c+log X), physicalWeight N P y T)-
      ((∫ T : ℝ in a..(c+log M), physicalWeight N P y T)+
        ∫ T : ℝ in (c+log X)..b, physicalWeight N P y T)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hq'' ((abs_add_le _ _).trans (add_le_add hli hri)))
    _ = _ := by ring


/-- The original fine-gap estimate, retained with its original constants. -/
theorem full_window_integer_error {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hOuter : log (pb.1*pb.2 : ℕ) ≤ (1949/1000 : ℝ)*N)
    (hP : log pb.1 < (243/200 : ℝ)*N)
    (hLU : lower N pb.1 pb.2 ≤ upper N pb.1 pb.2) (y : ℝ) :
    |(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T| ≤
      (6*(N : ℝ)+12+2*|y|)*radialEnvelope N*exp (-(N : ℝ)/1000) := by
  simpa only [neg_mul,div_mul_eq_mul_div,one_mul,neg_div] using
    full_window_integer_error_of_gap hN (1/1000)
    (by norm_num at hOuter ⊢; exact hOuter) hP hLU y


theorem fine_integer_window_error {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ fineRows u N) (y : ℝ) :
    |(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T| ≤
      (6*(N : ℝ)+12+2*|y|)*radialEnvelope N*exp (-(N : ℝ)/1000) := by
  exact full_window_integer_error hN
    (Finset.mem_filter.mp hpb).2.2.2.2.2.1
    (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
    (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2 y


private theorem full_physical_window_bound {u P : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (_hN : 32 ≤ N)
    (hP : 0 ≤ P) (hPl : P < (39/20 : ℝ)*N) {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N P y T)| ≤ ((N : ℝ)+1)*((N : ℝ)+9)*radialRate^N := by
  have hab : (39/20 : ℝ)*N ≤ (203/100 : ℝ)*N := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have he : (∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N P y T) =
      (∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N), ownerFourier N P y T).re := by
    change _=Complex.reCLM (∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      ownerFourier N P y T)
    rw [← Complex.reCLM.intervalIntegral_comp_comm
      (ownerFourier_integral N P y).1.intervalIntegrable]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro T ht
    change physicalWeight N P y T=(ownerFourier N P y T).re
    rw [ownerFourier_eq_literal N hP (hPl.trans_le ht.1) y]
    simp [physicalWeight,radialFourier,Complex.mul_re,Complex.exp_re,cos_neg]
    ring
  have hn := Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      ownerFourier N P y T))
  have he' : ((u : ℂ)^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      ownerFourier N P y T)).re =
      u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
        ownerFourier N P y T).re := by
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [he] at ⊢
  rw [he'] at hn
  exact hn.trans (owner_window_bound hu hU hP hy N)

private theorem fine_lattice_envelope {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/1000) ≤
      2*((N : ℝ)+1)*comparisonRate^N := by
  have hr : 0 ≤ 2*u*exp (-(1/1000 : ℝ)) := by positivity
  have hrate : 2*u*exp (-(1/1000 : ℝ)) ≤ comparisonRate := by
    apply (show 2*u*exp (-(1/1000 : ℝ)) ≤ fineRate u from ?_).trans
      (fineRate_bounds hu hU).2
    unfold fineRate
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by norm_num)) (by positivity)
  have he : u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/1000) =
      2*u*((N : ℝ)+1)*(2*u*exp (-(1/1000 : ℝ)))^N := by
    unfold radialEnvelope
    rw [mul_pow,mul_pow,← exp_nat_mul,pow_succ,pow_succ]
    rw [show -(N : ℝ)/1000=(N : ℝ)*(-(1/1000 : ℝ)) by ring]
    ring
  rw [he]
  have hfac : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact mul_le_mul hfac (pow_le_pow_left₀ hr hrate N) (pow_nonneg hr N) (by positivity)

/-- Joint rate for signed full-window cancellation, rounding and the
fine-threshold squarefree comparison. -/
def fineRateTotal : ℝ := max radialRate comparisonRate

theorem fineRateTotal_bounds : 0 < fineRateTotal ∧ fineRateTotal < 1 := by
  exact ⟨radialRate_bounds.1.trans_le (le_max_left _ _),
    max_lt radialRate_bounds.2 comparisonRate_bounds.2⟩

/-- Independent signed radial payment without a saturation assumption. -/
private theorem lattice_envelope_of_gap {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ)
    {β : ℝ} (hβ : (1/5000 : ℝ) ≤ β) :
    u^(N+1)*radialEnvelope N*exp (-β*N) ≤
      2*((N : ℝ)+1)*comparisonRate^N := by
  have hr : 0 ≤ 2*u*exp (-β) := by positivity
  have h2u : 2*u ≤ exp (1/10000 : ℝ) := by
    have he := add_one_le_exp (1/10000 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    linarith
  have hrate : 2*u*exp (-β) ≤ comparisonRate := by
    calc
      _ ≤ exp (1/10000 : ℝ)*exp (-β) :=
        mul_le_mul_of_nonneg_right h2u (exp_pos _).le
      _ = exp ((1/10000 : ℝ)-β) := by rw [sub_eq_add_neg,exp_add]
      _ ≤ _ := by unfold comparisonRate; apply exp_le_exp.mpr; linarith
  have he : u^(N+1)*radialEnvelope N*exp (-β*N) =
      2*u*((N : ℝ)+1)*(2*u*exp (-β))^N := by
    unfold radialEnvelope
    rw [mul_pow,mul_pow,← exp_nat_mul,pow_succ,pow_succ]
    rw [show -β*(N : ℝ)=(N : ℝ)*(-β) by ring]
    ring
  rw [he]
  have hfac : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact mul_le_mul hfac (pow_le_pow_left₀ hr hrate N) (pow_nonneg hr N) (by positivity)

/-- Signed full-window cancellation for the smaller displayed gap. -/
theorem full_window_weight_bound_of_gap {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    {β : ℝ} (hβ : (1/5000 : ℝ) ≤ β) {pb : ℕ×ℕ}
    (hOuter : log (pb.1*pb.2 : ℕ) ≤ ((39/20 : ℝ)-β)*N)
    (hP : log pb.1 < (243/200 : ℝ)*N)
    (hLU : lower N pb.1 pb.2 ≤ upper N pb.1 pb.2)
    {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
      ((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N := by
  have hq := full_window_integer_error_of_gap hN β hOuter hP hLU y
  have hPl : log pb.1 < (39/20 : ℝ)*N := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hi := full_physical_window_bound hu hU hN (log_natCast_nonneg pb.1) hPl hy
  have hnorm := (mul_le_mul_of_nonneg_left hq (pow_nonneg hu (N+1))).trans
    (by
      calc
        _ = (6*(N : ℝ)+12+2*|y|)*
            (u^(N+1)*radialEnvelope N*exp (-β*N)) := by ring
        _ ≤ (6*(N : ℝ)+12+2*|y|)*(2*((N : ℝ)+1)*comparisonRate^N) :=
          mul_le_mul_of_nonneg_left (lattice_envelope_of_gap hu hU N hβ) (by positivity))
  rw [← abs_of_nonneg (pow_nonneg hu (N+1)),← abs_mul] at hnorm
  have h1 := pow_le_pow_left₀ radialRate_bounds.1.le (le_max_left radialRate (comparisonRate)) N
  have h2 := pow_le_pow_left₀ comparisonRate_bounds.1.le (le_max_right radialRate (comparisonRate)) N
  have hi' := hi.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  have hq' := hnorm.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*((N : ℝ)+1)))
    (by positivity : 0 ≤ 6*(N : ℝ)+12+2*|y|))
  have ha := abs_add_le
    (u^(N+1)*((∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T))
    (u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N (log pb.1) y T))
  calc
    _ = |u^(N+1)*((∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T)+
        u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T)| := by congr 1; ring
    _ ≤ (6*(N : ℝ)+12+2*|y|)*(2*((N : ℝ)+1)*max radialRate (comparisonRate)^N)+
        ((N : ℝ)+1)*((N : ℝ)+9)*max radialRate (comparisonRate)^N :=
      ha.trans (add_le_add hq' hi')
    _ = _ := by unfold fineRateTotal; ring


theorem full_window_weight_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ}
    (hOuter : log (pb.1*pb.2 : ℕ) ≤ (1949/1000 : ℝ)*N)
    (hP : log pb.1 < (243/200 : ℝ)*N)
    (hLU : lower N pb.1 pb.2 ≤ upper N pb.1 pb.2)
    {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
      ((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N := by
  have hq := full_window_integer_error hN hOuter hP hLU y
  have hPl : log pb.1 < (39/20 : ℝ)*N := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hi := full_physical_window_bound hu hU hN (log_natCast_nonneg pb.1) hPl hy
  have hnorm := (mul_le_mul_of_nonneg_left hq (pow_nonneg hu (N+1))).trans
    (by
      calc
        _ = (6*(N : ℝ)+12+2*|y|)*
            (u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/1000)) := by ring
        _ ≤ (6*(N : ℝ)+12+2*|y|)*(2*((N : ℝ)+1)*comparisonRate^N) :=
          mul_le_mul_of_nonneg_left (fine_lattice_envelope hu hU N) (by positivity))
  rw [← abs_of_nonneg (pow_nonneg hu (N+1)),← abs_mul] at hnorm
  have h1 := pow_le_pow_left₀ radialRate_bounds.1.le (le_max_left radialRate (comparisonRate)) N
  have h2 := pow_le_pow_left₀ comparisonRate_bounds.1.le (le_max_right radialRate (comparisonRate)) N
  have hi' := hi.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  have hq' := hnorm.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*((N : ℝ)+1)))
    (by positivity : 0 ≤ 6*(N : ℝ)+12+2*|y|))
  have ha := abs_add_le
    (u^(N+1)*((∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T))
    (u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
      physicalWeight N (log pb.1) y T))
  calc
    _ = |u^(N+1)*((∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))-
        ∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T)+
        u^(N+1)*(∫ T : ℝ in ((39/20 : ℝ)*N)..((203/100 : ℝ)*N),
          physicalWeight N (log pb.1) y T)| := by congr 1; ring
    _ ≤ (6*(N : ℝ)+12+2*|y|)*(2*((N : ℝ)+1)*max radialRate (comparisonRate)^N)+
        ((N : ℝ)+1)*((N : ℝ)+9)*max radialRate (comparisonRate)^N :=
      ha.trans (add_le_add hq' hi')
    _ = _ := by unfold fineRateTotal; ring

theorem fine_weight_sum_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ fineRows u N) {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N pb.1 pb.2),
      physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
      ((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N := by
  exact full_window_weight_bound hu hU hN
    (Finset.mem_filter.mp hpb).2.2.2.2.2.1
    (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
    (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2 hy



private theorem fine_coefficient_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ fineRows u N) :
    |((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors| ≤ (1 : ℝ)/(pb.1*pb.2 : ℕ) := by
  have hg := fine_row_geometry hpb
  have hP := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hL0 : 0 < SquarefreeVaughanLogSource.length u N := by linarith
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by
    exact_mod_cast Nat.mul_pos hg.1.pos (by have := hg.2.1; omega)
  have hH := pairHinge_bounds (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
  have hHL : pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2 ≤
      SquarefreeVaughanLogSource.length u N := by linarith [hH.2]
  have hd := density_bounds (pb.1*pb.2).primeFactors (fun _ hq => Nat.prime_of_mem_primeFactors hq)
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [abs_mul,abs_div,abs_mul,abs_of_nonneg hH.1,abs_of_nonneg hd.1,
    abs_of_pos (mul_pos hL0 hpb0)]
  have hnum : |(μ pb.2 : ℝ)| * pairHinge
      (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*density (pb.1*pb.2).primeFactors ≤
      SquarefreeVaughanLogSource.length u N :=
    (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hH.1) hd.2).trans
      ((mul_le_of_le_one_left hH.1 hm).trans hHL)
  calc
    _ = (|(μ pb.2 : ℝ)| *pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2*
      density (pb.1*pb.2).primeFactors)/(SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) := by ring
    _ ≤ SquarefreeVaughanLogSource.length u N/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hL0 hpb0).le
    _ = _ := by field_simp

set_option backward.isDefEq.respectTransparency false in
/-- All outer counts have only harmonic mass after the unsigned leg is
joined and cancelled. No exponential count majorant is charged here. -/
theorem fine_outer_harmonic_bound (u : ℝ) (N : ℕ) :
    (∑ pb ∈ fineRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 := by
  let B := ⌊exp ((203/100 : ℝ)*N)⌋₊
  have hBn : 0 < B := Nat.floor_pos.mpr (one_le_exp (by positivity))
  have hB : (0 : ℝ)<B := by exact_mod_cast hBn
  have hlogB : log B ≤ (203/100 : ℝ)*N := by
    have hh := log_le_log hB (Nat.floor_le (exp_pos ((203/100 : ℝ)*N)).le)
    simpa only [log_exp] using hh
  have hsub : fineRows u N ⊆ (Finset.Icc 1 B).product (Finset.Icc 1 B) := by
    intro pb hpb
    have hg := fine_row_geometry hpb
    have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hpb).1).2
    have hp : log pb.1 ≤ (13/20 : ℝ)*((203/100 : ℝ)*N) := by
      have hP := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
      have hn := Nat.cast_nonneg (α := ℝ) N
      linarith
    have hpB : pb.1 ≤ B := by
      apply Nat.le_floor
      rw [← exp_log (by exact_mod_cast hg.1.pos : (0 : ℝ)<pb.1)]
      apply exp_le_exp.mpr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hg.1.pos,hpB⟩,
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hb).1; omega,(Finset.mem_Icc.mp hb).2⟩⟩
  have hhar : (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹) ≤ 1+(203/100 : ℝ)*N := by
    have hh := harmonic_le_one_add_log B
    rw [harmonic_eq_sum_Icc,Rat.cast_sum] at hh
    push_cast at hh
    exact hh.trans (add_le_add_right hlogB 1)
  have he : (∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ)) =
      (∑ d ∈ Finset.Icc 1 B, (d : ℝ)⁻¹)^2 := by
    calc
      _ = ∑ p ∈ Finset.Icc 1 B, ∑ b ∈ Finset.Icc 1 B, (1 : ℝ)/(p*b : ℕ) :=
        Finset.sum_product (Finset.Icc 1 B) (Finset.Icc 1 B)
          (fun pb : ℕ×ℕ => (1 : ℝ)/(pb.1*pb.2 : ℕ))
      _ = _ := by
        simp only [Nat.cast_mul,one_div,mul_inv]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,pow_two]
  calc
    _ ≤ ∑ pb ∈ (Finset.Icc 1 B).product (Finset.Icc 1 B), (1 : ℝ)/(pb.1*pb.2 : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := he
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hhar 2


/-- The joined SIGNED all-count density main on the fine full-window
rows. Its unsigned counting error is paid separately. -/
def fineDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ fineRows u N, densityRow N (SquarefreeVaughanLogSource.length u N) y
    pb.1 pb.2 (lower N pb.1 pb.2) (upper N pb.1 pb.2)

/-- A geometric bound for the main itself, not a positive allowance
assigned separately to each prime-count class. -/
def fineMainBudget (y : ℝ) (N : ℕ) : ℝ :=
  9*(33+4*|y|)*((N : ℝ)+1)^4*fineRateTotal^N

theorem tendsto_fineMainBudget (y : ℝ) : Tendsto (fineMainBudget y) atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 4
    fineRateTotal_bounds.1 fineRateTotal_bounds.2).const_mul (9*(33+4*|y|))
  simp only [mul_zero] at h
  convert h using 1
  ext N
  unfold fineMainBudget
  ring

/-- Signed cancellation of the full factorial/window amplitude is
performed first. Every original owner/cofactor count and the original
phase are retained in the resulting arithmetic bound. -/
theorem source_scaled_fineDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {y : ℝ} (hy : 54 ≤ |y|) :
    |u^(N+1)*fineDensityMain u y N| ≤ fineMainBudget y N := by
  have hrow pb (hpb : pb ∈ fineRows u N) :
      |u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (lower N pb.1 pb.2) (upper N pb.1 pb.2)| ≤
        (1 : ℝ)/(pb.1*pb.2 : ℕ)*
          (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [densityRow_physical]
    rw [show u^(N+1)*
      (((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors*
        (∑ d ∈ Finset.Ioc (lower N pb.1 pb.2) (upper N pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) =
      (((μ pb.2 : ℝ)*pairHinge (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
        (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
        density (pb.1*pb.2).primeFactors)*
        (u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2) (upper N pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))) by ring,
      abs_mul]
    exact mul_le_mul (fine_coefficient_bound hN hL hpb)
      (fine_weight_sum_bound hu hU hN hpb hy) (abs_nonneg _) (by positivity)
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum hrow)
  have hs : |u^(N+1)*fineDensityMain u y N| ≤
      (1+(203/100 : ℝ)*N)^2*
        (((N : ℝ)+1)*(13*(N : ℝ)+33+4*|y|)*fineRateTotal^N) := by
    rw [fineDensityMain,Finset.mul_sum]
    apply hsum.trans
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (fine_outer_harmonic_bound u N)
      (by positivity [fineRateTotal_bounds.1])
  have hp1 : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have h : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) h 2).trans_eq (by ring)
  have hp2 : 13*(N : ℝ)+33+4*|y| ≤ (33+4*|y|)*((N : ℝ)+1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg y)]
  apply hs.trans
  unfold fineMainBudget
  have h := mul_le_mul hp1
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2
      (show 0 ≤ (N : ℝ)+1 by positivity))
      (pow_nonneg fineRateTotal_bounds.1.le N))
    (by positivity [fineRateTotal_bounds.1]) (by positivity)
  convert h using 1
  ring


theorem geometry_subinterval {N p b M X M' X' : ℕ} {L : ℝ}
    (hg : RowGeometry N L p b M X) (hMM : M ≤ M') (hXX : X' ≤ X) (hMX : M' < X') :
    RowGeometry N L p b M' X' := by
  obtain ⟨hp,hb,hs,hpd,hmax,ha,hM,hlo,hhi,hsat,hshare⟩ := hg
  have hM' : 0 < M' := lt_of_lt_of_le hM hMM
  have hX' : 0 < X' := hM'.trans hMX
  have hm : log M ≤ log M' := log_le_log
    (by exact_mod_cast hM) (by exact_mod_cast hMM)
  have hx : log X' ≤ log X := log_le_log
    (by exact_mod_cast hX') (by exact_mod_cast hXX)
  refine ⟨hp,hb,hs,hpd,hmax,ha,hM',?_,?_,?_,?_⟩ <;> linarith

/-- Clamped dyadic boundaries; clamping adds no atom and causes every
post-endpoint shell to be empty. -/
def boundary (M X i : ℕ) : ℕ := min X (2^i*M)

theorem boundary_mono (M X : ℕ) : Monotone (boundary M X) := by
  intro i k hik
  unfold boundary
  exact min_le_min_left X (Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by omega) hik))

theorem boundary_le_twice (M X i : ℕ) : boundary M X (i+1) ≤ 2*boundary M X i := by
  unfold boundary
  rw [pow_succ]
  by_cases h : X ≤ 2^i*M
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by omega)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans_eq (by ring)

/-- An exact disjoint partition, for an arbitrary signed summand. This
is used before either squarefree comparison error is estimated. -/
theorem sum_boundary_shells (M X m : ℕ) (f : ℕ → ℝ) (hMX : M ≤ X) :
    (∑ i ∈ Finset.range m, ∑ d ∈ Finset.Ioc (boundary M X i) (boundary M X (i+1)), f d) =
      ∑ d ∈ Finset.Ioc M (boundary M X m), f d := by
  induction m with
  | zero => simp [boundary,min_eq_right hMX]
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    exact Finset.sum_Ioc_consecutive f
      (by unfold boundary; exact le_min hMX (by
        have hp : 1 ≤ 2^m := Nat.one_le_pow _ _ (by omega)
        nlinarith)) (boundary_mono M X (Nat.le_succ m))

private theorem last_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ fineRows u N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    boundary (lower N pb.1 pb.2)
      (upper N pb.1 pb.2) (N+1) =
        upper N pb.1 pb.2 := by
  have hg := fine_row_geometry hpb
  have ha := pairHinge_active hg.2.2.2.2.2.1
  have hp0 := hg.1.pos
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hlog : log (pb.1*pb.2 : ℕ)=log pb.1+log pb.2 := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hb0.ne')]
  have hU : (upper N pb.1 pb.2 : ℝ) ≤
      exp ((131/200 : ℝ)*N) := by
    have hf := Nat.floor_le (exp_pos (((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)))).le
    have he : ((203/100 : ℝ)*N-log (pb.1*pb.2 : ℕ)) ≤ (131/200 : ℝ)*N := by
      rw [← hlog] at ha
      linarith
    exact hf.trans (exp_le_exp.mpr he)
  have hpow : exp ((131/200 : ℝ)*N) ≤
      ((2^(N+1)*lower N pb.1 pb.2 : ℕ) : ℝ) := by
    have hbase := fine_row_large hpb
    have hrate : (131/200 : ℝ)*N ≤ (N+1 : ℕ)*log 2+(N : ℝ)/1000 := by
      push_cast
      nlinarith [log_two_gt_d9,log_pos (by norm_num : (1 : ℝ)<2)]
    calc
      _ ≤ exp ((N+1 : ℕ)*log 2+(N : ℝ)/1000) := exp_le_exp.mpr hrate
      _ = (2 : ℝ)^(N+1)*exp ((N : ℝ)/1000) := by rw [exp_add,exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<2)]
      _ ≤ (2 : ℝ)^(N+1)*lower N pb.1 pb.2 := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by push_cast; rfl
  unfold boundary
  exact min_eq_left (by exact_mod_cast hU.trans hpow)

/-- The dyadic grid on one canonical row. -/
def rowBoundary (_u : ℝ) (N i : ℕ) (pb : ℕ×ℕ) : ℕ :=
  boundary (lower N pb.1 pb.2)
    (upper N pb.1 pb.2) i

/-- Empty clamped shells are removed exactly, rather than estimated. -/
def shellRows (u : ℝ) (N i : ℕ) : Finset (ℕ×ℕ) :=
  (fineRows u N).filter (fun pb => rowBoundary u N i pb < rowBoundary u N (i+1) pb)

theorem lower_le_boundary {M X : ℕ} (hMX : M ≤ X) (i : ℕ) :
    M ≤ boundary M X i := by
  unfold boundary
  exact le_min hMX (by have hp : 1 ≤ 2^i := Nat.one_le_pow _ _ (by omega); nlinarith)

private theorem shell_geometry {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) :
    RowGeometry N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2
      (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  obtain ⟨hr,hMX⟩ := Finset.mem_filter.mp hpb
  have hlu := (Finset.mem_filter.mp hr).2.2.2.2.2.2.2.2
  apply geometry_subinterval (fine_row_geometry hr) _ _ hMX
  · exact lower_le_boundary hlu i
  · exact min_le_left _ _

set_option maxHeartbeats 800000 in
private theorem shell_large {u : ℝ} {N i : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ shellRows u N i) : exp ((N : ℝ)/1000) ≤ rowBoundary u N i pb := by
  have hr := (Finset.mem_filter.mp hpb).1
  have hlu := (Finset.mem_filter.mp hr).2.2.2.2.2.2.2.2
  exact (fine_row_large hr).trans
    (by exact_mod_cast lower_le_boundary hlu i)

private theorem coreRow_empty (u y : ℝ) (j p b M : ℕ) : coreRow u y j p b M M=0 := by
  simp [coreRow]

theorem densityRow_interval (N : ℕ) (L y : ℝ) (p b M X : ℕ) :
    densityRow N L y p b M X =
      ((μ b : ℝ)*pairHinge L p b/(L*(p*b : ℕ)))*density (p*b).primeFactors*
        ∑ d ∈ Finset.Ioc M X,
          ownedAmplitude N (log p) (log (p*b : ℕ)) d*
            cos (y*(log (p*b : ℕ)+log d))/(d : ℝ) := by
  unfold densityRow
  congr 1
  simp only [ZetaRieszCofactorDiscrepancy.shellWeight]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  · intro d _; rfl

theorem densityRow_empty (N : ℕ) (L y : ℝ) (p b M : ℕ) :
    densityRow N L y p b M M=0 := by rw [densityRow_interval]; simp

private theorem sum_shellRows_eq (u : ℝ) (N : ℕ)
    (F : (ℕ×ℕ) → ℕ → ℕ → ℝ) (hzero : ∀ pb M, F pb M M=0) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
        ∑ pb ∈ fineRows u N, ∑ i ∈ Finset.range (N+1),
          F pb (rowBoundary u N i pb) (rowBoundary u N (i+1) pb) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro pb _ hnot
  have hz : rowBoundary u N i pb=rowBoundary u N (i+1) pb := by
    apply le_antisymm (boundary_mono _ _ (Nat.le_succ i))
    exact le_of_not_gt (fun h => hnot (Finset.mem_filter.mpr ⟨by assumption,h⟩))
  rw [hz,hzero]

/-- All core row atoms are reassembled exactly after the error has been
paid shellwise. Original phases, masks and count cutoff stay inside. -/
private theorem sum_coreRow_shells (u y : ℝ) (j : ℕ)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
      ∑ pb ∈ shellRows u (dyadicMomentOrder j) i,
        coreRow u y j pb.1 pb.2
          (rowBoundary u (dyadicMomentOrder j) i pb)
          (rowBoundary u (dyadicMomentOrder j) (i+1) pb)) =
      ∑ pb ∈ fineRows u (dyadicMomentOrder j),
        coreRow u y j pb.1 pb.2 (lower (dyadicMomentOrder j) pb.1 pb.2)
          (upper (dyadicMomentOrder j) pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => coreRow_empty u y j pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2
  unfold coreRow
  dsimp only
  change (∑ i ∈ Finset.range (dyadicMomentOrder j+1),
    ∑ d ∈ Finset.Ioc (rowBoundary _ _ i _) (rowBoundary _ _ (i+1) _), _) = _
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]

/-- The SIGNED density rows are likewise recombined before any main-term
estimate. No norm, positive part or separate prime-count cost is inserted. -/
private theorem sum_densityRow_shells (u y : ℝ) (N : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ i ∈ Finset.range (N+1), ∑ pb ∈ shellRows u N i,
      densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (rowBoundary u N i pb) (rowBoundary u N (i+1) pb)) =
      ∑ pb ∈ fineRows u N,
        densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
          (lower N pb.1 pb.2) (upper N pb.1 pb.2) := by
  rw [sum_shellRows_eq _ _ _ (fun pb M => densityRow_empty _ _ _ pb.1 pb.2 M)]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2
  simp only [densityRow_interval,← Finset.mul_sum]
  simp only [rowBoundary]
  rw [sum_boundary_shells _ _ _ _ hlu,last_boundary hpb hL]



/-- The source-scaled comparison error on the fine threshold. -/
def fineComparisonBudget (y : ℝ) (N : ℕ) : ℝ :=
  fineErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N

/-- Main cancellation, exact sieve comparison and the original count
boundary, each used once. -/
def fineRowBudget (y : ℝ) (N : ℕ) : ℝ :=
  fineMainBudget y N+fineComparisonBudget y N+
    highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N

theorem tendsto_fineRowBudget (y : ℝ) : Tendsto (fineRowBudget y) atTop (𝓝 0) := by
  have he := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    comparisonRate_bounds.1 comparisonRate_bounds.2).const_mul (fineErrorConstant*(8+|y|))
  have hce : Tendsto (fineComparisonBudget y) atTop (𝓝 0) := by
    simp only [mul_zero] at he
    convert he using 1
    ext N
    unfold fineComparisonBudget
    ring
  have hc := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (by norm_num : (0 : ℝ)<49/50) (by norm_num : (49/50 : ℝ)<1)).const_mul highCountConstant
  have hcc : Tendsto (fun N : ℕ =>
      highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N) atTop (𝓝 0) := by
    simp only [mul_zero] at hc
    convert hc using 1
    ext N
    ring
  change Tendsto (fun N : ℕ => fineMainBudget y N+fineComparisonBudget y N+
    highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N) atTop (𝓝 0)
  simpa only [zero_add] using ((tendsto_fineMainBudget y).add hce).add hcc

/-- The original signed prime/cofactor/divisor incidence sum, including
its literal count cutoff and every original core mask. -/
def fineLiteralRows (u y : ℝ) (j : ℕ) : ℝ :=
  ∑ pb ∈ fineRows u (dyadicMomentOrder j),
    coreRow u y j pb.1 pb.2 (lower (dyadicMomentOrder j) pb.1 pb.2)
      (upper (dyadicMomentOrder j) pb.1 pb.2)

set_option maxHeartbeats 1200000 in
/-- An INDEPENDENT signed bound for the ORIGINAL fine-threshold row
population, across all counts and radial positions together. No zero,
prime-density approximation or unproved cancellation premise enters. -/
theorem eventually_abs_fineLiteralRows_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*fineLiteralRows u y j| ≤
        fineRowBudget y (dyadicMomentOrder j) := by
  let I := fun j => Finset.range (dyadicMomentOrder j+1)
  let B := fun j i => shellRows u (dyadicMomentOrder j) i
  let M := fun j i => rowBoundary u (dyadicMomentOrder j) i
  let X := fun j i => rowBoundary u (dyadicMomentOrder j) (i+1)
  have hgeo j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      RowGeometry (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
        pb.1 pb.2 (M j i pb) (X j i pb) := shell_geometry hpb
  have hpA j i (_hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      pb.1 ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) :=
    fine_row_owner_mem (Finset.mem_filter.mp hpb).1
  have hI j : (I j).card ≤ dyadicMomentOrder j+1 := by simp [I]
  have hcount := eventually_overflowShells_bound I B M X (fun _ => y)
    (by linarith : 0 ≤ u) hU hI hgeo hpA
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hcount,tendsto_dyadicMomentOrder.eventually hl,
    eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ))]
    with j hcount hlength hj hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hL : (11/8 : ℝ)*N ≤ L := by change _ ≤ L at hlength; nlinarith only [hlength]
  have hL0 : 0 < L := by
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hlog i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) :
      log (pb.1*pb.2 : ℕ) ≤ (203/100 : ℝ)*N := by
    have hg := hgeo j i hi pb hpb
    have hh := hg.2.2.2.2.2.2.2.2.1
    change _ ≤ (203/100 : ℝ)*N at hh
    linarith [log_natCast_nonneg (X j i pb)]
  have hPL i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) : log pb.1 ≤ L := by
    have hP := (Finset.mem_filter.mp (Finset.mem_filter.mp hpb).1).2.2.2.2.2.2.1
    change _ < (243/200 : ℝ)*N at hP
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hT i (hi : i ∈ I j) pb (hpb : pb ∈ B j i) d
      (hd : d ∈ Finset.Icc (M j i pb+1) (X j i pb)) :
      1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    have hg := hgeo j i hi pb hpb
    have hm : 0 < M j i pb := hg.2.2.2.2.2.2.1
    have hmd : M j i pb ≤ d := by have := Finset.mem_Icc.mp hd; omega
    have hdlog := log_le_log (by exact_mod_cast hm : (0 : ℝ)<M j i pb)
      (by exact_mod_cast hmd : (M j i pb : ℝ)≤d)
    have hlo := hg.2.2.2.2.2.2.2.1
    change (39/20 : ℝ)*N ≤ _ at hlo
    have hn : (32 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have herr := source_scaled_fine_shells_error (I j) (B j) hN (M j) (X j) hL0
    (by linarith : 0 ≤ u) hU y (hI j)
    (fun i hi pb hpb => ⟨(hgeo j i hi pb hpb).1,
      (hgeo j i hi pb hpb).2.2.1,(hgeo j i hi pb hpb).2.2.2.1⟩)
    hlog (fun i hi pb hpb => (hgeo j i hi pb hpb).2.2.2.2.2.2.1)
    (fun _ _ _ hpb => (Finset.mem_filter.mp hpb).2)
    (fun i _ pb _ => boundary_le_twice _ _ i)
    (fun _ _ _ hpb => shell_large hpb) hPL hT
  have hsum : (∑ i ∈ I j, ∑ pb ∈ B j i,
      coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) =
      (∑ i ∈ I j, ∑ pb ∈ B j i, densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))+
      (∑ i ∈ I j, ∑ pb ∈ B j i, ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))-
      (∑ i ∈ I j, ∑ pb ∈ B j i, overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb)) := by
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro pb hpb
    have h := coreRow_add_overflow (y := y) j hj hu hU hL (hgeo j i hi pb hpb) (hpA j i hi pb hpb)
    change _+_=densityRow N L y _ _ _ _+ownedShellDiscrepancy N L y _ _ _ _ at h
    linarith
  have hm := source_scaled_fineDensityMain_bound (by linarith : 0 ≤ u) hU hN hL hy
  change |u^(N+1)*fineLiteralRows u y j| ≤ fineRowBudget y N
  rw [fineLiteralRows,← sum_coreRow_shells u y j hL]
  change |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i, coreRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| ≤ _
  rw [hsum,mul_sub,mul_add]
  have hmain : |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
      densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))| ≤ fineMainBudget y N := by
    simpa only [I,B,M,X,N,L,sum_densityRow_shells u y (dyadicMomentOrder j) hL,
      fineDensityMain] using hm
  calc
    _ ≤ |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          densityRow N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          ownedShellDiscrepancy N L y pb.1 pb.2 (M j i pb) (X j i pb))|+
        |u^(N+1)*(∑ i ∈ I j, ∑ pb ∈ B j i,
          overflowRow u y j pb.1 pb.2 (M j i pb) (X j i pb))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ fineMainBudget y N+
        fineErrorConstant*(8+|y|)*((N : ℝ)+1)^3*comparisonRate^N+
        highCountConstant*((N : ℝ)+1)^2*(49/50 : ℝ)^N :=
      add_le_add (add_le_add hmain herr) hcount
    _ = fineRowBudget y N := rfl

/-- Concrete source-o(1) saving for the ORIGINAL retained signed
prime-incidence sum on the enlarged population. -/
theorem tendsto_fineLiteralRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*fineLiteralRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => fineRowBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_fineRowBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using eventually_abs_fineLiteralRows_bound hu hU hy

/-- Every incidence outside the fine selection remains literal and
signed. No numerical lower bound for this remainder is asserted. -/
def fineRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  remainingIncidences u y j (fineRows u (dyadicMomentOrder j))
    (fun pb => lower (dyadicMomentOrder j) pb.1 pb.2)
    (fun pb => upper (dyadicMomentOrder j) pb.1 pb.2)

/-- Exact signed partition of the existing owner carrier. -/
theorem coreConvolution_re_eq_fineRemaining (u y : ℝ) (j : ℕ) :
    (coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re =
      fineRemaining u y j+fineLiteralRows u y j := by
  exact coreConvolution_eq_remaining_rows _ _ _ u y j (fun _ h => fine_row_geometry h)

/-- The enlarged signed payment can be subtracted from the WHOLE
joined carrier. The original nonowner payment occurs once, and the
remaining arithmetic numerical floor is still open. -/
theorem tendsto_joined_re_sub_fineRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        fineRemaining u y j)) atTop (𝓝 0) := by
  have herr := ((ZetaRieszSaturatedRowFloor.tendsto_joinedRowErrorBudget y).sub
    (ZetaRieszSaturatedRowFloor.tendsto_rowErrorBudget y)).comp tendsto_dyadicMomentOrder
  simp only [sub_zero,Function.comp_def] at herr
  have hd : Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      (ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
        coreConvolution u y (dyadicMomentOrder j) (dyadicPrimeCount j))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun j =>
      joinedRowErrorBudget y (dyadicMomentOrder j)-rowErrorBudget y (dyadicMomentOrder j)) ?_ herr
    filter_upwards [tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hL
    have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
        SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
    convert joined_sub_convolution_bound (by linarith : 0 ≤ u) hU
      (dyadicMomentOrder j) (dyadicPrimeCount j) y hL' using 1
    unfold joinedRowErrorBudget
    ring
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hd
  have ht := hre.add (tendsto_fineLiteralRows hu hU hy)
  simp only [Complex.zero_re,zero_add] at ht
  apply ht.congr'
  filter_upwards [] with j
  simp only [Function.comp_def]
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.sub_re,coreConvolution_re_eq_fineRemaining]
  ring

/-- The unsigned unit incidence is NEVER paid by this population.
In particular, the balanced-triple obstruction is not removed merely
by lowering the unsigned comparison threshold. -/
theorem unit_unsigned_not_selected (u : ℝ) (N n b : ℕ) :
    (1,b) ∉ selectedDivisors (fineRows u N)
      (fun pb => lower N pb.1 pb.2) (fun pb => upper N pb.1 pb.2) n := by
  intro h
  obtain ⟨v,hv,hpair⟩ := Finset.mem_image.mp h
  obtain ⟨hinc,_⟩ := Finset.mem_filter.mp hv
  obtain ⟨pb,_hpb,hv⟩ := Finset.mem_biUnion.mp hinc
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
  have hdone : d=1 := congrArg Prod.fst hpair
  have hmd := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
  change lower N pb.1 pb.2 < d at hmd
  have hm := lower_pos N pb.1 pb.2
  omega

private theorem fine_endpoint_cofactor {u : ℝ} {N : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ fineRows u N)
    (hsieve : sieve (pb.1*pb.2).primeFactors (lower N pb.1 pb.2) ≠ 0) :
    Squarefree (pb.2*lower N pb.1 pb.2) ∧
      2 ≤ (pb.2*lower N pb.1 pb.2).primeFactors.card ∧
      ∀ q ∈ (pb.2*lower N pb.1 pb.2).primeFactors, q < pb.1 := by
  have hg := fine_row_geometry hpb
  obtain ⟨hp,hb,hbs,hpd,hmax,ha,hM,_,_,hsat,_⟩ := hg
  have houter : Squarefree (pb.1*pb.2) :=
    Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hp.squarefree,hbs⟩
  have hwhole : Squarefree ((pb.1*pb.2)*lower N pb.1 pb.2) := by
    rw [sieve_eq_product_squarefree houter] at hsieve
    split_ifs at hsieve with h
    · exact h
    · contradiction
  have hc : Squarefree (pb.2*lower N pb.1 pb.2) := by
    rw [mul_assoc] at hwhole
    exact (Nat.squarefree_mul_iff.mp hwhole).2.2
  have hd1 : 1 < lower N pb.1 pb.2 := by
    have h := fine_row_large hpb
    have he := add_one_le_exp ((N : ℝ)/1000)
    have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
    have hr : (1 : ℝ)<lower N pb.1 pb.2 := by linarith
    exact_mod_cast hr
  have hdmax : lower N pb.1 pb.2 < pb.1 := by
    have hlog : log (pb.2*lower N pb.1 pb.2 : ℕ) ≤ SquarefreeVaughanLogSource.length u N := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast (by omega : 0 < pb.2).ne')
        (by exact_mod_cast hM.ne')]
      have hmu := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2
      have hm : log (lower N pb.1 pb.2) ≤
          log (upper N pb.1 pb.2) :=
        log_le_log (by exact_mod_cast hM : (0 : ℝ)<lower N pb.1 pb.2)
        (by exact_mod_cast hmu)
      linarith
    exact active_unsigned_lt_owner hp.pos (by omega) hM hlog ha
  have hdis : Disjoint pb.2.primeFactors (lower N pb.1 pb.2).primeFactors := by
    apply Finset.disjoint_left.mpr
    intro q hq hqd
    have hqp := Nat.prime_of_mem_primeFactors hq
    exact (hqp.coprime_iff_not_dvd.mp
      ((Nat.squarefree_mul_iff.mp hc).1.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq)))
        (Nat.dvd_of_mem_primeFactors hqd)
  refine ⟨hc,?_,?_⟩
  · rw [Nat.primeFactors_mul (by omega) hM.ne',Finset.card_union_of_disjoint hdis]
    have hbcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hb)
    have hdcard := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hd1)
    omega
  · intro q hq
    rw [Nat.primeFactors_mul (by omega) hM.ne',Finset.mem_union] at hq
    exact hq.elim (hmax q) (fun h => (Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors h)).trans_lt hdmax)

private theorem fine_endpoint_atom_bound {u : ℝ} {N : ℕ} (hN : 32 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    {pb : ℕ×ℕ} (hpb : pb ∈ fineRows u N) (y : ℝ) :
    |rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
      (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2 (lower N pb.1 pb.2)| ≤
        radialEnvelope N*exp (-(N : ℝ)/1000)/(pb.1*pb.2 : ℕ) := by
  have hg := fine_row_geometry hpb
  let d := lower N pb.1 pb.2
  let L := SquarefreeVaughanLogSource.length u N
  change |rowAtom _ N L y pb.1 pb.2 d| ≤ _
  have hd0 : 0 < d := lower_pos N pb.1 pb.2
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hpb0 : (0 : ℝ)<(pb.1*pb.2 : ℕ) := by exact_mod_cast Nat.mul_pos hg.1.pos hb0
  have hnr : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < L := by dsimp [L]; nlinarith
  have hP : log pb.1 ≤ L := by
    obtain ⟨_,_,_,_,_,_,_,_,hhi,_,hshare⟩ := hg
    have hmU : log d ≤ log (upper N pb.1 pb.2) :=
      log_le_log (by exact_mod_cast hd0 : (0 : ℝ)<d)
      (by exact_mod_cast (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2)
    change _ ≤ (203/100 : ℝ)*N at hhi
    change log pb.1 ≤ (13/20 : ℝ)*(log (pb.1*pb.2 : ℕ)+log d) at hshare
    dsimp [L]
    nlinarith
  by_cases hz : sieve (pb.1*pb.2).primeFactors d=0
  · simp only [rowAtom,hz,mul_zero,abs_zero]
    positivity [radialEnvelope_pos N]
  have hco := fine_endpoint_cofactor hN hpb hz
  have houter : Squarefree (pb.1*pb.2) := Nat.squarefree_mul_iff.mpr
    ⟨hg.1.coprime_iff_not_dvd.mpr hg.2.2.2.1,hg.1.squarefree,hg.2.2.1⟩
  have hsieve : sieve (pb.1*pb.2).primeFactors d=1 := by
    rw [sieve_eq_product_squarefree houter] at hz ⊢
    by_cases hs : Squarefree ((pb.1*pb.2)*d)
    · simp only [if_pos hs]
    · simp only [if_neg hs,not_true_eq_false] at hz
  have hT : 1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    have hlo := hg.2.2.2.2.2.2.2.1
    change (39/20 : ℝ)*N ≤ log (pb.1*pb.2 : ℕ)+log d at hlo
    linarith
  have hPT : log pb.1 ≤ log (pb.1*pb.2 : ℕ)+log d := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hg.1.ne_zero) (by exact_mod_cast hb0.ne')]
    linarith [log_natCast_nonneg pb.2,log_natCast_nonneg d]
  have hamp := ownedAmplitude_bound N (log_natCast_nonneg pb.1) hT hPT
  have hh := pairHinge_bounds L pb.1 pb.2
  have hm : |(μ pb.2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := pb.2)
  rw [rowAtom,owner_phase_eq_amplitude (ZetaRieszAnnulusJoint.intermediatePrimes u N) N L y
    hg.1 hb0 hd0 hco.1 hco.2.1 hco.2.2
    (fine_row_owner_mem hpb),hsieve,mul_one,abs_mul,abs_mul,abs_div,abs_mul,
    abs_of_pos (by positivity : 0 < L*(pb.1*pb.2 : ℕ)*d),abs_of_nonneg hh.1]
  have hc := abs_cos_le_one (y*(log (pb.1*pb.2 : ℕ)+log d))
  have hR := radialEnvelope_pos N
  have hnum : |ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
      *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2 ≤
      radialEnvelope N*L := by
    have h1 := mul_le_mul hamp hc (abs_nonneg _) (radialEnvelope_pos N).le
    have h2 := mul_le_mul h1 hm (abs_nonneg _) (by positivity : 0 ≤ radialEnvelope N*1)
    exact (mul_le_mul h2 (hh.2.trans hP) hh.1 (by positivity : 0 ≤ radialEnvelope N*1*1)).trans_eq
      (by ring)
  have hdlarge := fine_row_large hpb
  have hinv : (d : ℝ)⁻¹ ≤ exp (-(N : ℝ)/1000) := by
    rw [neg_div,exp_neg]
    exact inv_anti₀ (exp_pos _) hdlarge
  calc
    _ = (|ownedAmplitude N (log pb.1) (log (pb.1*pb.2 : ℕ)) d|
        *|cos (y*(log (pb.1*pb.2 : ℕ)+log d))| * |(μ pb.2 : ℝ)| * pairHinge L pb.1 pb.2)/
          (L*(pb.1*pb.2 : ℕ)*d) := by ring
    _ ≤ radialEnvelope N*L/(L*(pb.1*pb.2 : ℕ)*d) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = radialEnvelope N/(pb.1*pb.2 : ℕ)*(d : ℝ)⁻¹ := by field_simp
    _ ≤ radialEnvelope N/(pb.1*pb.2 : ℕ)*exp (-(N : ℝ)/1000) :=
      mul_le_mul_of_nonneg_left hinv (by positivity [radialEnvelope_pos N])
    _ = _ := by ring


/-- The single possibly surviving rounded atom per fine row. The core
mask, count cutoff, squarefree sieve and original allocation are literal. -/
def fineEndpointRows (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  ∑ pb ∈ fineRows u N,
    if pb.1*(pb.2*lower N pb.1 pb.2) ∈ ZetaRieszParityPacket.coreBand u N (dyadicPrimeCount j)
      then rowAtom A N L y pb.1 pb.2 (lower N pb.1 pb.2) else 0

/-- A strict endpoint saving after the entire source growth has been
included. It does not require any zero or height hypothesis. -/
def fineEndpointRate : ℝ := exp (-(9/10000 : ℝ))

theorem fineEndpointRate_bounds : 0 < fineEndpointRate ∧ fineEndpointRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

/-- The all-count endpoint budget has only polynomial outer-row cost. -/
def fineEndpointBudget (N : ℕ) : ℝ := 18*((N : ℝ)+1)^3*fineEndpointRate^N

/-- ALL rounded endpoints of the fine population are independently
paid, including those at a degenerate interval. Absolute values are used
only for this sparse boundary, after its exponential saving is proved. -/
theorem source_scaled_fineEndpointRows_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (j : ℕ)
    (hN : 32 ≤ dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    |u^(dyadicMomentOrder j+1)*fineEndpointRows u y j| ≤
      fineEndpointBudget (dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  have hsum : |fineEndpointRows u y j| ≤
      radialEnvelope N*exp (-(N : ℝ)/1000)*(1+(203/100 : ℝ)*N)^2 := by
    unfold fineEndpointRows
    dsimp only
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ pb ∈ fineRows u N,
          radialEnvelope N*exp (-(N : ℝ)/1000)/(pb.1*pb.2 : ℕ) := by
        apply Finset.sum_le_sum
        intro pb hpb
        split_ifs
        · exact fine_endpoint_atom_bound hN hL hpb y
        · simp only [abs_zero]
          positivity [radialEnvelope_pos N]
      _ = radialEnvelope N*exp (-(N : ℝ)/1000)*
          (∑ pb ∈ fineRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pb _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (fine_outer_harmonic_bound u N)
        (by positivity [radialEnvelope_pos N])
  have h2u : 2*u ≤ exp (1/10000 : ℝ) := by
    have he := add_one_le_exp (1/10000 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    linarith
  have hr : (2*u)^N*exp (-(N : ℝ)/1000) ≤ fineEndpointRate^N := by
    calc
      _ ≤ (exp (1/10000 : ℝ))^N*exp (-(N : ℝ)/1000) := by gcongr
      _ = exp (-(9/10000 : ℝ))^N := by
        rw [← exp_nat_mul,← exp_add,← exp_nat_mul]
        congr 1
        ring
      _ = _ := rfl
  have hp : (1+(203/100 : ℝ)*N)^2 ≤ 9*((N : ℝ)+1)^2 := by
    have hh : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact (pow_le_pow_left₀ (by positivity) hh 2).trans_eq (by ring)
  have hf : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  apply (mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)).trans
  have heq : u^(N+1)*(radialEnvelope N*exp (-(N : ℝ)/1000)*
      (1+(203/100 : ℝ)*N)^2) =
      (2*u*((N : ℝ)+1))*((2*u)^N*exp (-(N : ℝ)/1000))*
        (1+(203/100 : ℝ)*N)^2 := by
    unfold radialEnvelope
    rw [pow_succ,pow_succ,mul_pow]
    ring
  rw [heq]
  have hh := mul_le_mul
    (mul_le_mul hf hr (by positivity) (by positivity)) hp
    (sq_nonneg _) (by positivity [fineEndpointRate_bounds.1])
  convert hh using 1
  unfold fineEndpointBudget
  ring

/-- The new endpoint payment tends to zero at source scale. -/
theorem tendsto_fineEndpointBudget : Tendsto fineEndpointBudget atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    fineEndpointRate_bounds.1 fineEndpointRate_bounds.2).const_mul (18 : ℝ)
  simp only [mul_zero] at h
  convert h using 1
  ext N
  unfold fineEndpointBudget
  ring

/-- Independently vanishing ORIGINAL endpoint atoms, uniformly in any
fixed real height. All finite masks remain in the sum. -/
theorem tendsto_fineEndpointRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*fineEndpointRows u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => fineEndpointBudget (dyadicMomentOrder j)) ?_
    (tendsto_fineEndpointBudget.comp tendsto_dyadicMomentOrder)
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (32 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
        (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source))] with j hN hL
  have hL' : (11/8 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by nlinarith only [hL]
  simpa only [Real.norm_eq_abs] using
    source_scaled_fineEndpointRows_bound (by linarith : 0 ≤ u) hU y j hN hL'

/-- The fine row together with its single rounded boundary is exactly
its CLOSED integer interval. No changed count or owner mask appears. -/
theorem fine_rows_closed_eq (u y : ℝ) (j : ℕ) :
    (∑ pb ∈ fineRows u (dyadicMomentOrder j),
      ∑ d ∈ Finset.Icc (lower (dyadicMomentOrder j) pb.1 pb.2)
        (upper (dyadicMomentOrder j) pb.1 pb.2),
        if pb.1*(pb.2*d) ∈ ZetaRieszParityPacket.coreBand u
            (dyadicMomentOrder j) (dyadicPrimeCount j)
          then rowAtom (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (dyadicMomentOrder j) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
            y pb.1 pb.2 d else 0) = fineLiteralRows u y j+fineEndpointRows u y j := by
  simp only [fineLiteralRows,fineEndpointRows,coreRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pb hpb
  have hlu := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.2.2
  have he : Finset.Icc (lower (dyadicMomentOrder j) pb.1 pb.2)
      (upper (dyadicMomentOrder j) pb.1 pb.2) =
      insert (lower (dyadicMomentOrder j) pb.1 pb.2)
        (Finset.Ioc (lower (dyadicMomentOrder j) pb.1 pb.2)
          (upper (dyadicMomentOrder j) pb.1 pb.2)) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ioc]
    omega
  rw [he,Finset.sum_insert (by simp)]
  ring

/-- A paid rounded endpoint is NOT any previously selected fine-row
incidence. The original divisor allocation, rather than just the label,
is disjoint; this prevents a second credit for the same incidence. -/
theorem fine_endpoint_not_selected {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ fineRows u N) :
    (lower N pb.1 pb.2,pb.2) ∉ selectedDivisors (fineRows u N)
      (fun pc => lower N pc.1 pc.2) (fun pc => upper N pc.1 pc.2)
        (pb.1*(pb.2*lower N pb.1 pb.2)) := by
  intro h
  obtain ⟨v,hv,hpair⟩ := Finset.mem_image.mp h
  obtain ⟨hinc,hn⟩ := Finset.mem_filter.mp hv
  obtain ⟨pc,_hpc,hv⟩ := Finset.mem_biUnion.mp hinc
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
  have hd' : d=lower N pb.1 pb.2 := congrArg Prod.fst hpair
  have hb' : pc.2=pb.2 := by
    simpa only using congrArg (fun v : ℕ×ℕ => v.2) hpair
  have hg := fine_row_geometry hpb
  have hb0 : 0 < pb.2 := by have := hg.2.1; omega
  have hp' : pc.1=pb.1 := by
    change pc.1*(pc.2*d)=pb.1*(pb.2*lower N pb.1 pb.2) at hn
    rw [hb',hd'] at hn
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hb0 (lower_pos N pb.1 pb.2)) hn
  have hmd := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
  change lower N pc.1 pc.2 < d at hmd
  rw [hp',hb',hd'] at hmd
  exact lt_irrefl _ hmd

/-- EVERY literal incidence with this fine full-window outer geometry
lies in the now-paid closed row. There is no remaining rounding gap.
The core label/count masks are not relaxed by this support theorem. -/
theorem fine_literal_row_covered {u : ℝ} {N p b d : ℕ}
    (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hb : 1 < b) (hs : Squarefree b) (hpd : ¬p ∣ b)
    (hmax : ∀ q ∈ b.primeFactors, q < p)
    (ha : pairHinge (SquarefreeVaughanLogSource.length u N) p b ≠ 0)
    (hc : log (p*b : ℕ) ≤ (1949/1000 : ℝ)*N)
    (hP : log p < (243/200 : ℝ)*N)
    (hsat : (203/100 : ℝ)*N ≤ log p+SquarefreeVaughanLogSource.length u N)
    (hlo : (39/20 : ℝ)*N < log (p*b : ℕ)+log d)
    (hhi : log (p*b : ℕ)+log d ≤ (203/100 : ℝ)*N) :
    (p,b) ∈ fineRows u N ∧ d ∈ Finset.Icc (lower N p b) (upper N p b) := by
  have hpP := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hp).1
  have hb0 : 0 < b := by omega
  have hd0 : 0 < d := by
    by_contra hn
    have hd : d=0 := by omega
    rw [hd,Nat.cast_zero,log_zero,add_zero] at hlo
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hdl : lower N p b ≤ d := by
    apply Nat.ceil_le.mpr
    have hh := exp_le_exp.mpr (by linarith : (39/20 : ℝ)*N-log (p*b : ℕ) ≤ log d)
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using hh
  have hdu : d ≤ upper N p b := by
    apply Nat.le_floor
    have hh := exp_le_exp.mpr (by linarith : log d ≤ (203/100 : ℝ)*N-log (p*b : ℕ))
    simpa only [exp_log (by exact_mod_cast hd0 : (0 : ℝ)<d)] using hh
  have hlog : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpP.ne_zero) (by exact_mod_cast hb0.ne')]
  have hbB : b ≤ ⌊exp ((203/100 : ℝ)*N)⌋₊ := by
    apply Nat.le_floor
    have hhlog : log b ≤ (203/100 : ℝ)*N := by
      rw [hlog] at hhi
      linarith [log_natCast_nonneg p,log_natCast_nonneg d]
    have hh := exp_le_exp.mpr hhlog
    simpa only [exp_log (by exact_mod_cast hb0 : (0 : ℝ)<b)] using hh
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hp,Finset.mem_Icc.mpr ⟨by omega,hbB⟩⟩,hs,hpd,hmax,ha,hc,hP,hsat,
      hdl.trans hdu⟩,Finset.mem_Icc.mpr ⟨hdl,hdu⟩⟩

/-- The independent full-window payment now includes EVERY integer in
the fine interval, not just the interval missing its lower endpoint. -/
theorem tendsto_fineClosedRows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      (fineLiteralRows u y j+fineEndpointRows u y j)) atTop (𝓝 0) := by
  simpa only [mul_add,zero_add] using
    (tendsto_fineLiteralRows hu hU hy).add (tendsto_fineEndpointRows hu hU y)

/-- Subtracting ONLY the paid endpoints leaves an exact source-equivalent
joint remainder. This is not the numerical floor for that remainder. -/
theorem tendsto_joined_re_sub_closedFineRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        (fineRemaining u y j-fineEndpointRows u y j))) atTop (𝓝 0) := by
  have ht := (tendsto_joined_re_sub_fineRemaining hu hU hy).add
    (tendsto_fineEndpointRows hu hU y)
  simp only [zero_add] at ht
  convert ht using 1
  ext j
  ring


end RiemannGaussian.ZetaRieszFineDivisorRows
