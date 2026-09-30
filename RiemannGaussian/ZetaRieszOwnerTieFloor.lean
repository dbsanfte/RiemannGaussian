/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszStaggeredFloor

/-!
# Paying the close-owner boundary of the staggered prime periods

Two nearly equal largest prime logarithms occupy one short window after
the remaining cofactor is fixed. Two actual prime reciprocal estimates
pay this boundary, with an extra inverse radial power. No prime phase is
approximated, and no bound for the whole carrier is inferred.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszOwnerTieFloor
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod

/-- An actual short-prime reciprocal estimate, including both endpoints. -/
theorem short_prime_mass {a h : ℝ} (ha : 5000 ≤ a) (hh : 0 ≤ h) (hhu : h ≤ 1/4) :
    (∑ p ∈ logPrimes a h, (p : ℝ)⁻¹) ≤ 1/a := by
  have ha0 : 0 < a := by linarith
  have hb := ZetaRieszQuantitativePrimePeriod.signed_profile_bound
    (fun _ => 1) (fun _ => 0) 0 (fun t => hasDerivAt_const t 1) continuous_const
    ha (show a ≤ a+h by linarith)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0)
    (by intros; norm_num) (by intros; norm_num)
  simp only [add_zero,intervalIntegral.integral_const,smul_eq_mul,mul_one,
    add_sub_cancel_left,zero_add,one_mul] at hb
  have hcost : h^2+(41/100 : ℝ)*(2+2*h) ≤ 2 := by
    nlinarith [pow_le_pow_left₀ hh hhu 2]
  have hu := (abs_le.mp hb).2
  have herr := div_le_div_of_nonneg_right hcost (sq_nonneg a)
  have hmain := div_le_div_of_nonneg_right hhu ha0.le
  have hden : (1/4 : ℝ)/a+2/a^2 ≤ 1/a := by
    have hh : 2/a^2 ≤ (3/4 : ℝ)/a :=
      (div_le_div_iff₀ (sq_pos_of_pos ha0) ha0).mpr (by nlinarith)
    have he : (1/4 : ℝ)/a+(3/4 : ℝ)/a = 1/a := by ring
    linarith only [hh,he]
  have hset : logPrimes a h = (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+h)⌋₊).filter Nat.Prime := by
    dsimp [logPrimes,PrimeWindow.primesInWindow]
    rw [← Real.exp_add,add_comm h a]
  rw [hset]
  simpa only [one_div] using (show
    (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+h)⌋₊).filter Nat.Prime,
      (1 : ℝ)/(p : ℝ)) ≤ 1/a by linarith only [hu,herr,hmain,hden])

/-- Both close large primes lie in this one fixed cofactor window. -/
def pairWindow (v : ℝ) (b : ℕ) : Finset ℕ :=
  logPrimes ((v-Real.log b)/2-1/8) (1/4)

/-- The geometric cofactor cap leaves both prime logarithms proportional
to the radial center, even at total prime count 55. -/
theorem pairWindow_mass {v : ℝ} (hv : 1000000 ≤ v) {b : ℕ}
    (hb : Real.log b ≤ (27/28 : ℝ)*v) :
    (∑ p ∈ pairWindow v b, (p : ℝ)⁻¹) ≤ 60/v := by
  have hv0 : 0 < v := by linarith
  have hlo : v/60 ≤ (v-Real.log b)/2-1/8 := by linarith
  have ha : 5000 ≤ (v-Real.log b)/2-1/8 := by linarith
  exact (short_prime_mass ha (by norm_num) (by norm_num)).trans
    ((div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < v/60) hlo).trans_eq (by ring))

/-- Deleting two specified distinct prime factors preserves the actual
squarefree remainder and its prime count. -/
theorem two_prime_factorization {n p q k : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = k+2) (hp : p ∈ n.primeFactors)
    (hq : q ∈ n.primeFactors) (hpq : p ≠ q) :
    ∃ b : ℕ, n = p*(q*b) ∧ Squarefree b ∧ b.primeFactors.card = k := by
  let U := (n.primeFactors.erase p).erase q
  let b := ∏ r ∈ U, r
  have hqe : q ∈ n.primeFactors.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hq⟩
  have hprime : ∀ r ∈ U, r.Prime := by
    intro r hr
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have he : n = p*(q*b) := by
    calc
      n = ∏ r ∈ n.primeFactors, r := (Nat.prod_primeFactors_of_squarefree hn).symm
      _ = p*∏ r ∈ n.primeFactors.erase p, r := (Finset.mul_prod_erase _ _ hp).symm
      _ = _ := by rw [← Finset.mul_prod_erase _ _ hqe]
  refine ⟨b,he,(he ▸ hn).of_mul_right.of_mul_right,?_⟩
  rw [show b.primeFactors = U from Nat.primeFactors_prod hprime]
  dsimp only [U]
  rw [Finset.card_erase_of_mem hqe,Finset.card_erase_of_mem hp,hc]
  omega

/-- The close-owner condition forces both deleted primes into the same
short window; its leftover cofactor is in the actual finite product cover. -/
theorem close_owner_cover {k n p q : ℕ} (hk : k ≤ 53) {v : ℝ}
    (hv : 1000000 ≤ v) (hn : Squarefree n) (hc : n.primeFactors.card = k+2)
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hpq : p ≠ q)
    (howner : ∀ r ∈ n.primeFactors, r ≤ p)
    (hgap : Real.log p-1/8 < Real.log q)
    (hT : v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) :
    ∃ b ∈ ZetaRieszCofactorMass.products k v,
      Real.log b ≤ (27/28 : ℝ)*v ∧ p ∈ pairWindow v b ∧
      q ∈ pairWindow v b ∧ n = p*(q*b) := by
  obtain ⟨b,he,hs,hbc⟩ := two_prime_factorization hn hc hp hq hpq
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hb0 := hs.ne_zero
  have hlog : Real.log n = Real.log p+Real.log q+Real.log b := by
    rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hqp.ne_zero hb0),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hqp.ne_zero) (by exact_mod_cast hb0)]
    ring
  have hqpLog : Real.log q ≤ Real.log p := Real.log_le_log
    (by exact_mod_cast hqp.pos) (by exact_mod_cast howner q hq)
  have hpmean : Real.log n ≤ 55*Real.log p := by
    have hpoint (r : ℕ) (hr : r ∈ n.primeFactors) : Real.log r ≤ Real.log p := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos : (0 : ℝ) < r)
      (by exact_mod_cast howner r hr)
    have hsum := Finset.sum_le_sum hpoint
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn,
      Finset.sum_const,nsmul_eq_mul,hc] at hsum
    have hkr : (k : ℝ)+2 ≤ 55 := by exact_mod_cast (show k+2 ≤ 55 by omega)
    have hm := mul_le_mul_of_nonneg_right hkr (Real.log_natCast_nonneg p)
    push_cast at hsum
    exact hsum.trans hm
  have hbcap : Real.log b ≤ (27/28 : ℝ)*v := by
    nlinarith [hT.2]
  have hbm : b ∈ ZetaRieszCofactorMass.products k v :=
    ZetaRieszCofactorMass.mem_products_of_squarefree hs hbc (by
      intro r hr
      have hrle : r ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) (Nat.dvd_of_mem_primeFactors hr)
      have hh : Real.log r ≤ Real.log b := Real.log_le_log
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos : (0 : ℝ) < r)
        (by exact_mod_cast hrle)
      linarith)
  refine ⟨b,hbm,hbcap,?_,?_,he⟩
  · apply (mem_logPrimes_iff _ _ _).mpr
    exact ⟨hpp,by nlinarith [hT.1],by nlinarith [hT.2]⟩
  · apply (mem_logPrimes_iff _ _ _).mpr
    exact ⟨hqp,by nlinarith [hT.1],by nlinarith [hT.2]⟩


/-- A positive prime count makes every product-cover cofactor nonzero
and nonunit, including repeated-prime choices in the upper cover. -/
theorem products_nonunit {k b : ℕ} (hk : 0 < k) {v : ℝ}
    (hb : b ∈ ZetaRieszCofactorMass.products k v) : b ≠ 0 ∧ b ≠ 1 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
  have hprime (i : Fin k) := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero),?_⟩
  intro he
  have hd : p ⟨0,hk⟩ ∣ ∏ i, p i := Finset.dvd_prod_of_mem p (Finset.mem_univ _)
  rw [he] at hd
  exact (hprime ⟨0,hk⟩).ne_one (Nat.eq_one_of_dvd_one hd)

/-- The actual least-prime coefficient allowance can be charged to a
nonunit remaining cofactor, before the two large primes are counted. -/
theorem coefficient_norm_cofactor {k n b : ℕ} {L : ℝ} (hL : 0 < L)
    (hn : Squarefree n) (hc : n.primeFactors.card = k+2) (hb : b ≠ 1)
    (hbn : b ∣ n) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤
      (Real.log n/L)*responseConstant (k+2)*Real.log b.minFac := by
  have h₀ : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity k 0 := Nat.cast_nonneg _
  have h₁ : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity k 1 := Nat.cast_nonneg _
  have hC₀ : (ZetaRieszSignedSperner.parityCapacity k 0 : ℝ) ≤ responseConstant (k+2) := by
    simp only [responseConstant,Nat.add_sub_cancel_right]
    linarith
  have hC₁ : (ZetaRieszSignedSperner.parityCapacity k 1 : ℝ) ≤ responseConstant (k+2) := by
    simp only [responseConstant,Nat.add_sub_cancel_right]
    linarith
  have hm : Real.log n.minFac ≤ Real.log b.minFac := Real.log_le_log
    (by exact_mod_cast Nat.minFac_pos n)
    (by exact_mod_cast Nat.minFac_le_of_dvd (Nat.minFac_prime hb).two_le ((Nat.minFac_dvd b).trans hbn))
  have hbase : 0 ≤ Real.log n/L*Real.log n.minFac := by positivity
  have hbounds := ZetaRieszSignedSperner.coefficient_bounds_minFac hL hn (by omega)
  rw [hc,Nat.add_sub_cancel_right] at hbounds
  have hab : |(SquarefreeVaughanLogSource.coefficient L n).re| ≤
      (Real.log n/L)*Real.log n.minFac*responseConstant (k+2) := by
    apply abs_le.mpr
    have hu := mul_le_mul_of_nonneg_left hC₁ hbase
    have hl := mul_le_mul_of_nonneg_left hC₀ hbase
    constructor <;> nlinarith only [hbounds.1,hbounds.2,hu,hl]
  have hreal : SquarefreeVaughanLogSource.coefficient L n =
      ((SquarefreeVaughanLogSource.coefficient L n).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [ZetaRieszCosineCarrier.coefficient_im_eq_zero]
  calc
    _ = |(SquarefreeVaughanLogSource.coefficient L n).re| := by
      conv => lhs; rw [hreal,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := hab
    _ = (Real.log n/L)*responseConstant (k+2)*Real.log n.minFac := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity [responseConstant_pos (k+2)])

/-- Pointwise norm control is used only on the close-owner boundary. The
full original allocation and complex phase remain inside its left side. -/
theorem boundary_atom_norm {k n b N : ℕ} (A : Finset ℕ) (y : ℝ)
    {v L : ℝ} (_hv : 0 < v) (hNv : (N : ℝ)+1 ≤ v) (hL : 0 < L)
    (hn : Squarefree n) (hc : n.primeFactors.card = k+2) (hb : b ≠ 1) (hbn : b ∣ n)
    (hT : |Real.log n-v| ≤ 1) :
    ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (2*amplitude N v*responseConstant (k+2)/L)*(Real.log b.minFac/(n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn.ne_zero
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn.ne_zero,hn1⟩)
  have hc' := coefficient_norm_cofactor hL hn hc hb hbn
  have hr : ‖ZetaRieszJointAllocation.residualCoefficient A L N n‖ ≤
      ‖SquarefreeVaughanLogSource.coefficient L n‖ := by
    rw [ZetaRieszJointAllocation.residualCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(ZetaRieszJointAllocation.boundedShare_bounds A N n).2])]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(ZetaRieszJointAllocation.boundedShare_bounds A N n).1])
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) = Real.exp (-Real.log n/2)/(n : ℝ) := by
    rw [show -(3/2 : ℝ)*Real.log n = -Real.log n/2-Real.log n by ring,
      Real.exp_sub,Real.exp_log hn0]
  have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
      (Real.log n)^N/N.factorial*Real.exp (-(3/2 : ℝ)*Real.log n) := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight]
  have hpoint := mul_le_mul_of_nonneg_right (hr.trans hc')
    (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) n))
  rw [← norm_mul,hker,he] at hpoint
  have hfactor : ((Real.log n/L)*responseConstant (k+2)*Real.log b.minFac)*
      ((Real.log n)^N/N.factorial*(Real.exp (-Real.log n/2)/(n : ℝ))) =
      (responseConstant (k+2)/L)*(Real.log b.minFac/(n : ℝ))*amplitude N (Real.log n) := by
    unfold amplitude
    rw [pow_succ]
    ring
  rw [hfactor] at hpoint
  have hnear := amplitude_near N hNv hlog hT
  have hh := mul_le_mul_of_nonneg_left hnear
    (show 0 ≤ (responseConstant (k+2)/L)*(Real.log b.minFac/(n : ℝ)) by positivity [responseConstant_pos (k+2)])
  exact hpoint.trans (hh.trans_eq (by ring))


/-- An actual label has two distinct close owner primes, one of which
is largest. No primality, coprimality or multiplicity is relaxed here. -/
def CloseOwners (n : ℕ) : Prop :=
  ∃ p ∈ n.primeFactors, ∃ q ∈ n.primeFactors,
    p ≠ q ∧ (∀ r ∈ n.primeFactors, r ≤ p) ∧ Real.log p-1/8 < Real.log q

/-- The finite upper counting cover only; all original masks can remain
in the subset being estimated. -/
def remainders (k : ℕ) (v : ℝ) : Finset ℕ :=
  (ZetaRieszCofactorMass.products k v).filter (fun b => Real.log b ≤ (27/28 : ℝ)*v)

/-- Count-dependent debit for the close-owner boundary. -/
def tieConstant (k : ℕ) : ℝ :=
  14400*responseConstant (k+2)*ZetaRieszCofactorMass.logMassConstant k

/-- The complete actual norm mass of any selected close-owner labels is
an inverse radial power of one supply unit. Repeated counting choices only
increase this boundary upper bound; no carrier is completed. -/
theorem close_owner_norm_bound {k N : ℕ} (hk : 0 < k) (hku : k ≤ 53)
    (A D : Finset ℕ) (y : ℝ) {v L : ℝ} (hv : 1000000 ≤ v)
    (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ n.primeFactors.card = k+2 ∧
      (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
        (tieConstant k/v)*(amplitude N v/v) := by
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  let R := remainders k v
  let V := R.sigma (fun b => (pairWindow v b).product (pairWindow v b))
  let label := fun x : Σ _ : ℕ, ℕ×ℕ => x.2.1*(x.2.2*x.1)
  let f := fun n => if n ∈ D then
    ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ else 0
  let B := 2*amplitude N v*responseConstant (k+2)/L
  have hB : 0 ≤ B := by dsimp [B]; positivity [amplitude_nonneg N hv0.le,responseConstant_pos (k+2)]
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hcover : D ⊆ V.image label := by
    intro n hn
    obtain ⟨hs,hc,hT,p,hp,q,hq,hpq,howner,hgap⟩ := hD n hn
    obtain ⟨b,hb,hcap,hpw,hqw,he⟩ := close_owner_cover hku hv hs hc hp hq hpq howner hgap hT
    apply Finset.mem_image.mpr
    refine ⟨⟨b,(p,q)⟩,Finset.mem_sigma.mpr ⟨?_,Finset.mem_product.mpr ⟨hpw,hqw⟩⟩,?_⟩
    · exact Finset.mem_filter.mpr ⟨hb,hcap⟩
    · exact he.symm
  have hfirst : (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤ ∑ x ∈ V, f (label x) := by
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans
      (Finset.sum_image_le_of_nonneg (fun n _ => hf n))
    simpa only [f,ite_true,Finset.sum_congr rfl (fun n hn => if_pos hn)] using hh
  have hpoint (b : ℕ) (hb : b ∈ R) (p : ℕ) (_hp : p ∈ pairWindow v b)
      (q : ℕ) (_hq : q ∈ pairWindow v b) :
      f (p*(q*b)) ≤ B*(Real.log b.minFac*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹ := by
    have hb' := (Finset.mem_filter.mp hb).1
    have hb1 := (products_nonunit hk hb').2
    by_cases hn : p*(q*b) ∈ D
    · have hd := hD _ hn
      have hnT : |Real.log (p*(q*b) : ℕ)-v| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hd.2.2.1.1],by linarith [hd.2.2.1.2]⟩
      have hh := boundary_atom_norm A y hv0 hNv hL0 hd.1 hd.2.1 hb1
        (dvd_mul_of_dvd_right (dvd_mul_left b q) p) hnT
      dsimp only [f]
      rw [if_pos hn]
      convert hh using 1
      dsimp [B]
      simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
      ring
    · dsimp only [f]
      rw [if_neg hn]
      positivity [Real.log_natCast_nonneg b.minFac]
  have hsum : (∑ x ∈ V, f (label x)) ≤
      B*(3600/v^2)*(ZetaRieszCofactorMass.logMassConstant k*v) := by
    have hreindex : (∑ x ∈ V, f (label x)) =
        ∑ b ∈ R, ∑ p ∈ pairWindow v b, ∑ q ∈ pairWindow v b, f (p*(q*b)) := by
      dsimp only [V]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_product _ _ (fun x : ℕ×ℕ => f (x.1*(x.2*b)))
    rw [hreindex]
    have h₁ := Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun p hp =>
      Finset.sum_le_sum (fun q hq => hpoint b hb p hp q hq)))
    apply h₁.trans
    have hpairs (b : ℕ) (hb : b ∈ R) :
        (∑ p ∈ pairWindow v b, ∑ q ∈ pairWindow v b,
          B*(Real.log b.minFac*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹) ≤
        B*(Real.log b.minFac*(b : ℝ)⁻¹)*(3600/v^2) := by
      have hm := pairWindow_mass hv (Finset.mem_filter.mp hb).2
      have hnon : 0 ≤ ∑ p ∈ pairWindow v b, (p : ℝ)⁻¹ := by positivity
      have hsq := pow_le_pow_left₀ hnon hm 2
      have he : (∑ p ∈ pairWindow v b, ∑ q ∈ pairWindow v b,
          B*(Real.log b.minFac*(b : ℝ)⁻¹)*(p : ℝ)⁻¹*(q : ℝ)⁻¹) =
          (B*(Real.log b.minFac*(b : ℝ)⁻¹))*(∑ p ∈ pairWindow v b, (p : ℝ)⁻¹)^2 := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul,← Finset.mul_sum,pow_two]
        ring
      rw [he]
      convert mul_le_mul_of_nonneg_left hsq
        (show 0 ≤ B*(Real.log b.minFac*(b : ℝ)⁻¹) by positivity) using 1 <;> first | rfl | ring
    have hh := Finset.sum_le_sum hpairs
    have he : (∑ b ∈ R, B*(Real.log b.minFac*(b : ℝ)⁻¹)*(3600/v^2)) =
        (B*(3600/v^2))*(∑ b ∈ R, Real.log b.minFac*(b : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (ZetaRieszCofactorMass.log_mass hk hv0 R (Finset.filter_subset _ _)) (by positivity))
  have hpre : 2*amplitude N v*responseConstant (k+2)/L ≤
      4*(amplitude N v/v)*responseConstant (k+2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ 2*amplitude N v*responseConstant (k+2) by positivity [amplitude_nonneg N hv0.le,responseConstant_pos (k+2)])
      (by positivity : 0 < v/2) hL
    convert hh using 1
    all_goals first | rfl | ring
  have hcost := mul_le_mul_of_nonneg_right hpre
    (show 0 ≤ (3600/v^2)*(ZetaRieszCofactorMass.logMassConstant k*v) by positivity [(ZetaRieszCofactorMass.constants_pos hk).1])
  have he : (4*(amplitude N v/v)*responseConstant (k+2))*
      ((3600/v^2)*(ZetaRieszCofactorMass.logMassConstant k*v)) =
      (tieConstant k/v)*(amplitude N v/v) := by
    unfold tieConstant
    field_simp
    ring
  rw [he] at hcost
  exact hfirst.trans (hsum.trans (by simpa only [B,mul_assoc] using hcost))

/-- One finite debit pays every close-owner count from 3 through 55.
This constant is retained; it is not asserted uniform in growing counts. -/
def allTieConstant : ℝ := ∑ k ∈ Finset.Icc 1 53, tieConstant k

/-- The whole close-owner boundary through count 55 is paid together.
Any original support or previously unpaid mask can be retained in `D`. -/
theorem bounded_count_norm_bound (A D : Finset ℕ) (y : ℝ) {N : ℕ} {v L : ℝ}
    (hv : 1000000 ≤ v) (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55 ∧
      (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
        (allTieConstant/v)*(amplitude N v/v) := by
  have hidx (n : ℕ) (hn : n ∈ D) : n.primeFactors.card-2 ∈ Finset.Icc 1 53 := by
    apply Finset.mem_Icc.mpr
    have h := hD n hn
    omega
  have he := Finset.sum_fiberwise_of_maps_to (s := D) (t := Finset.Icc 1 53)
    hidx (fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖)
  rw [← he]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 53, (tieConstant k/v)*(amplitude N v/v) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkr := Finset.mem_Icc.mp hk
      apply close_owner_norm_bound (by omega) hkr.2 A _ y hv hNv hL
      intro n hn
      have hd := Finset.mem_filter.mp hn
      have h := hD n hd.1
      exact ⟨h.1,by omega,h.2.2.2.1,h.2.2.2.2⟩
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_div]; rfl

open ZetaRieszStaggeredFloor

/-- At most one arithmetic-sign part is nonzero on each label. Paying
both missed parts therefore costs one atom, not two. -/
theorem signedParts_abs_eq (A : Finset ℕ) (L y : ℝ) (N n : ℕ) :
    |signedPart 1 A L y N n|+|signedPart (-1) A L y N n| =
      |(ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| := by
  rw [← signedPart_add]
  by_cases hc : 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re
  · have he : signedPart (-1) A L y N n = 0 := by
      unfold signedPart
      simp only [neg_one_mul]
      rw [max_eq_right (by linarith :
        -(SquarefreeVaughanLogSource.coefficient L n).re ≤ 0)]
      ring
    rw [he,abs_zero,add_zero,add_zero]
  · have he : signedPart 1 A L y N n = 0 := by
      unfold signedPart
      simp only [one_mul]
      rw [max_eq_right (le_of_not_ge hc)]
      ring
    rw [he,abs_zero,zero_add,zero_add]

/-- Two arbitrary missing sign selections inside one boundary set have
a single norm debit. No sign of the cofactor or the cosine is assumed. -/
theorem missed_parts_floor (A D P Q : Finset ℕ) (L y : ℝ) (N : ℕ) :
    -(∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      (∑ n ∈ D\P, signedPart 1 A L y N n)+
        (∑ n ∈ D\Q, signedPart (-1) A L y N n) := by
  have h₁ := Finset.sum_le_sum_of_subset_of_nonneg
    (show D\P ⊆ D from Finset.sdiff_subset) (fun n _ _ => abs_nonneg (signedPart 1 A L y N n))
  have h₂ := Finset.sum_le_sum_of_subset_of_nonneg
    (show D\Q ⊆ D from Finset.sdiff_subset) (fun n _ _ => abs_nonneg (signedPart (-1) A L y N n))
  have hab := Finset.sum_le_sum (fun n (_hn : n ∈ D) =>
    (signedParts_abs_eq A L y N n).le.trans (Complex.abs_re_le_norm _))
  rw [Finset.sum_add_distrib] at hab
  have hlow₁ := Finset.sum_le_sum (fun n (_hn : n ∈ D\P) =>
    neg_abs_le (signedPart 1 A L y N n))
  have hlow₂ := Finset.sum_le_sum (fun n (_hn : n ∈ D\Q) =>
    neg_abs_le (signedPart (-1) A L y N n))
  simp only [Finset.sum_neg_distrib] at hlow₁ hlow₂
  linarith only [h₁,h₂,hab,hlow₁,hlow₂]

/-- Both staggered-grid omissions on the literal close-owner boundary
are now charged only `allTieConstant/v` radial units in total. -/
theorem bounded_count_parts_floor (A D P Q : Finset ℕ) (y : ℝ)
    {N : ℕ} {v L : ℝ} (hv : 1000000 ≤ v) (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55 ∧
      (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n) :
    -(allTieConstant/v)*(amplitude N v/v) ≤
      (∑ n ∈ D\P, signedPart 1 A L y N n)+
        (∑ n ∈ D\Q, signedPart (-1) A L y N n) := by
  have hb := bounded_count_norm_bound A D y hv hNv hL hD
  have hf := missed_parts_floor A D P Q L y N
  linarith only [hb,hf]

/-- The original moving length and all original allocation masks remain.
Uniformly over the linear core, the whole boundary through count 55 costs
less than any fixed positive radial fraction, for either missed sign. -/
theorem eventually_core_tie_norm_bound {u ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (v y : ℝ) (D : Finset ℕ),
      (39/20 : ℝ)*N ≤ v → v ≤ (203/100 : ℝ)*N →
      (∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
        n.primeFactors.card ≤ 55 ∧
        (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n) →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N;
      (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          ε*(Real.exp (-v/2)*v^N/N.factorial) := by
  have ht : Tendsto (fun v : ℝ => allTieConstant/v) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  have hroom : u < Real.exp (-(11/16 : ℝ)) :=
    hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop v₀,
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom,
    eventually_ge_atTop (1000000 : ℕ)] with N hNv₀ hL hlarge v y D hv hvu hD
  have hNR : (1000000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hpay := bounded_count_norm_bound (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    D y (N := N) (v := v) (L := SquarefreeVaughanLogSource.length u N)
    (by linarith) (by linarith) (by linarith) hD
  have hbound := (hv₀ v (by linarith)).le
  have hs := mul_le_mul_of_nonneg_right hbound
    (div_nonneg (amplitude_nonneg N hv0.le) hv0.le)
  have he : amplitude N v/v = Real.exp (-v/2)*v^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  rw [he] at hs hpay
  exact hpay.trans hs

/-- The small literal boundary norm pays both missed arithmetic signs.
The original phase and allocation are retained for every chosen label. -/
theorem eventually_core_tie_parts_floor {u ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (v y : ℝ) (D P Q : Finset ℕ),
      (39/20 : ℝ)*N ≤ v → v ≤ (203/100 : ℝ)*N →
      (∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
        n.primeFactors.card ≤ 55 ∧
        (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n) →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N;
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        (∑ n ∈ D\P, signedPart 1 A L y N n)+
          (∑ n ∈ D\Q, signedPart (-1) A L y N n) := by
  filter_upwards [eventually_core_tie_norm_bound hu hU hε] with N hN v y D P Q hv hvu hD
  have hn := hN v y D hv hvu hD
  have hp := missed_parts_floor (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    D P Q (SquarefreeVaughanLogSource.length u N) y N
  dsimp only at hn ⊢
  linarith only [hn,hp]

/-- Removing a boundary from either missing cover has an exact disjoint
ledger. This does not remove any complete-period incidence. -/
theorem missed_boundary_split (S D P : Finset ℕ) (hD : D ⊆ S) (f : ℕ → ℝ) :
    (∑ n ∈ S\P, f n) = (∑ n ∈ S\(P ∪ D), f n)+(∑ n ∈ D\P, f n) := by
  have hsub : D\P ⊆ S\P := fun n hn =>
    Finset.mem_sdiff.mpr ⟨hD (Finset.mem_sdiff.mp hn).1,(Finset.mem_sdiff.mp hn).2⟩
  have he : (S\P)\(D\P) = S\(P ∪ D) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  have h := Finset.sum_sdiff hsub (f := f)
  rw [he] at h
  exact h.symm

/-- The signed period estimate is strengthened on its original carrier:
the close-owner labels leave BOTH explicit unmatched parts with just one
inverse-radial debit. Period payments and earlier allocations are unchanged. -/
theorem two_cover_floor_with_ties (A S D I J : Finset ℕ) (P Q : ℕ → Finset ℕ)
    (y : ℝ) (N : ℕ) {v L : ℝ} (hv : 1000000 ≤ v)
    (hNv : (N : ℝ)+1 ≤ v) (hL : v/2 ≤ L) (d e : ℕ → ℝ)
    (hDsub : D ⊆ S)
    (hD : ∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55 ∧
      (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n)
    (hP : ∀ i ∈ I, P i ⊆ S) (hQ : ∀ i ∈ J, Q i ⊆ S)
    (hPd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j))
    (hQd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j))
    (hpayP : ∀ i ∈ I, -d i ≤ ∑ n ∈ P i, signedPart 1 A L y N n)
    (hpayQ : ∀ i ∈ J, -e i ≤ ∑ n ∈ Q i, signedPart (-1) A L y N n) :
    (∑ n ∈ S\(I.biUnion P ∪ D), signedPart 1 A L y N n)+
      (∑ n ∈ S\(J.biUnion Q ∪ D), signedPart (-1) A L y N n)-
      ((∑ i ∈ I, d i)+(∑ i ∈ J, e i)+(allTieConstant/v)*(amplitude N v/v)) ≤
        (∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := bounded_count_parts_floor A D (I.biUnion P) (J.biUnion Q) y hv hNv hL hD
  have hf := two_cover_floor A S I J P Q L y N d e hP hQ hPd hQd hpayP hpayQ
  rw [missed_boundary_split S D (I.biUnion P) hDsub (signedPart 1 A L y N),
    missed_boundary_split S D (J.biUnion Q) hDsub (signedPart (-1) A L y N)] at hf
  linarith only [hb,hf]

/-- The boundary saving strengthens the current source-equivalent
`joinedPhysical` floor itself. No selected mode is estimated, and only
the independently paid core/joined error is added. -/
theorem joined_two_cover_floor_with_ties {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N K : ℕ)
    (hLcore : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (D I J : Finset ℕ) (P Q : ℕ → Finset ℕ) (d e : ℕ → ℝ) {v : ℝ}
    (hv : 1000000 ≤ v) (hNv : (N : ℝ)+1 ≤ v)
    (hL : v/2 ≤ SquarefreeVaughanLogSource.length u N) :
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := ZetaRieszParityPacket.coreBand u N K;
    D ⊆ S →
    (∀ n ∈ D, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55 ∧
      (v-1/16 < Real.log n ∧ Real.log n ≤ v+1/16) ∧ CloseOwners n) →
    (∀ i ∈ I, P i ⊆ S) → (∀ i ∈ J, Q i ⊆ S) →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j)) →
    (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j)) →
    (∀ i ∈ I, -d i ≤ ∑ n ∈ P i, signedPart 1 A L y N n) →
    (∀ i ∈ J, -e i ≤ ∑ n ∈ Q i, signedPart (-1) A L y N n) →
    u^(N+1)*((∑ n ∈ S\(I.biUnion P ∪ D), signedPart 1 A L y N n)+
      (∑ n ∈ S\(J.biUnion Q ∪ D), signedPart (-1) A L y N n)-
      ((∑ i ∈ I, d i)+(∑ i ∈ J, e i)+(allTieConstant/v)*(amplitude N v/v)))-
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) ≤
        ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  dsimp only
  intro hDsub hD hP hQ hPd hQd hpayP hpayQ
  have hf := two_cover_floor_with_ties _ _ D I J P Q y N hv hNv hL d e
    hDsub hD hP hQ hPd hQd hpayP hpayQ
  have hs := mul_le_mul_of_nonneg_left hf (pow_nonneg hu (N+1))
  have hb := (Complex.re_le_norm ((u : ℂ)^(N+1)*
    (ZetaRieszParityPacket.coreResponse u y N K-ZetaRieszGammaJoint.joinedPhysical u y N K))).trans
      (ZetaRieszGammaJoint.core_joined_bound hu hU N K y hLcore)
  rw [mul_sub,Complex.sub_re] at hb
  have hc : ((u : ℂ)^(N+1)*ZetaRieszParityPacket.coreResponse u y N K).re =
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hc] at hb
  change _ ≤ u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re at hs
  linarith only [hs,hb]

/-- A growing finite radial cover pays all of its close-owner labels.
Overlap only enlarges this boundary cost; it never duplicates the original
carrier or spends a signed-period credit again. -/
theorem grouped_count_norm_bound (A D H : Finset ℕ) (B : ℕ → Finset ℕ)
    (y : ℝ) (N : ℕ) (v : ℕ → ℝ) {L : ℝ}
    (hcover : D ⊆ H.biUnion B)
    (hgeo : ∀ i ∈ H, 1000000 ≤ v i ∧ (N : ℝ)+1 ≤ v i ∧ v i/2 ≤ L)
    (hB : ∀ i ∈ H, ∀ n ∈ B i, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55 ∧
      (v i-1/16 < Real.log n ∧ Real.log n ≤ v i+1/16) ∧ CloseOwners n) :
    (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
      ∑ i ∈ H, (allTieConstant/v i)*(amplitude N (v i)/v i) := by
  let V := H.sigma B
  let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
  have hsub : D ⊆ V.image (fun x => x.2) := by
    intro n hn
    obtain ⟨i,hi,hni⟩ := Finset.mem_biUnion.mp (hcover hn)
    exact Finset.mem_image.mpr ⟨⟨i,n⟩,Finset.mem_sigma.mpr ⟨hi,hni⟩,rfl⟩
  have hs := (Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
    (fun n _ _ => norm_nonneg _)).trans
      (Finset.sum_image_le_of_nonneg (fun n _ => norm_nonneg _))
  change (∑ n ∈ D, f n) ≤ _
  apply hs.trans
  change (∑ x ∈ H.sigma B, f x.2) ≤ _
  rw [Finset.sum_sigma]
  apply Finset.sum_le_sum
  intro i hi
  have hg := hgeo i hi
  exact bounded_count_norm_bound A (B i) y hg.1 hg.2.1 hg.2.2 (hB i hi)

/-- The growing cover's single norm debit pays both missing sign parts
of its selected literal boundary labels, with no disjointness assumption. -/
theorem grouped_tie_parts_floor (A D P Q H : Finset ℕ) (B : ℕ → Finset ℕ)
    (y : ℝ) (N : ℕ) (v : ℕ → ℝ) {L : ℝ}
    (hcover : D ⊆ H.biUnion B)
    (hgeo : ∀ i ∈ H, 1000000 ≤ v i ∧ (N : ℝ)+1 ≤ v i ∧ v i/2 ≤ L)
    (hB : ∀ i ∈ H, ∀ n ∈ B i, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55 ∧
      (v i-1/16 < Real.log n ∧ Real.log n ≤ v i+1/16) ∧ CloseOwners n) :
    -(∑ i ∈ H, (allTieConstant/v i)*(amplitude N (v i)/v i)) ≤
      (∑ n ∈ D\P, signedPart 1 A L y N n)+
        (∑ n ∈ D\Q, signedPart (-1) A L y N n) := by
  have hb := grouped_count_norm_bound A D H B y N v hcover hgeo hB
  have hf := missed_parts_floor A D P Q L y N
  linarith only [hb,hf]

/-- Every growing finite collection of boundary windows in the original
linear core has arbitrarily small relative debit, summed only after the
literal labels are covered. This is not source-scale decay. -/
theorem eventually_core_grouped_tie_floor {u ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (y : ℝ) (D P Q H : Finset ℕ)
      (B : ℕ → Finset ℕ) (v : ℕ → ℝ),
      D ⊆ H.biUnion B →
      (∀ i ∈ H, (39/20 : ℝ)*N ≤ v i ∧ v i ≤ (203/100 : ℝ)*N) →
      (∀ i ∈ H, ∀ n ∈ B i, Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
        n.primeFactors.card ≤ 55 ∧
        (v i-1/16 < Real.log n ∧ Real.log n ≤ v i+1/16) ∧ CloseOwners n) →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N;
      -ε*(∑ i ∈ H, Real.exp (-v i/2)*(v i)^N/N.factorial) ≤
        (∑ n ∈ D\P, signedPart 1 A L y N n)+
          (∑ n ∈ D\Q, signedPart (-1) A L y N n) := by
  filter_upwards [eventually_core_tie_norm_bound hu hU hε] with N hN y D P Q H B v hcover hgeo hB
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  have hnorm (i : ℕ) (hi : i ∈ H) :
      (∑ n ∈ B i, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
        ε*(Real.exp (-v i/2)*(v i)^N/N.factorial) := by
    exact hN (v i) y (B i) (hgeo i hi).1 (hgeo i hi).2 (hB i hi)
  have hb := missed_parts_floor A D P Q L y N
  have hg : (∑ n ∈ D, ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
        ∑ i ∈ H, ε*(Real.exp (-v i/2)*(v i)^N/N.factorial) := by
    let V := H.sigma B
    let f := fun n => ‖ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖
    have hsub : D ⊆ V.image (fun x => x.2) := by
      intro n hn
      obtain ⟨i,hi,hni⟩ := Finset.mem_biUnion.mp (hcover hn)
      exact Finset.mem_image.mpr ⟨⟨i,n⟩,Finset.mem_sigma.mpr ⟨hi,hni⟩,rfl⟩
    have hs := (Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
      (fun n _ _ => norm_nonneg _)).trans
        (Finset.sum_image_le_of_nonneg (fun n _ => norm_nonneg _))
    apply hs.trans
    change (∑ x ∈ H.sigma B, f x.2) ≤ _
    rw [Finset.sum_sigma]
    exact Finset.sum_le_sum hnorm
  rw [← Finset.mul_sum] at hg
  linarith only [hb,hg]

end RiemannGaussian.ZetaRieszOwnerTieFloor
