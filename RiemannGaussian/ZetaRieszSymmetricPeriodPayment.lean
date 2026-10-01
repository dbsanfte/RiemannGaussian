/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTransitionFiveFloor
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false

/-! # Symmetry savings for the joined signed prime-period population

Every squarefree cofactor has exactly `k!` distinct orderings of its prime
factors. Removing this overcount divides the existing signed period cost
by `k!`. The arithmetic response, phase, allocation, and selected complete
prime fibres are unchanged. Clipped periods and the literal owner holes
are not completed by this estimate.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSymmetricPeriodPayment
open ZetaRieszCofactorMass ZetaRieszFixedCountPeriod ZetaRieszSignedPeriodFloor
open ZetaRieszStaggeredFloor ZetaRieszAllowancePrimeBoxes
open ZetaRieszTransitionFiveFloor

/-- The prime ordering overcount is exactly factorial, even for an
arbitrary selected squarefree population. -/
theorem factorial_product_mass (D P : Finset ℕ) (k : ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, 0 ≤ f p)
    (hD : ∀ a ∈ D, Squarefree a ∧ a.primeFactors.card = k ∧
      a.primeFactors ⊆ P) :
    (k.factorial : ℝ) * (∑ a ∈ D, ∏ p ∈ a.primeFactors, f p) ≤
      (∑ p ∈ P, f p)^k := by
  let ord (a : {a // a ∈ D}) :=
    a.val.primeFactors.orderEmbOfFin (hD a.val a.property).2.1
  let E := D.attach.product (Finset.univ : Finset (Equiv.Perm (Fin k)))
  let g (x : {a // a ∈ D} × Equiv.Perm (Fin k)) (i : Fin k) := ord x.1 (x.2 i)
  have hprod (a : {a // a ∈ D}) (F : ℕ → ℝ) :
      (∏ i, F (ord a i)) = ∏ p ∈ a.val.primeFactors, F p := by
    have he := a.val.primeFactors.image_orderEmbOfFin_univ (hD a.val a.property).2.1
    rw [← he, Finset.prod_image (ord a).injective.injOn]
  have hnat (a : {a // a ∈ D}) : (∏ i, ord a i) = a.val := by
    have he := a.val.primeFactors.image_orderEmbOfFin_univ (hD a.val a.property).2.1
    rw [← Nat.prod_primeFactors_of_squarefree (hD a.val a.property).1,
      ← he, Finset.prod_image (ord a).injective.injOn]
  have hgnat (x : {a // a ∈ D} × Equiv.Perm (Fin k)) : (∏ i, g x i) = x.1.val := by
    change (∏ i, ord x.1 (x.2 i)) = x.1.val
    rw [Equiv.prod_comp, hnat]
  have hginj : Function.Injective g := by
    rintro ⟨a, σ⟩ ⟨b, τ⟩ h
    have hab : a = b := Subtype.ext (by
      simpa only [hgnat] using congrArg (fun q : Fin k → ℕ => ∏ i, q i) h)
    subst b
    have hστ : σ = τ := by
      apply Equiv.ext
      intro i
      exact (ord a).injective (congrFun h i)
    subst τ
    rfl
  have hmem : E.image g ⊆ Fintype.piFinset (fun _ : Fin k => P) := by
    intro q hq
    obtain ⟨⟨a, σ⟩, _, rfl⟩ := Finset.mem_image.mp hq
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (hD a.val a.property).2.2
      (a.val.primeFactors.orderEmbOfFin_mem (hD a.val a.property).2.1 (σ i))
  have heq : (∑ x ∈ E, ∏ i, f (g x i)) =
      (k.factorial : ℝ) * (∑ a ∈ D, ∏ p ∈ a.primeFactors, f p) := by
    have hw (x : {a // a ∈ D} × Equiv.Perm (Fin k)) :
        (∏ i, f (g x i)) = ∏ p ∈ x.1.val.primeFactors, f p :=
      (Equiv.prod_comp x.2 (fun i => f (ord x.1 i))).trans (hprod x.1 f)
    dsimp only [E]
    rw [Finset.product_eq_sprod]
    rw [Finset.sum_product D.attach (Finset.univ : Finset (Equiv.Perm (Fin k)))
      (fun x : {a // a ∈ D} × Equiv.Perm (Fin k) => ∏ i, f (g x i))]
    simp only [hw, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      ]
    congr 1
    exact Finset.sum_attach D (fun a => ∏ p ∈ a.primeFactors, f p)
  calc
    _ = ∑ x ∈ E, ∏ i, f (g x i) := heq.symm
    _ = ∑ q ∈ E.image g, ∏ i, f (q i) :=
      (Finset.sum_image (f := fun q : Fin k → ℕ => ∏ i, f (q i)) hginj.injOn).symm
    _ ≤ ∑ q ∈ Fintype.piFinset (fun _ : Fin k => P), ∏ i, f (q i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hmem (by
        intro q hq _
        exact Finset.prod_nonneg (fun i _ => hf _ (Fintype.mem_piFinset.mp hq i)))
    _ = _ := (Finset.sum_pow' P f k).symm

private theorem prime_moment {v e : ℝ} (hv : 0 < v) (he : 0 < e) :
    (∑ p ∈ primes v, (Real.log p)^e*(p : ℝ)⁻¹) ≤
      ZetaRieszPrimeFractionalBudget.momentConstant e*v^e := by
  have hh := ZetaRieszPrimeFractionalBudget.prime_fractional_log_mass_le (primes v) hv he
    (by intro p hp; have hb := logPrimes_bounds hp; exact ⟨hb.1,by simpa using hb.2.2⟩)
  have heq (p : ℕ) (hp : p ∈ primes v) : Real.exp (-Real.log p) = (p : ℝ)⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast (logPrimes_bounds hp).1.pos)]
  exact (Finset.sum_congr rfl (fun p hp => by rw [heq p hp])).le.trans hh

private theorem primeFactors_subset {D : Finset ℕ} {k : ℕ} {v : ℝ}
    (hD : D ⊆ products k v) {a : ℕ} (ha : a ∈ D) : a.primeFactors ⊆ primes v := by
  obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp (hD ha)
  intro q hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  rw [← hpa] at hqd
  obtain ⟨i, _, hi⟩ :=
    ((Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hq)).dvd_finsetProd_iff p).mp hqd
  have hpi := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  have heq := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hpi).mp hi
  exact heq ▸ Fintype.mem_piFinset.mp hp i

/-- The original least-prime weighted cofactor cost loses its exact
factorial overcount. No phase or label is averaged. -/
theorem factorial_log_mass {k : ℕ} (hk : 0 < k) {v : ℝ} (hv : 0 < v)
    (D : Finset ℕ) (hD : D ⊆ products k v)
    (hSF : ∀ a ∈ D, Squarefree a ∧ a.primeFactors.card = k) :
    (k.factorial : ℝ) * (∑ a ∈ D, Real.log a.minFac*(a : ℝ)⁻¹) ≤
      logMassConstant k*v := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let f := fun p : ℕ => (Real.log p)^(1/(k : ℝ))*(p : ℝ)⁻¹
  have hpoint (a : ℕ) (ha : a ∈ D) :
      Real.log a.minFac*(a : ℝ)⁻¹ ≤ ∏ p ∈ a.primeFactors, f p := by
    let p := a.primeFactors.orderEmbOfFin (hSF a ha).2
    have hp (i : Fin k) : p i ∈ a.primeFactors :=
      a.primeFactors.orderEmbOfFin_mem (hSF a ha).2 i
    have hn1 : a ≠ 1 := by
      intro h
      have hc := (hSF a ha).2
      rw [h] at hc
      simp only [Nat.primeFactors_one, Finset.card_empty] at hc
      omega
    have ht : 0 < Real.log a.minFac :=
      Real.log_pos (by exact_mod_cast (Nat.minFac_prime hn1).one_lt)
    have hb := minimum_le_product hk ht (fun i => Real.log (p i)) (by
      intro i
      exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos a)
        (by exact_mod_cast (Nat.minFac_le_of_dvd
          (Nat.prime_of_mem_primeFactors (hp i)).two_le (Nat.dvd_of_mem_primeFactors (hp i)))))
    have he := a.primeFactors.image_orderEmbOfFin_univ (hSF a ha).2
    have hprod : (∏ i, p i) = a := by
      rw [← Nat.prod_primeFactors_of_squarefree (hSF a ha).1, ← he,
        Finset.prod_image p.injective.injOn]
    have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ (a : ℝ)⁻¹ by positivity)
    rw [← he, Finset.prod_image p.injective.injOn]
    simpa only [f, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      ← Nat.cast_prod, hprod] using hh
  have hmass := factorial_product_mass D (primes v) k f (by intro p _; positivity)
    (by intro a ha; exact ⟨(hSF a ha).1,(hSF a ha).2,primeFactors_subset hD ha⟩)
  calc
    _ ≤ (k.factorial : ℝ)*(∑ a ∈ D, ∏ p ∈ a.primeFactors, f p) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (Nat.cast_nonneg _)
    _ ≤ (∑ p ∈ primes v, f p)^k := hmass
    _ ≤ (ZetaRieszPrimeFractionalBudget.momentConstant (1/(k : ℝ))*v^(1/(k : ℝ)))^k :=
      pow_le_pow_left₀ (by positivity) (prime_moment hv (by positivity)) k
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hv.le]
      simp [logMassConstant, hkR.ne']

/-- The same symmetry saving applies to the unsigned reciprocal mass
used for the already-signed prime-period cutoff variation. -/
theorem factorial_reciprocal_mass {k : ℕ} (hk : 0 < k) {v : ℝ} (hv : 0 < v)
    (D : Finset ℕ) (hD : D ⊆ products k v)
    (hSF : ∀ a ∈ D, Squarefree a ∧ a.primeFactors.card = k) :
    (k.factorial : ℝ) * (∑ a ∈ D, (a : ℝ)⁻¹) ≤
      variationConstant k*v^(1/2 : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let e : ℝ := 1/(2*(k : ℝ))
  have he : 0 < e := by dsimp [e]; positivity
  have heu : e ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hprime : (∑ p ∈ primes v, (p : ℝ)⁻¹) ≤
      (2*ZetaRieszPrimeFractionalBudget.momentConstant e)*v^e := by
    have hpoint (p : ℕ) (hp : p ∈ primes v) :
        (p : ℝ)⁻¹ ≤ 2*((Real.log p)^e*(p : ℝ)⁻¹) := by
      have hp0 := (logPrimes_bounds hp).1
      have hlo : (1/2 : ℝ) ≤ Real.log p := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ p by exact_mod_cast hp0.two_le)
        linarith [Real.log_two_gt_d9]
      have hb := (Real.self_le_rpow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num) heu).trans (Real.rpow_le_rpow (by norm_num) hlo he.le)
      nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ (p : ℝ)⁻¹ by positivity)]
    calc
      _ ≤ ∑ p ∈ primes v, 2*((Real.log p)^e*(p : ℝ)⁻¹) := Finset.sum_le_sum hpoint
      _ ≤ _ := by rw [← Finset.mul_sum]; nlinarith only [prime_moment hv he]
  have hmass := factorial_product_mass D (primes v) k (fun p => (p : ℝ)⁻¹)
    (by intro p _; positivity)
    (by intro a ha; exact ⟨(hSF a ha).1,(hSF a ha).2,primeFactors_subset hD ha⟩)
  have heq (a : ℕ) (ha : a ∈ D) : (∏ p ∈ a.primeFactors, (p : ℝ)⁻¹) = (a : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hSF a ha).1]
  calc
    _ = (k.factorial : ℝ)*(∑ a ∈ D, ∏ p ∈ a.primeFactors, (p : ℝ)⁻¹) := by
      rw [Finset.sum_congr rfl heq]
    _ ≤ (∑ p ∈ primes v, (p : ℝ)⁻¹)^k := hmass
    _ ≤ ((2*ZetaRieszPrimeFractionalBudget.momentConstant e)*v^e)^k :=
      pow_le_pow_left₀ (by positivity) hprime k
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hv.le]
      have heq : e*(k : ℝ) = 1/2 := by dsimp [e]; field_simp
      rw [heq]
      rfl

/-- The original complete-period signed cost divided by its exact
squarefree prime-ordering multiplicity. -/
def symmetricCost (k : ℕ) : ℝ := populationConstant k/(k.factorial : ℝ)

theorem symmetricCost_nonneg (k : ℕ) : 0 ≤ symmetricCost k := by
  by_cases hk : 0 < k
  · have hCl := (constants_pos hk).1
    have hCv := (constants_pos hk).2
    unfold symmetricCost populationConstant
    positivity [responseConstant_pos k]
  · have hk0 : k = 0 := by omega
    subst k
    norm_num [symmetricCost, populationConstant, logMassConstant, variationConstant,
      responseConstant, ZetaRieszSignedSperner.parityCapacity]
    positivity

/-- On the unresolved seven-or-more-prime labels, every cofactor has
at least six factors. The ENTIRE selected count budget loses a factor
of at least `6! = 720`, including moving count sets. -/
theorem sum_symmetricCost_le_six_factorial (I : Finset ℕ)
    (hI : ∀ k ∈ I, 6 ≤ k) :
    (∑ k ∈ I, symmetricCost k) ≤ (∑ k ∈ I, populationConstant k)/720 := by
  have hh (k : ℕ) (hk : k ∈ I) : symmetricCost k ≤ populationConstant k/720 := by
    have hk0 : 0 < k := by have hb := hI k hk; omega
    have hCl := (constants_pos hk0).1
    have hCv := (constants_pos hk0).2
    have hpop : 0 ≤ populationConstant k := by
      unfold populationConstant
      positivity [responseConstant_pos k]
    have hfact : (720 : ℝ) ≤ k.factorial := by
      have hb := Nat.factorial_le (hI k hk)
      norm_num at hb
      exact_mod_cast hb
    exact div_le_div_of_nonneg_left hpop (by norm_num) hfact
  simpa only [Finset.sum_div] using Finset.sum_le_sum hh

/-- The symmetry saving applies after each prime fibre was summed with
its literal sign, factorial weight, and owner allocation. It holds at
every count, without a fixed-count eventual threshold. -/
theorem signed_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    (A S : Finset ℕ) {v y L : ℝ} (hv : 500000 ≤ v)
    (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L)
    (hS : S ⊆ ZetaRieszTransitionFiveFloor.cofactors k v)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -(symmetricCost k*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e A L y N (p*a) := by
  have hv0 : 0 < v := by linarith
  have hk0 : 0 < k := by omega
  have hCl := (constants_pos hk0).1
  have hCv := (constants_pos hk0).2
  have hFct : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  let F := 200000*responseConstant k/v^2+
    1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2
  let G := 400*(2 : ℝ)^k/v
  have hF : 0 ≤ F := by dsimp [F]; positivity [responseConstant_pos k]
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hset : S ⊆ products k v := hS.trans (Finset.filter_subset _ _)
  have hSF (a : ℕ) (ha : a ∈ S) : Squarefree a ∧ a.primeFactors.card = k := by
    have hb := ZetaRieszTransitionFiveFloor.cofactor_data (hS ha)
    exact ⟨hb.1,hb.2.1⟩
  have hlog := factorial_log_mass hk0 hv0 S hset hSF
  have hrec := factorial_reciprocal_mass hk0 hv0 S hset hSF
  have hmass : (k.factorial : ℝ)*(∑ a ∈ S,
      (F*(Real.log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
      F*(logMassConstant k*v)+G*(variationConstant k*v^(1/2 : ℝ)) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    have hl := mul_le_mul_of_nonneg_left hlog hF
    have hr := mul_le_mul_of_nonneg_left hrec hG
    nlinarith only [hl,hr]
  have hrat : v^(1/2 : ℝ)/v = v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have hsqrt : Real.sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt (show (N : ℝ)+1 ≤ v by linarith)) hv0.le
    rwa [Real.sqrt_eq_rpow v,hrat] at hh
  have hinv : 1/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ v by linarith)
      (show (-1 : ℝ) ≤ -(1/2 : ℝ) by norm_num)
    simpa only [Real.rpow_neg_one,one_div] using hh
  have hcosteq : F*(logMassConstant k*v)+G*(variationConstant k*v^(1/2 : ℝ)) =
      200000*responseConstant k*logMassConstant k*(1/v)+
        1200*((k : ℝ)+1)*responseConstant k*logMassConstant k*(Real.sqrt (N+1)/v)+
        400*(2 : ℝ)^k*variationConstant k*(v^(1/2 : ℝ)/v) := by
    dsimp [F,G]
    field_simp
  have hpay : F*(logMassConstant k*v)+G*(variationConstant k*v^(1/2 : ℝ)) ≤
      populationConstant k*v^(-(1/2 : ℝ)) := by
    rw [hcosteq,hrat]
    have h₁ := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ 200000*responseConstant k*logMassConstant k by
        positivity [responseConstant_pos k])
    have h₂ := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 1200*((k : ℝ)+1)*responseConstant k*logMassConstant k by
        positivity [responseConstant_pos k])
    unfold populationConstant
    nlinarith only [h₁,h₂]
  have hcost : (∑ a ∈ S, (F*(Real.log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
      symmetricCost k*v^(-(1/2 : ℝ)) := by
    have hh : (∑ a ∈ S, (F*(Real.log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
        (populationConstant k*v^(-(1/2 : ℝ)))/(k.factorial : ℝ) :=
      (le_div_iff₀ hFct).mpr (by nlinarith only [hmass.trans hpay])
    simpa only [symmetricCost, div_mul_eq_mul_div] using hh
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    signedPart_fibre_radial hk he A hv hNv hy hL (hS ha) (hA a ha) hpeak hsign)
  rw [← Finset.mul_sum] at hrow
  have hh := mul_le_mul_of_nonpos_left hcost (neg_nonpos.mpr hbase)
  calc
    _ = -(amplitude N v/v)*(symmetricCost k*v^(-(1/2 : ℝ))) := by ring
    _ ≤ _ := hh.trans hrow

/-- All selected counts are charged jointly against one radial unit.
The count set and the literal cofactor selectors may move with the order. -/
theorem joined_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ → Finset ℕ) {v y L : ℝ} (hI : ∀ k ∈ I, 2 ≤ k) (he : |e| = 1)
    (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L)
    (hS : ∀ k ∈ I, S k ⊆ ZetaRieszTransitionFiveFloor.cofactors k v)
    (hA : ∀ k ∈ I, ∀ a ∈ S k,
      ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -((∑ k ∈ I, symmetricCost k)*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      ∑ k ∈ I, ∑ a ∈ S k,
        ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
          signedPart e A L y N (p*a) := by
  have hh := Finset.sum_le_sum (fun k hk =>
    signed_population_floor (hI k hk) he A (S k) hv hNv hy hL (hS k hk)
      (hA k hk) hpeak hsign)
  simpa only [neg_mul,← Finset.sum_mul,Finset.sum_neg_distrib] using hh

/-- A uniform linear bound on the existing fractional prime-moment
constant. This makes the factorial saving quantitative as the count grows. -/
theorem momentConstant_reciprocal_le {k : ℕ} (hk : 0 < k) :
    ZetaRieszPrimeFractionalBudget.momentConstant (1/(k : ℝ)) ≤ 48*(k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let x : ℝ := Real.log 2/k
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one hk0).mpr
    linarith [Real.log_two_lt_d9]
  have hxlo : 1/(2*(k : ℝ)) ≤ x := by
    dsimp [x]
    rw [show 1/(2*(k : ℝ)) = (1/2 : ℝ)/k by ring]
    apply div_le_div_of_nonneg_right _ hk0.le
    linarith [Real.log_two_gt_d9]
  have hexp : (1+x)*Real.exp (-x) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_nonneg (-x))
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hh
    nlinarith only [hh]
  have hgap0 : 0 ≤ 1-Real.exp (-x) := by
    have hh := Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)
    linarith
  have hgap : 1/(4*(k : ℝ)) ≤ 1-Real.exp (-x) := by
    have hh := mul_le_mul_of_nonneg_right (show 1+x ≤ 2 by linarith) hgap0
    have hxgap : x ≤ (1+x)*(1-Real.exp (-x)) := by nlinarith only [hexp]
    have hfour : 1/(4*(k : ℝ)) = (1/(2*(k : ℝ)))/2 := by ring
    rw [hfour]
    nlinarith only [hh,hxgap,hxlo]
  have heq : (1/2 : ℝ)^(1/(k : ℝ)) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    congr 1
    rw [show (1/2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    dsimp [x]
    ring
  rw [← heq] at hgap
  have hden : 0 < 1-(1/2 : ℝ)^(1/(k : ℝ)) :=
    (by positivity : (0 : ℝ) < 1/(4*(k : ℝ))).trans_le hgap
  have hlog4 : Real.log 4 < 2 := by
    have he : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  unfold ZetaRieszPrimeFractionalBudget.momentConstant
  apply (div_le_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left hgap (show (0 : ℝ) ≤ 48*k by positivity)
  have he : (48*(k : ℝ))*(1/(4*(k : ℝ))) = 12 := by field_simp; ring
  rw [he] at hmul
  linarith

private theorem factorial_power_bound {k : ℕ} {B : ℝ}
    (hB : 0 ≤ B) {M : ℝ} (hM : 0 ≤ M) (hMbound : M ≤ B*k) :
    M^k/(k.factorial : ℝ) ≤ (3*B)^k := by
  have hF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hh := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hM hMbound k) hF.le
  have hp := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg _) k
  have he : Real.exp (k : ℝ) ≤ (3 : ℝ)^k := by
    rw [show (k : ℝ) = (k : ℝ)*1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_three.le k
  calc
    _ ≤ (B*(k : ℝ))^k/(k.factorial : ℝ) := hh
    _ = B^k*((k : ℝ)^k/(k.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ B^k*(3 : ℝ)^k := mul_le_mul_of_nonneg_left (hp.trans he) (pow_nonneg hB k)
    _ = _ := by rw [← mul_pow]; ring

/-- After symmetry, the least-prime mass constant grows only
exponentially in the cofactor count. -/
theorem logMassConstant_div_factorial {k : ℕ} (hk : 0 < k) :
    logMassConstant k/(k.factorial : ℝ) ≤ (144 : ℝ)^k := by
  have he : 0 < (1/(k : ℝ)) := by positivity
  have hp := ZetaRieszPrimeFractionalBudget.momentConstant_pos he
  have hh := factorial_power_bound (by norm_num : (0 : ℝ) ≤ 48) hp.le
    (momentConstant_reciprocal_le hk)
  norm_num at hh
  norm_num [logMassConstant]
  exact hh

/-- The cutoff-variation mass has the same uniform exponential behavior. -/
theorem variationConstant_div_factorial {k : ℕ} (hk : 0 < k) :
    variationConstant k/(k.factorial : ℝ) ≤ (576 : ℝ)^k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 := momentConstant_reciprocal_le (show 0 < 2*k by omega)
  have hcast : ((2*k : ℕ) : ℝ) = 2*(k : ℝ) := by norm_num
  rw [hcast] at h2
  have he : 0 < 1/(2*(k : ℝ)) := by positivity
  have hp := ZetaRieszPrimeFractionalBudget.momentConstant_pos he
  have hM : 2*ZetaRieszPrimeFractionalBudget.momentConstant (1/(2*(k : ℝ))) ≤ 192*k := by
    nlinarith only [h2]
  have hh := factorial_power_bound (by norm_num : (0 : ℝ) ≤ 192)
    (show 0 ≤ 2*ZetaRieszPrimeFractionalBudget.momentConstant (1/(2*(k : ℝ))) by positivity)
    hM
  norm_num at hh
  norm_num [variationConstant]
  exact hh

private theorem successor_le_two_pow (k : ℕ) : ((k : ℝ)+1) ≤ (2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ, pow_succ]
    have ht : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
    nlinarith only [ih, ht]

private theorem responseConstant_le (k : ℕ) : responseConstant k ≤ 6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ) ≤ (2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    have ht : (2 : ℕ)^(k-2) ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hh.trans ht
  have h0 := hp 0
  have h1 := hp 1
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  unfold responseConstant
  nlinarith only [h0,h1,hpow]

/-- One uniform count-dependent price for the actual signed complete
prime periods. The former `k^k` overcount is absent. -/
theorem symmetricCost_le_exponential {k : ℕ} (hk : 0 < k) :
    symmetricCost k ≤ 2000000*(2048 : ℝ)^k := by
  have hL := logMassConstant_div_factorial hk
  have hV := variationConstant_div_factorial hk
  have hL0 : 0 ≤ logMassConstant k/(k.factorial : ℝ) := by
    positivity [(constants_pos hk).1]
  have hV0 : 0 ≤ variationConstant k/(k.factorial : ℝ) := by
    positivity [(constants_pos hk).2]
  have hR0 := (responseConstant_pos k).le
  have hR := responseConstant_le k
  have hsucc := successor_le_two_pow k
  have heq : symmetricCost k =
      200000*responseConstant k*(logMassConstant k/(k.factorial : ℝ))+
        1200*((k : ℝ)+1)*responseConstant k*(logMassConstant k/(k.factorial : ℝ))+
        400*(2 : ℝ)^k*(variationConstant k/(k.factorial : ℝ)) := by
    unfold symmetricCost populationConstant
    ring
  have h₁ : 200000*responseConstant k*(logMassConstant k/(k.factorial : ℝ)) ≤
      1200000*(288 : ℝ)^k := by
    calc
      _ ≤ 200000*(6*(2 : ℝ)^k)*(144 : ℝ)^k := by gcongr
      _ = _ := by rw [show (288 : ℝ) = 2*144 by norm_num, mul_pow]; ring
  have h₂ : 1200*((k : ℝ)+1)*responseConstant k*(logMassConstant k/(k.factorial : ℝ)) ≤
      7200*(576 : ℝ)^k := by
    calc
      _ ≤ 1200*(2 : ℝ)^k*(6*(2 : ℝ)^k)*(144 : ℝ)^k := by gcongr
      _ = _ := by rw [show (576 : ℝ) = 2*2*144 by norm_num]; simp only [mul_pow]; ring
  have h₃ : 400*(2 : ℝ)^k*(variationConstant k/(k.factorial : ℝ)) ≤
      400*(1152 : ℝ)^k := by
    calc
      _ ≤ 400*(2 : ℝ)^k*(576 : ℝ)^k := by gcongr
      _ = _ := by rw [show (1152 : ℝ) = 2*576 by norm_num, mul_pow]; ring
  have hp₁ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 288) (by norm_num : (288 : ℝ) ≤ 2048) k
  have hp₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 576) (by norm_num : (576 : ℝ) ≤ 2048) k
  have hp₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1152) (by norm_num : (1152 : ℝ) ≤ 2048) k
  have hp₀ : 0 ≤ (2048 : ℝ)^k := by positivity
  rw [heq]
  nlinarith only [h₁,h₂,h₃,hp₁,hp₂,hp₃,hp₀]

/-- The entire selected count band has one exponential-in-count price,
rather than an unquantified sum of fixed-count eventual constants. -/
theorem sum_symmetricCost_le (I : Finset ℕ) (K : ℕ)
    (hI : ∀ k ∈ I, 0 < k ∧ k ≤ K) :
    (∑ k ∈ I, symmetricCost k) ≤ 2000000*(4096 : ℝ)^K := by
  have hsub : I ⊆ Finset.range (K+1) := by
    intro k hk
    exact Finset.mem_range.mpr (by have hh := (hI k hk).2; omega)
  have hcard : (I.card : ℝ) ≤ (K : ℝ)+1 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_range] at hh
    exact_mod_cast hh
  have hsingle (k : ℕ) (hk : k ∈ I) : symmetricCost k ≤ 2000000*(2048 : ℝ)^K :=
    (symmetricCost_le_exponential (hI k hk).1).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (hI k hk).2) (by norm_num))
  calc
    _ ≤ ∑ _k ∈ I, 2000000*(2048 : ℝ)^K := Finset.sum_le_sum hsingle
    _ = (I.card : ℝ)*(2000000*(2048 : ℝ)^K) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ((K : ℝ)+1)*(2000000*(2048 : ℝ)^K) := by gcongr
    _ ≤ (2 : ℝ)^K*(2000000*(2048 : ℝ)^K) := by
      exact mul_le_mul_of_nonneg_right (successor_le_two_pow K) (by positivity)
    _ = _ := by rw [mul_left_comm, ← mul_pow]; norm_num

/-- The joined count cost is a vanishing fraction of a radial supply
unit as long as the fourth power of its exponential count scale fits
inside the radial length. -/
theorem joined_count_cost_le (I : Finset ℕ) (K : ℕ) {v : ℝ} (hv : 0 < v)
    (hI : ∀ k ∈ I, 0 < k ∧ k ≤ K) (hK : ((4096 : ℝ)^K)^4 ≤ v) :
    (∑ k ∈ I, symmetricCost k)*v^(-(1/2 : ℝ)) ≤
      2000000*v^(-(1/4 : ℝ)) := by
  have hpower : (4096 : ℝ)^K ≤ v^(1/4 : ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((4096 : ℝ)^K)^4)
      hK (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (4096 : ℝ)^K)] at hh
    norm_num at hh
    exact hh
  calc
    _ ≤ (2000000*(4096 : ℝ)^K)*v^(-(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (sum_symmetricCost_le I K hI) (by positivity)
    _ ≤ (2000000*v^(1/4 : ℝ))*v^(-(1/2 : ℝ)) := by gcongr
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hv]
      norm_num

/-- A deterministic growing count band with one quantitative joint
price. It is logarithmic in the order, not a fixed fifty-five cutoff. -/
def periodCountCeiling (N : ℕ) : ℕ := Nat.log 4096 (N+1)/4

theorem periodCountCeiling_power (N : ℕ) :
    ((4096 : ℝ)^periodCountCeiling N)^4 ≤ (N : ℝ)+1 := by
  have hm : periodCountCeiling N*4 ≤ Nat.log 4096 (N+1) := by
    exact Nat.div_mul_le_self _ _
  have hp := (Nat.pow_le_pow_right (by norm_num : 0 < (4096 : ℕ)) hm).trans
    (Nat.pow_log_le_self 4096 (Nat.succ_ne_zero N))
  rw [← pow_mul]
  exact_mod_cast hp

/-- The paid complete-period count range is genuinely unbounded. -/
theorem tendsto_periodCountCeiling : Tendsto periodCountCeiling atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (4096^(4*K) : ℕ)] with N hN
  have hpow : (4096 : ℕ)^(4*K) ≤ N+1 := by omega
  have hh := Nat.le_log_of_pow_le (by norm_num : 1 < (4096 : ℕ)) hpow
  change K ≤ Nat.log 4096 (N+1)/4
  omega

/-- A signed global estimate on every selected COMPLETE prime-period
fibre through the growing count ceiling. The cost is explicit and tends
to zero relative to the same radial supply; no count-dependent eventual
threshold or cancellation hypothesis is assumed. -/
theorem growing_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ → Finset ℕ) {v y L : ℝ}
    (hI : ∀ k ∈ I, 2 ≤ k ∧ k ≤ periodCountCeiling N) (he : |e| = 1)
    (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L)
    (hS : ∀ k ∈ I, S k ⊆ ZetaRieszTransitionFiveFloor.cofactors k v)
    (hA : ∀ k ∈ I, ∀ a ∈ S k,
      ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -(2000000*v^(-(1/4 : ℝ)))*(Real.exp (-v/2)*v^N/N.factorial) ≤
      ∑ k ∈ I, ∑ a ∈ S k,
        ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
          signedPart e A L y N (p*a) := by
  have hv0 : 0 < v := by linarith
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hcost := joined_count_cost_le I (periodCountCeiling N) hv0
    (by intro k hk; have hh := hI k hk; exact ⟨by omega,hh.2⟩)
    ((periodCountCeiling_power N).trans (by linarith))
  have hjoined := joined_counts_floor I N e A S (fun k hk => (hI k hk).1)
    he hv hNv hy hL hS hA hpeak hsign
  have hh := mul_le_mul_of_nonneg_right (neg_le_neg hcost) hbase
  have heq : amplitude N v/v = Real.exp (-v/2)*v^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  rw [heq] at hh hjoined
  exact hh.trans hjoined

theorem tendsto_growing_count_relative_cost :
    Tendsto (fun N : ℕ => 2000000*((N : ℝ)+1)^(-(1/4 : ℝ))) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).const_mul (2000000 : ℝ)
  have ht : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [mul_zero, Function.comp_def] using hlim.comp ht

/-- Counts and radial periods are summed before pricing. All selected
cofactor and prime fibres remain literal; the SAME radial units carry
one shrinking fraction, independently of the number of periods. -/
theorem radial_periods_floor (J : Finset ℕ) (N : ℕ) (A : Finset ℕ)
    (I : ℕ → Finset ℕ) (S : ℕ → ℕ → Finset ℕ) (v e : ℕ → ℝ)
    {y L : ℝ} (hy : 54 ≤ y)
    (hI : ∀ i ∈ J, ∀ k ∈ I i, 2 ≤ k ∧ k ≤ periodCountCeiling N)
    (he : ∀ i ∈ J, |e i| = 1)
    (hv : ∀ i ∈ J, 500000 ≤ v i ∧ (N : ℝ)+2 ≤ v i)
    (hL : ∀ i ∈ J, (67/100 : ℝ)*v i ≤ L)
    (hS : ∀ i ∈ J, ∀ k ∈ I i, S i k ⊆
      ZetaRieszTransitionFiveFloor.cofactors k (v i))
    (hA : ∀ i ∈ J, ∀ k ∈ I i, ∀ a ∈ S i k,
      ∀ p ∈ logPrimes (v i-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : ∀ i ∈ J, Real.sin (y*v i) = 0)
    (hsign : ∀ i ∈ J, e i*Real.cos (y*v i) ≤ 0) :
    -(2000000*((N : ℝ)+1)^(-(1/4 : ℝ)))*
        (∑ i ∈ J, Real.exp (-v i/2)*(v i)^N/N.factorial) ≤
      ∑ i ∈ J, ∑ k ∈ I i, ∑ a ∈ S i k,
        ∑ p ∈ logPrimes (v i-Real.pi/y-Real.log a) (2*Real.pi/y),
          signedPart (e i) A L y N (p*a) := by
  have hrow (i : ℕ) (hi : i ∈ J) :
      -(2000000*((N : ℝ)+1)^(-(1/4 : ℝ)))*
        (Real.exp (-v i/2)*(v i)^N/N.factorial) ≤
        ∑ k ∈ I i, ∑ a ∈ S i k,
          ∑ p ∈ logPrimes (v i-Real.pi/y-Real.log a) (2*Real.pi/y),
            signedPart (e i) A L y N (p*a) := by
    have hb := growing_counts_floor (I i) N (e i) A (S i) (hI i hi) (he i hi)
      (hv i hi).1 (hv i hi).2 hy (hL i hi) (hS i hi) (hA i hi) (hpeak i hi) (hsign i hi)
    have hcost : 2000000*(v i)^(-(1/4 : ℝ)) ≤
        2000000*((N : ℝ)+1)^(-(1/4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (N : ℝ)+1)
        (by have hh := (hv i hi).2; linarith) (by norm_num)
    have hunit : 0 ≤ Real.exp (-v i/2)*(v i)^N/N.factorial := by
      positivity [(show 0 ≤ v i by have hh := (hv i hi).1; linarith)]
    exact (mul_le_mul_of_nonneg_right (neg_le_neg hcost) hunit).trans hb
  have hh := Finset.sum_le_sum hrow
  simpa only [← Finset.mul_sum] using hh

/-- The joined growing-count population uses arbitrarily little of ANY
already-checked positive supply paying the same radial units. This is a
relative signed floor, not an independent source-scale numerical floor. -/
theorem eventually_radial_periods_supply_floor {ε κ y : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hy : 54 ≤ y) :
    ∀ᶠ N : ℕ in atTop, ∀ (J A : Finset ℕ) (I : ℕ → Finset ℕ)
      (S : ℕ → ℕ → Finset ℕ) (v e : ℕ → ℝ) (L supply : ℝ),
      (∀ i ∈ J, ∀ k ∈ I i, 2 ≤ k ∧ k ≤ periodCountCeiling N) →
      (∀ i ∈ J, |e i| = 1) →
      (∀ i ∈ J, (N : ℝ)+2 ≤ v i) →
      (∀ i ∈ J, (67/100 : ℝ)*v i ≤ L) →
      (∀ i ∈ J, ∀ k ∈ I i, S i k ⊆
        ZetaRieszTransitionFiveFloor.cofactors k (v i)) →
      (∀ i ∈ J, ∀ k ∈ I i, ∀ a ∈ S i k,
        ∀ p ∈ logPrimes (v i-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A) →
      (∀ i ∈ J, Real.sin (y*v i) = 0) →
      (∀ i ∈ J, e i*Real.cos (y*v i) ≤ 0) →
      κ*(∑ i ∈ J, Real.exp (-v i/2)*(v i)^N/N.factorial) ≤ supply →
      -ε*supply ≤ ∑ i ∈ J, ∑ k ∈ I i, ∑ a ∈ S i k,
        ∑ p ∈ logPrimes (v i-Real.pi/y-Real.log a) (2*Real.pi/y),
          signedPart (e i) A L y N (p*a) := by
  have ht := tendsto_growing_count_relative_cost.eventually_lt_const
    (show (0 : ℝ) < ε*κ by positivity)
  filter_upwards [ht, eventually_ge_atTop (500000 : ℕ)] with N hcost hN
    J A I S v e L supply hI he hv hL hS hA hpeak hsign hbudget
  have hNR : (500000 : ℝ) ≤ N := by exact_mod_cast hN
  have hbig : ∀ i ∈ J, 500000 ≤ v i ∧ (N : ℝ)+2 ≤ v i := by
    intro i hi
    exact ⟨by linarith only [hv i hi,hNR], hv i hi⟩
  have hf := radial_periods_floor J N A I S v e hy hI he hbig hL hS hA hpeak hsign
  have hunit : 0 ≤ ∑ i ∈ J, Real.exp (-v i/2)*(v i)^N/N.factorial :=
    Finset.sum_nonneg (fun i hi => by
      have hv0 : 0 ≤ v i := by linarith only [hv i hi]
      positivity)
  have hcostunit := mul_le_mul_of_nonneg_right hcost.le hunit
  have hpaid := mul_le_mul_of_nonneg_left hbudget hε.le
  nlinarith only [hf,hcostunit,hpaid]

end RiemannGaussian.ZetaRieszSymmetricPeriodPayment
