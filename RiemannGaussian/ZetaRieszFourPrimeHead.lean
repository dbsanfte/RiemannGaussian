/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPrimeExact
import RiemannGaussian.ZetaRieszJointSmoothFloor

/-!
# Arithmetic cost of the small-prime four-factor sector

Two small factors cancel exactly. Every surviving label therefore has
three macroscopic prime factors, whose unsigned counting cost can be
paid by the existing actual signed supply. The original moment, complex
phase, residual coefficient and all inherited finite selections remain.
-/

namespace RiemannGaussian.ZetaRieszFourPrimeHead
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime

/-- In the retained length range, two small prime factors force exact
saturation cancellation. No phase or factorial weight is estimated. -/
theorem coefficient_zero_of_two_small {n r p M : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 4)
    (hr : r ∈ n.primeFactors) (hp : p ∈ n.primeFactors.erase r)
    (hrlog : Real.log r ≤ (M : ℝ)/32) (hplog : Real.log p ≤ (M : ℝ)/16)
    (hmax : ∀ q ∈ n.primeFactors, Real.log q ≤ (5/4 : ℝ)*M)
    (hlo : 2*(M : ℝ) ≤ Real.log n) {L : ℝ}
    (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M) :
    SquarefreeVaughanLogSource.coefficient L n = 0 := by
  have hcard : ((n.primeFactors.erase r).erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hp,Finset.card_erase_of_mem hr,hc]
  obtain ⟨q,t,hqt,he⟩ := Finset.card_eq_two.mp hcard
  have hqE : q ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have htE : t ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hq := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqE)
  have ht := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase htE)
  have hr' := Nat.prime_of_mem_primeFactors hr
  have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hq' := Nat.prime_of_mem_primeFactors hq
  have ht' := Nat.prime_of_mem_primeFactors ht
  have hn : n = q*(t*(r*p)) := by
    rw [← Nat.prod_primeFactors_of_squarefree hs,
      ← Finset.mul_prod_erase _ _ hr,← Finset.mul_prod_erase _ _ hp,he]
    simp only [Finset.prod_insert (show q ∉ ({t} : Finset ℕ) by simpa using hqt),Finset.prod_singleton]
    ring
  have ha0 : r*p ≠ 0 := Nat.mul_ne_zero hr'.ne_zero hp'.ne_zero
  have ha1 : r*p ≠ 1 := by
    intro h
    exact hr'.ne_one (mul_eq_one.mp h).1
  have halog : Real.log (r*p : ℕ) = Real.log r+Real.log p := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hr'.ne_zero) (by exact_mod_cast hp'.ne_zero)]
  have hlog : Real.log n = Real.log q+Real.log t+Real.log (r*p : ℕ) := by
    rw [hn,Nat.cast_mul,Real.log_mul (by exact_mod_cast hq'.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero ht'.ne_zero ha0),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast ht'.ne_zero) (by exact_mod_cast ha0)]
    ring
  have hz := ZetaRieszJointSmoothFloor.coefficient_two_primes_composite_zero hq' ht'
    (hn ▸ hs) ha1 (Nat.not_prime_mul hr'.ne_one hp'.ne_one)
    (L := L) (by linarith [hmax q hq,Nat.cast_nonneg (α := ℝ) M])
    (by linarith [hmax t ht,Nat.cast_nonneg (α := ℝ) M])
    (by linarith [Nat.cast_nonneg (α := ℝ) M])
  simpa only [← hn] using hz

private def macroPrimes (M : ℕ) (x : ℝ) : Finset ℕ :=
  logPrimes ((M : ℝ)/16) (x-(M : ℝ)/16)

private theorem macro_mem {M p : ℕ} {x : ℝ} (hp : p.Prime)
    (hlo : (M : ℝ)/16 < Real.log p) (hhi : Real.log p ≤ x) :
    p ∈ macroPrimes M x := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (Real.exp_nonneg _)).mpr
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr hlo
  · apply Nat.le_floor
    simpa only [← Real.exp_add,sub_add_cancel,Real.exp_log hpR] using Real.exp_le_exp.mpr hhi

private theorem macro_bounds {M p : ℕ} {x : ℝ} (hp : p ∈ macroPrimes M x) :
    p.Prime ∧ (M : ℝ)/16 < Real.log p ∧ Real.log p ≤ x := by
  simpa only [macroPrimes,add_sub_cancel] using logPrimes_bounds hp

private theorem macro_card {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    ((macroPrimes M x).card : ℝ) ≤ 32*Real.log 4*Real.exp x/((M : ℝ)+1) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  by_cases hx : (M : ℝ)/16 ≤ x
  · have hb := ZetaRieszQuadrupleCompensation.interval_card_upper
      (show 0 < (M : ℝ)/16 by positivity) (sub_nonneg.mpr hx)
    change ((macroPrimes M x).card : ℝ) ≤ _ at hb
    have hden : ((M : ℝ)+1)/32 ≤ (M : ℝ)/16 := by linarith
    apply hb.trans
    rw [add_sub_cancel]
    have h := div_le_div_of_nonneg_left (show 0 ≤ Real.log 4*Real.exp x by positivity)
      (show 0 < ((M : ℝ)+1)/32 by positivity) hden
    convert h using 1
    field_simp
  · have he : macroPrimes M x = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      have h := macro_bounds hp
      linarith [h.2.1,h.2.2])
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

private theorem macro_reciprocal {M : ℕ} (hM : 1 ≤ M) :
    (∑ p ∈ macroPrimes M (2*(M : ℝ)+2), Real.exp (-Real.log p)) ≤ 96*Real.log 4 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmass := ZetaRieszCoreExtensions.prime_log_mass_le
    (macroPrimes M (2*(M : ℝ)+2)) (show 0 ≤ 2*(M : ℝ)+2 by positivity)
    (fun _ hp => ⟨(macro_bounds hp).1,(macro_bounds hp).2.2⟩)
  have hlow : (((M : ℝ)+1)/32)*
      (∑ p ∈ macroPrimes M (2*(M : ℝ)+2), Real.exp (-Real.log p)) ≤
      ∑ p ∈ macroPrimes M (2*(M : ℝ)+2), Real.log p*Real.exp (-Real.log p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    have h := (macro_bounds hp).2.1
    linarith
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hmain := hlow.trans hmass
  nlinarith

private theorem factorization {n M Q : ℕ} {L : ℝ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 4)
    (hlo : 2*(M : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2*(M : ℝ)+2)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ Q)
    (hQ : Real.log Q ≤ (M : ℝ)/32)
    (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M)
    (hnz : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    ∃ r ∈ Nat.primesLE Q, ∃ p ∈ macroPrimes M (2*(M : ℝ)+2),
      ∃ q ∈ macroPrimes M (2*(M : ℝ)+2),
        ∃ t ∈ macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log p-Real.log q),
          n = r*(p*(q*t)) := by
  obtain ⟨r,hr,hrQ⟩ := hsmall
  have hr' := Nat.prime_of_mem_primeFactors hr
  have hrlog : Real.log r ≤ (M : ℝ)/32 :=
    (Real.log_le_log (by exact_mod_cast hr'.pos) (by exact_mod_cast hrQ)).trans hQ
  have hcard : (n.primeFactors.erase r).card = 3 := by
    rw [Finset.card_erase_of_mem hr,hc]
  obtain ⟨p,q,t,hpq,hpt,hqt,he⟩ := Finset.card_eq_three.mp hcard
  have hpE : p ∈ n.primeFactors.erase r := by simp [he]
  have hqE : q ∈ n.primeFactors.erase r := by simp [he]
  have htE : t ∈ n.primeFactors.erase r := by simp [he]
  have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hpE)
  have hqq := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hqE)
  have htt := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase htE)
  have hn : n = r*(p*(q*t)) := by
    rw [← Nat.prod_primeFactors_of_squarefree hs,← Finset.mul_prod_erase _ _ hr,he]
    simp [hpq,hpt,hqt]
  have hlog : Real.log n = Real.log r+Real.log p+Real.log q+Real.log t := by
    rw [hn,Nat.cast_mul,Real.log_mul (by exact_mod_cast hr'.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hpp.ne_zero (Nat.mul_ne_zero hqq.ne_zero htt.ne_zero)),
      Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hqq.ne_zero htt.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hqq.ne_zero) (by exact_mod_cast htt.ne_zero)]
    ring
  have hmacro (a : ℕ) (ha : a ∈ n.primeFactors.erase r) : (M : ℝ)/16 < Real.log a := by
    by_contra h
    exact hnz (coefficient_zero_of_two_small hs hc hr ha hrlog (le_of_not_gt h) hmax hlo hL hLu)
  refine ⟨r,Nat.mem_primesLE.mpr ⟨hrQ,hr'⟩,p,macro_mem hpp (hmacro p hpE) ?_,
    q,macro_mem hqq (hmacro q hqE) ?_,t,macro_mem htt (hmacro t htE) ?_,hn⟩
  all_goals linarith [Real.log_natCast_nonneg r,Real.log_natCast_nonneg p,
    Real.log_natCast_nonneg q,Real.log_natCast_nonneg t]

private theorem atom_norm_bound (A : Finset ℕ) {n r N M : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hc : n.primeFactors.card = 4)
    (hr : r ∈ n.primeFactors) (hlo : 2*(M : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 2*(M : ℝ)+2) {L : ℝ}
    (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M) (y : ℝ) :
    ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      4*Real.log r*Real.exp 2*radialEnvelope N M := by
  have hm : (100 : ℝ) ≤ M := by exact_mod_cast hM
  have hratio : Real.log n/L ≤ 4 := (div_le_iff₀ hL0).mpr (by linarith)
  have hb := ZetaRieszFourPrimeExact.norm_coefficient_le_marked_log hc hr hL0
    (by linarith : L ≤ Real.log n) (by linarith : 2*Real.log n ≤ 3*L)
  have hc' : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 4*Real.log r :=
    hb.trans (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg r))
  have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight,amplitude]
    ring
  rw [norm_mul,hker]
  exact (mul_le_mul ((ZetaRieszJointCountFloor.norm_residual_le A L N n).trans hc')
    (amplitude_le_radial (by omega) hNM hlo hhi)
    (by unfold amplitude; positivity) (by positivity)).trans_eq (by ring)

private theorem triple_count_upper {M r : ℕ} (hM : 1 ≤ M) :
    (∑ pq ∈ (macroPrimes M (2*(M : ℝ)+2)).product (macroPrimes M (2*(M : ℝ)+2)),
      ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log pq.1-Real.log pq.2)).card : ℝ)) ≤
      294912*(Real.log 4)^3*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) := by
  let G := macroPrimes M (2*(M : ℝ)+2)
  have hb := Finset.sum_le_sum (s := G.product G) (fun pq _ =>
    macro_card hM (2*(M : ℝ)+2-Real.log r-Real.log pq.1-Real.log pq.2))
  have he : (∑ pq ∈ G.product G,
      32*Real.log 4*Real.exp (2*(M : ℝ)+2-Real.log r-Real.log pq.1-Real.log pq.2)/((M : ℝ)+1)) =
      (32*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))*
        (∑ p ∈ G, Real.exp (-Real.log p))^2 := by
    simp_rw [sub_eq_add_neg,Real.exp_add]
    rw [pow_two,Finset.sum_mul_sum,Finset.mul_sum,Finset.product_eq_sprod,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he] at hb
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)) (macro_reciprocal hM) 2
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 32*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) by positivity)
  exact hb.trans (hh.trans_eq (by ring))

/-- Every literal selected four-prime atom with a small prime is counted,
including all phases and original allocations. The bound pays an entire
population, not one fixed cofactor fibre or a continuum density model. -/
theorem small_four_norm_upper (S A : Finset ℕ) {N M Q : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hQ : Real.log Q ≤ (M : ℝ)/32)
    {L : ℝ} (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (hLu : L ≤ (143/100 : ℝ)*M) (y : ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 4 ∧
      2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
      (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) :
    ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (1179648*(Real.log 4)^4*Real.exp 4)*(1+Real.log Q)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let V := S.filter (fun n => SquarefreeVaughanLogSource.coefficient L n ≠ 0)
  let G := macroPrimes M (2*(M : ℝ)+2)
  let D := (Nat.primesLE Q).sigma (fun r => (G.product G).sigma
    (fun pq => macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log pq.1-Real.log pq.2)))
  let prod := fun x : Σ _r : ℕ, Σ _pq : ℕ × ℕ, ℕ => x.1*(x.2.1.1*(x.2.1.2*x.2.2))
  let g := fun n => if n ∈ V then ‖f n‖ else 0
  let H := 4*Real.exp 2*radialEnvelope N M
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_nonneg N M]
  have hsum : (∑ n ∈ V, f n) = ∑ n ∈ S, f n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnV
    have hz : SquarefreeVaughanLogSource.coefficient L n = 0 := by
      by_contra h
      exact hnV (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp [f,residualCoefficient,hz]
  have hsub : V ⊆ D.image prod := by
    intro n hn
    obtain ⟨hnS,hnz⟩ := Finset.mem_filter.mp hn
    obtain ⟨hs,hc,hlo,hhi,hmax,hsmall⟩ := hS n hnS
    obtain ⟨r,hr,p,hp,q,hq,t,ht,he⟩ := factorization hs hc hlo hhi hmax hsmall hQ hL hLu hnz
    exact Finset.mem_image.mpr ⟨⟨r,(p,q),t⟩,Finset.mem_sigma.mpr
      ⟨hr,Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,ht⟩⟩,he.symm⟩
  have hpoint (x : Σ _r : ℕ, Σ _pq : ℕ × ℕ, ℕ) (hx : x ∈ D) :
      g (prod x) ≤ H*Real.log x.1 := by
    have hr := (Nat.mem_primesLE.mp (Finset.mem_sigma.mp hx).1).2
    dsimp only [g]
    split_ifs with hn
    · obtain ⟨hnS,_⟩ := Finset.mem_filter.mp hn
      obtain ⟨hs,hc,hlo,hhi,_⟩ := hS _ hnS
      have hmem : x.1 ∈ (prod x).primeFactors := Nat.mem_primeFactors.mpr
        ⟨hr,dvd_mul_right _ _,hs.ne_zero⟩
      exact (atom_norm_bound A hM hNM hc hmem hlo hhi hL0 hL hLu y).trans_eq (by dsimp [H]; ring)
    · positivity
  have hb : ‖∑ n ∈ S, f n‖ ≤ ∑ x ∈ D, H*Real.log x.1 := by
    rw [← hsum]
    calc
      _ ≤ ∑ n ∈ V, ‖f n‖ := norm_sum_le _ _
      _ = ∑ n ∈ V, g n := Finset.sum_congr rfl (fun n hn => by simp only [g,if_pos hn])
      _ ≤ ∑ n ∈ D.image prod, g n := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro n _ _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ ∑ x ∈ D, g (prod x) := Finset.sum_image_le_of_nonneg
        (by intro n _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ _ := Finset.sum_le_sum hpoint
  have he : (∑ x ∈ D, H*Real.log x.1) =
      ∑ r ∈ Nat.primesLE Q, H*Real.log r*(∑ pq ∈ G.product G,
        ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log pq.1-Real.log pq.2)).card : ℝ)) := by
    simp only [D,Finset.sum_sigma,Finset.sum_const,nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_sigma,Nat.cast_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pq _
    ring
  rw [he] at hb
  have ht := Finset.sum_le_sum (s := Nat.primesLE Q) (fun r _ =>
    mul_le_mul_of_nonneg_left (triple_count_upper (r := r) (by omega : 1 ≤ M))
      (mul_nonneg hH (Real.log_natCast_nonneg r)))
  have he' : (∑ r ∈ Nat.primesLE Q, H*Real.log r*
      (294912*(Real.log 4)^3*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))) =
      (H*294912*(Real.log 4)^3*Real.exp (2*(M : ℝ)+2)/((M : ℝ)+1))*
        (∑ r ∈ Nat.primesLE Q, Real.log r*Real.exp (-Real.log r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he'] at ht
  have hmass := ZetaRieszCoreExtensions.prime_log_mass_le (Nat.primesLE Q)
    (Real.log_natCast_nonneg Q) (fun r hr => ⟨(Nat.mem_primesLE.mp hr).2,
      Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hr).2.pos)
        (by exact_mod_cast (Nat.mem_primesLE.mp hr).1)⟩)
  refine (hb.trans ht).trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq ?_)
  dsimp [H]
  rw [Real.exp_add]
  have he4 : Real.exp (2 : ℝ)*Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (1179648*(Real.log 4)^4*(Real.exp 2*Real.exp 2))*(1+Real.log Q)*
      Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by ring
    _ = _ := by rw [he4]

private theorem tendsto_head_rate :
    Tendsto (fun N : ℕ => (1+2*Real.log N)/(N : ℝ)) atTop (𝓝 0) := by
  have h₀ := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₁ := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  convert h₀.add h₁ using 1 <;> simp [add_div,mul_div_assoc]

/-- The small-prime four-factor cost is an arbitrarily small fraction
of the actual supply's radial scale. It is uniform in fixed or varying
height, and does not require an arithmetic cancellation hypothesis. -/
theorem eventually_small_four_cost {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (S A : Finset ℕ) (L y : ℝ),
      N ≤ 2*M → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
      (∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 4 ∧
        2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
        (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ N^2) →
      ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        b*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let B : ℝ := 1179648*(Real.log 4)^4*Real.exp 4
  have hB : 0 < B := by dsimp [B]; positivity
  filter_upwards [eventually_ge_atTop (200 : ℕ),
    tendsto_head_rate.eventually_lt_const (show 0 < b/(2*B) by positivity),
    tendsto_head_rate.eventually_lt_const (by norm_num : (0 : ℝ) < 1/64)]
    with N hN hcost hsmall M S A L y hNM hL0 hL hLu hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnm : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
  have hlog : Real.log (N^2 : ℕ) = 2*Real.log N := by rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hQ : Real.log (N^2 : ℕ) ≤ (M : ℝ)/32 := by
    rw [hlog]
    have ht := (div_lt_iff₀ hn).mp hsmall
    linarith
  have hbudget : B*(1+Real.log (N^2 : ℕ)) ≤ b*M := by
    rw [hlog]
    have ht := (div_lt_iff₀ hn).mp hcost
    have ht' := mul_lt_mul_of_pos_left ht hB
    have he : B*(b/(2*B)*N) = b/2*N := by field_simp
    rw [he] at ht'
    nlinarith
  have hbound := small_four_norm_upper S A (by omega : 100 ≤ M) hNM hQ hL0 hL hLu y hS
  apply hbound.trans
  have ht := mul_le_mul_of_nonneg_right hbudget
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  convert ht using 1 <;> ring

open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation

/-- One and the same actual signed supply pays a balanced triple band,
the small-prime triple head and the small-prime four-factor head. The
fractions are half plus one eighth plus one eighth, leaving one quarter.
This is a simultaneous capacity theorem, not three independent budgets. -/
theorem eventually_joint_slabs_spending {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (D S H A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ N^2) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := (∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M (N^2), f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y := by
  obtain ⟨h,hh,hhhi,hphase⟩ := exists_short_negative_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_lower hh hhhi
  let B : ℝ := 27*(6*Real.log 4)^3*Real.exp 8
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min (1/1000 : ℝ) (Real.sqrt (c/(2*B)))
  have hη : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hηu : η ≤ 1/1000 := min_le_left _ _
  have hηcost : B*η^2 ≤ c/2 := by
    have hs := pow_le_pow_left₀ hη.le (min_le_right (1/1000 : ℝ) (Real.sqrt (c/(2*B)))) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have ht := (le_div_iff₀ (by positivity : 0 < 2*B)).mp hs
    nlinarith
  refine ⟨η,h,hη,hηu,hh,hhhi,?_⟩
  filter_upwards [hsupply,eventually_small_slabs_cost (show 0 < c/8 by positivity),
    eventually_small_four_cost (show 0 < c/8 by positivity),eventually_ge_atTop (200 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2/η)]
    with N hs hsmall3 hsmall4 hN hsize M D S H A L hNM hL0 hL hLu hH
  have hM : 20 ≤ M := by omega
  have hηM : 1 ≤ η*M := by
    have ht := (div_le_iff₀ hη).mp hsize
    have hnr : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
    nlinarith
  obtain ⟨v,hv,hvhi,hcos⟩ := hphase (2*(M : ℝ))
  have hpos := hs M A v L y hNM hv hvhi hL0 hL hLu hcos
  have hLM : (M : ℝ) ≤ L := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hneg := slab_norm_upper D A hη hηu hM hηM hNM hL0 hLM y
  have hsm3 := hsmall3 M S A L y hNM hL0 hLM
  have hsm4 := hsmall4 M H A L y hNM hL0 hL hLu hH
  refine ⟨v,hv,hvhi,?_⟩
  dsimp only
  refine ⟨lt_of_lt_of_le (by positivity [radialEnvelope_pos N (show 0 < M by omega)]) hpos,?_,?_,?_⟩
  · have hbudget := mul_le_mul_of_nonneg_right hηcost
      (show 0 ≤ (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
        positivity [radialEnvelope_nonneg N M])
    have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/2)
    change ‖_‖ ≤ B*η^2*_*_/_*_ at hneg
    have hmid : B*η^2*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (1/2 : ℝ)*(c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
      calc
        _ = B*η^2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
        _ ≤ c/2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := hbudget
        _ = _ := by ring
    exact hneg.trans (hmid.trans hh)
  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm3.trans
    convert hh using 1
    ring
  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm4.trans
    convert hh using 1
    ring

/-- Exact disjoint spending for the three paid populations and one
supply. Every other integer remains in the same signed finite sum. -/
theorem re_sum_ge_joint_spending {D X Z H Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : X ∪ Z ∪ H ∪ Y ⊆ D) (hXZ : Disjoint X Z)
    (hXH : Disjoint X H) (hZH : Disjoint Z H)
    (hXY : Disjoint X Y) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hX : ‖∑ n ∈ X, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ Y, f n).re)
    (hZ : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hH : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re) :
    (∑ n ∈ D\(X ∪ Z ∪ H ∪ Y), f n).re+
      max (∑ n ∈ X, f n).re 0+max (∑ n ∈ Z, f n).re 0+
      max (∑ n ∈ H, f n).re 0+(∑ n ∈ Y, f n).re/4 ≤ (∑ n ∈ D, f n).re := by
  have hledger := Finset.sum_sdiff (f := f) hsub
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hXY,hZY⟩,hHY⟩),
    Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hXH,hZH⟩),Finset.sum_union hXZ] at hledger
  have he := congrArg Complex.re hledger
  simp only [Complex.add_re] at he
  have hx := (abs_le.mp ((Complex.abs_re_le_norm _).trans hX)).1
  have hz := (abs_le.mp ((Complex.abs_re_le_norm _).trans hZ)).1
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans hH)).1
  have hy : 0 ≤ (∑ n ∈ Y, f n).re := by nlinarith [norm_nonneg (∑ n ∈ X, f n)]
  rcases le_total (∑ n ∈ X, f n).re 0 with hx' | hx' <;>
    rcases le_total (∑ n ∈ Z, f n).re 0 with hz' | hz' <;>
    rcases le_total (∑ n ∈ H, f n).re 0 with hh' | hh'
  all_goals simp only [max_eq_left hx',max_eq_right hx',max_eq_left hz',max_eq_right hz',
    max_eq_left hh',max_eq_right hh']
  all_goals linarith

/-- Literal four-factor head in one half-open original radial slab. -/
def smallFours (S : Finset ℕ) (M Q : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 4 ∧
    2*(M : ℝ) ≤ Real.log n ∧ Real.log n < 2*(M : ℝ)+2 ∧
    (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q)

/-- Radial selections are used only in the joint signed inequality below. -/
def radialFours (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (radialIndices N).biUnion (fun M => smallFours S M (N^2))

/-- Every original small-prime four-factor label in the inner radial
core below the already paid 60.1% endpoint enters the compensated union.
No least-share approximation or arbitrary new prime cutoff is used. -/
theorem mem_radialFours_of_geometry {S : Finset ℕ} {N n : ℕ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hc : n.primeFactors.card = 4)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (601/1000 : ℝ)*Real.log n)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ N^2) : n ∈ radialFours S N := by
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hMR : (M : ℝ) ≤ 2*N := by linarith
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : M ≤ 2*N := by exact_mod_cast hMR
      omega
    constructor <;> linarith
  apply Finset.mem_biUnion.mpr
  refine ⟨M,hM,Finset.mem_filter.mpr ⟨hnS,hs,hc,by linarith,by linarith,?_,hsmall⟩⟩
  intro p hp
  linarith [hmax p hp]

theorem smallFours_disjoint (S : Finset ℕ) (Q : ℕ) :
    Pairwise (fun M M' : ℕ => Disjoint (smallFours S M Q) (smallFours S M' Q)) := by
  intro M M' hne
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := (Finset.mem_filter.mp hn).2
  have hb' := (Finset.mem_filter.mp hn').2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr : (M : ℝ)+1 ≤ M' := by exact_mod_cast hlt
    linarith [hb.2.2.2.1,hb'.2.2.1]
  · have hr : (M' : ℝ)+1 ≤ M := by exact_mod_cast hlt
    linarith [hb'.2.2.2.1,hb.2.2.1]

private theorem norm_radial_payment {N : ℕ} {E : ℕ → Finset ℕ} {f : ℕ → ℂ}
    {h : ℝ} {v : ℕ → ℝ} {b : ℝ}
    (hE : (radialIndices N : Set ℕ).PairwiseDisjoint E)
    (hh : h ≤ 1/20) (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2)
    (hpay : ∀ M ∈ radialIndices N,
      ‖∑ n ∈ E M, f n‖ ≤ b*(∑ n ∈ supply M h (v M), f n).re) :
    ‖∑ n ∈ (radialIndices N).biUnion E, f n‖ ≤ b*(∑ n ∈ radialSupply N h v, f n).re := by
  rw [Finset.sum_biUnion hE,radialSupply,Finset.sum_biUnion (supply_disjoint hh hv)]
  calc
    _ ≤ ∑ M ∈ radialIndices N, ‖∑ n ∈ E M, f n‖ := norm_sum_le _ _
    _ ≤ ∑ M ∈ radialIndices N, b*(∑ n ∈ supply M h (v M), f n).re := Finset.sum_le_sum hpay
    _ = _ := by rw [← Finset.mul_sum,Complex.re_sum]

private theorem radial_supply_geometry {N n : ℕ} {h : ℝ} {v : ℕ → ℝ}
    (hN : 2000 ≤ N) (hh : 0 < h) (hhu : h ≤ 1/20)
    (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2)
    (hn : n ∈ radialSupply N h v) :
    n.primeFactors.card = 4 ∧ ∀ p ∈ n.primeFactors, (N : ℝ)/5 < Real.log p := by
  obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
  have hb := (Finset.mem_filter.mp hM).2
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : h+v M ≤ (M : ℝ)/1000 := by linarith [(hv M hM).2]
  obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  refine ⟨tuple_count hh hi hj hk (hv M hM).1 hw hp,?_⟩
  intro q hq
  rw [tuple_primeFactors hh hi hj hk (hv M hM).1 hw hp] at hq
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
  have hs := start_bounds hh hi hj hk (hv M hM).1 hw a
  have ht := (tuple_bounds hp a).2.1
  linarith [hs.1,hb.1]

open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- A new actual whole-core lower comparison pays three populations
simultaneously on every radial slab. Both triple credits, the four-prime
head credit and a quarter of the same supply remain. The rest stays signed.
No zero hypothesis or signed prime-density transport is used. -/
theorem eventually_core_joint_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := radialSmallTriples (S\Xs) N
        let Hs := radialFours S N
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+(∑ n ∈ Ys, f n).re/4) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,hη,hηu,hh,hhu,hpay⟩ := eventually_joint_slabs_spending hy
  refine ⟨η,h,hη,hηu,hh,hhu,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (tendsto_head_rate.eventually_lt_const (by norm_num : (0 : ℝ) < 1/64))]
    with j hpay hL hsub hN hsmall
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := radialSmallTriples (S\Xs) N
  let Hs := radialFours S N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M (N^2), f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M (N^2), f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH⟩ := hpay M S (S\Xs) (smallFours S M (N^2)) A L
        (hL M hM).1 (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ys := radialSupply N h v
  have hY : 0 < (∑ n ∈ Ys, f n).re := by
    change 0 < (∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending hhu hvb (fun M hM => (hv M hM).2.2.2.1)
  have hZpay := norm_radial_payment
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) (N^2) hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment
    (fun _ _ _ _ hne => smallFours_disjoint S (N^2) hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2)
  have hXsub : Xs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hZsub : Zs ⊆ S\Xs := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hHsub : Hs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hX3 : ∀ n ∈ Xs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hZ3 : ∀ n ∈ Zs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hH4 : ∀ n ∈ Hs, n.primeFactors.card = 4 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hY4 : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => (radial_supply_geometry hN hh hhu hvb hn).1
  have hdisj (B C : Finset ℕ) (hB : ∀ n ∈ B, n.primeFactors.card = 3)
      (hC : ∀ n ∈ C, n.primeFactors.card = 4) : Disjoint B C :=
    Finset.disjoint_left.mpr (fun n hb hc => by have := hB n hb; have := hC n hc; omega)
  have hXZ : Disjoint Xs Zs := Finset.disjoint_left.mpr
    (fun _ hx hz => (Finset.mem_sdiff.mp (hZsub hz)).2 hx)
  have hHY : Disjoint Hs Ys := by
    apply Finset.disjoint_left.mpr
    intro n hn hnY
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨_,_,_,_,_,_,r,hr,hrsmall⟩ := Finset.mem_filter.mp hn
    have hrlog := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
      (show (r : ℝ) ≤ (N^2 : ℕ) by exact_mod_cast hrsmall)
    rw [Nat.cast_pow,Real.log_pow] at hrlog
    have hl := (div_lt_iff₀ (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))).mp hsmall
    have hh := (radial_supply_geometry hN hh hhu hvb hnY).2 r hr
    change 1+2*Real.log N < (1/64 : ℝ)*N at hl
    norm_num at hrlog
    linarith
  have hsuball : Xs ∪ Zs ∪ Hs ∪ Ys ⊆ S := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.union_subset hXsub
        (fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1)) hHsub
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvb M hM).1 (hvb M hM).2 hn
  have hfloor := re_sum_ge_joint_spending f hsuball hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hXpay hZpay hHpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

/-- The same logarithmic population bounds pay an exponential prime head.
The width is fixed before the order tends to infinity. This is a relative
budget for the actual prime sums, not a source-normalized norm estimate. -/
theorem exists_log_head_budget {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ M Q : ℕ, N ≤ 2*M → Real.log Q ≤ δ*N →
        Real.log Q ≤ (M : ℝ)/32 ∧
        (768*(Real.log 4)^3*Real.exp 4)*(1+Real.log Q) ≤ b*M ∧
        (1179648*(Real.log 4)^4*Real.exp 4)*(1+Real.log Q) ≤ b*M := by
  let B₃ : ℝ := 768*(Real.log 4)^3*Real.exp 4
  let B₄ : ℝ := 1179648*(Real.log 4)^4*Real.exp 4
  let B := B₃+B₄
  have hB₃ : 0 < B₃ := by dsimp [B₃]; positivity
  have hB₄ : 0 < B₄ := by dsimp [B₄]; positivity
  have hB : 0 < B := add_pos hB₃ hB₄
  let δ := min (1/128 : ℝ) (b/(8*B))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδu : δ ≤ 1/128 := min_le_left _ _
  have hδb : 8*B*δ ≤ b := by
    have h := (le_div_iff₀ (by positivity : 0 < 8*B)).mp
      (min_le_right (1/128 : ℝ) (b/(8*B)))
    nlinarith
  refine ⟨δ,hδ,hδu,?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1/δ)]
    with N hN M Q hNM hQ
  have hsize : 1 ≤ δ*N := by
    have h := (div_le_iff₀ hδ).mp hN
    nlinarith
  have hnm : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
  have hδN : δ*N ≤ (M : ℝ)/64 := by
    have h := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith
  have hhead : 1+Real.log Q ≤ 4*δ*M := by nlinarith
  have hcost : B*(1+Real.log Q) ≤ b*M := by
    have h := mul_le_mul_of_nonneg_left hhead hB.le
    have h' := mul_le_mul_of_nonneg_right hδb (Nat.cast_nonneg (α := ℝ) M)
    nlinarith [mul_nonneg hb.le (Nat.cast_nonneg (α := ℝ) M)]
  have hpos : 0 ≤ 1+Real.log Q := by positivity [Real.log_natCast_nonneg Q]
  refine ⟨by linarith,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (show B₃ ≤ B by dsimp [B]; linarith) hpos).trans hcost
  · exact (mul_le_mul_of_nonneg_right (show B₄ ≤ B by dsimp [B]; linarith) hpos).trans hcost

/-- A fixed exponential small-prime range, together with the balanced
triple band, is paid by ONE four-prime supply. The fractions remain
one half plus two eighths. The width and phase window are chosen once. -/
theorem eventually_joint_slabs_spending_log_head {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (D S H A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := (∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y := by
  obtain ⟨h,hh,hhhi,hphase⟩ := exists_short_negative_window hy
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_lower hh hhhi
  let B : ℝ := 27*(6*Real.log 4)^3*Real.exp 8
  have hB : 0 < B := by dsimp [B]; positivity
  let η := min (1/1000 : ℝ) (Real.sqrt (c/(2*B)))
  have hη : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hηu : η ≤ 1/1000 := min_le_left _ _
  have hηcost : B*η^2 ≤ c/2 := by
    have hs := pow_le_pow_left₀ hη.le (min_le_right (1/1000 : ℝ) (Real.sqrt (c/(2*B)))) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have ht := (le_div_iff₀ (by positivity : 0 < 2*B)).mp hs
    nlinarith
  obtain ⟨δ,hδ,hδu,hbudget⟩ := exists_log_head_budget (show 0 < c/8 by positivity)
  refine ⟨η,h,δ,hη,hηu,hh,hhhi,hδ,hδu,?_⟩
  filter_upwards [hsupply,hbudget,eventually_ge_atTop (200 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2/η)]
    with N hs hbudget hN hsize M Q D S H A L hNM hQ hL0 hL hLu hH
  have hM : 20 ≤ M := by omega
  have hηM : 1 ≤ η*M := by
    have ht := (div_le_iff₀ hη).mp hsize
    have hnr : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
    nlinarith
  obtain ⟨v,hv,hvhi,hcos⟩ := hphase (2*(M : ℝ))
  have hpos := hs M A v L y hNM hv hvhi hL0 hL hLu hcos
  have hLM : (M : ℝ) ≤ L := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hneg := slab_norm_upper D A hη hηu hM hηM hNM hL0 hLM y
  obtain ⟨hQ32,hbudget3,hbudget4⟩ := hbudget M Q hNM hQ
  have hsm3 := small_triples_norm_upper S A (by omega : 1 ≤ M) hNM
    (by linarith [Nat.cast_nonneg (α := ℝ) M] : Real.log Q ≤ (M : ℝ)/8) hL0 hLM y
  have hsm4 := small_four_norm_upper H A (by omega : 100 ≤ M) hNM hQ32 hL0 hL hLu y hH
  have hb3 := mul_le_mul_of_nonneg_right hbudget3
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  have hb4 := mul_le_mul_of_nonneg_right hbudget4
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  refine ⟨v,hv,hvhi,?_⟩
  dsimp only
  refine ⟨lt_of_lt_of_le (by positivity [radialEnvelope_pos N (show 0 < M by omega)]) hpos,?_,?_,?_⟩
  · have hbudget := mul_le_mul_of_nonneg_right hηcost
      (show 0 ≤ (M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
        positivity [radialEnvelope_nonneg N M])
    have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/2)
    change ‖_‖ ≤ B*η^2*_*_/_*_ at hneg
    have hmid : B*η^2*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (1/2 : ℝ)*(c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
      calc
        _ = B*η^2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by ring
        _ ≤ c/2*((M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := hbudget
        _ = _ := by ring
    exact hneg.trans (hmid.trans hh)
  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm3.trans
    calc
      _ ≤ (c/8*M)*(Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
        simpa only [div_eq_mul_inv,mul_assoc] using hb3
      _ ≤ _ := by convert hh using 1 <;> first | rfl | ring
  · have hh := mul_le_mul_of_nonneg_left hpos (by norm_num : (0 : ℝ) ≤ 1/8)
    apply hsm4.trans
    calc
      _ ≤ (c/8*M)*(Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) := by
        simpa only [div_eq_mul_inv,mul_assoc] using hb4
      _ ≤ _ := by convert hh using 1 <;> first | rfl | ring

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h

/-- A fixed exponential prime head is paid throughout the original
radial union. This enlarges the two paid head selections; it does not add
another copy of the supply. All unselected labels remain signed, and all
three positive credits and one quarter of the same supply remain. -/
theorem eventually_core_exponential_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+(∑ n ∈ Ys, f n).re/4) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hpay⟩ := eventually_joint_slabs_spending_log_head hy
  refine ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH⟩ := hpay M Q S (S\Xs) (smallFours S M Q) A L
        (hL M hM).1 hQ (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ys := radialSupply N h v
  have hY : 0 < (∑ n ∈ Ys, f n).re := by
    change 0 < (∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending hhu hvb (fun M hM => (hv M hM).2.2.2.1)
  have hZpay := norm_radial_payment
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) Q hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment
    (fun _ _ _ _ hne => smallFours_disjoint S Q hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2)
  have hXsub : Xs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hZsub : Zs ⊆ S\Xs := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hHsub : Hs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hX3 : ∀ n ∈ Xs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hZ3 : ∀ n ∈ Zs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hH4 : ∀ n ∈ Hs, n.primeFactors.card = 4 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hY4 : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => (radial_supply_geometry hN hh hhu hvb hn).1
  have hdisj (B C : Finset ℕ) (hB : ∀ n ∈ B, n.primeFactors.card = 3)
      (hC : ∀ n ∈ C, n.primeFactors.card = 4) : Disjoint B C :=
    Finset.disjoint_left.mpr (fun n hb hc => by have := hB n hb; have := hC n hc; omega)
  have hXZ : Disjoint Xs Zs := Finset.disjoint_left.mpr
    (fun _ hx hz => (Finset.mem_sdiff.mp (hZsub hz)).2 hx)
  have hHY : Disjoint Hs Ys := by
    apply Finset.disjoint_left.mpr
    intro n hn hnY
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨_,_,_,_,_,_,r,hr,hrsmall⟩ := Finset.mem_filter.mp hn
    have hrlog := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
      (show (r : ℝ) ≤ Q by exact_mod_cast hrsmall)
    have hh := (radial_supply_geometry hN hh hhu hvb hnY).2 r hr
    have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsuball : Xs ∪ Zs ∪ Hs ∪ Ys ⊆ S := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.union_subset hXsub
        (fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1)) hHsub
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvb M hM).1 (hvb M hM).2 hn
  have hfloor := re_sum_ge_joint_spending f hsuball hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hXpay hZpay hHpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

/-- The new threshold eventually exceeds every fixed polynomial prime
threshold, not just the previously used square of the moment order. -/
theorem eventually_polynomial_le_exponential {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, N^k ≤ ⌊Real.exp (δ*N)⌋₊ := by
  have hlog := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (k : ℝ)
  have ht : Tendsto (fun N : ℕ => (k : ℝ)*Real.log N/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul,zero_add,add_zero,Real.rpow_one,
      Real.rpow_zero,zero_mul,mul_zero,pow_one,mul_div_assoc] using hlog
  filter_upwards [eventually_ge_atTop (1 : ℕ),ht.eventually_lt_const hδ] with N hN hsmall
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply Nat.le_floor
  have h := Real.exp_le_exp.mpr ((div_lt_iff₀ hn).mp hsmall).le
  rw [Real.exp_nat_mul,Real.exp_log hn] at h
  exact_mod_cast h

/-- Every original triple or four-factor label in the inner radial
core below the paid dominant-prime boundary enters the enlarged paid
selection as soon as one prime has log at most δN. -/
theorem mem_exponential_paid_of_geometry {S : Finset ℕ} {N n : ℕ} {δ η : ℝ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hc : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (601/1000 : ℝ)*Real.log n)
    (hsmall : ∃ r ∈ n.primeFactors, Real.log r ≤ δ*N) :
    let X := radialTriples S N η
    let Q := ⌊Real.exp (δ*N)⌋₊
    n ∈ X ∪ (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q) ∪
      (radialIndices N).biUnion (fun M => smallFours S M Q) := by
  dsimp only
  by_cases hnX : n ∈ radialTriples S N η
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hnX)
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : M ≤ 2*N := by
        have h' : (M : ℝ) ≤ 2*N := by linarith
        exact_mod_cast h'
      omega
    constructor <;> linarith
  have hQ : ∃ r ∈ n.primeFactors, r ≤ ⌊Real.exp (δ*N)⌋₊ := by
    obtain ⟨r,hr,hrlog⟩ := hsmall
    refine ⟨r,hr,Nat.le_floor ?_⟩
    have h := Real.exp_le_exp.mpr hrlog
    rwa [Real.exp_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)] at h
  have hmax' : ∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M := by
    intro p hp
    linarith [hmax p hp]
  rcases hc with hc | hc
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨M,hM,Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hnS,hnX⟩,hs,hc,by linarith,by linarith,?_,hQ⟩⟩
    intro p hp
    linarith [hmax' p hp,Nat.cast_nonneg (α := ℝ) M]
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨M,hM,Finset.mem_filter.mpr
      ⟨hnS,hs,hc,by linarith,by linarith,hmax',hQ⟩⟩

/-- The surviving three- and four-prime complement has a fixed positive
least-prime share on the inner, nondominant core. This identifies the
smaller actual signed region still requiring an estimate. -/
theorem remaining_prime_log_gt_exponential {S : Finset ℕ} {N n : ℕ} {δ η : ℝ}
    (hN : 4000 ≤ N)
    (hn : n ∈ S\(radialTriples S N η ∪
      (radialIndices N).biUnion (fun M => smallTriples (S\radialTriples S N η) M
        ⌊Real.exp (δ*N)⌋₊) ∪
      (radialIndices N).biUnion (fun M => smallFours S M ⌊Real.exp (δ*N)⌋₊)))
    (hs : Squarefree n) (hc : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (601/1000 : ℝ)*Real.log n) :
    ∀ p ∈ n.primeFactors, δ*N < Real.log p := by
  obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp hn
  intro p hp
  by_contra h
  exact hnnot (mem_exponential_paid_of_geometry hN hnS hs hc hlo hhi hmax
    ⟨p,hp,le_of_not_gt h⟩)

open LogarithmicDeviation ZetaArithmeticDeviationBounds

/-- Only the already bounded radial edges and dominant-prime sector can
escape the enlarged head selection. This pays those failures on the
actual cofinal schedule, with every original residual weight retained. -/
theorem exists_exponential_head_missed_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (j : ℕ) (η δ y u : ℝ), 32 ≤ j → 4000 ≤ dyadicMomentOrder j →
        0 < η → 4 ≤ η*dyadicMomentOrder j →
        0 ≤ δ → 1/2 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let X := radialTriples S N η
        let Z := (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q)
        let H := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) ∧
          ∃ p ∈ n.primeFactors, p ≤ Q)
        ‖(u : ℂ)^(N+1)*∑ n ∈ B\(X ∪ Z ∪ H),
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
            r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000) := by
  obtain ⟨r,C,hr,hr1,hC,hbound⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 244/125) (by norm_num) (by norm_num : (2 : ℝ) < 2029/1000)
    radial_edge_costs.1 radial_edge_costs.2
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro j η δ y u hj hN hη hηN hδ hu hU
  dsimp only
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let X := radialTriples S N η
  let Z := (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q)
  let H := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) ∧ ∃ p ∈ n.primeFactors, p ≤ Q)
  let D := B\(X ∪ Z ∪ H)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let P := fun n : ℕ => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ A ∧ ZetaRieszJointAllocation.eligibleCofactor p (n/p) ∧
      (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let E := (D.filter (fun n => ¬P n)).filter (fun n => residualCoefficient A L N n ≠ 0)
  have hE : deviationBand E (244/125) (2029/1000) N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnE,hlo,hhi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnD,hcoeff⟩ := Finset.mem_filter.mp hnE
    obtain ⟨hnD,hnP⟩ := Finset.mem_filter.mp hnD
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hnD
    rcases Finset.mem_union.mp hnB with hbal | hnB
    · exact hnnot (Finset.mem_union_left _ (Finset.mem_union_left _
        (balanced_mem_radialTriples hN hη hηN hbal hlo hhi)))
    obtain ⟨hnS,hs,hcount,p,hp,hpQ⟩ := Finset.mem_filter.mp hnB
    have hmax := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u
      (Finset.mem_filter.mpr ⟨hnS,hnP⟩) hcoeff
    have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hplog : Real.log p ≤ δ*N := by
      have h := Real.log_le_log hpR (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
      exact h.trans (log_floor_exp_le (mul_nonneg hδ (Nat.cast_nonneg (α := ℝ) N)))
    exact hnnot (mem_exponential_paid_of_geometry hN hnS hs hcount hlo hhi
      (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩)
  have hEsum : (∑ n ∈ E, f n) = ∑ n ∈ D.filter (fun n => ¬P n), f n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnE
    have hz : residualCoefficient A L N n = 0 := by
      by_contra h
      exact hnE (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [f,hz,zero_mul]
  have hedge := hbound N E (residualCoefficient A L N)
    (fun n _ => ZetaRieszJointAllocation.norm_residualCoefficient_le A
      (SquarefreeVaughanLogSource.length_pos u N) N n) y u (by linarith) hU
  have hedge' : ‖(u : ℂ)^(N+1)*∑ n ∈ D.filter (fun n => ¬P n), f n‖ ≤ r^N*C := by
    rw [← hEsum]
    simpa only [hE,Finset.sum_empty,sub_zero,zetaPrimeLogKernel,
      SquarefreeEulerQuadratic.primeFilterKernel_one,f,L] using hedge
  have hL : L ≤ (139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hlog : 2*Real.log 2 ≤ (139/100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hdom := ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A (D.filter P)
    N (by omega : 320 ≤ N) y (by linarith : 0 ≤ u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hL (by
      intro n hn
      obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hn
      refine ⟨hs,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
      exact (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not D P f,mul_add]
  exact (norm_add_le _ _).trans ((add_le_add hdom hedge').trans_eq (by ring))

/-- The whole exponential head of the actual three- and four-prime
classes and the original balanced triple band are paid simultaneously.
One supply retains a quarter, all positive selected observations remain,
and every other label remains signed. Only previously controlled radial
and dominant-prime errors are subtracted. The numerical floor is open. -/
theorem eventually_core_full_exponential_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Ys := radialSupply N h v
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) ∧ ∃ p ∈ n.primeFactors, p ≤ Q)
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ B), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+(∑ n ∈ Ys, f n).re/4)-
              (r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)) ≤
                ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hspend⟩ := eventually_core_exponential_floor hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_exponential_head_missed_bound
  refine ⟨η,h,δ,r,C,hη,hηu,hh,hhu,hδ,hδu,hr,hr1,hC,?_⟩
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hspend,eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    hord.eventually_ge_atTop (4/η)] with j hj hj32 hN hsize
  obtain ⟨v,hvb,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Ys := radialSupply N h v
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) ∧ ∃ p ∈ n.primeFactors, p ≤ Q)
  let D := B\(Xs ∪ Zs ∪ Hs)
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed j η δ y u hj32 hN hη hηN hδ.le hu.le hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _ at hnorm
  have hreal : -(r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/1000000)) ≤ u^(N+1)*(∑ n ∈ D, f n).re := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hBY : Disjoint B Ys := by
    apply Finset.disjoint_left.mpr
    intro n hnB hnY
    have hsupply := radial_supply_geometry (by omega : 2000 ≤ N) hh hhu hvb hnY
    rcases Finset.mem_union.mp hnB with hbal | hhead
    · have hc := (Finset.mem_filter.mp hbal).2.2.1
      omega
    obtain ⟨_,_,_,p,hp,hpQ⟩ := Finset.mem_filter.mp hhead
    have hplog : Real.log p ≤ δ*N := by
      have ht := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
      exact ht.trans (log_floor_exp_le (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N)))
    have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith [(hsupply.2 p hp),Nat.cast_nonneg (α := ℝ) N]
  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ Hs ∪ Ys) := by
    intro n hn
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn <;> exact (Finset.mem_filter.mp hn).1
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hnnot h
    · exact Finset.disjoint_left.mp hBY hnB h
  have hset : (S\(Xs ∪ Zs ∪ Hs ∪ Ys))\D = S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ B) := by
    ext n
    simp only [D,Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨⟨hn,hpaid⟩,hnot⟩
      refine ⟨hn,?_⟩
      rintro (hpaid' | hB)
      · exact hpaid hpaid'
      · exact hnot ⟨hB,fun h => hpaid (Or.inl h)⟩
    · rintro ⟨hn,hall⟩
      refine ⟨⟨hn,fun h => hall (Or.inl h)⟩,?_⟩
      rintro ⟨hB,_⟩
      exact hall (Or.inr hB)
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ B), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+(∑ n ∈ Ys, f n).re/4)-_ ≤ _
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+(∑ n ∈ Ys, f n).re/4) ≤ _ at hfloor
  rw [← hre] at hfloor
  nlinarith only [hfloor,hreal]

/-- Both error allowances in the enlarged whole-core comparison vanish
on the original schedule. The spent population itself need not decay. -/
theorem tendsto_exponential_head_allowance {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (C : ℝ) :
    Tendsto (fun j => r^dyadicMomentOrder j*C+
      2*zetaMoebiusLogMajorantMass (1+1/262144)*
        Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)) atTop (𝓝 0) := by
  have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C
  have h₂ := ZetaRieszJointDominantFloor.Refined.tendsto_allowance
  simpa only [zero_mul,zero_add,Function.comp_def] using (h₁.add h₂).comp tendsto_dyadicMomentOrder

/-- After the full-head payment, every prime of a surviving squarefree
three- or four-factor label exceeds the exponential threshold. This
holds throughout the original core, including the paid edge failures. -/
theorem remaining_full_head_prime_log_gt {S E : Finset ℕ} {N n : ℕ} {δ η : ℝ}
    (hn : n ∈ S\(E ∪ (balancedTriples S N η ∪ S.filter (fun m => Squarefree m ∧
      (m.primeFactors.card = 3 ∨ m.primeFactors.card = 4) ∧
      ∃ p ∈ m.primeFactors, p ≤ ⌊Real.exp (δ*N)⌋₊))))
    (hs : Squarefree n) (hc : n.primeFactors.card = 3 ∨ n.primeFactors.card = 4) :
    ∀ p ∈ n.primeFactors, δ*N < Real.log p := by
  obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp hn
  intro p hp
  by_contra h
  have hpQ : p ≤ ⌊Real.exp (δ*N)⌋₊ := by
    apply Nat.le_floor
    have ht := Real.exp_le_exp.mpr (le_of_not_gt h)
    rwa [Real.exp_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)] at ht
  exact hnnot (Finset.mem_union_right _ (Finset.mem_union_right _
    (Finset.mem_filter.mpr ⟨hnS,hs,hc,p,hp,hpQ⟩)))

end
end RiemannGaussian.ZetaRieszFourPrimeHead
