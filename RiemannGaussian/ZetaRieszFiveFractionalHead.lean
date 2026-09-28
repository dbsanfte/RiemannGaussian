/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFractionalBudget
import RiemannGaussian.ZetaRieszSignedSperner
import RiemannGaussian.ZetaRieszHeadCeiling

/-!
# Fractional counting pays both signs of a five-prime exponential head

The least prime remains in the divisor coefficient until after the
literal prime count. A marked small prime receives exponent one half;
the other three cofactor primes receive one sixth each. This gives an
arbitrarily small fixed fraction of the existing signed supply scale,
including the previously unpaid negative-coefficient five-prime sector.
-/

namespace RiemannGaussian.ZetaRieszFiveFractionalHead
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime ZetaRieszPrimeFractionalBudget

private theorem logPrimes_mem {p : ℕ} (hp : p.Prime) {a h : ℝ}
    (hlo : a < Real.log p) (hhi : Real.log p ≤ a+h) : p ∈ logPrimes a h := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (Real.exp_nonneg _)).mpr
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr hlo
  · apply Nat.le_floor
    simpa only [← Real.exp_add,Real.exp_log hpR,add_comm h a] using Real.exp_le_exp.mpr hhi

private def allPrimes (M : ℕ) : Finset ℕ := logPrimes 0 (2*(M : ℝ)+2)

private theorem all_mem {M p : ℕ} (hp : p.Prime)
    (hhi : Real.log p ≤ 2*(M : ℝ)+2) : p ∈ allPrimes M := by
  exact logPrimes_mem hp (Real.log_pos (by exact_mod_cast hp.one_lt)) (by simpa using hhi)

private theorem all_bounds {M p : ℕ} (hp : p ∈ allPrimes M) :
    p.Prime ∧ 0 < Real.log p ∧ Real.log p ≤ 2*(M : ℝ)+2 := by
  simpa only [allPrimes,zero_add] using logPrimes_bounds hp

private def macroPrimes (M : ℕ) (x : ℝ) : Finset ℕ :=
  logPrimes ((M : ℝ)/8) (x-(M : ℝ)/8)

private theorem macro_mem {M p : ℕ} {x : ℝ} (hp : p.Prime)
    (hlo : (M : ℝ)/8 < Real.log p) (hhi : Real.log p ≤ x) : p ∈ macroPrimes M x :=
  logPrimes_mem hp hlo (by simpa using hhi)

private theorem macro_card {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    ((macroPrimes M x).card : ℝ) ≤ 16*Real.log 4*Real.exp x/((M : ℝ)+1) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  by_cases hx : (M : ℝ)/8 ≤ x
  · have hh := ZetaRieszQuadrupleCompensation.interval_card_upper
      (show 0 < (M : ℝ)/8 by positivity) (sub_nonneg.mpr hx)
    change ((macroPrimes M x).card : ℝ) ≤ _ at hh
    rw [add_sub_cancel] at hh
    refine hh.trans ?_
    have hd : ((M : ℝ)+1)/16 ≤ (M : ℝ)/8 := by linarith
    have hb := div_le_div_of_nonneg_left
      (show 0 ≤ Real.log 4*Real.exp x by positivity) (show 0 < ((M : ℝ)+1)/16 by positivity) hd
    convert hb using 1
    field_simp
  · have he : macroPrimes M x = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      have hh := logPrimes_bounds hp
      linarith [hh.2.1,hh.2.2])
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

private theorem factorization {n M Q : ℕ} (hM : 1 ≤ M)
    (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hlo : 2*(M : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2*(M : ℝ)+2)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ Q) (hQ : Real.log Q ≤ (M : ℝ)/32) :
    ∃ r ∈ Nat.primesLE Q, ∃ a ∈ allPrimes M, ∃ b ∈ allPrimes M,
      ∃ c ∈ allPrimes M,
        ∃ p ∈ macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log a-Real.log b-Real.log c),
          n = r*(a*(b*(c*p))) := by
  obtain ⟨r,hr,hrQ⟩ := hsmall
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrlog : Real.log r ≤ (M : ℝ)/32 :=
    (Real.log_le_log (by exact_mod_cast hrp.pos) (by exact_mod_cast hrQ)).trans hQ
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hex : ∃ p ∈ n.primeFactors, (M : ℝ)/8 < Real.log p := by
    by_contra! h
    have hh := Finset.sum_le_sum (s := n.primeFactors) h
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hh
    simp only [Finset.sum_const,nsmul_eq_mul,hc,Nat.cast_ofNat] at hh
    linarith
  obtain ⟨p,hp,hplog⟩ := hex
  have hpr : p ≠ r := by intro he; rw [he] at hplog; linarith
  have hpE : p ∈ n.primeFactors.erase r := Finset.mem_erase.mpr ⟨hpr,hp⟩
  have hcard : ((n.primeFactors.erase r).erase p).card = 3 := by
    rw [Finset.card_erase_of_mem hpE,Finset.card_erase_of_mem hr,hc]
  obtain ⟨a,b,c,hab,hac,hbc,he⟩ := Finset.card_eq_three.mp hcard
  have haE : a ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hbE : b ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hcE : c ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hall (q : ℕ) (hq : q ∈ n.primeFactors) : q ∈ allPrimes M := by
    have hqn : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hq)
    have hlog : Real.log q ≤ Real.log n := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos) (by exact_mod_cast hqn)
    exact all_mem (Nat.prime_of_mem_primeFactors hq) (hlog.trans hhi)
  have hn : n = r*(a*(b*(c*p))) := by
    rw [← Nat.prod_primeFactors_of_squarefree hs,← Finset.mul_prod_erase _ _ hr,
      ← Finset.mul_prod_erase _ _ hpE,he]
    simp only [Finset.prod_insert (by simp [hab,hac] : a ∉ {b,c}),
      Finset.prod_insert (by simp [hbc] : b ∉ {c}),Finset.prod_singleton]
    ring
  have hlog := CoprimeEulerPhase.squarefree_log_eq_prime_sum hs
  rw [← Finset.add_sum_erase _ _ hr,← Finset.add_sum_erase _ _ hpE,he] at hlog
  simp only [Finset.sum_insert (by simp [hab,hac] : a ∉ {b,c}),
    Finset.sum_insert (by simp [hbc] : b ∉ {c}),Finset.sum_singleton] at hlog
  refine ⟨r,Nat.mem_primesLE.mpr ⟨hrQ,hrp⟩,a,hall a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haE)),
    b,hall b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hbE)),
    c,hall c (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcE)),
    p,macro_mem (Nat.prime_of_mem_primeFactors hp) hplog (by linarith),hn⟩

private theorem atom_norm_bound (A : Finset ℕ) {n r N M : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hr : r ∈ n.primeFactors) (hlo : 2*(M : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 2*(M : ℝ)+2) {L : ℝ}
    (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (y : ℝ) :
    ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      12*Real.log r*Real.exp 2*radialEnvelope N M := by
  have hm : (100 : ℝ) ≤ M := by exact_mod_cast hM
  have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL0.le
  have hratio : Real.log n/L ≤ 4 := (div_le_iff₀ hL0).mpr (by linarith)
  have hc' := ZetaRieszSignedSperner.coefficient_bounds_minFac hL0 hs (by omega)
  have hcaps : ZetaRieszSignedSperner.parityCapacity 3 0 = 3 ∧
      ZetaRieszSignedSperner.parityCapacity 3 1 = 3 := by decide +kernel
  simp only [hc,show 5-2 = (3 : ℕ) by decide,hcaps.1,hcaps.2,Nat.cast_ofNat] at hc'
  have hleast : Real.log n.minFac ≤ Real.log r := Real.log_le_log
    (by exact_mod_cast Nat.minFac_pos n)
    (by exact_mod_cast (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hr).two_le
      (Nat.dvd_of_mem_primeFactors hr)))
  have hmin := mul_le_mul_of_nonneg_left hleast (show 0 ≤ 3*(Real.log n/L) by positivity)
  have hb : |(SquarefreeVaughanLogSource.coefficient L n).re| ≤ 3*(Real.log n/L)*Real.log r := by
    rw [abs_le]
    have hpos := mul_nonneg hscale (Real.log_natCast_nonneg n.minFac)
    constructor <;> nlinarith only [hc'.1,hc'.2,hmin,hpos]
  have hi := ZetaRieszCosineCarrier.coefficient_im_eq_zero L n
  have he := Complex.re_add_im (SquarefreeVaughanLogSource.coefficient L n)
  rw [hi,Complex.ofReal_zero,zero_mul,add_zero] at he
  have hnorm : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 12*Real.log r := by
    rw [← he,Complex.norm_real,Real.norm_eq_abs]
    refine hb.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg r)]
  have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight,amplitude]
    ring
  rw [norm_mul,hker]
  exact (mul_le_mul ((ZetaRieszJointCountFloor.norm_residual_le A L N n).trans hnorm)
    (amplitude_le_radial (by omega) hNM hlo hhi)
    (by unfold amplitude; positivity) (by positivity)).trans_eq (by ring)

private theorem fractional_cofactor_count_upper {M r : ℕ} (hM : 1 ≤ M) :
    let G := allPrimes M
    let w := fun p : ℕ => (Real.log p)^(1/6 : ℝ)
    (∑ v ∈ (G.product G).product G,
      (w v.1.1*w v.1.2*w v.2)*
      ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1-Real.log v.1.2-Real.log v.2)).card : ℝ)) ≤
      (16*Real.log 4*(momentConstant (1/6))^3)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) := by
  dsimp only
  let G := allPrimes M
  let w := fun p : ℕ => (Real.log p)^(1/6 : ℝ)
  have hw (p : ℕ) : 0 ≤ w p := Real.rpow_nonneg (Real.log_natCast_nonneg p) _
  have hb := Finset.sum_le_sum (s := (G.product G).product G) (fun v _ =>
    mul_le_mul_of_nonneg_left (macro_card hM
      (2*(M : ℝ)+2-Real.log r-Real.log v.1.1-Real.log v.1.2-Real.log v.2))
        (show 0 ≤ w v.1.1*w v.1.2*w v.2 by positivity))
  have he : (∑ v ∈ (G.product G).product G,
      (w v.1.1*w v.1.2*w v.2)*
      (16*Real.log 4*Real.exp (2*(M : ℝ)+2-Real.log r-Real.log v.1.1-Real.log v.1.2-Real.log v.2)/((M : ℝ)+1))) =
      (16*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))*
        (∑ p ∈ G, w p*Real.exp (-Real.log p))^3 := by
    simp_rw [sub_eq_add_neg,Real.exp_add]
    rw [pow_succ,pow_two,Finset.sum_mul_sum,Finset.sum_mul_sum]
    simp_rw [Finset.product_eq_sprod,Finset.sum_product]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he] at hb
  have hmass := prime_fractional_log_mass_le G
    (by positivity : 0 < 2*(M : ℝ)+2) (by norm_num : (0 : ℝ) < 1/6)
    (fun p hp => ⟨(all_bounds hp).1,(all_bounds hp).2.2⟩)
  have hp := pow_le_pow_left₀
    (Finset.sum_nonneg (fun p _ => mul_nonneg (hw p) (Real.exp_nonneg _))) hmass 3
  have hsqrt : ((2*(M : ℝ)+2)^(1/6 : ℝ))^3 = Real.sqrt (2*(M : ℝ)+2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0 ≤ 2*(M : ℝ)+2)]
    norm_num [Real.sqrt_eq_rpow]
  rw [mul_pow,hsqrt] at hp
  have ht := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 16*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) by positivity)
  exact hb.trans (ht.trans_eq (by ring))

/-- Explicit constant for the fractional-logarithm five-prime head bound. -/
def exponentialHeadConstant : ℝ :=
  192*Real.log 4*Real.exp 4*momentConstant (1/2)*(momentConstant (1/6))^3

/-- The exponential head's actual counting constant is positive. -/
theorem exponentialHeadConstant_pos : 0 < exponentialHeadConstant := by
  unfold exponentialHeadConstant
  positivity [momentConstant_pos (by norm_num : (0 : ℝ) < 1/2),
    momentConstant_pos (by norm_num : (0 : ℝ) < 1/6)]

/-- Keeping the minimum logarithm before summing removes the artificial
three logarithmic losses. Both coefficient signs and all original weights
are included. The cutoff may now be exponential in the moving order. -/
theorem small_five_fractional_norm_upper (S A : Finset ℕ) {N M Q : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hQ2 : 2 ≤ Q) (hQ : Real.log Q ≤ (M : ℝ)/32)
    {L : ℝ} (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (y : ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 5 ∧
      2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
      ∃ r ∈ n.primeFactors, r ≤ Q) :
    ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      exponentialHeadConstant*Real.sqrt (Real.log Q)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let G := allPrimes M
  let w := fun p : ℕ => (Real.log p)^(1/6 : ℝ)
  let D := (Nat.primesLE Q).sigma (fun r => ((G.product G).product G).sigma
    (fun v => macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1-Real.log v.1.2-Real.log v.2)))
  let prod := fun x : Σ _r : ℕ, Σ _v : (ℕ × ℕ) × ℕ, ℕ =>
    x.1*(x.2.1.1.1*(x.2.1.1.2*(x.2.1.2*x.2.2)))
  let g := fun n => if n ∈ S then ‖f n‖ else 0
  let H := 12*Real.exp 2*radialEnvelope N M
  let B := fun x : Σ _r : ℕ, Σ _v : (ℕ × ℕ) × ℕ, ℕ =>
    H*(Real.log x.1)^(1/2 : ℝ)*w x.2.1.1.1*w x.2.1.1.2*w x.2.1.2
  have hw (p : ℕ) : 0 ≤ w p := Real.rpow_nonneg (Real.log_natCast_nonneg p) _
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_nonneg N M]
  have hsub : S ⊆ D.image prod := by
    intro n hn
    obtain ⟨hs,hc,hlo,hhi,hsmall⟩ := hS n hn
    obtain ⟨r,hr,a,ha,b,hb,c,hc',p,hp,he⟩ :=
      factorization (by omega : 1 ≤ M) hs hc hlo hhi hsmall hQ
    exact Finset.mem_image.mpr ⟨⟨r,((a,b),c),p⟩,Finset.mem_sigma.mpr
      ⟨hr,Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hc'⟩,hp⟩⟩,he.symm⟩
  have hpoint (x : Σ _r : ℕ, Σ _v : (ℕ × ℕ) × ℕ, ℕ) (hx : x ∈ D) :
      g (prod x) ≤ B x := by
    rcases x with ⟨r,v,p⟩
    rcases v with ⟨⟨a,b⟩,c⟩
    obtain ⟨hr,hv⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hv,_⟩ := Finset.mem_sigma.mp hv
    obtain ⟨hab,hc⟩ := Finset.mem_product.mp hv
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    dsimp only [g]
    split_ifs with hn
    · obtain ⟨hs,hcount,hlo,hhi,_⟩ := hS _ hn
      have hn1 : prod ⟨r,((a,b),c),p⟩ ≠ 1 := by
        intro he
        rw [he] at hcount
        norm_num at hcount
      have hpmin := Nat.minFac_prime hn1
      have hmmin := hpmin.mem_primeFactors (Nat.minFac_dvd _) hs.ne_zero
      have ht : 0 < Real.log (prod ⟨r,((a,b),c),p⟩).minFac :=
        Real.log_pos (by exact_mod_cast hpmin.one_lt)
      have hlog (q : ℕ) (hqp : q.Prime) (hqd : q ∣ prod ⟨r,((a,b),c),p⟩) :
          Real.log (prod ⟨r,((a,b),c),p⟩).minFac ≤ Real.log q :=
        Real.log_le_log (by exact_mod_cast hpmin.pos)
          (by exact_mod_cast Nat.minFac_le_of_dvd hqp.two_le hqd)
      have hgeom := minimum_le_weighted_product_three ht
        (hlog r (Nat.mem_primesLE.mp hr).2 ⟨a*(b*(c*p)),rfl⟩)
        (hlog a (all_bounds ha).1 ⟨r*(b*(c*p)),by dsimp [prod]; ring⟩)
        (hlog b (all_bounds hb).1 ⟨r*(a*(c*p)),by dsimp [prod]; ring⟩)
        (hlog c (all_bounds hc).1 ⟨r*(a*(b*p)),by dsimp [prod]; ring⟩)
      have ht := mul_le_mul_of_nonneg_left hgeom hH
      have hh := atom_norm_bound A hM hNM hs hcount hmmin hlo hhi hL0 hL y
      exact hh.trans ((le_of_eq (by dsimp [H]; ring)).trans (ht.trans_eq (by dsimp [B,w]; ring)))
    · dsimp [B]
      positivity [Real.rpow_nonneg (Real.log_natCast_nonneg r) (1/2 : ℝ)]
  have hb : ‖∑ n ∈ S, f n‖ ≤ ∑ x ∈ D, B x := by
    calc
      _ ≤ ∑ n ∈ S, ‖f n‖ := norm_sum_le _ _
      _ = ∑ n ∈ S, g n := Finset.sum_congr rfl (fun n hn => by simp only [g,if_pos hn])
      _ ≤ ∑ n ∈ D.image prod, g n := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro n _ _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ ∑ x ∈ D, g (prod x) := Finset.sum_image_le_of_nonneg
        (by intro n _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ _ := Finset.sum_le_sum hpoint
  have he : (∑ x ∈ D, B x) =
      ∑ r ∈ Nat.primesLE Q, H*(Real.log r)^(1/2 : ℝ)*
        (∑ v ∈ (G.product G).product G,
          (w v.1.1*w v.1.2*w v.2)*
          ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1-Real.log v.1.2-Real.log v.2)).card : ℝ)) := by
    simp only [D,B,Finset.sum_sigma,Finset.sum_const,nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he] at hb
  have ht := Finset.sum_le_sum (s := Nat.primesLE Q) (fun r _ =>
    mul_le_mul_of_nonneg_left (fractional_cofactor_count_upper (r := r) (by omega : 1 ≤ M))
      (mul_nonneg hH (Real.rpow_nonneg (Real.log_natCast_nonneg r) (1/2 : ℝ))))
  have he' : (∑ r ∈ Nat.primesLE Q, H*(Real.log r)^(1/2 : ℝ)*
      ((16*Real.log 4*(momentConstant (1/6))^3)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))) =
      (H*16*Real.log 4*(momentConstant (1/6))^3*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ)+2)/((M : ℝ)+1))*
          (∑ r ∈ Nat.primesLE Q, (Real.log r)^(1/2 : ℝ)*Real.exp (-Real.log r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he'] at ht
  have hmass := prime_fractional_log_mass_le (Nat.primesLE Q) (X := Real.log Q)
    (Real.log_pos (by exact_mod_cast (show 1 < Q by omega))) (by norm_num : (0 : ℝ) < 1/2)
    (fun r hr => ⟨(Nat.mem_primesLE.mp hr).2,
      Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hr).2.pos)
        (by exact_mod_cast (Nat.mem_primesLE.mp hr).1)⟩)
  refine (hb.trans ht).trans ((mul_le_mul_of_nonneg_left hmass
    (by positivity [momentConstant_pos (by norm_num : (0 : ℝ) < 1/6)])).trans_eq ?_)
  dsimp [H,exponentialHeadConstant]
  rw [Real.exp_add,← Real.sqrt_eq_rpow]
  have he4 : Real.exp (2 : ℝ)*Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (192*Real.log 4*(Real.exp 2*Real.exp 2)*momentConstant (1/2)*(momentConstant (1/6))^3)*
      Real.sqrt (Real.log Q)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by ring
    _ = _ := by rw [he4]

/-- A fixed positive exponential five-prime head costs any prescribed
fraction of signed supply. The minimum-prime geometry is preserved before
the fractional prime sums are bounded. This includes BOTH coefficient signs. -/
theorem eventually_small_five_log_cost {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (S A : Finset ℕ) (L y : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L →
        (∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          ∃ r ∈ n.primeFactors, r ≤ Q) →
        ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
          b*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let B := exponentialHeadConstant
  have hB : 0 < B := exponentialHeadConstant_pos
  let δ := min (1/128 : ℝ) ((b/(4*B))^2)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδu : δ ≤ 1/128 := min_le_left _ _
  have hsqrt : 4*B*Real.sqrt δ ≤ b := by
    have hs := Real.sqrt_le_sqrt (min_le_right (1/128 : ℝ) ((b/(4*B))^2))
    rw [Real.sqrt_sq (by positivity : 0 ≤ b/(4*B))] at hs
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*B by positivity)
    have he : (4*B)*(b/(4*B)) = b := by field_simp
    exact h.trans_eq he
  refine ⟨δ,hδ,hδu,?_⟩
  filter_upwards [eventually_ge_atTop (200 : ℕ)] with N hN M Q S A L y hNM hQ hL0 hL hS
  have hM : 100 ≤ M := by omega
  have hmr : (100 : ℝ) ≤ M := by exact_mod_cast hM
  have hnm : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
  by_cases hQ2 : 2 ≤ Q
  · have hQ' : Real.log Q ≤ (M : ℝ)/32 := by
      have ht := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
      nlinarith
    have hbound := small_five_fractional_norm_upper S A hM hNM hQ2 hQ' hL0 hL y hS
    have hQδ : Real.log Q ≤ 2*δ*M := by nlinarith
    have hprod : Real.log Q*(2*(M : ℝ)+2) ≤ (2*δ*M)*(4*M) :=
      mul_le_mul hQδ (by linarith) (by positivity) (by positivity)
    have hsp : Real.sqrt (Real.log Q)*Real.sqrt (2*(M : ℝ)+2) ≤ 4*Real.sqrt δ*M := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      have hq := Real.sq_sqrt (Real.log_natCast_nonneg Q)
      have ht := Real.sq_sqrt (show 0 ≤ 2*(M : ℝ)+2 by positivity)
      have hd := Real.sq_sqrt hδ.le
      calc
        _ = Real.log Q*(2*(M : ℝ)+2) := by rw [mul_pow,hq,ht]
        _ ≤ (2*δ*M)*(4*M) := hprod
        _ ≤ (4*Real.sqrt δ*M)^2 := by
          simp only [mul_pow,hd]
          nlinarith [mul_nonneg hδ.le (sq_nonneg (M : ℝ))]
    have hcost : B*Real.sqrt (Real.log Q)*Real.sqrt (2*(M : ℝ)+2) ≤ b*M := by
      have h := mul_le_mul_of_nonneg_left hsp hB.le
      have h' := mul_le_mul_of_nonneg_right hsqrt (Nat.cast_nonneg (α := ℝ) M)
      nlinarith only [h,h']
    apply hbound.trans
    have ht := mul_le_mul_of_nonneg_right hcost
      (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
        positivity [radialEnvelope_nonneg N M])
    convert ht using 1 <;> ring
  · have hEmpty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro n hn
      obtain ⟨_,_,_,_,r,hr,hrQ⟩ := hS n hn
      have := (Nat.prime_of_mem_primeFactors hr).two_le
      omega)
    rw [hEmpty,Finset.sum_empty,norm_zero]
    positivity [radialEnvelope_nonneg N M]

end
end RiemannGaussian.ZetaRieszFiveFractionalHead
