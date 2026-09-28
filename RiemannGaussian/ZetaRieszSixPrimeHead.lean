/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFractionalBudget
import RiemannGaussian.ZetaRieszSixPrimeGeometry
import RiemannGaussian.ZetaRieszHeadCeiling

/-!
# Counting and paying six-prime heads

The signed six-prime coefficient bound leaves one small-prime logarithm.
Count one genuinely large prime and retain the logarithmic reciprocal
cost of the other four primes. This bounds the whole literal population,
including both coefficient signs, relative to the existing signed supply.
The fractional-logarithm refinement preserves the least-prime information
across all five cofactor factors and pays a fixed exponential head too.
Its full-core transfer is in `ZetaRieszSixPrimeExponentialHead`.
-/

namespace RiemannGaussian.ZetaRieszSixPrimeHead
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime

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

private theorem shell_reciprocal (j : ℕ) :
    (∑ p ∈ logPrimes (((j : ℝ)+1)/2) (1/2), Real.exp (-Real.log p)) ≤
      (2*Real.exp (1/2)*Real.log 4)/((j : ℝ)+1) := by
  let a := ((j : ℝ)+1)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hh := ZetaRieszQuadrupleCompensation.interval_card_upper ha (by norm_num : (0 : ℝ) ≤ 1/2)
  have hs := Finset.sum_le_sum (s := logPrimes a (1/2)) (fun p hp =>
    Real.exp_le_exp.mpr (neg_le_neg (logPrimes_bounds hp).2.1.le))
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := hs.trans (mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-a)))
  have he : Real.log 4*Real.exp (a+1/2)/a*Real.exp (-a) =
      (2*Real.exp (1/2)*Real.log 4)/((j : ℝ)+1) := by
    rw [Real.exp_add]
    have hcancel : Real.exp a*Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
    calc
      _ = (Real.log 4*Real.exp (1/2)/a)*(Real.exp a*Real.exp (-a)) := by ring
      _ = _ := by rw [hcancel]; dsimp [a]; field_simp
  exact hb.trans_eq he

/-- An elementary logarithmic bound for the literal reciprocal prime
mass. Half-unit log shells are counted with Chebyshev, not approximated
by a prime density. -/
theorem prime_reciprocal_le (M : ℕ) :
    (∑ p ∈ logPrimes 0 (2*(M : ℝ)+2), Real.exp (-Real.log p)) ≤
      (2*Real.exp (1/2)*Real.log 4)*(1+Real.log (4*M+4 : ℕ)) := by
  let J := 4*M+4
  let B := fun j : ℕ => logPrimes (((j : ℝ)+1)/2) (1/2)
  let D := (Finset.range J).sigma B
  have hcover : allPrimes M ⊆ D.image (fun z => z.2) := by
    intro p hp
    have hb := all_bounds hp
    have hlog : (1/2 : ℝ) < Real.log p := by
      have hl : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hb.1.two_le)
      linarith [Real.log_two_gt_d9]
    let q := ⌈2*Real.log p⌉₊
    have hqlo : 2*Real.log p ≤ (q : ℝ) := Nat.le_ceil _
    have hqhi : (q : ℝ) < 2*Real.log p+1 := Nat.ceil_lt_add_one (by linarith)
    have hq2 : 2 ≤ q := by
      have hh : (1 : ℝ) < q := by linarith
      have hh' : 1 < q := by exact_mod_cast hh
      omega
    have hqJ : q ≤ J := Nat.ceil_le.mpr (by dsimp [J]; push_cast; linarith [hb.2.2])
    let j := q-2
    have hej : (j : ℝ)+2 = q := by exact_mod_cast Nat.sub_add_cancel hq2
    have hpB : p ∈ B j := logPrimes_mem hb.1 (by linarith) (by linarith)
    exact Finset.mem_image.mpr ⟨⟨j,p⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (by dsimp [j,J] at *; omega),hpB⟩,rfl⟩
  have hs : (∑ p ∈ allPrimes M, Real.exp (-Real.log p)) ≤
      ∑ j ∈ Finset.range J, ∑ p ∈ B j, Real.exp (-Real.log p) := by
    calc
      _ ≤ ∑ p ∈ (D.image (fun z => z.2) : Finset ℕ), Real.exp (-Real.log p) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun p : ℕ => Real.exp (-Real.log p)) hcover (fun _ _ _ => Real.exp_nonneg _)
      _ ≤ ∑ z ∈ D, Real.exp (-Real.log z.2) :=
        Finset.sum_image_le_of_nonneg
          (s := D) (g := fun z : Σ _j : ℕ, ℕ => z.2)
          (f := fun p : ℕ => Real.exp (-Real.log p)) (fun _ _ => Real.exp_nonneg _)
      _ = _ := Finset.sum_sigma _ _ _
  have hb := Finset.sum_le_sum (s := Finset.range J) (fun j _ => shell_reciprocal j)
  have he : (∑ j ∈ Finset.range J, (2*Real.exp (1/2)*Real.log 4)/((j : ℝ)+1)) =
      (2*Real.exp (1/2)*Real.log 4)*(harmonic J : ℝ) := by
    rw [harmonic]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv]
  rw [he] at hb
  exact (hs.trans hb).trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J)
    (by positivity))

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
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hlo : 2*(M : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2*(M : ℝ)+2)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ Q) (hQ : Real.log Q ≤ (M : ℝ)/32) :
    ∃ r ∈ Nat.primesLE Q, ∃ a ∈ allPrimes M, ∃ b ∈ allPrimes M,
      ∃ c ∈ allPrimes M, ∃ d ∈ allPrimes M,
        ∃ p ∈ macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log a-Real.log b-Real.log c-Real.log d),
          n = r*(a*(b*(c*(d*p)))) := by
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
  have hcard : ((n.primeFactors.erase r).erase p).card = 4 := by
    rw [Finset.card_erase_of_mem hpE,Finset.card_erase_of_mem hr,hc]
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,he⟩ := Finset.card_eq_four.mp hcard
  have haE : a ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hbE : b ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hcE : c ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hdE : d ∈ (n.primeFactors.erase r).erase p := by simp [he]
  have hall (q : ℕ) (hq : q ∈ n.primeFactors) : q ∈ allPrimes M := by
    have hqn : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hq)
    have hlog : Real.log q ≤ Real.log n := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos) (by exact_mod_cast hqn)
    exact all_mem (Nat.prime_of_mem_primeFactors hq) (hlog.trans hhi)
  have hn : n = r*(a*(b*(c*(d*p)))) := by
    rw [← Nat.prod_primeFactors_of_squarefree hs,← Finset.mul_prod_erase _ _ hr,
      ← Finset.mul_prod_erase _ _ hpE,he]
    simp only [Finset.prod_insert (by simp [hab,hac,had] : a ∉ {b,c,d}),
      Finset.prod_insert (by simp [hbc,hbd] : b ∉ {c,d}),
      Finset.prod_insert (by simp [hcd] : c ∉ {d}),Finset.prod_singleton]
    ring
  have hlog := CoprimeEulerPhase.squarefree_log_eq_prime_sum hs
  rw [← Finset.add_sum_erase _ _ hr,← Finset.add_sum_erase _ _ hpE,he] at hlog
  simp only [Finset.sum_insert (by simp [hab,hac,had] : a ∉ {b,c,d}),
    Finset.sum_insert (by simp [hbc,hbd] : b ∉ {c,d}),
    Finset.sum_insert (by simp [hcd] : c ∉ {d}),Finset.sum_singleton] at hlog
  refine ⟨r,Nat.mem_primesLE.mpr ⟨hrQ,hrp⟩,a,hall a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haE)),
    b,hall b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hbE)),
    c,hall c (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcE)),
    d,hall d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hdE)),
    p,macro_mem (Nat.prime_of_mem_primeFactors hp) hplog (by linarith),hn⟩

private theorem atom_norm_bound (A : Finset ℕ) {n r N M : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hc : n.primeFactors.card = 6)
    (hr : r ∈ n.primeFactors) (hlo : 2*(M : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 2*(M : ℝ)+2) {L : ℝ}
    (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (y : ℝ) :
    ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      16*Real.log r*Real.exp 2*radialEnvelope N M := by
  have hm : (100 : ℝ) ≤ M := by exact_mod_cast hM
  have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL0.le
  have hratio : Real.log n/L ≤ 4 := (div_le_iff₀ hL0).mpr (by linarith)
  have hc' := ZetaRieszSixPrimeGeometry.coefficient_six_bounds hL0 hc (by linarith)
  have hleast : Real.log n.minFac ≤ Real.log r := Real.log_le_log
    (by exact_mod_cast Nat.minFac_pos n)
    (by exact_mod_cast (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hr).two_le
      (Nat.dvd_of_mem_primeFactors hr)))
  have hmin := mul_le_mul_of_nonneg_left hleast (show 0 ≤ 4*(Real.log n/L) by positivity)
  have hb : |(SquarefreeVaughanLogSource.coefficient L n).re| ≤ 4*(Real.log n/L)*Real.log r := by
    rw [abs_le]
    have hpos := mul_nonneg hscale (Real.log_natCast_nonneg n.minFac)
    constructor <;> nlinarith only [hc'.1,hc'.2,hmin,hpos]
  have hi := ZetaRieszCosineCarrier.coefficient_im_eq_zero L n
  have he := Complex.re_add_im (SquarefreeVaughanLogSource.coefficient L n)
  rw [hi,Complex.ofReal_zero,zero_mul,add_zero] at he
  have hnorm : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 16*Real.log r := by
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

private theorem cofactor_count_upper {M r : ℕ} (hM : 1 ≤ M) :
    let G := allPrimes M
    (∑ v ∈ ((G.product G).product G).product G,
      ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
        Real.log v.1.2-Real.log v.2)).card : ℝ)) ≤
      (16*Real.log 4*(2*Real.exp (1/2)*Real.log 4)^4)*
        (1+Real.log (4*M+4 : ℕ))^4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) := by
  dsimp only
  let G := allPrimes M
  have hb := Finset.sum_le_sum (s := ((G.product G).product G).product G) (fun v _ =>
    macro_card hM (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
      Real.log v.1.2-Real.log v.2))
  have he : (∑ v ∈ ((G.product G).product G).product G,
      16*Real.log 4*Real.exp (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
        Real.log v.1.2-Real.log v.2)/((M : ℝ)+1)) =
      (16*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))*
        (∑ p ∈ G, Real.exp (-Real.log p))^4 := by
    simp_rw [sub_eq_add_neg,Real.exp_add]
    rw [pow_succ,pow_succ,pow_two,Finset.sum_mul_sum,Finset.sum_mul_sum,Finset.sum_mul_sum]
    simp_rw [Finset.product_eq_sprod,Finset.sum_product]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he] at hb
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))
    (prime_reciprocal_le M) 4
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 16*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) by positivity)
  exact hb.trans (hh.trans_eq (by rw [mul_pow]; ring))

/-- An explicit absolute counting constant. It pays a finite polynomial
head relative to signed supply, not relative to the source normalization. -/
def headConstant : ℝ :=
  256*(Real.log 4)^2*Real.exp 4*(2*Real.exp (1/2)*Real.log 4)^4

/-- The literal head constant is strictly positive. -/
theorem headConstant_pos : 0 < headConstant := by unfold headConstant; positivity

/-- All six-prime labels with a small prime are bounded together, with
both arithmetic signs, original complex phase and original allocation.
The other four prime sizes are unrestricted inside the actual radial slab. -/
theorem small_six_norm_upper (S A : Finset ℕ) {N M Q : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hQ : Real.log Q ≤ (M : ℝ)/32)
    {L : ℝ} (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (y : ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 6 ∧
      2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
      ∃ r ∈ n.primeFactors, r ≤ Q) :
    ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      headConstant*(1+Real.log Q)*(1+Real.log (4*M+4 : ℕ))^4*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let G := allPrimes M
  let D := (Nat.primesLE Q).sigma (fun r => (((G.product G).product G).product G).sigma
    (fun v => macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
      Real.log v.1.2-Real.log v.2)))
  let prod := fun x : Σ _r : ℕ, Σ _v : ((ℕ × ℕ) × ℕ) × ℕ, ℕ =>
    x.1*(x.2.1.1.1.1*(x.2.1.1.1.2*(x.2.1.1.2*(x.2.1.2*x.2.2))))
  let g := fun n => if n ∈ S then ‖f n‖ else 0
  let H := 16*Real.exp 2*radialEnvelope N M
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_nonneg N M]
  have hsub : S ⊆ D.image prod := by
    intro n hn
    obtain ⟨hs,hc,hlo,hhi,hsmall⟩ := hS n hn
    obtain ⟨r,hr,a,ha,b,hb,c,hc',d,hd,p,hp,he⟩ :=
      factorization (by omega : 1 ≤ M) hs hc hlo hhi hsmall hQ
    exact Finset.mem_image.mpr ⟨⟨r,(((a,b),c),d),p⟩,Finset.mem_sigma.mpr
      ⟨hr,Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hc'⟩,hd⟩,hp⟩⟩,he.symm⟩
  have hpoint (x : Σ _r : ℕ, Σ _v : ((ℕ × ℕ) × ℕ) × ℕ, ℕ) (hx : x ∈ D) :
      g (prod x) ≤ H*Real.log x.1 := by
    have hr := (Nat.mem_primesLE.mp (Finset.mem_sigma.mp hx).1).2
    dsimp only [g]
    split_ifs with hn
    · obtain ⟨hs,hc,hlo,hhi,_⟩ := hS _ hn
      have hmem : x.1 ∈ (prod x).primeFactors := Nat.mem_primeFactors.mpr
        ⟨hr,dvd_mul_right _ _,hs.ne_zero⟩
      exact (atom_norm_bound A hM hNM hc hmem hlo hhi hL0 hL y).trans_eq (by dsimp [H]; ring)
    · positivity
  have hb : ‖∑ n ∈ S, f n‖ ≤ ∑ x ∈ D, H*Real.log x.1 := by
    calc
      _ ≤ ∑ n ∈ S, ‖f n‖ := norm_sum_le _ _
      _ = ∑ n ∈ S, g n := Finset.sum_congr rfl (fun n hn => by simp only [g,if_pos hn])
      _ ≤ ∑ n ∈ D.image prod, g n := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro n _ _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ ∑ x ∈ D, g (prod x) := Finset.sum_image_le_of_nonneg
        (by intro n _; exact ite_nonneg (norm_nonneg _) le_rfl)
      _ ≤ _ := Finset.sum_le_sum hpoint
  have he : (∑ x ∈ D, H*Real.log x.1) =
      ∑ r ∈ Nat.primesLE Q, H*Real.log r*
        (∑ v ∈ ((G.product G).product G).product G,
          ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
            Real.log v.1.2-Real.log v.2)).card : ℝ)) := by
    simp only [D,Finset.sum_sigma,Finset.sum_const,nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_sigma,Nat.cast_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he] at hb
  have ht := Finset.sum_le_sum (s := Nat.primesLE Q) (fun r _ =>
    mul_le_mul_of_nonneg_left (cofactor_count_upper (r := r) (by omega : 1 ≤ M))
      (mul_nonneg hH (Real.log_natCast_nonneg r)))
  have he' : (∑ r ∈ Nat.primesLE Q, H*Real.log r*
      ((16*Real.log 4*(2*Real.exp (1/2)*Real.log 4)^4)*
        (1+Real.log (4*M+4 : ℕ))^4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))) =
      (H*16*Real.log 4*(2*Real.exp (1/2)*Real.log 4)^4*
        (1+Real.log (4*M+4 : ℕ))^4*Real.exp (2*(M : ℝ)+2)/((M : ℝ)+1))*
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
  dsimp [H,headConstant]
  rw [Real.exp_add]
  have he4 : Real.exp (2 : ℝ)*Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (256*(Real.log 4)^2*(Real.exp 2*Real.exp 2)*(2*Real.exp (1/2)*Real.log 4)^4)*
      (1+Real.log Q)*(1+Real.log (4*M+4 : ℕ))^4*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by ring
    _ = _ := by rw [he4]



open ZetaRieszPrimeFractionalBudget

private theorem fractional_cofactor_count_upper {M r : ℕ} (hM : 1 ≤ M) :
    let G := allPrimes M
    let w := fun p : ℕ => (Real.log p)^(1/8 : ℝ)
    (∑ v ∈ ((G.product G).product G).product G,
      (w v.1.1.1*w v.1.1.2*w v.1.2*w v.2)*
      ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
        Real.log v.1.2-Real.log v.2)).card : ℝ)) ≤
      (16*Real.log 4*(momentConstant (1/8))^4)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) := by
  dsimp only
  let G := allPrimes M
  let w := fun p : ℕ => (Real.log p)^(1/8 : ℝ)
  have hw (p : ℕ) : 0 ≤ w p := Real.rpow_nonneg (Real.log_natCast_nonneg p) _
  have hb := Finset.sum_le_sum (s := ((G.product G).product G).product G) (fun v _ =>
    mul_le_mul_of_nonneg_left (macro_card hM
      (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-Real.log v.1.2-Real.log v.2))
        (show 0 ≤ w v.1.1.1*w v.1.1.2*w v.1.2*w v.2 by positivity))
  have he : (∑ v ∈ ((G.product G).product G).product G,
      (w v.1.1.1*w v.1.1.2*w v.1.2*w v.2)*
      (16*Real.log 4*Real.exp (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
        Real.log v.1.2-Real.log v.2)/((M : ℝ)+1))) =
      (16*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))*
        (∑ p ∈ G, w p*Real.exp (-Real.log p))^4 := by
    simp_rw [sub_eq_add_neg,Real.exp_add]
    rw [pow_succ,pow_succ,pow_two,Finset.sum_mul_sum,Finset.sum_mul_sum,Finset.sum_mul_sum]
    simp_rw [Finset.product_eq_sprod,Finset.sum_product]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he] at hb
  have hmass := prime_fractional_log_mass_le G
    (by positivity : 0 < 2*(M : ℝ)+2) (by norm_num : (0 : ℝ) < 1/8)
    (fun p hp => ⟨(all_bounds hp).1,(all_bounds hp).2.2⟩)
  have hp := pow_le_pow_left₀
    (Finset.sum_nonneg (fun p _ => mul_nonneg (hw p) (Real.exp_nonneg _))) hmass 4
  have hsqrt : ((2*(M : ℝ)+2)^(1/8 : ℝ))^4 = Real.sqrt (2*(M : ℝ)+2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0 ≤ 2*(M : ℝ)+2)]
    norm_num [Real.sqrt_eq_rpow]
  rw [mul_pow,hsqrt] at hp
  have ht := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 16*Real.log 4*Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1) by positivity)
  exact hb.trans (ht.trans_eq (by ring))

/-- Explicit constant for the fractional-logarithm six-prime head bound. -/
def exponentialHeadConstant : ℝ :=
  256*Real.log 4*Real.exp 4*momentConstant (1/2)*(momentConstant (1/8))^4

/-- The exponential head's actual counting constant is positive. -/
theorem exponentialHeadConstant_pos : 0 < exponentialHeadConstant := by
  unfold exponentialHeadConstant
  positivity [momentConstant_pos (by norm_num : (0 : ℝ) < 1/2),
    momentConstant_pos (by norm_num : (0 : ℝ) < 1/8)]

/-- Keeping the minimum logarithm before summing removes the artificial
four logarithmic losses. Both coefficient signs and all original weights
are included. The cutoff may now be exponential in the moving order. -/
theorem small_six_fractional_norm_upper (S A : Finset ℕ) {N M Q : ℕ}
    (hM : 100 ≤ M) (hNM : N ≤ 2*M) (hQ2 : 2 ≤ Q) (hQ : Real.log Q ≤ (M : ℝ)/32)
    {L : ℝ} (hL0 : 0 < L) (hL : (271/200 : ℝ)*M ≤ L) (y : ℝ)
    (hS : ∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 6 ∧
      2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
      ∃ r ∈ n.primeFactors, r ≤ Q) :
    ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      exponentialHeadConstant*Real.sqrt (Real.log Q)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let G := allPrimes M
  let w := fun p : ℕ => (Real.log p)^(1/8 : ℝ)
  let D := (Nat.primesLE Q).sigma (fun r => (((G.product G).product G).product G).sigma
    (fun v => macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
      Real.log v.1.2-Real.log v.2)))
  let prod := fun x : Σ _r : ℕ, Σ _v : ((ℕ × ℕ) × ℕ) × ℕ, ℕ =>
    x.1*(x.2.1.1.1.1*(x.2.1.1.1.2*(x.2.1.1.2*(x.2.1.2*x.2.2))))
  let g := fun n => if n ∈ S then ‖f n‖ else 0
  let H := 16*Real.exp 2*radialEnvelope N M
  let B := fun x : Σ _r : ℕ, Σ _v : ((ℕ × ℕ) × ℕ) × ℕ, ℕ =>
    H*(Real.log x.1)^(1/2 : ℝ)*w x.2.1.1.1.1*w x.2.1.1.1.2*w x.2.1.1.2*w x.2.1.2
  have hw (p : ℕ) : 0 ≤ w p := Real.rpow_nonneg (Real.log_natCast_nonneg p) _
  have hH : 0 ≤ H := by dsimp [H]; positivity [radialEnvelope_nonneg N M]
  have hsub : S ⊆ D.image prod := by
    intro n hn
    obtain ⟨hs,hc,hlo,hhi,hsmall⟩ := hS n hn
    obtain ⟨r,hr,a,ha,b,hb,c,hc',d,hd,p,hp,he⟩ :=
      factorization (by omega : 1 ≤ M) hs hc hlo hhi hsmall hQ
    exact Finset.mem_image.mpr ⟨⟨r,(((a,b),c),d),p⟩,Finset.mem_sigma.mpr
      ⟨hr,Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hc'⟩,hd⟩,hp⟩⟩,he.symm⟩
  have hpoint (x : Σ _r : ℕ, Σ _v : ((ℕ × ℕ) × ℕ) × ℕ, ℕ) (hx : x ∈ D) :
      g (prod x) ≤ B x := by
    rcases x with ⟨r,v,p⟩
    rcases v with ⟨⟨⟨a,b⟩,c⟩,d⟩
    obtain ⟨hr,hv⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hv,_⟩ := Finset.mem_sigma.mp hv
    obtain ⟨habc,hd⟩ := Finset.mem_product.mp hv
    obtain ⟨hab,hc⟩ := Finset.mem_product.mp habc
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    dsimp only [g]
    split_ifs with hn
    · obtain ⟨hs,hcount,hlo,hhi,_⟩ := hS _ hn
      have hn1 : prod ⟨r,(((a,b),c),d),p⟩ ≠ 1 := by
        intro he
        rw [he] at hcount
        norm_num at hcount
      have hpmin := Nat.minFac_prime hn1
      have hmmin := hpmin.mem_primeFactors (Nat.minFac_dvd _) hs.ne_zero
      have ht : 0 < Real.log (prod ⟨r,(((a,b),c),d),p⟩).minFac :=
        Real.log_pos (by exact_mod_cast hpmin.one_lt)
      have hlog (q : ℕ) (hqp : q.Prime) (hqd : q ∣ prod ⟨r,(((a,b),c),d),p⟩) :
          Real.log (prod ⟨r,(((a,b),c),d),p⟩).minFac ≤ Real.log q :=
        Real.log_le_log (by exact_mod_cast hpmin.pos)
          (by exact_mod_cast Nat.minFac_le_of_dvd hqp.two_le hqd)
      have hgeom := minimum_le_weighted_product ht
        (hlog r (Nat.mem_primesLE.mp hr).2 ⟨a*(b*(c*(d*p))),rfl⟩)
        (hlog a (all_bounds ha).1 ⟨r*(b*(c*(d*p))),by dsimp [prod]; ring⟩)
        (hlog b (all_bounds hb).1 ⟨r*(a*(c*(d*p))),by dsimp [prod]; ring⟩)
        (hlog c (all_bounds hc).1 ⟨r*(a*(b*(d*p))),by dsimp [prod]; ring⟩)
        (hlog d (all_bounds hd).1 ⟨r*(a*(b*(c*p))),by dsimp [prod]; ring⟩)
      have ht := mul_le_mul_of_nonneg_left hgeom hH
      have hh := atom_norm_bound A hM hNM hcount hmmin hlo hhi hL0 hL y
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
        (∑ v ∈ ((G.product G).product G).product G,
          (w v.1.1.1*w v.1.1.2*w v.1.2*w v.2)*
          ((macroPrimes M (2*(M : ℝ)+2-Real.log r-Real.log v.1.1.1-Real.log v.1.1.2-
            Real.log v.1.2-Real.log v.2)).card : ℝ)) := by
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
      ((16*Real.log 4*(momentConstant (1/8))^4)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ)+2)*Real.exp (-Real.log r)/((M : ℝ)+1))) =
      (H*16*Real.log 4*(momentConstant (1/8))^4*Real.sqrt (2*(M : ℝ)+2)*
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
  refine (hb.trans ht).trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq ?_)
  dsimp [H,exponentialHeadConstant]
  rw [Real.exp_add,← Real.sqrt_eq_rpow]
  have he4 : Real.exp (2 : ℝ)*Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (256*Real.log 4*(Real.exp 2*Real.exp 2)*momentConstant (1/2)*(momentConstant (1/8))^4)*
      Real.sqrt (Real.log Q)*Real.sqrt (2*(M : ℝ)+2)*
        Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by ring
    _ = _ := by rw [he4]

private theorem log_head_bound {M : ℕ} (hM : 2 ≤ M) :
    1+Real.log (4*M+4 : ℕ) ≤ 6*Real.log M := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hl : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have hx : (0 : ℝ) < (4*M+4 : ℕ) := by positivity
  have hb : ((4*M+4 : ℕ) : ℝ) ≤ 8*(M : ℝ) := by
    have hh : (2 : ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    linarith
  have h := Real.log_le_log hx hb
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hm.ne'] at h
  have he : Real.log (8 : ℝ) = 3*Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num,Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

private theorem tendsto_log_fifth_rate :
    Tendsto (fun M : ℕ => (Real.log M)^5/(M : ℝ)) atTop (𝓝 0) := by
  simpa only [one_mul,add_zero,Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 5 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_log_rate :
    Tendsto (fun M : ℕ => Real.log M/(M : ℝ)) atTop (𝓝 0) := by
  simpa only [pow_one,one_mul,add_zero,Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The ENTIRE polynomial six-prime head has arbitrarily small relative
cost against the actual signed supply scale. This is not a claim of
source-normalized decay of the head on its own. -/
theorem eventually_small_six_cost {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, ∀ (M : ℕ) (S A : Finset ℕ) (L y : ℝ),
      N ≤ 2*M → 0 < L → (271/200 : ℝ)*M ≤ L →
      (∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 6 ∧
        2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
        ∃ r ∈ n.primeFactors, r ≤ N^2) →
      ‖∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        b*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M := by
  have hf := tendsto_log_fifth_rate.eventually_lt_const
    (show 0 < b/(2*headConstant*6^5) by positivity [headConstant_pos])
  have hl := tendsto_log_rate.eventually_lt_const (by norm_num : (0 : ℝ) < 1/384)
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp (hf.and hl)
  filter_upwards [eventually_ge_atTop (2*M0),eventually_ge_atTop (200 : ℕ)]
    with N hN0 hN M S A L y hNM hL0 hL hS
  have hM : 100 ≤ M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hsmall,hslope⟩ := hM0 M (by omega)
  have hH := log_head_bound (by omega : 2 ≤ M)
  let H := 1+Real.log (4*M+4 : ℕ)
  have hH0 : 0 ≤ H := by dsimp [H]; positivity [Real.log_natCast_nonneg (4*M+4)]
  have hlogN : Real.log N ≤ Real.log (4*M+4 : ℕ) :=
    Real.log_le_log hn (by exact_mod_cast (show N ≤ 4*M+4 by omega))
  have hQeq : Real.log (N^2 : ℕ) = 2*Real.log N := by
    rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hQH : 1+Real.log (N^2 : ℕ) ≤ 2*H := by dsimp [H]; rw [hQeq]; linarith
  have hQ : Real.log (N^2 : ℕ) ≤ (M : ℝ)/32 := by
    have ht := (div_lt_iff₀ hm).mp hslope
    rw [hQeq]
    linarith
  have hpow := pow_le_pow_left₀ hH0 hH 5
  have hcost : headConstant*(1+Real.log (N^2 : ℕ))*H^4 ≤ b*M := by
    calc
      _ ≤ headConstant*(2*H)*H^4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQH headConstant_pos.le)
          (pow_nonneg hH0 4)
      _ = (2*headConstant)*H^5 := by ring
      _ ≤ (2*headConstant)*(6*Real.log M)^5 :=
        mul_le_mul_of_nonneg_left hpow (by positivity [headConstant_pos])
      _ = (2*headConstant*6^5)*(Real.log M)^5 := by ring
      _ ≤ b*M := by
        have ht := mul_le_mul_of_nonneg_left ((div_lt_iff₀ hm).mp hsmall).le
          (show 0 ≤ 2*headConstant*6^5 by positivity [headConstant_pos])
        have he : (2*headConstant*6^5)*(b/(2*headConstant*6^5)*M) = b*M := by
          field_simp [headConstant_pos.ne']
        exact ht.trans_eq he
  have hbound := small_six_norm_upper S A hM hNM hQ hL0 hL y hS
  apply hbound.trans
  have ht := mul_le_mul_of_nonneg_right hcost
    (show 0 ≤ Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M by
      positivity [radialEnvelope_nonneg N M])
  convert ht using 1 <;> ring



/-- A fixed positive exponential six-prime head costs any prescribed
fraction of signed supply. The minimum-prime geometry is preserved before
the fractional prime sums are bounded. This includes BOTH coefficient signs. -/
theorem eventually_small_six_log_cost {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (S A : Finset ℕ) (L y : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L →
        (∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 6 ∧
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
    have hbound := small_six_fractional_norm_upper S A hM hNM hQ2 hQ' hL0 hL y hS
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

open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- One original signed supply pays the old exponential count-3/4/positive-5
heads and the entire polynomial count-6 head. Exactly one sixteenth
remains available; the previous supply is not counted again. -/
theorem eventually_joint_slabs_floor {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (D S H F G A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧ n.primeFactors.card = 6 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          ∃ r ∈ n.primeFactors, r ≤ N^2) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := (∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ G, f n‖ ≤ (1/16 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    ZetaRieszFivePositiveHead.eventually_joint_slabs_spending_log_head_with_scale hy
  refine ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,?_⟩
  filter_upwards [hpay,eventually_small_six_cost (show 0 < c/16 by positivity)]
    with N hpay hsmall M Q D S H F G A L hNM hQ hL0 hL hLu hH hF hG
  obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  refine ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay,?_⟩
  have hGpay := hsmall M G A L y hNM hL0 hL hG
  have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/16)
  apply hGpay.trans
  convert h using 1
  ring

/-- One original signed supply pays the old exponential count-3/4/positive-5
heads and the entire polynomial count-6 head. Exactly one sixteenth
remains available; the previous supply is not counted again. -/
theorem eventually_joint_slabs_ceiling {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q : ℕ) (D S H F G A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧ n.primeFactors.card = 6 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          ∃ r ∈ n.primeFactors, r ≤ N^2) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := -(∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ G, f n‖ ≤ (1/16 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    ZetaRieszHeadCeiling.eventually_joint_slabs_upper_log_head_with_scale hy
  refine ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,?_⟩
  filter_upwards [hpay,eventually_small_six_cost (show 0 < c/16 by positivity)]
    with N hpay hsmall M Q D S H F G A L hNM hQ hL0 hL hLu hH hF hG
  obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  refine ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay,?_⟩
  have hGpay := hsmall M G A L y hNM hL0 hL hG
  have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/16)
  apply hGpay.trans
  convert h using 1
  ring


/-- Exact lower spending from ONE supply, with the new six-prime head
and all favorable selected observations retained. -/
theorem re_sum_ge_joint_spending {D X Z H F G Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : X ∪ Z ∪ H ∪ Y ∪ F ∪ G ⊆ D) (hXZ : Disjoint X Z)
    (hXH : Disjoint X H) (hZH : Disjoint Z H)
    (hXY : Disjoint X Y) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hF : Disjoint F (X ∪ Z ∪ H ∪ Y))
    (hG : Disjoint G (X ∪ Z ∪ H ∪ Y ∪ F))
    (hXcost : ‖∑ n ∈ X, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ Y, f n).re)
    (hZcost : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hHcost : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hFcost : ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hGcost : ‖∑ n ∈ G, f n‖ ≤ (1/16 : ℝ)*(∑ n ∈ Y, f n).re) :
    (∑ n ∈ D\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G), f n).re+
      max (∑ n ∈ X, f n).re 0+max (∑ n ∈ Z, f n).re 0+
      max (∑ n ∈ H, f n).re 0+max (∑ n ∈ F, f n).re 0+
      max (∑ n ∈ G, f n).re 0+(∑ n ∈ Y, f n).re/16 ≤ (∑ n ∈ D, f n).re := by
  have hsub' : X ∪ Z ∪ H ∪ Y ∪ F ⊆ D\G := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_union_left G hn),
      fun hnG => Finset.disjoint_left.mp hG hnG hn⟩
  have hgsub : G ⊆ D := fun _ hn => hsub (Finset.mem_union_right _ hn)
  have hledger := ZetaRieszFivePositiveHead.re_sum_ge_joint_spending f hsub' hXZ hXH hZH
    hXY hZY hHY hF hXcost hZcost hHcost hFcost
  have he : (D\G)\(X ∪ Z ∪ H ∪ Y ∪ F) = D\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [he] at hledger
  have hsum := congrArg Complex.re (Finset.sum_sdiff (f := f) hgsub)
  simp only [Complex.add_re] at hsum
  have hg := (abs_le.mp ((Complex.abs_re_le_norm _).trans hGcost)).1
  have hy : 0 ≤ (∑ n ∈ Y, f n).re := by nlinarith [norm_nonneg (∑ n ∈ G, f n)]
  rcases le_total (∑ n ∈ G, f n).re 0 with hg' | hg'
  · rw [max_eq_right hg']
    linarith
  · rw [max_eq_left hg']
    linarith

/-- Exact upper spending, retaining the new head's favorable negative
observation and the complete signed complement. -/
theorem re_sum_le_joint_spending {D X Z H F G Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : X ∪ Z ∪ H ∪ Y ∪ F ∪ G ⊆ D) (hXZ : Disjoint X Z)
    (hXH : Disjoint X H) (hZH : Disjoint Z H)
    (hXY : Disjoint X Y) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hF : Disjoint F (X ∪ Z ∪ H ∪ Y))
    (hG : Disjoint G (X ∪ Z ∪ H ∪ Y ∪ F))
    (hXcost : ‖∑ n ∈ X, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hZcost : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hHcost : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hFcost : ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ Y, f n).re))
    (hGcost : ‖∑ n ∈ G, f n‖ ≤ (1/16 : ℝ)*(-(∑ n ∈ Y, f n).re)) :
    (∑ n ∈ D, f n).re ≤
      (∑ n ∈ D\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G), f n).re+
      min (∑ n ∈ X, f n).re 0+min (∑ n ∈ Z, f n).re 0+
      min (∑ n ∈ H, f n).re 0+min (∑ n ∈ F, f n).re 0+
      min (∑ n ∈ G, f n).re 0+(∑ n ∈ Y, f n).re/16 := by
  have h := re_sum_ge_joint_spending (fun n => -f n)
    hsub hXZ hXH hZH hXY hZY hHY hF hG
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hXcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hZcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hHcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hFcost)
    (by simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using hGcost)
  have hm (a : ℝ) : max (-a) 0 = -min a 0 := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  simp only [Finset.sum_neg_distrib,Complex.neg_re,hm] at h
  linarith only [h]

/-- All six-prime labels with a marked polynomially small factor in one
half-open radial slab, with no coefficient-sign or largest-share restriction. -/
def smallSixes (S : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 6 ∧
    2*(M : ℝ) ≤ Real.log n ∧ Real.log n < 2*(M : ℝ)+2 ∧
    ∃ r ∈ n.primeFactors, r ≤ N^2)

/-- The six-prime head is selected inside the unchanged radial union. -/
def radialSixes (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (radialIndices N).biUnion (fun M => smallSixes S M N)

/-- Radial six-prime selections do not overlap. -/
theorem smallSixes_disjoint (S : Finset ℕ) (N : ℕ) :
    Pairwise (fun M M' : ℕ => Disjoint (smallSixes S M N) (smallSixes S M' N)) := by
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

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h


/-- The original core comparison pays the six-prime polynomial head in
its radial union as well as the previous exponential heads. It retains
one sixteenth of ONE supply, every favorable selected observation and
one exact signed complement. Boundary labels remain in that complement. -/
theorem eventually_core_floor {u y : ℝ} (hu : 1/2 < u)
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
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hpay⟩ := eventually_joint_slabs_floor hy
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
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallSixes S M N, f n‖ ≤ (1/16 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF,hG⟩ := hpay M Q S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallSixes S M N) A L
        (hL M hM).1 hQ (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall,hpos⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall,hpos⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hsmall⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF,hG⟩⟩
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
    (fun M hM => (hv M hM).2.2.2.2.2.1)
  have hFpay := norm_radial_payment
    (fun _ _ _ _ hne => smallPositiveFives_disjoint S Q L hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.1)
  have hGpay := norm_radial_payment
    (fun _ _ _ _ hne => smallSixes_disjoint S N hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.2)
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
  have hFsub : Fs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hGsub : Gs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hG6 : ∀ n ∈ Gs, n.primeFactors.card = 6 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
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
  have hFdisj : Disjoint Fs (Xs ∪ Zs ∪ Hs ∪ Ys) := by
    apply Finset.disjoint_left.mpr
    intro n hnF hn
    have hf := hF5 n hnF
    rcases Finset.mem_union.mp hn with hn | hnY
    · rcases Finset.mem_union.mp hn with hn | hnH
      · rcases Finset.mem_union.mp hn with hnX | hnZ
        · have := hX3 n hnX; omega
        · have := hZ3 n hnZ; omega
      · have := hH4 n hnH; omega
    · have := hY4 n hnY; omega
  have hGdisj : Disjoint Gs (Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs) := by
    apply Finset.disjoint_left.mpr
    intro n hnG hn
    have hg := hG6 n hnG
    rcases Finset.mem_union.mp hn with hn | hnF
    · rcases Finset.mem_union.mp hn with hn | hnY
      · rcases Finset.mem_union.mp hn with hn | hnH
        · rcases Finset.mem_union.mp hn with hnX | hnZ
          · have := hX3 n hnX; omega
          · have := hZ3 n hnZ; omega
        · have := hH4 n hnH; omega
      · have := hY4 n hnY; omega
    · have := hF5 n hnF; omega
  have hfloor := ZetaRieszSixPrimeHead.re_sum_ge_joint_spending f (Finset.union_subset (Finset.union_subset hsuball hFsub) hGsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hGdisj hXpay hZpay hHpay hFpay hGpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm


/-- The original core comparison pays the six-prime polynomial head in
its radial union as well as the previous exponential heads. It retains
one sixteenth of ONE supply, every favorable selected observation and
one exact signed complement. Boundary labels remain in that complement. -/
theorem eventually_core_ceiling {u y : ℝ} (hu : 1/2 < u)
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
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hpay⟩ := eventually_joint_slabs_ceiling hy
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
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < -(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallSixes S M N, f n‖ ≤ (1/16 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF,hG⟩ := hpay M Q S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallSixes S M N) A L
        (hL M hM).1 hQ (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall,hpos⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall,hpos⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hsmall⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF,hG⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ys := radialSupply N h v
  have hY : 0 < -(∑ n ∈ Ys, f n).re := by
    change 0 < -(∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending (f := fun n => -f n) hhu hvb (fun M hM => by
    simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.1)
  have hZpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) Q hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallFours_disjoint S Q hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.1)
  have hFpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallPositiveFives_disjoint S Q L hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2.1)
  have hGpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallSixes_disjoint S N hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2.2)
  simp only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] at hXpay hZpay hHpay hFpay hGpay
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
  have hFsub : Fs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hGsub : Gs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hG6 : ∀ n ∈ Gs, n.primeFactors.card = 6 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
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
  have hFdisj : Disjoint Fs (Xs ∪ Zs ∪ Hs ∪ Ys) := by
    apply Finset.disjoint_left.mpr
    intro n hnF hn
    have hf := hF5 n hnF
    rcases Finset.mem_union.mp hn with hn | hnY
    · rcases Finset.mem_union.mp hn with hn | hnH
      · rcases Finset.mem_union.mp hn with hnX | hnZ
        · have := hX3 n hnX; omega
        · have := hZ3 n hnZ; omega
      · have := hH4 n hnH; omega
    · have := hY4 n hnY; omega
  have hGdisj : Disjoint Gs (Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs) := by
    apply Finset.disjoint_left.mpr
    intro n hnG hn
    have hg := hG6 n hnG
    rcases Finset.mem_union.mp hn with hn | hnF
    · rcases Finset.mem_union.mp hn with hn | hnY
      · rcases Finset.mem_union.mp hn with hn | hnH
        · rcases Finset.mem_union.mp hn with hnX | hnZ
          · have := hX3 n hnX; omega
          · have := hZ3 n hnZ; omega
        · have := hH4 n hnH; omega
      · have := hY4 n hnY; omega
    · have := hF5 n hnF; omega
  have hfloor := ZetaRieszSixPrimeHead.re_sum_le_joint_spending f (Finset.union_subset (Finset.union_subset hsuball hFsub) hGsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hGdisj hXpay hZpay hHpay hFpay hGpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re ≤ _
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm


/-- Every six-prime head label inside the inner radial window is selected.
No dominant-prime assumption or coefficient-sign test is required. -/
theorem mem_radialSixes_of_geometry {S : Finset ℕ} {N n : ℕ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hc : n.primeFactors.card = 6)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ N^2) : n ∈ radialSixes S N := by
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
  exact Finset.mem_biUnion.mpr ⟨M,hM,Finset.mem_filter.mpr
    ⟨hnS,hs,hc,by linarith,by linarith,hsmall⟩⟩

/-- The entire six-prime polynomial head in a literal selected carrier,
including its radial boundary labels. -/
def wholeSixes (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 6 ∧
    ∃ p ∈ n.primeFactors, p ≤ N^2)

open LogarithmicDeviation ZetaArithmeticDeviationBounds

/-- The previous source-normalized radial/dominant allowance also pays
all missing six-prime boundary labels. Thus the new head payment covers
the whole original core, not just the interior radial selections. -/
theorem exists_full_head_missed_bound :
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
        let F := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let G := radialSixes S N
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)) ∧
          ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S N
        ‖(u : ℂ)^(N+1)*∑ n ∈ B\(X ∪ Z ∪ H ∪ F ∪ G),
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
  let F := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let G := radialSixes S N
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S N
  let D := B\(X ∪ Z ∪ H ∪ F ∪ G)
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
    rcases Finset.mem_union.mp hnB with hnB | hn6
    · have hnold : n ∉ X ∪ Z ∪ H ∪ F :=
        fun h => hnnot (Finset.mem_union_left G h)
      rcases Finset.mem_union.mp hnB with hbal | hnB
      · exact hnold (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (balanced_mem_radialTriples hN hη hηN hbal hlo hhi))))
      obtain ⟨hnS,hs,hcount,p,hp,hpQ⟩ := Finset.mem_filter.mp hnB
      have hmax := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u
        (Finset.mem_filter.mpr ⟨hnS,hnP⟩) hcoeff
      have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have hplog : Real.log p ≤ δ*N := by
        have h := Real.log_le_log hpR (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
        exact h.trans (log_floor_exp_le (mul_nonneg hδ (Nat.cast_nonneg (α := ℝ) N)))
      rcases hcount with h3 | h4 | ⟨h5,hpos⟩
      · exact hnold (Finset.mem_union_left _ (mem_exponential_paid_of_geometry hN hnS hs
          (Or.inl h3) hlo hhi (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩))
      · exact hnold (Finset.mem_union_left _ (mem_exponential_paid_of_geometry hN hnS hs
          (Or.inr h4) hlo hhi (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩))
      · exact hnold (Finset.mem_union_right _ (mem_exponential_positive_paid_of_geometry
          hN hnS hs h5 hpos hlo hhi (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩))
    · obtain ⟨hnS,hs,hcount,hsmall⟩ := Finset.mem_filter.mp hn6
      exact hnnot (Finset.mem_union_right _
        (mem_radialSixes_of_geometry hN hnS hs hcount hlo hhi hsmall))
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

private theorem sdiff_union_payment (S X Z H Y F G B : Finset ℕ) :
    (S\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G))\(B\(X ∪ Z ∪ H ∪ F ∪ G)) =
      S\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ B) := by
  ext n
  simp only [Finset.mem_sdiff,Finset.mem_union]
  tauto

/-- Joint comparison after paying the ENTIRE six-prime polynomial head
and the old exponential heads, including radial/dominant boundaries.
One sixteenth of the same supply, favorable observations and the exact
signed rest are retained. This is not a bound for the whole signed rest. -/
theorem eventually_core_full_floor {u y : ℝ} (hu : 1/2 < u)
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
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S N
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)-
              (r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)) ≤
                ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hspend⟩ := eventually_core_floor hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_full_head_missed_bound
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
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S N
  let D := B\(Xs ∪ Zs ∪ Hs ∪ Fs ∪ Gs)
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
    rcases Finset.mem_union.mp hnB with hnB | hn6
    ·
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
    · have hc := (Finset.mem_filter.mp hn6).2.2.1
      omega

  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := by
    intro n hn
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn
      · rcases Finset.mem_union.mp hn with hn | hn <;> exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    have hnY : n ∉ Ys := fun h => Finset.disjoint_left.mp hBY hnB h
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | hg
    · rcases Finset.mem_union.mp h with h | hf
      · rcases Finset.mem_union.mp h with h | hy
        · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_left Fs h))
        · exact hnY hy
      · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_right _ hf))
    · exact hnnot (Finset.mem_union_right _ hg)
  have hset : (S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs))\D =
      S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B) := by
    exact sdiff_union_payment S Xs Zs Hs Ys Fs Gs B
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)-_ ≤ _
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) ≤ _ at hfloor
  rw [← hre] at hfloor
  nlinarith only [hfloor,hreal]


/-- Joint comparison after paying the ENTIRE six-prime polynomial head
and the old exponential heads, including radial/dominant boundaries.
One sixteenth of the same supply, favorable observations and the exact
signed rest are retained. This is not a bound for the whole signed rest. -/
theorem eventually_core_full_ceiling {u y : ℝ} (hu : 1/2 < u)
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
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S N
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)+
                (r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)) := by
  obtain ⟨η,h,δ,hη,hηu,hh,hhu,hδ,hδu,hspend⟩ := eventually_core_ceiling hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_full_head_missed_bound
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
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S N
  let D := B\(Xs ∪ Zs ∪ Hs ∪ Fs ∪ Gs)
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed j η δ y u hj32 hN hη hηN hδ.le hu.le hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _ at hnorm
  have hreal : u^(N+1)*(∑ n ∈ D, f n).re ≤ r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/1000000) := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hBY : Disjoint B Ys := by
    apply Finset.disjoint_left.mpr
    intro n hnB hnY
    have hsupply := radial_supply_geometry (by omega : 2000 ≤ N) hh hhu hvb hnY
    rcases Finset.mem_union.mp hnB with hnB | hn6
    ·
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
    · have hc := (Finset.mem_filter.mp hn6).2.2.1
      omega

  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := by
    intro n hn
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn
      · rcases Finset.mem_union.mp hn with hn | hn <;> exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    have hnY : n ∉ Ys := fun h => Finset.disjoint_left.mp hBY hnB h
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | hg
    · rcases Finset.mem_union.mp h with h | hf
      · rcases Finset.mem_union.mp h with h | hy
        · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_left Fs h))
        · exact hnY hy
      · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_right _ hf))
    · exact hnnot (Finset.mem_union_right _ hg)
  have hset : (S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs))\D =
      S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B) := by
    exact sdiff_union_payment S Xs Zs Hs Ys Fs Gs B
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change _ ≤ u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n).re+
    min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)+_
  change _ ≤ u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n).re+
    min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) at hfloor
  rw [← hre] at hfloor
  nlinarith only [hfloor,hreal]


/-- Every prime in a surviving six-prime label exceeds the polynomial
threshold once the full head has been paid. -/
theorem remaining_six_prime_gt {S E : Finset ℕ} {N n : ℕ}
    (hn : n ∈ S\(E ∪ wholeSixes S N)) (hs : Squarefree n)
    (hc : n.primeFactors.card = 6) : ∀ p ∈ n.primeFactors, N^2 < p := by
  obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp hn
  intro p hp
  by_contra h
  exact hnnot (Finset.mem_union_right E
    (Finset.mem_filter.mpr ⟨hnS,hs,hc,p,hp,le_of_not_gt h⟩))

end
end RiemannGaussian.ZetaRieszSixPrimeHead
