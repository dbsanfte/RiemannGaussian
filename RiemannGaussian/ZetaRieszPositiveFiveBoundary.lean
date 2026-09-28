/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPositiveFiveBounds
import RiemannGaussian.ZetaRieszCoreExtensions

/-!
# A literal least-prime boundary payment for the joint five-prime estimate

A positive coefficient with largest share below `119/200` cannot have two
small cofactor primes. The marked small prime keeps its logarithmic weight;
Chebyshev pays that entire boundary, while three macroscopic reciprocal
prime sums and the exact last-prime interval pay its full finite population.
The final bound is spent in the whole joint ledger, not a new completion.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveBoundary
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic ZetaRieszPrimeEndpoint

/-- A fixed logarithmic head; its width does not shrink with the moment. -/
def headShare : ℝ := 1/100000000

/-- Every positive five-prime boundary label in the original support. -/
def population (S : Finset ℕ) (L t h : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 5 ∧
    t < Real.log n ∧ Real.log n ≤ t+h ∧
    0 < (SquarefreeVaughanLogSource.coefficient L n).re ∧
    Real.log (largestPrime n) < (119/200 : ℝ)*Real.log n ∧
    ∃ r ∈ n.primeFactors, Real.log r ≤ headShare*Real.log n)

private theorem largest_mem {n : ℕ} (hc : n.primeFactors.card = 5) :
    largestPrime n ∈ n.primeFactors := by
  have hn : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  rw [largestPrime,dif_pos hn]
  exact Finset.max'_mem _ _

private theorem largest_log {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 5) :
    Real.log n ≤ 5*Real.log (largestPrime n) := by
  have hm (p : ℕ) (hp : p ∈ n.primeFactors) : Real.log p ≤ Real.log (largestPrime n) := by
    have hn : n.primeFactors.Nonempty := ⟨p,hp⟩
    apply Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    have hp' := Finset.le_max' n.primeFactors p hp
    rw [largestPrime,dif_pos hn]
    exact_mod_cast hp'
  have hsum := Finset.sum_le_sum hm
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs,Finset.sum_const,hc,nsmul_eq_mul] at hsum
  simpa using hsum

private theorem owner_lower {S : Finset ℕ} {L t h : ℝ} (ht : 1 ≤ t)
    (hhu : h ≤ 1/100000) (hL : (69/100 : ℝ)*t ≤ L) (hLu : L ≤ (7/10 : ℝ)*t)
    {n : ℕ} (hn : n ∈ population S L t h) :
    (107/200 : ℝ)*t-h/2 < Real.log (largestPrime n) := by
  obtain ⟨_,_,hc,htn,hnt,hpos,_,_⟩ := Finset.mem_filter.mp hn
  have hL0 : 0 < L := by linarith
  have hgate : 3*L < 2*Real.log (largestPrime n)+Real.log n := by
    by_contra hh
    have hz := ZetaRieszFivePrimeFloor.coefficient_five_nonpos hc hL0
      (by linarith) (by linarith) (Or.inl (le_of_not_gt hh))
    linarith
  linarith

/-- Positivity forces every cofactor other than the marked small prime
into a fixed macroscopic log interval. This is derived from the coefficient,
not imposed as an additional support restriction. -/
theorem other_cofactor_log_gt {S : Finset ℕ} {L t h : ℝ} (ht : 1 ≤ t)
    (hhu : h ≤ 1/100000) (hL : (69/100 : ℝ)*t ≤ L) (hLu : L ≤ (7/10 : ℝ)*t)
    {n r : ℕ} (hn : n ∈ population S L t h)
    (hr : r ∈ n.primeFactors) (hrsmall : Real.log r ≤ headShare*Real.log n) :
    r ∈ n.primeFactors.erase (largestPrime n) ∧
    ∀ q ∈ (n.primeFactors.erase (largestPrime n)).erase r, (9/100 : ℝ)*t < Real.log q := by
  obtain ⟨_,hs,hc,htn,hnt,hpos,howner,_⟩ := Finset.mem_filter.mp hn
  have hL0 : 0 < L := by linarith
  have hrb : Real.log r ≤ (t+h)/100000000 := by
    dsimp only [headShare] at hrsmall
    linarith
  have hrP : r ≠ largestPrime n := by
    intro he
    have hp := largest_log hs hc
    rw [he] at hrb
    linarith
  have hr' : r ∈ n.primeFactors.erase (largestPrime n) := Finset.mem_erase.mpr ⟨hrP,hr⟩
  refine ⟨hr',?_⟩
  intro q hq
  by_contra hh
  have hq' : Real.log q ≤ (9/100 : ℝ)*t := le_of_not_gt hh
  have hz := ZetaRieszFivePositiveHead.positiveAllowance_eq_zero_of_pair hc hr' hq
    (L := L) (by linarith)
  rw [ZetaRieszFivePrimeReserve.positiveAllowance_eq hc hL0 (by linarith) (by linarith),
    max_eq_right hpos.le] at hz
  linarith

private def smallPrimes (t : ℝ) : Finset ℕ := logPrimes 0 (2*headShare*t)
private def largePrimes (t : ℝ) : Finset ℕ := logPrimes ((9/100 : ℝ)*t) ((19/50 : ℝ)*t)
private def cofactors (t : ℝ) : Finset (ℕ × (Fin 3 → ℕ)) :=
  (smallPrimes t).product (Fintype.piFinset (fun _ : Fin 3 => largePrimes t))
private def cofactor (v : ℕ × (Fin 3 → ℕ)) : ℕ := v.1*∏ i, v.2 i
private def lastPrimes (t h : ℝ) (v : ℕ × (Fin 3 → ℕ)) : Finset ℕ :=
  if t/2 ≤ t-Real.log (cofactor v) then logPrimes (t-Real.log (cofactor v)) h else ∅
private def representations (t h : ℝ) : Finset ((ℕ × (Fin 3 → ℕ)) × ℕ) :=
  (cofactors t).biUnion (fun v => (lastPrimes t h v).image (fun p => (v,p)))

private theorem population_covered (S : Finset ℕ) {L t h : ℝ} (ht : 1 ≤ t)
    (hhu : h ≤ 1/100000) (hL : (69/100 : ℝ)*t ≤ L) (hLu : L ≤ (7/10 : ℝ)*t) :
    population S L t h ⊆ (representations t h).image (fun v => cofactor v.1*v.2) := by
  intro n hn
  obtain ⟨_,hs,hc,htn,hnt,_,_,r,hr,hrsmall⟩ := Finset.mem_filter.mp hn
  obtain ⟨hr',hlarge⟩ := other_cofactor_log_gt ht hhu hL hLu hn hr hrsmall
  have hP := largest_mem hc
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hcard : ((n.primeFactors.erase (largestPrime n)).erase r).card = 3 := by
    rw [Finset.card_erase_of_mem hr',Finset.card_erase_of_mem hP,hc]
  obtain ⟨a,b,c,hab,hac,hbc,he⟩ := Finset.card_eq_three.mp hcard
  let v : Fin 3 → ℕ := ![a,b,c]
  have hv (i : Fin 3) : v i ∈ (n.primeFactors.erase (largestPrime n)).erase r := by
    fin_cases i <;> simp [v,he]
  have hprime (i : Fin 3) := Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hv i)))
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrmem : r ∈ smallPrimes t := by
    apply (mem_logPrimes_iff _ _ _).mpr
    refine ⟨hrp,Real.log_pos (by exact_mod_cast hrp.one_lt),?_⟩
    dsimp only [headShare] at hrsmall ⊢
    linarith
  have hPlo := owner_lower ht hhu hL hLu hn
  have hvlog (i : Fin 3) : Real.log (v i) ≤ (47/100 : ℝ)*t := by
    have hsume := Finset.sum_erase_add n.primeFactors (fun p => Real.log p) hP
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hsume
    have hqsum := Finset.single_le_sum (fun p (_ : p ∈ n.primeFactors.erase (largestPrime n)) =>
      Real.log_natCast_nonneg p) (Finset.mem_of_mem_erase (hv i))
    linarith
  have hvmem (i : Fin 3) : v i ∈ largePrimes t :=
    (mem_logPrimes_iff _ _ _).mpr ⟨hprime i,hlarge _ (hv i),by linarith [hvlog i]⟩
  have hnprod : cofactor (r,v)*largestPrime n = n := by
    calc
      _ = (r*∏ p ∈ (n.primeFactors.erase (largestPrime n)).erase r, p)*largestPrime n := by
        rw [he]
        simp [cofactor,v,Fin.prod_univ_three,hab,hac,hbc,mul_assoc]
      _ = (∏ p ∈ n.primeFactors.erase (largestPrime n), p)*largestPrime n := by
        rw [Finset.mul_prod_erase _ (fun p : ℕ => p) hr']
      _ = ∏ p ∈ n.primeFactors, p := Finset.prod_erase_mul _ _ hP
      _ = n := Nat.prod_primeFactors_of_squarefree hs
  have hm : cofactor (r,v) ≠ 0 := mul_ne_zero hrp.ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero))
  have hlog : Real.log n = Real.log (cofactor (r,v))+Real.log (largestPrime n) := by
    conv_lhs => rw [← hnprod,Nat.cast_mul]
    exact Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hPp.ne_zero)
  have hlast : t/2 ≤ t-Real.log (cofactor (r,v)) := by
    linarith only [hPlo,hlog,hnt,hhu,ht]
  apply Finset.mem_image.mpr
  refine ⟨((r,v),largestPrime n),?_,hnprod⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(r,v),Finset.mem_product.mpr ⟨hrmem,Fintype.mem_piFinset.mpr hvmem⟩,
    Finset.mem_image.mpr ⟨largestPrime n,?_,rfl⟩⟩
  rw [lastPrimes,if_pos hlast]
  exact (mem_logPrimes_iff _ _ _).mpr ⟨hPp,by linarith,by linarith⟩

private theorem small_log_mass {t : ℝ} (ht : 1 ≤ headShare*t) :
    (∑ r ∈ smallPrimes t, Real.log r*(r : ℝ)⁻¹) ≤ 10*headShare*t := by
  have ht0 : 0 < t := by dsimp [headShare] at ht; linarith
  have hb := ZetaRieszCoreExtensions.prime_log_mass_le (smallPrimes t)
    (show 0 ≤ 2*headShare*t by dsimp [headShare]; positivity) (by
      intro p hp
      have hh := logPrimes_bounds hp
      exact ⟨hh.1,by simpa only [zero_add] using hh.2.2⟩)
  have he : (∑ r ∈ smallPrimes t, Real.log r*Real.exp (-Real.log r)) =
      ∑ r ∈ smallPrimes t, Real.log r*(r : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast (logPrimes_bounds hr).1.pos)]
  rw [he] at hb
  have hl : Real.log 4 ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1; norm_num
  have hd : 0 ≤ headShare*t := by dsimp [headShare]; positivity
  nlinarith [mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+2*headShare*t by nlinarith [hd])]

private theorem amplitude_le_window {n : ℕ} (hn : n ≠ 0) {t h : ℝ}
    (ht : t ≤ Real.log n) (hth : Real.log n ≤ t+h) (N : ℕ) :
    amplitude N n ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    rw [show (n : ℝ)⁻¹ = Real.exp (-Real.log n) by rw [Real.exp_neg,Real.exp_log hnR],
      ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial ≤
      Real.exp (-t/2)*(t+h)^N/N.factorial := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
      (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hth N) (by positivity) (Real.exp_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr hnR.le)
  unfold amplitude
  rw [he]
  convert hm using 1 <;> first | rfl | ring


private theorem atom_norm_le {S A : Finset ℕ} {L t h : ℝ} (ht : 1 ≤ t)
    (hhu : h ≤ 1/100000) (hL : (69/100 : ℝ)*t ≤ L) (hLu : L ≤ (7/10 : ℝ)*t)
    {N n r : ℕ} (hn : n ∈ population S L t h) (hr : r ∈ n.primeFactors) (y : ℝ) :
    ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*(Real.exp (-t/2)*(t+h)^N/N.factorial)*Real.log r*(n : ℝ)⁻¹ := by
  obtain ⟨_,hs,hc,htn,hnt,hpos,_,_⟩ := Finset.mem_filter.mp hn
  have hL0 : 0 < L := by linarith
  have hb := ZetaRieszFivePositiveHead.positiveAllowance_le_marked_log hc hr hL0
  rw [ZetaRieszFivePrimeReserve.positiveAllowance_eq hc hL0 (by linarith) (by linarith),
    max_eq_right hpos.le] at hb
  have hrati : Real.log n/L ≤ 2 := (div_le_iff₀ hL0).mpr (by linarith)
  have hc' : ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ 2*Real.log r := by
    have he := Complex.re_add_im (SquarefreeVaughanLogSource.coefficient L n)
    rw [ZetaRieszCosineCarrier.coefficient_im_eq_zero,Complex.ofReal_zero,zero_mul,add_zero] at he
    rw [← he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpos.le]
    exact hb.trans (mul_le_mul_of_nonneg_right hrati (Real.log_natCast_nonneg r))
  have hker : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ = amplitude N n := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight,amplitude]
    ring
  rw [norm_mul,hker]
  have he := mul_le_mul ((ZetaRieszJointCountFloor.norm_residual_le A L N n).trans hc')
    (amplitude_le_window hs.ne_zero htn.le hnt N)
    (by unfold amplitude; positivity) (by positivity : 0 ≤ 2*Real.log r)
  convert he using 1 <;> first | rfl | ring

/-- The complete literal least-prime boundary costs at most `3/40000`
of the original short-cell radial scale. No order, phase, or support mask
is removed from the selected atom. -/
theorem eventually_norm_mass_sharp {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L y : ℝ),
      (N : ℝ) ≤ t → (69/100 : ℝ)*t ≤ L → L ≤ (7/10 : ℝ)*t →
      (∑ n ∈ population S L t h, ‖residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (3/40000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*h := by
  filter_upwards [eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 9/100) (by norm_num : (0 : ℝ) < 19/50),
    ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu
      (by norm_num : (0 : ℝ) < 1/2),eventually_ge_atTop (100000000 : ℕ)]
    with N hmacro hlast hN S A t L y hNt hL hLu
  have hNR : (100000000 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let g := fun n => if n ∈ population S L t h then ‖f n‖ else 0
  have hg (n : ℕ) : 0 ≤ g n := by dsimp [g]; split_ifs <;> positivity
  have hmass : (∑ p ∈ largePrimes t, (p : ℝ)⁻¹) ≤ 5 := by
    have he := (hmacro ((9/100 : ℝ)*t) ((19/50 : ℝ)*t) (by linarith) (by linarith)).2
    change (∑ p ∈ largePrimes t, (p : ℝ)⁻¹) ≤ (5001/5000 : ℝ)*((19/50 : ℝ)*t)/((9/100 : ℝ)*t) at he
    have hr : (5001/5000 : ℝ)*((19/50 : ℝ)*t)/((9/100 : ℝ)*t) ≤ 5 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact he.trans hr
  have hsmall : (∑ r ∈ smallPrimes t, Real.log r*(r : ℝ)⁻¹) ≤ 10*headShare*t :=
    small_log_mass (by dsimp [headShare]; linarith)
  have hlast' (v : ℕ × (Fin 3 → ℕ)) :
      (∑ p ∈ lastPrimes t h v, (p : ℝ)⁻¹) ≤ 3*h/t := by
    unfold lastPrimes
    split_ifs with hv
    · have ha : (1/2 : ℝ)*N ≤ t-Real.log (cofactor v) := by linarith
      apply (hlast _ ha).2.trans
      apply (div_le_div_iff₀ (show 0 < t-Real.log (cofactor v) by linarith) ht0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hv hh.le]
    · simp only [Finset.sum_empty]
      positivity
  have hpoint (v : ℕ × (Fin 3 → ℕ)) (hv : v ∈ cofactors t)
      (p : ℕ) (hp : p ∈ lastPrimes t h v) :
      g (cofactor v*p) ≤ (2*V)*(Real.log v.1*(cofactor v : ℝ)⁻¹)*(p : ℝ)⁻¹ := by
    by_cases hn : cofactor v*p ∈ population S L t h
    · have hrp := (logPrimes_bounds (Finset.mem_product.mp hv).1).1
      have hn0 := (Finset.mem_filter.mp hn).2.1.ne_zero
      have hrd : v.1 ∣ cofactor v*p := by dsimp [cofactor]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      have hr := Nat.mem_primeFactors.mpr ⟨hrp,hrd,hn0⟩
      have he := atom_norm_le ht hhu hL hLu hn hr y (N := N) (A := A)
      dsimp only [g,f,V]
      rw [if_pos hn]
      simpa only [Nat.cast_mul,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm] using he
    · rw [show g (cofactor v*p) = 0 by simp [g,hn]]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hV)
        (mul_nonneg (Real.log_natCast_nonneg _) (by positivity))) (by positivity)
  have hcover : (∑ n ∈ population S L t h, ‖f n‖) ≤
      ∑ v ∈ cofactors t, ∑ p ∈ lastPrimes t h v, g (cofactor v*p) := by
    calc
      _ = ∑ n ∈ population S L t h, g n := Finset.sum_congr rfl (by intro n hn; simp [g,hn])
      _ ≤ ∑ n ∈ (representations t h).image (fun v => cofactor v.1*v.2), g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (population_covered S ht hhu hL hLu)
          (fun n _ _ => hg n)
      _ ≤ ∑ v ∈ representations t h, g (cofactor v.1*v.2) :=
        Finset.sum_image_le_of_nonneg (fun n _ => hg n)
      _ = _ := by
        rw [representations,Finset.sum_biUnion (by
          intro v _ w _ hvw
          apply Finset.disjoint_left.mpr
          intro x hx hy
          obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨q,_,he⟩ := Finset.mem_image.mp hy
          exact hvw (congrArg Prod.fst he).symm)]
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_image (by intro p _ q _ he; exact congrArg Prod.snd he)]
  have hrow (v : ℕ × (Fin 3 → ℕ)) (hv : v ∈ cofactors t) :
      (∑ p ∈ lastPrimes t h v, g (cofactor v*p)) ≤
      (2*V)*(Real.log v.1*(cofactor v : ℝ)⁻¹)*(3*h/t) := by
    have he := Finset.sum_le_sum (hpoint v hv)
    rw [← Finset.mul_sum] at he
    exact he.trans (mul_le_mul_of_nonneg_left (hlast' v) (by positivity))
  have hs := Finset.sum_le_sum hrow
  rw [← Finset.sum_mul,← Finset.mul_sum] at hs
  have he : (∑ v ∈ cofactors t, Real.log v.1*(cofactor v : ℝ)⁻¹) =
      (∑ r ∈ smallPrimes t, Real.log r*(r : ℝ)⁻¹)*
        (∑ p ∈ largePrimes t, (p : ℝ)⁻¹)^3 := by
    rw [cofactors,Finset.product_eq_sprod,Finset.sum_product]
    have hpoint (r : ℕ) (v : Fin 3 → ℕ) :
        Real.log r*(cofactor (r,v) : ℝ)⁻¹ =
          (Real.log r*(r : ℝ)⁻¹)*(∏ i : Fin 3, (v i : ℝ)⁻¹) := by
      simp only [cofactor,Nat.cast_mul,Fin.prod_univ_three,Nat.cast_mul,mul_inv_rev]
      ring
    simp_rw [hpoint,← Finset.mul_sum]
    rw [← Finset.sum_mul]
    congr 1
    exact (Finset.sum_pow' (largePrimes t) (fun p : ℕ => (p : ℝ)⁻¹) 3).symm

  rw [he] at hs
  have hw := mul_le_mul hsmall
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hmass 3)
    (by positivity) (by dsimp [headShare]; positivity : 0 ≤ 10*headShare*t)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw
    (show 0 ≤ 2*V by positivity)) (show 0 ≤ 3*h/t by positivity)
  have hc : 2*V*(10*headShare*t*5^3)*(3*h/t) ≤ (3/40000 : ℝ)*V*h := by
    have he : 2*V*(10*headShare*t*5^3)*(3*h/t) = (7500/100000000 : ℝ)*V*h := by
      dsimp [headShare]
      field_simp
      ring
    rw [he]
    nlinarith only [mul_nonneg hV hh.le]
  exact hcover.trans (hs.trans (hb.trans hc))

/-- The preceding local allowance remains available as a consequence
of the stronger literal prime count. -/
theorem eventually_norm_mass {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L y : ℝ),
      (N : ℝ) ≤ t → (69/100 : ℝ)*t ≤ L → L ≤ (7/10 : ℝ)*t →
      (∑ n ∈ population S L t h, ‖residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*h := by
  filter_upwards [eventually_norm_mass_sharp hh hhu] with N hmass S A t L y ht hL hLu
  have ht0 : 0 ≤ t := (Nat.cast_nonneg N).trans ht
  exact (hmass S A t L y ht hL hLu).trans (by
    nlinarith only [mul_nonneg (show 0 ≤ Real.exp (-t/2)*(t+h)^N/N.factorial by positivity) hh.le])

open ZetaRieszCapacityPhaseBudget

/-- The complete original phase period of boundary labels. -/
def periodPopulation (S : Finset ℕ) (L v y : ℝ) (m : ℕ) : Finset ℕ :=
  (Finset.range (8*m)).biUnion (fun i => population S L
    (v+periodAngle m i/|y|) (Real.pi/(4*m*|y|)))

/-- The complete period subset retains all its original labels. -/
theorem periodPopulation_subset (S : Finset ℕ) (L v y : ℝ) (m : ℕ) :
    periodPopulation S L v y m ⊆ S := by
  intro n hn
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hn
  exact (Finset.mem_filter.mp hi).1


/-- The entire half-open period is covered, including every phase-cell boundary. -/
theorem mem_periodPopulation {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < |y|)
    (S : Finset ℕ) (L v : ℝ) (n : ℕ) :
    n ∈ periodPopulation S L v y m ↔
      n ∈ S ∧ Squarefree n ∧ n.primeFactors.card = 5 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      0 < (SquarefreeVaughanLogSource.coefficient L n).re ∧
      Real.log (largestPrime n) < (119/200 : ℝ)*Real.log n ∧
      ∃ r ∈ n.primeFactors, Real.log r ≤ headShare*Real.log n := by
  constructor
  · intro hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hn,hs,hc,hlo,hhi,hpos,howner,hsmall⟩ := Finset.mem_filter.mp hn
    have ht := period_cell_bounds hm (Finset.mem_range.mp hi) v hy
    exact ⟨hn,hs,hc,ht.1.trans_lt hlo,hhi.trans ht.2,hpos,howner,hsmall⟩
  · rintro ⟨hn,hs,hc,hlo,hhi,hpos,howner,hsmall⟩
    obtain ⟨i,hi,hil,hih⟩ := period_cells_cover hm hy hlo hhi
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hn,hs,hc,hil,hih,hpos,howner,hsmall⟩⟩

/-- After payment every remaining positive-five label in this period has
all prime shares strictly above the fixed head cutoff. -/
theorem remaining_prime_log_gt {S : Finset ℕ} {L v y : ℝ} {m n : ℕ}
    (hm : 0 < m) (hy : 0 < |y|) (hn : n ∈ S\periodPopulation S L v y m)
    (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hlo : v-Real.pi/|y| < Real.log n) (hhi : Real.log n ≤ v+Real.pi/|y|)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
    (howner : Real.log (largestPrime n) < (119/200 : ℝ)*Real.log n) :
    ∀ p ∈ n.primeFactors, headShare*Real.log n < Real.log p := by
  intro p hp
  by_contra h
  exact (Finset.mem_sdiff.mp hn).2 ((mem_periodPopulation hm hy S L v n).mpr
    ⟨(Finset.mem_sdiff.mp hn).1,hs,hc,hlo,hhi,hpos,howner,p,hp,le_of_not_gt h⟩)

/-- The positive-five small-prime boundary over the entire period costs at most
`m V₀ h / 1600`, with the exact radial kernel and original phase. -/
theorem eventually_period_norm_mass_sharp {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 54 ≤ |y|)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L v V₀ : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*(v+periodAngle m i/|y|) ≤ L ∧
        L ≤ (7/10 : ℝ)*(v+periodAngle m i/|y|)) →
      0 ≤ V₀ → Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ →
      (∑ n ∈ periodPopulation S L v y m,
        ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (m : ℝ)/1600*V₀*(Real.pi/(4*m*|y|)) := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_norm_mass_sharp hh hhu,eventually_ge_atTop (1 : ℕ)]
    with N hmass hN S A L v V₀ hlo hhi hL hV₀ hVr
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+periodAngle m i/|y|
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨V₁,hV₁,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable
    (by omega : 0 < N) hy hlo hhi
  have hVbase : V₁ ≤ Real.exp (-v/2)*v^N/N.factorial := by
    simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).1
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (∑ n ∈ population S L (T i) h,
        ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (303/4000000 : ℝ)*V₀*h := by
    have hg := period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have hNt : (N : ℝ) ≤ T i := by dsimp [T]; nlinarith [hg.1]
    have ht0 : 0 < T i := by nlinarith
    have hu := (upper_radial ht0 hNt hh.le hhu).trans
      (mul_le_mul_of_nonneg_left
        (hV (periodAngle m i) (periodAngle_bounds hm (Finset.mem_range.mp hi).le)).2
        (by norm_num : (0 : ℝ) ≤ 1001/1000))
    have hrad : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤ (101/100 : ℝ)*V₀ := by
      dsimp only [T,h] at hu ⊢
      nlinarith only [hu,hVbase,hVr,hV₀]
    have hb := hmass S A (T i) L y hNt (hL i hi).1 (hL i hi).2
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℝ) ≤ 3/40000)) hh.le
    exact hb.trans (by nlinarith only [hc])
  have hdisj : (↑(Finset.range (8*m)) : Set ℕ).PairwiseDisjoint
      (fun i => population S L (T i) h) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro n hni hnj
    obtain ⟨_,_,_,hli,hui,_,_,_⟩ := Finset.mem_filter.mp hni
    obtain ⟨_,_,_,hlj,huj,_,_,_⟩ := Finset.mem_filter.mp hnj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have he := period_cells_separated hm hij v hy0
      change T i+h ≤ T j at he
      linarith
    · have he := period_cells_separated hm hji v hy0
      change T j+h ≤ T i at he
      linarith
  have hs := Finset.sum_le_sum hrow
  rw [periodPopulation,Finset.sum_biUnion hdisj]
  apply hs.trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [mul_nonneg (Nat.cast_nonneg m) (mul_nonneg hV₀ hh.le)]

/-- Compatibility with the earlier period debit; no population changes. -/
theorem eventually_period_norm_mass {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 54 ≤ |y|)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L v V₀ : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*(v+periodAngle m i/|y|) ≤ L ∧
        L ≤ (7/10 : ℝ)*(v+periodAngle m i/|y|)) →
      0 ≤ V₀ → Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ →
      (∑ n ∈ periodPopulation S L v y m,
        ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (m : ℝ)/1200*V₀*(Real.pi/(4*m*|y|)) := by
  filter_upwards [eventually_period_norm_mass_sharp hm hy hhu] with N hmass S A L v V₀ hlo hhi hL hV hVr
  exact (hmass S A L v V₀ hlo hhi hL hV hVr).trans (by
    have hp : 0 ≤ (m : ℝ)*V₀*(Real.pi/(4*m*|y|)) := by positivity
    nlinarith only [hp])


end
end RiemannGaussian.ZetaRieszPositiveFiveBoundary
