/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerCutoff
import RiemannGaussian.ArithmeticOperatorSelbergSourceAudit
import RiemannGaussian.ZetaPrimePairDiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Complete CRT periods of distinct prime-power Kummer columns

Retain the literal balanced carry at each positive prime-power order.
Complete common-period joining factors EXACTLY for arbitrary functions,
not only carries. Normalizing the positive single-column means restores
the complete distinct-prime pair coefficient, including every proper power.
Its actual double-zero source and pole centering survive, but this complete
period supplies no additional signed arithmetic relation.

This is a rejection of complete-period/free-matrix bookkeeping ONLY.
No native cutoff boundary is norm-paid or silently completed. A signed
literal incomplete-period constraint using actual Gamma data remains open.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerCrtAudit
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical

/-- Literal balanced Kummer carry on one complete denominator period. -/
def carryResidue (d : ℕ) (x : ZMod d) : ℝ :=
  SuzukiIntegerCarry.carry x.val d

/-- Its exact finite mean; this is not a prime-density approximation. -/
def carryMean (d : ℕ) [NeZero d] : ℝ :=
  (∑ x : ZMod d,carryResidue d x)/(d : ℝ)

/-- Complete common-period statistic BEFORE taking norms, with both
literal residue coordinates and the actual endpoint at every class. -/
def periodMean {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (f : ZMod d → ℂ) (g : ZMod e → ℂ) : ℂ :=
  (∑ x : ZMod (d*e),f ((ZMod.chineseRemainder hc x).1)*
    g ((ZMod.chineseRemainder hc x).2))/((d*e : ℕ) : ℂ)

/-- Nonseparable residue/phase code on the SAME common integer period.
No decomposition of the joint code into independent rows is assumed. -/
def correlatedPeriod {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (code : ZMod d → ZMod e → ℂ) : ℂ :=
  (∑ x : ZMod (d*e),code ((ZMod.chineseRemainder hc x).1)
    ((ZMod.chineseRemainder hc x).2))/((d*e : ℕ) : ℂ)

/-- Full CRT joining for arbitrary correlated codes is only Cartesian
averaging. This finite identity survives arbitrary arithmetic weights. -/
theorem correlatedPeriod_eq_cartesian {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (code : ZMod d → ZMod e → ℂ) :
    correlatedPeriod hc code=
      (∑ x : ZMod d,∑ y : ZMod e,code x y)/((d*e : ℕ) : ℂ) := by
  unfold correlatedPeriod
  rw [Fintype.sum_equiv (ZMod.chineseRemainder hc).toEquiv
    (fun x => code ((ZMod.chineseRemainder hc x).1) ((ZMod.chineseRemainder hc x).2))
    (fun x : ZMod d×ZMod e => code x.1 x.2) (fun _ => rfl),Fintype.sum_prod_type]

/-- Even with the integer period unaltered, free correlated residue
codes realize ANY scalar. A bounded scalar uses the same bounded code. -/
theorem correlatedPeriod_constant {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (c : ℂ) : correlatedPeriod hc (fun _ _ => c)=c := by
  rw [correlatedPeriod_eq_cartesian]
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have hdn : (d : ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hen : (e : ℂ)≠0 := by exact_mod_cast NeZero.ne e
  push_cast
  field_simp [hdn,hen]

/-- CRT joining is exactly a free two-column product. No primality,
phase factorization beyond the named columns, or density premise enters. -/
theorem periodMean_eq_product {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (f : ZMod d → ℂ) (g : ZMod e → ℂ) :
    periodMean hc f g=((∑ x : ZMod d,f x)/(d : ℂ))*
      ((∑ x : ZMod e,g x)/(e : ℂ)) := by
  unfold periodMean
  rw [Fintype.sum_equiv (ZMod.chineseRemainder hc).toEquiv
    (fun x => f ((ZMod.chineseRemainder hc x).1)*g ((ZMod.chineseRemainder hc x).2))
    (fun x : ZMod d×ZMod e => f x.1*g x.2) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]
  push_cast
  ring

/-- Every order is an ACTUAL binary Kummer carry. -/
theorem carryResidue_eq_indicator {d : ℕ} [NeZero d] (x : ZMod d) :
    carryResidue d x=if d≤2*x.val then 1 else 0 := by
  have hx := ZMod.val_lt x
  have hd := Nat.pos_of_ne_zero (NeZero.ne d)
  unfold carryResidue SuzukiIntegerCarry.carry
  rw [Nat.div_eq_of_lt hx,mul_zero,Nat.sub_zero]
  by_cases h : d≤2*x.val
  · rw [ite_eq_left h]
    have hlo : 1≤2*x.val/d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hhi : 2*x.val/d<2 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
    exact_mod_cast (by omega : 2*x.val/d=1)
  · rw [ite_eq_right h,Nat.div_eq_of_lt (by omega)]
    norm_num

/-- The mean is nonzero at EVERY ordinary positive prime-power order,
including powers of two; no proper-power term is removed. -/
theorem carryMean_pos {d : ℕ} [NeZero d] (hd : 2≤d) : 0<carryMean d := by
  unfold carryMean
  apply div_pos _ (by exact_mod_cast (show 0<d by omega))
  apply Finset.sum_pos'
  · intro x _
    unfold carryResidue
    positivity
  · refine ⟨((d-1 : ℕ) : ZMod d),Finset.mem_univ _,?_⟩
    rw [carryResidue_eq_indicator,ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega : d-1<d),ite_eq_left (by omega)]
    norm_num

/-- Exact residue reduction of the actual integer carry. -/
theorem carry_eq_mod (N d : ℕ) (hd : 0<d) :
    SuzukiIntegerCarry.carry N d=SuzukiIntegerCarry.carry (N%d) d := by
  have he : 2*N=2*(N%d)+(2*(N/d))*d := by nlinarith [Nat.mod_add_div N d]
  unfold SuzukiIntegerCarry.carry
  rw [he,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt (Nat.mod_lt N hd)]
  omega

private theorem finEquiv_natCast {d : ℕ} [NeZero d] (N : Fin d) :
    ZMod.finEquiv d N=(N.val : ZMod d) := by
  apply (ZMod.val_injective d)
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt N.is_lt]
  cases d
  · exact (NeZero.ne 0 rfl).elim
  · rfl

private theorem crt_nat_fst {d e : ℕ}
    (hc : d.Coprime e) (N : ℕ) :
    (ZMod.chineseRemainder hc (N : ZMod (d*e))).1=(N : ZMod d) := by
  simp [ZMod.chineseRemainder]

private theorem crt_nat_snd {d e : ℕ}
    (hc : d.Coprime e) (N : ℕ) :
    (ZMod.chineseRemainder hc (N : ZMod (d*e))).2=(N : ZMod e) := by
  simp [ZMod.chineseRemainder]

/-- The CRT expression is the original integer-period carry product,
including EVERY literal cutoff endpoint in 0<=N<d*e. -/
theorem periodMean_carries_native {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) :
    periodMean hc (fun x => (carryResidue d x : ℂ))
      (fun x => (carryResidue e x : ℂ))=
    (∑ N : Fin (d*e),(SuzukiIntegerCarry.carry N.val d : ℂ)*
      (SuzukiIntegerCarry.carry N.val e : ℂ))/((d*e : ℕ) : ℂ) := by
  unfold periodMean
  congr 1
  refine (Fintype.sum_equiv (ZMod.finEquiv (d*e)).toEquiv _ _ ?_).symm
  intro N
  change (SuzukiIntegerCarry.carry N.val d : ℂ)*
    (SuzukiIntegerCarry.carry N.val e : ℂ)=
    (carryResidue d ((ZMod.chineseRemainder hc) (ZMod.finEquiv (d*e) N)).1 : ℂ)*
      (carryResidue e ((ZMod.chineseRemainder hc) (ZMod.finEquiv (d*e) N)).2 : ℂ)
  rw [finEquiv_natCast,crt_nat_fst,crt_nat_snd]
  dsimp only [carryResidue]
  rw [ZMod.val_natCast,ZMod.val_natCast,
    ←carry_eq_mod N.val d (Nat.pos_of_ne_zero (NeZero.ne d)),
    ←carry_eq_mod N.val e (Nat.pos_of_ne_zero (NeZero.ne e))]
  push_cast
  rfl

/-- Raw, unnormalized complete periods also retain only the product of
their exact one-column means. No code is being approximated here. -/
theorem periodMean_carries_eq_means {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) :
    periodMean hc (fun x => (carryResidue d x : ℂ))
      (fun x => (carryResidue e x : ℂ))=(carryMean d : ℂ)*(carryMean e : ℂ) := by
  rw [periodMean_eq_product]
  simp only [carryMean,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast]

/-- The unchanged two carry profiles; only their exact finite means
are used to normalize. All prime-power orders are admissible. -/
theorem normalized_period_eq_one {d e : ℕ} [NeZero d] [NeZero e]
    (hd : 2≤d) (he : 2≤e) (hc : d.Coprime e) :
    periodMean hc (fun x => (carryResidue d x : ℂ)/carryMean d)
      (fun x => (carryResidue e x : ℂ)/carryMean e)=1 := by
  have hdm : (carryMean d : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (carryMean_pos hd).ne'
  have hem : (carryMean e : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (carryMean_pos he).ne'
  have hdn : (d : ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hen : (e : ℂ)≠0 := by exact_mod_cast NeZero.ne e
  have hds : (∑ x : ZMod d,(carryResidue d x : ℂ))=(d : ℂ)*(carryMean d : ℂ) := by
    rw [carryMean]
    push_cast
    field_simp [hdn]
  have hes : (∑ x : ZMod e,(carryResidue e x : ℂ))=(e : ℂ)*(carryMean e : ℂ) := by
    rw [carryMean]
    push_cast
    field_simp [hen]
  rw [periodMean_eq_product,←Finset.sum_div,←Finset.sum_div,hds,hes]
  field_simp [hdm,hem,hdn,hen]

/-- A total definition retaining the unit/zero exceptions explicitly.
For every coprime nonunit column pair the literal complete-period
normalized carry value is exactly one. -/
def normalizedPair (d e : ℕ) : ℂ :=
  if h : 2≤d ∧ 2≤e ∧ d.Coprime e then
    letI : NeZero d := ⟨by omega⟩
    letI : NeZero e := ⟨by omega⟩
    periodMean h.2.2 (fun x => (carryResidue d x : ℂ)/carryMean d)
      (fun x => (carryResidue e x : ℂ)/carryMean e)
  else 0

theorem normalizedPair_eq (d e : ℕ) :
    normalizedPair d e=if 2≤d ∧ 2≤e ∧ d.Coprime e then 1 else 0 := by
  unfold normalizedPair
  split_ifs with h
  · have : NeZero d := ⟨by omega⟩
    have : NeZero e := ⟨by omega⟩
    exact normalized_period_eq_one h.1 h.2.1 h.2.2
  · rfl

/-- All literal product fibers and prime-power coefficients; no complete
Euler product is inserted before this finite definition. -/
def pairCoefficient (n : ℕ) : ℂ :=
  ∑ t∈n.divisorsAntidiagonal,
    (ArithmeticFunction.vonMangoldt t.1 : ℂ)*
      (ArithmeticFunction.vonMangoldt t.2 : ℂ)*normalizedPair t.1 t.2

/-- Complete CRT joining holds for ANY arithmetic weights and ANY
correlated pair kernel. It supplies no extra prime-specific relation. -/
def codedPairs (P Q : Finset ℕ) (w v : ℕ → ℂ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ d∈P,∑ e∈Q,w d*v e*K d e*normalizedPair d e

theorem codedPairs_eq_free (P Q : Finset ℕ) (w v : ℕ → ℂ) (K : ℕ → ℕ → ℂ) :
    codedPairs P Q w v K=
      ∑ d∈P,∑ e∈Q,if 2≤d ∧ 2≤e ∧ d.Coprime e then w d*v e*K d e else 0 := by
  simp only [codedPairs,normalizedPair_eq,mul_ite,mul_one,mul_zero]

private theorem coprime_primePowers_iff {d e : ℕ} (hd : IsPrimePow d)
    (he : IsPrimePow e) : d.Coprime e ↔ ¬IsPrimePow (d*e) := by
  obtain ⟨p,r,hp,hr,rfl⟩ := (isPrimePow_nat_iff d).mp hd
  obtain ⟨q,t,hq,ht,rfl⟩ := (isPrimePow_nat_iff e).mp he
  constructor
  · intro hc hn
    obtain ⟨l,_,huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hn
    have hpl := huniq p ⟨hp,dvd_mul_of_dvd_left (dvd_pow_self p hr.ne') _⟩
    have hql := huniq q ⟨hq,dvd_mul_of_dvd_right (dvd_pow_self q ht.ne') _⟩
    have hpq : p=q := hpl.trans hql.symm
    rw [←hpq] at hc
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p,hp,dvd_pow_self p hr.ne',dvd_pow_self p ht.ne'⟩) hc
  · intro hn
    apply Nat.coprime_pow_primes r t hp hq
    intro hpq
    subst q
    exact hn ((isPrimePow_nat_iff _).mpr ⟨p,r+t,hp,by omega,by rw [pow_add]⟩)

private theorem two_le_of_mangoldt_ne_zero {d : ℕ}
    (hd : ArithmeticFunction.vonMangoldt d≠0) : 2≤d := by
  have hdp : IsPrimePow d := by
    by_contra hn
    exact hd (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn)
  obtain ⟨p,r,hp,hr,rfl⟩ := (isPrimePow_nat_iff d).mp hdp
  exact hp.two_le.trans (Nat.le_of_dvd (pow_pos hp.pos r) (dvd_pow_self p hr.ne'))

private theorem normalizedPair_mangoldt (d e : ℕ) :
    (ArithmeticFunction.vonMangoldt d : ℂ)*(ArithmeticFunction.vonMangoldt e : ℂ)*
      normalizedPair d e=
    if IsPrimePow (d*e) then 0 else
      (ArithmeticFunction.vonMangoldt d : ℂ)*(ArithmeticFunction.vonMangoldt e : ℂ) := by
  by_cases hd : ArithmeticFunction.vonMangoldt d=0
  · simp [hd]
  by_cases he : ArithmeticFunction.vonMangoldt e=0
  · simp [he]
  have hdp : IsPrimePow d := by
    by_contra hn
    exact hd (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn)
  have hep : IsPrimePow e := by
    by_contra hn
    exact he (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn)
  have hc := coprime_primePowers_iff hdp hep
  rw [normalizedPair_eq]
  by_cases hp : IsPrimePow (d*e)
  · have hnc : ¬d.Coprime e := by intro hh;exact hc.mp hh hp
    simp [hp,hnc]
  · simp [hp,hc.mpr hp,two_le_of_mangoldt_ne_zero hd,two_le_of_mangoldt_ne_zero he]

/-- The complete normalized carry/CRT candidate is EXACTLY the old
distinct-prime pair arithmetic, including every positive exponent. -/
theorem pairCoefficient_eq_distinct (n : ℕ) :
    pairCoefficient n=(zetaDistinctPrimePairCoefficient n : ℂ) := by
  unfold pairCoefficient
  simp_rw [normalizedPair_mangoldt]
  have ht (t : ℕ×ℕ) (ht : t∈n.divisorsAntidiagonal) : t.1*t.2=n :=
    (Nat.mem_divisorsAntidiagonal.mp ht).1
  rw [zetaDistinctPrimePairCoefficient]
  split_ifs with hn
  · simp only [Complex.ofReal_zero]
    exact Finset.sum_eq_zero (fun t h => by rw [ht t h,ite_eq_left hn])
  · rw [zetaPrimePairArithmetic,ArithmeticFunction.mul_apply]
    push_cast
    exact Finset.sum_congr rfl (fun t h => by rw [ht t h,ite_eq_right hn])

/-- Actual complete response after deleting only the same-base pairs,
whose series is independently analytic for real part above one half. -/
def response (s : ℂ) : ℂ :=
  (logDeriv riemannZeta s)^2-zetaPrimeDiagonalResponse s

/-- Genuine Euler identity of the literal complete CRT coefficient;
the entire complex Dirichlet phase and every proper power remain. -/
theorem response_euler {s : ℂ} (hs : 1<s.re) :
    LSeriesHasSum pairCoefficient s (response s) := by
  have hf : pairCoefficient=(fun n => (zetaPrimePairArithmetic n : ℂ))-
      (fun n => (zetaPrimeDiagonalCoefficient n : ℂ)) := by
    funext n
    simp only [Pi.sub_apply,pairCoefficient_eq_distinct]
    rw [zetaPrimePairCoefficient_split]
    push_cast
    ring
  rw [hf]
  exact (LSeriesHasSum_zetaPrimePairArithmetic hs).sub
    (LSeriesSummable_zetaPrimeDiagonal (by linarith : 1/2<s.re)).LSeriesHasSum

/-- Source preflight uses the ACTUAL zero divisor and multiplicity,
not a diagnostic inference for an unestimated nonlinear boundary. -/
theorem actual_zero_source (rho : NontrivialZetaZero) (hr : 1/2<rho.1.re) :
    Tendsto (fun s => (s-rho.1)^2*response s) (𝓝[≠] rho.1)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ)^2)) := by
  have hl := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).pow 2
  have hz : Tendsto (fun s : ℂ => (s-rho.1)^2) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1)
        (𝓝 (rho.1-rho.1))).pow 2
  have hd : Tendsto zetaPrimeDiagonalResponse (𝓝[≠] rho.1)
      (𝓝 (zetaPrimeDiagonalResponse rho.1)) :=
    (analyticAt_zetaPrimeDiagonalResponse hr).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds
  convert hl.sub (hz.mul hd) using 1
  · funext s
    dsimp [response]
    ring
  · simp [analyticZetaZeroMultiplicity]

/-- Pole centering preserves the full nonzero source for every analytic
multiplicity, including a simple zero. -/
theorem actual_centered_zero_source (rho : NontrivialZetaZero) (hr : 1/2<rho.1.re) :
    Tendsto (fun s => (s-rho.1)^2*((s-1)^2*response s)) (𝓝[≠] rho.1)
      (𝓝 ((rho.1-1)^2*(analyticZetaZeroMultiplicity rho : ℂ)^2)) := by
  have hc : Tendsto (fun s : ℂ => (s-1)^2) (𝓝[≠] rho.1) (𝓝 ((rho.1-1)^2)) :=
    ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).pow 2
  convert hc.mul (actual_zero_source rho hr) using 1
  funext s
  ring

theorem centered_zero_source_ne_zero (rho : NontrivialZetaZero) :
    (rho.1-1)^2*(analyticZetaZeroMultiplicity rho : ℂ)^2≠0 := by
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr rho.2.2.2))
    (pow_ne_zero 2 (by exact_mod_cast
      Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho)))

/-- The density pole is removed as a local analytic germ, not just
its leading residue. All regular cross terms are retained. -/
theorem centered_response_analytic_at_pole :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E 1 ∧
      (fun s => (s-1)^2*response s)=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  let H : ℂ → ℂ := logDeriv riemannZeta₁
  have hH : AnalyticAt ℂ H 1 :=
    ((differentiable_riemannZeta₁).analyticAt 1).deriv.div
      ((differentiable_riemannZeta₁).analyticAt 1) (by simp)
  have hD := analyticAt_zetaPrimeDiagonalResponse (by norm_num : 1/2<(1 : ℂ).re)
  refine ⟨fun s => (-1+(s-1)*H s)^2-(s-1)^2*zetaPrimeDiagonalResponse s,
    ((analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hH)).pow 2).sub
      (((analyticAt_id.sub analyticAt_const).pow 2).mul hD),?_⟩
  have hne : ∀ᶠ s in 𝓝 (1 : ℂ),riemannZeta₁ s≠0 :=
    (differentiable_riemannZeta₁ 1).continuousAt.eventually_ne (by simp)
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with s hs (hs1 : s≠1)
  have hz : riemannZeta s≠0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hs
  have he := neg_logDeriv_riemannZeta_eq_pole_sub hs1 hz
  dsimp [H,response] at *
  have hlog : logDeriv riemannZeta s=-(s-1)⁻¹+logDeriv riemannZeta₁ s := by
    linear_combination -he
  rw [hlog]
  field_simp [sub_ne_zero.mpr hs1]

/-- No unrestricted free-weight allowance follows from complete CRT
joining, even at one literal coprime nonunit pair. -/
theorem no_free_weight_allowance (B : ℝ) :
    ¬∀ w v : ℕ → ℂ, ‖codedPairs {2} {3} w v (fun _ _ => 1)‖≤B := by
  intro hh
  have h := hh (fun _ => ((|B|+1 : ℝ) : ℂ)) (fun _ => 1)
  norm_num [codedPairs,normalizedPair_eq] at h
  have h' : ‖((|B|+1 : ℝ) : ℂ)‖≤B := by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using h
  rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)] at h'
  linarith [le_abs_self B]

end
end RiemannGaussian.ArithmeticOperatorKummerCrtAudit
