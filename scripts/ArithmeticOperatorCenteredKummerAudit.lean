/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerCutoff
import RiemannGaussian.ZetaPrimePairDiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Exact constant column centering of complete Kummer CRT periods

Every native endpoint, positive prime-power order, and original complex
pair phase remains. Subtracting the exact finite column mean before the
complete coprime product annihilates the WHOLE distinct-prime coefficient,
including its genuine zero source. A fixed scalar partial subtraction
rescales both source and pole by exactly the same constant.

This freezes only constant column-mean subtraction in complete periods.
No incomplete cutoff boundary is completed or paid. Analytic s-dependent
pole centering, nonseparable residue codes, and prescribed native signed
packets are separate. Free/smooth/generalized controls are not granted
actual Gamma, binomial, or prime compatibility by the generic identity.
-/

namespace RiemannGaussian.ArithmeticOperatorCenteredKummerAudit
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical

/-- Exact one-column finite average. -/
def mean {d : ℕ} [NeZero d] (f : ZMod d → ℂ) : ℂ :=
  (∑ x : ZMod d, f x)/(d : ℂ)

/-- Joined complete native common-period average. -/
def periodMean {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (f : ZMod d → ℂ) (g : ZMod e → ℂ) : ℂ :=
  (∑ x : ZMod (d*e), f ((ZMod.chineseRemainder hc x).1)*
    g ((ZMod.chineseRemainder hc x).2))/((d*e : ℕ) : ℂ)

/-- Exact native integer CRT joining, with no arithmetic hypothesis on f,g. -/
theorem periodMean_eq_product {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (f : ZMod d → ℂ) (g : ZMod e → ℂ) :
    periodMean hc f g=mean f*mean g := by
  unfold periodMean mean
  rw [Fintype.sum_equiv (ZMod.chineseRemainder hc).toEquiv
    (fun x => f ((ZMod.chineseRemainder hc x).1)*g ((ZMod.chineseRemainder hc x).2))
    (fun x : ZMod d×ZMod e => f x.1*g x.2) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]
  push_cast
  ring

/-- Fixed scalar subtraction from a column's EXACT finite mean. -/
def subtractMean {d : ℕ} [NeZero d] (eta : ℂ) (f : ZMod d → ℂ)
    (x : ZMod d) : ℂ := f x-eta*mean f

theorem mean_subtractMean {d : ℕ} [NeZero d] (eta : ℂ) (f : ZMod d → ℂ) :
    mean (subtractMean eta f)=(1-eta)*mean f := by
  have hd : (d : ℂ)≠0 := by exact_mod_cast NeZero.ne d
  simp only [mean,subtractMean,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,ZMod.card,nsmul_eq_mul]
  field_simp [hd]

/-- A FREE-array identity. Constant mean centering does not exploit primes. -/
theorem periodMean_subtractMean {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (eta xi : ℂ) (f : ZMod d → ℂ) (g : ZMod e → ℂ) :
    periodMean hc (subtractMean eta f) (subtractMean xi g)=
      ((1-eta)*(1-xi))*(mean f*mean g) := by
  rw [periodMean_eq_product,mean_subtractMean,mean_subtractMean]
  ring

theorem periodMean_centered_eq_zero {d e : ℕ} [NeZero d] [NeZero e]
    (hc : d.Coprime e) (f : ZMod d → ℂ) (g : ZMod e → ℂ) :
    periodMean hc (subtractMean 1 f) (subtractMean 1 g)=0 := by
  simp [periodMean_subtractMean]

/-- Literal binary Kummer carry at the unchanged residue endpoint. -/
def carryResidue (d : ℕ) (x : ZMod d) : ℝ := SuzukiIntegerCarry.carry x.val d

/-- Exact real carry mean; no prime-density premise. -/
def carryMean (d : ℕ) [NeZero d] : ℝ :=
  (∑ x : ZMod d,carryResidue d x)/(d : ℝ)

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

/-- Carry column divided by its exact nonzero mean. -/
def normalizedCarry (d : ℕ) [NeZero d] (x : ZMod d) : ℂ :=
  (carryResidue d x : ℂ)/(carryMean d : ℂ)

theorem mean_normalizedCarry {d : ℕ} [NeZero d] (hd : 2≤d) :
    mean (normalizedCarry d)=1 := by
  have hdn : (d : ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hdm : (carryMean d : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (carryMean_pos hd).ne'
  have hds : (∑ x : ZMod d,(carryResidue d x : ℂ))=(d : ℂ)*(carryMean d : ℂ) := by
    rw [carryMean]
    push_cast
    field_simp [hdn]
  unfold mean
  simp only [normalizedCarry]
  rw [←Finset.sum_div,hds]
  field_simp [hdn,hdm]

/-- Constant subtraction from the normalized actual carry column. -/
def centeredCarry (d : ℕ) [NeZero d] (eta : ℂ) (x : ZMod d) : ℂ :=
  normalizedCarry d x-eta

theorem mean_centeredCarry {d : ℕ} [NeZero d] (hd : 2≤d) (eta : ℂ) :
    mean (centeredCarry d eta)=1-eta := by
  have he : centeredCarry d eta=subtractMean eta (normalizedCarry d) := by
    funext x
    simp [centeredCarry,subtractMean,mean_normalizedCarry hd]
  rw [he,mean_subtractMean,mean_normalizedCarry hd,mul_one]

/-- Every positive prime-power order is retained; primality is unnecessary. -/
theorem periodMean_centeredCarry {d e : ℕ} [NeZero d] [NeZero e]
    (hd : 2≤d) (he : 2≤e) (hc : d.Coprime e) (eta xi : ℂ) :
    periodMean hc (centeredCarry d eta) (centeredCarry e xi)=(1-eta)*(1-xi) := by
  rw [periodMean_eq_product,mean_centeredCarry hd,mean_centeredCarry he]

theorem carry_eq_mod (N d : ℕ) (hd : 0<d) :
    SuzukiIntegerCarry.carry N d=SuzukiIntegerCarry.carry (N%d) d := by
  have he : 2*N=2*(N%d)+(2*(N/d))*d := by nlinarith [Nat.mod_add_div N d]
  unfold SuzukiIntegerCarry.carry
  rw [he,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt (Nat.mod_lt N hd)]
  omega

private theorem finEquiv_natCast {d : ℕ} [NeZero d] (N : Fin d) :
    ZMod.finEquiv d N=(N.val : ZMod d) := by
  apply ZMod.val_injective d
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt N.is_lt]
  cases d
  · exact (NeZero.ne 0 rfl).elim
  · rfl

/-- Literal 0<=N<d*e endpoint identity, before any completion or norm. -/
theorem periodMean_centeredCarry_native {d e : ℕ} [NeZero d] [NeZero e]
    (hd : 2≤d) (he : 2≤e) (hc : d.Coprime e) (eta xi : ℂ) :
    (∑ N : Fin (d*e),
      ((SuzukiIntegerCarry.carry N.val d : ℂ)/carryMean d-eta)*
      ((SuzukiIntegerCarry.carry N.val e : ℂ)/carryMean e-xi))/((d*e : ℕ) : ℂ)=
      (1-eta)*(1-xi) := by
  rw [←periodMean_centeredCarry hd he hc eta xi]
  unfold periodMean
  congr 1
  refine Fintype.sum_equiv (ZMod.finEquiv (d*e)).toEquiv
    (fun N : Fin (d*e) =>
      ((SuzukiIntegerCarry.carry N.val d : ℂ)/carryMean d-eta)*
      ((SuzukiIntegerCarry.carry N.val e : ℂ)/carryMean e-xi))
    (fun x : ZMod (d*e) =>
      centeredCarry d eta ((ZMod.chineseRemainder hc x).1)*
      centeredCarry e xi ((ZMod.chineseRemainder hc x).2)) ?_
  intro N
  change ((SuzukiIntegerCarry.carry N.val d : ℂ)/carryMean d-eta)*
    ((SuzukiIntegerCarry.carry N.val e : ℂ)/carryMean e-xi)=
    centeredCarry d eta ((ZMod.chineseRemainder hc (ZMod.finEquiv (d*e) N)).1)*
      centeredCarry e xi ((ZMod.chineseRemainder hc (ZMod.finEquiv (d*e) N)).2)
  rw [finEquiv_natCast]
  have hf : (ZMod.chineseRemainder hc (N.val : ZMod (d*e))).1=(N.val : ZMod d) := by
    simp [ZMod.chineseRemainder]
  have hs : (ZMod.chineseRemainder hc (N.val : ZMod (d*e))).2=(N.val : ZMod e) := by
    simp [ZMod.chineseRemainder]
  rw [hf,hs]
  dsimp only [centeredCarry,normalizedCarry,carryResidue]
  rw [ZMod.val_natCast,ZMod.val_natCast]
  rw [←carry_eq_mod N.val d (Nat.pos_of_ne_zero (NeZero.ne d)),
    ←carry_eq_mod N.val e (Nat.pos_of_ne_zero (NeZero.ne e))]
  push_cast
  rfl

/-- Constant column subtraction, with unit/zero exceptions still explicit. -/
def subtractedPair (eta xi : ℂ) (d e : ℕ) : ℂ :=
  if h : 2≤d ∧ 2≤e ∧ d.Coprime e then
    letI : NeZero d := ⟨by omega⟩
    letI : NeZero e := ⟨by omega⟩
    periodMean h.2.2 (centeredCarry d eta) (centeredCarry e xi)
  else 0

theorem subtractedPair_eq (eta xi : ℂ) (d e : ℕ) :
    subtractedPair eta xi d e=
      if 2≤d ∧ 2≤e ∧ d.Coprime e then (1-eta)*(1-xi) else 0 := by
  unfold subtractedPair
  split_ifs with h
  · have : NeZero d := ⟨by omega⟩
    have : NeZero e := ⟨by omega⟩
    exact periodMean_centeredCarry h.1 h.2.1 h.2.2 eta xi
  · rfl

theorem subtractedPair_centered (d e : ℕ) : subtractedPair 1 1 d e=0 := by
  simp [subtractedPair_eq]

/-- Arbitrary correlated arithmetic weights/phases are kept outside
the unchanged complete residue period. The centered coefficient is zero. -/
theorem centered_codedPairs (P Q : Finset ℕ) (w v : ℕ → ℂ)
    (K : ℕ → ℕ → ℂ) :
    (∑ d∈P,∑ e∈Q,w d*v e*K d e*subtractedPair 1 1 d e)=0 := by
  simp [subtractedPair_centered]

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

private theorem subtractedPair_mangoldt (eta xi : ℂ) (d e : ℕ) :
    (ArithmeticFunction.vonMangoldt d : ℂ)*(ArithmeticFunction.vonMangoldt e : ℂ)*
      subtractedPair eta xi d e=
    ((1-eta)*(1-xi))*(if IsPrimePow (d*e) then 0 else
      (ArithmeticFunction.vonMangoldt d : ℂ)*(ArithmeticFunction.vonMangoldt e : ℂ)) := by
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
  rw [subtractedPair_eq]
  by_cases hp : IsPrimePow (d*e)
  · have hnc : ¬d.Coprime e := by intro hh;exact hc.mp hh hp
    simp [hp,hnc]
  · rw [ite_eq_left ⟨two_le_of_mangoldt_ne_zero hd,two_le_of_mangoldt_ne_zero he,
      hc.mpr hp⟩,ite_eq_right hp]
    ring

/-- Full literal divisor product, with every positive prime-power order. -/
def pairCoefficient (eta xi : ℂ) (n : ℕ) : ℂ :=
  ∑ t∈n.divisorsAntidiagonal,
    (ArithmeticFunction.vonMangoldt t.1 : ℂ)*
      (ArithmeticFunction.vonMangoldt t.2 : ℂ)*subtractedPair eta xi t.1 t.2

theorem pairCoefficient_eq_distinct (eta xi : ℂ) (n : ℕ) :
    pairCoefficient eta xi n=((1-eta)*(1-xi))*(zetaDistinctPrimePairCoefficient n : ℂ) := by
  unfold pairCoefficient
  simp_rw [subtractedPair_mangoldt]
  rw [←Finset.mul_sum]
  congr 1
  have ht (t : ℕ×ℕ) (ht : t∈n.divisorsAntidiagonal) : t.1*t.2=n :=
    (Nat.mem_divisorsAntidiagonal.mp ht).1
  rw [zetaDistinctPrimePairCoefficient]
  split_ifs with hn
  · simp only [Complex.ofReal_zero]
    exact Finset.sum_eq_zero (fun t h => by rw [ht t h,ite_eq_left hn])
  · rw [zetaPrimePairArithmetic,ArithmeticFunction.mul_apply]
    push_cast
    exact Finset.sum_congr rfl (fun t h => by rw [ht t h,ite_eq_right hn])

theorem pairCoefficient_centered (n : ℕ) : pairCoefficient 1 1 n=0 := by
  simp [pairCoefficient_eq_distinct]

/-- EXACT arbitrary physical mask/factorial/phase retention, not a
source inference from independently completed prime legs. -/
theorem pairCoefficient_weighted (eta xi : ℂ) (P : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n∈P,pairCoefficient eta xi n*w n)=
      ((1-eta)*(1-xi))*(∑ n∈P,(zetaDistinctPrimePairCoefficient n : ℂ)*w n) := by
  simp only [pairCoefficient_eq_distinct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Actual complete distinct-prime-pair Euler response, including proper powers. -/
def originalResponse (s : ℂ) : ℂ :=
  (logDeriv riemannZeta s)^2-zetaPrimeDiagonalResponse s

/-- Actual response after constant mean subtraction on each complete column. -/
def subtractedResponse (eta xi : ℂ) (s : ℂ) : ℂ :=
  ((1-eta)*(1-xi))*originalResponse s

/-- Genuine Euler equality of the native coefficient, with full
Dirichlet phase; no density approximation or power-mode substitution. -/
theorem response_euler (eta xi : ℂ) {s : ℂ} (hs : 1<s.re) :
    LSeriesHasSum (pairCoefficient eta xi) s (subtractedResponse eta xi s) := by
  have hf : (fun n => (zetaDistinctPrimePairCoefficient n : ℂ))=
      (fun n => (zetaPrimePairArithmetic n : ℂ))-
      (fun n => (zetaPrimeDiagonalCoefficient n : ℂ)) := by
    funext n
    simp only [Pi.sub_apply]
    rw [zetaPrimePairCoefficient_split]
    push_cast
    ring
  have h := (LSeriesHasSum_zetaPrimePairArithmetic hs).sub
    (LSeriesSummable_zetaPrimeDiagonal (by linarith : 1/2<s.re)).LSeriesHasSum
  rw [←hf] at h
  have hc := LSeriesHasSum.smul ((1-eta)*(1-xi)) h
  convert hc using 1
  · funext n
    exact pairCoefficient_eq_distinct eta xi n
  · rfl

theorem actual_zero_source (rho : NontrivialZetaZero) (hr : 1/2<rho.1.re) :
    Tendsto (fun s => (s-rho.1)^2*originalResponse s) (𝓝[≠] rho.1)
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
    dsimp [originalResponse]
    ring
  · simp [analyticZetaZeroMultiplicity]

/-- Constant partial centering retains only the same constant multiple
of the ACTUAL zero source, for every analytic multiplicity. -/
theorem actual_subtracted_zero_source (eta xi : ℂ) (rho : NontrivialZetaZero)
    (hr : 1/2<rho.1.re) :
    Tendsto (fun s => (s-rho.1)^2*subtractedResponse eta xi s) (𝓝[≠] rho.1)
      (𝓝 (((1-eta)*(1-xi))*(analyticZetaZeroMultiplicity rho : ℂ)^2)) := by
  convert (actual_zero_source rho hr).const_mul ((1-eta)*(1-xi)) using 1
  funext s
  simp only [subtractedResponse]
  ring

theorem centered_response_eq_zero (s : ℂ) : subtractedResponse 1 1 s=0 := by
  simp [subtractedResponse]

/-- The difference between the old candidate and its centered version
retains the ENTIRE original genuine zero source. Centering does not pay it. -/
theorem actual_source_lost_by_centering (rho : NontrivialZetaZero)
    (hr : 1/2<rho.1.re) :
    Tendsto (fun s => (s-rho.1)^2*
      (originalResponse s-subtractedResponse 1 1 s)) (𝓝[≠] rho.1)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ)^2)) := by
  simpa only [centered_response_eq_zero,sub_zero] using actual_zero_source rho hr

theorem lost_source_ne_zero (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℂ)^2≠0 := by
  exact pow_ne_zero 2 (by exact_mod_cast
    (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho)))

/-- No source-o(1) bridge from the complete original candidate to the
column-centered candidate exists at an actual right-half zero. -/
theorem centering_difference_not_source_small (rho : NontrivialZetaZero)
    (hr : 1/2<rho.1.re) :
    ¬Tendsto (fun s => (s-rho.1)^2*
      (originalResponse s-subtractedResponse 1 1 s)) (𝓝[≠] rho.1) (𝓝 0) := by
  intro h
  exact lost_source_ne_zero rho (tendsto_nhds_unique (actual_source_lost_by_centering rho hr) h)

private theorem zeta_density_log_source :
    Tendsto (fun s : ℂ => (s-1)*(-logDeriv riemannZeta s))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have ha := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have hn : riemannZeta₁ (1 : ℂ)≠0 := by simp [riemannZeta₁_one]
  have hc : ContinuousAt (logDeriv riemannZeta₁) (1 : ℂ) :=
    ha.deriv.continuousAt.div ha.continuousAt hn
  have hz : Tendsto (fun s : ℂ => s-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-1)
      (𝓝[≠] (1 : ℂ)) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := tendsto_const_nhds (x := (1 : ℂ)) |>.sub
    (hz.mul (hc.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,sub_zero] at ht
  apply ht.congr'
  filter_upwards [ha.continuousAt.eventually_ne hn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs1
  have hzeta : riemannZeta s≠0 := by
    intro he
    apply hs
    rw [riemannZeta₁_eq_sub_one_mul hs1,he,mul_zero]
  rw [neg_logDeriv_riemannZeta_eq_pole_sub hs1 hzeta]
  field_simp [sub_ne_zero.mpr hs1]

/-- Actual ordinary density double-pole coefficient, with same-base
proper powers retained in the analytic diagonal term. -/
theorem actual_density_source :
    Tendsto (fun s : ℂ => (s-1)^2*originalResponse s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have hl := zeta_density_log_source.pow 2
  have hz : Tendsto (fun s : ℂ => (s-1)^2) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds : Tendsto (fun s : ℂ => s-1) (𝓝[≠] (1 : ℂ))
          (𝓝 ((1 : ℂ)-1))).pow 2
  have hd : Tendsto zetaPrimeDiagonalResponse (𝓝[≠] (1 : ℂ))
      (𝓝 (zetaPrimeDiagonalResponse 1)) :=
    (analyticAt_zetaPrimeDiagonalResponse (by norm_num : 1/2<(1 : ℂ).re)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  convert hl.sub (hz.mul hd) using 1
  · funext s
    dsimp [originalResponse]
    ring
  · norm_num

theorem actual_subtracted_density_source (eta xi : ℂ) :
    Tendsto (fun s : ℂ => (s-1)^2*subtractedResponse eta xi s)
      (𝓝[≠] (1 : ℂ)) (𝓝 ((1-eta)*(1-xi))) := by
  convert actual_density_source.const_mul ((1-eta)*(1-xi)) using 1
  · funext s
    simp only [subtractedResponse]
    ring
  · ring

/-- Fixed scalar column centering kills density iff it kills one whole
column. This concerns fixed scalar subtraction ONLY, not analytic filters. -/
theorem density_killed_iff (eta xi : ℂ) :
    Tendsto (fun s : ℂ => (s-1)^2*subtractedResponse eta xi s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) ↔ eta=1 ∨ xi=1 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (actual_subtracted_density_source eta xi) h
    rcases mul_eq_zero.mp he with he|he
    · exact Or.inl (sub_eq_zero.mp he).symm
    · exact Or.inr (sub_eq_zero.mp he).symm
  · rintro (rfl|rfl) <;> simp only [subtractedResponse,sub_self,zero_mul,mul_zero]
    all_goals exact tendsto_const_nhds

/-- Source-sensitive no-go: fixed constant column-mean subtraction that
removes the actual density response also removes every actual zero source. -/
theorem density_killed_implies_zero_source_killed (eta xi : ℂ)
    (hdensity : Tendsto (fun s : ℂ => (s-1)^2*subtractedResponse eta xi s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0)) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)^2*subtractedResponse eta xi s)
      (𝓝[≠] rho.1) (𝓝 0) := by
  rcases (density_killed_iff eta xi).mp hdensity with rfl|rfl <;>
    simp only [subtractedResponse,sub_self,zero_mul,mul_zero]
  all_goals exact tendsto_const_nhds

end
end RiemannGaussian.ArithmeticOperatorCenteredKummerAudit

#lint+ in RiemannGaussian.ArithmeticOperatorCenteredKummerAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty centered Kummer audit."
  logInfo m!"Centered-Kummer audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-centered-kummer"
  IO.FS.writeFile ".lake/arithmetic-operator-centered-kummer/axioms.json"
    (Json.mkObj [("scope",toJson "fixed scalar complete column-mean subtraction annihilates actual distinct-prime source; no incomplete cutoff boundary estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
