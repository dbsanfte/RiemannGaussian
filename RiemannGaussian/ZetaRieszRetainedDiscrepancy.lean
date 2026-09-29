/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDiscrepancyEnergy

/-!
# The original retained carrier's coupled arithmetic discrepancy

Keep the full cofactor phase by a rotation, then use the exact retained
factorial coefficients.  Every order, both Riesz hinges and the original
allocation remain in the signed comparison with the smooth response.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszRetainedDiscrepancy
open Real ZetaRieszDiscrepancyEnergy ZetaRieszWeightedPrimeTail
open ZetaRieszJointPrimeError ZetaRieszRetainedFactorial ZetaRieszJointAllocation

private theorem density_integrable (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => F (log x)/(x*log x)) volume (exp a) (exp b) := by
  have hx x (hx : x ∈ Icc (exp a) (exp b)) : 0 < x := (exp_pos a).trans_le hx.1
  have hl x (hx' : x ∈ Icc (exp a) (exp b)) : 0 < log x :=
    ha.trans_le ((le_log_iff_exp_le (hx x hx')).mpr hx'.1)
  have hc : ContinuousOn (fun x => F (log x)/(x*log x)) (Icc (exp a) (exp b)) :=
    (hF.comp_continuousOn (continuousOn_id.log (fun x hx' => (hx x hx').ne'))).div
      (continuousOn_id.mul (continuousOn_id.log (fun x hx' => (hx x hx').ne')))
      (fun x hx' => mul_ne_zero (hx x hx').ne' (hl x hx').ne')
  exact hc.intervalIntegrable_of_Icc (exp_le_exp.mpr hab)

private theorem smoothTail_linear (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L A B t : ℝ) :
    smoothTail (fun x => A*F x+B*G x) a b L t =
      A*smoothTail F a b L t+B*smoothTail G a b L t := by
  by_cases ht : t ∈ Ioc (L-b) L
  · simp only [smoothTail,indicator_of_mem ht]
    have hD : 0 < max a (L-t) := ha.trans_le (le_max_left _ _)
    have hDb : max a (L-t) ≤ b := max_le hab (by linarith [ht.1])
    have hFi := density_integrable F hF hD hDb
    have hGi := density_integrable G hG hD hDb
    have he x : (A*F (log x)+B*G (log x))/(x*log x) =
        A*(F (log x)/(x*log x))+B*(G (log x)/(x*log x)) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_add (hFi.const_mul A) (hGi.const_mul B),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  · simp only [smoothTail,indicator_of_notMem ht,mul_zero,add_zero]

/-- Linearity retains the complete signed smooth response, including both
cutoff boundaries. It permits an exact cofactor-phase rotation. -/
theorem smoothResponse_linear (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L A B : ℝ) (n : ℕ) :
    smoothResponse (fun x => A*F x+B*G x) a b L n =
      A*smoothResponse F a b L n+B*smoothResponse G a b L n := by
  have he k : smoothDifference (fun x => A*F x+B*G x) a b L k =
      A*smoothDifference F a b L k+B*smoothDifference G a b L k := by
    simp only [smoothDifference,smoothTail_linear F G hF hG ha hab]
    rw [intervalIntegral.integral_add
      ((smoothTail_integrable F hF ha hab L).intervalIntegrable.const_mul A)
      ((smoothTail_integrable G hG ha hab L).intervalIntegrable.const_mul B),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  simp only [smoothResponse,he,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

private theorem primeResponse_linear (F G : ℝ → ℝ) (a b L A B : ℝ) (n : ℕ) :
    primeResponse (fun x => A*F x+B*G x) a b L n =
      A*primeResponse F a b L n+B*primeResponse G a b L n := by
  simp only [primeResponse,add_div,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> (apply Finset.sum_congr rfl; intro p _; ring)

/-- The actual two-cutoff arithmetic discrepancy with its full phase. -/
def cosineError (G : ℝ → ℝ) (a b y L c : ℝ) (n : ℕ) : ℝ :=
  primeResponse (fun t => G t*cos (y*(t+c))) a b L n-
    smoothResponse (fun t => G t*cos (y*(t+c))) a b L n

private theorem cosine_error_square (G : ℝ → ℝ) (hG : Continuous G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y L c : ℝ) (n : ℕ) :
    (cosineError G a b y L c n)^2 ≤
      (primeResponse (fun t => G t*cos (y*t)) a b L n-
        smoothResponse (fun t => G t*cos (y*t)) a b L n)^2+
      (primeResponse (fun t => G t*sin (y*t)) a b L n-
        smoothResponse (fun t => G t*sin (y*t)) a b L n)^2 := by
  let F := fun t => G t*cos (y*t)
  let H := fun t => G t*sin (y*t)
  have hF : Continuous F := hG.mul (by fun_prop)
  have hH : Continuous H := hG.mul (by fun_prop)
  have he : (fun t => G t*cos (y*(t+c))) = fun t => cos (y*c)*F t+(-sin (y*c))*H t := by
    funext t
    dsimp [F,H]
    rw [mul_add,cos_add]
    ring
  rw [cosineError,he,primeResponse_linear,smoothResponse_linear F H hF hH ha hab]
  have hs := sin_sq_add_cos_sq (y*c)
  let A := primeResponse F a b L n-smoothResponse F a b L n
  let B := primeResponse H a b L n-smoothResponse H a b L n
  have hid : (cos (y*c)*A-sin (y*c)*B)^2+(sin (y*c)*A+cos (y*c)*B)^2=A^2+B^2 := by
    calc
      _ = (sin (y*c)^2+cos (y*c)^2)*(A^2+B^2) := by ring
      _ = _ := by rw [hs,one_mul]
  have hp := sq_nonneg (sin (y*c)*A+cos (y*c)*B)
  dsimp [A,B,F,H] at hid hp
  nlinarith only [hid,hp]

private theorem oscillating_profile (F G : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t) (hG : Continuous G)
    (y : ℝ) {a b W V : ℝ} (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hFW : ∀ t ∈ Icc a b, |F t| ≤ W) (hGV : ∀ t ∈ Icc a b, |G t| ≤ V) :
    ∃ Gc Gs : ℝ → ℝ,
      (∀ t, HasDerivAt (fun t => F t*cos (y*t)) (Gc t) t) ∧ Continuous Gc ∧
      (∀ t, HasDerivAt (fun t => F t*sin (y*t)) (Gs t) t) ∧ Continuous Gs ∧
      (∀ t ∈ Icc a b, |F t*cos (y*t)| ≤ W ∧ |F t*sin (y*t)| ≤ W) ∧
      (∀ t ∈ Icc a b, |Gc t| ≤ V+|y| * W ∧ |Gs t| ≤ V+|y| * W) := by
  let Gc := fun t => G t*cos (y*t)-y*F t*sin (y*t)
  let Gs := fun t => G t*sin (y*t)+y*F t*cos (y*t)
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  refine ⟨Gc,Gs,?_,?_,?_,?_,?_,?_⟩
  · intro t
    apply ((hF t).mul (((hasDerivAt_id t).const_mul y).cos)).congr_deriv
    simp only [Gc,id_eq]
    ring
  · exact (hG.mul (by fun_prop)).sub ((continuous_const.mul hFc).mul (by fun_prop))
  · intro t
    apply ((hF t).mul (((hasDerivAt_id t).const_mul y).sin)).congr_deriv
    simp only [Gs,id_eq]
    ring
  · exact (hG.mul (by fun_prop)).add ((continuous_const.mul hFc).mul (by fun_prop))
  · intro t ht
    constructor
    · rw [abs_mul]
      exact (mul_le_mul (hFW t ht) (abs_cos_le_one _) (abs_nonneg _) hW).trans_eq (mul_one _)
    · rw [abs_mul]
      exact (mul_le_mul (hFW t ht) (abs_sin_le_one _) (abs_nonneg _) hW).trans_eq (mul_one _)
  · intro t ht
    have hc : |G t*cos (y*t)| ≤ V := by
      rw [abs_mul]
      exact (mul_le_mul (hGV t ht) (abs_cos_le_one _) (abs_nonneg _) hV).trans_eq (mul_one _)
    have hs : |G t*sin (y*t)| ≤ V := by
      rw [abs_mul]
      exact (mul_le_mul (hGV t ht) (abs_sin_le_one _) (abs_nonneg _) hV).trans_eq (mul_one _)
    have hcy : |y*F t*cos (y*t)| ≤ |y| * W := by
      rw [abs_mul,abs_mul]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hFW t ht) (abs_nonneg y))
        (abs_cos_le_one _) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    have hsy : |y*F t*sin (y*t)| ≤ |y| * W := by
      rw [abs_mul,abs_mul]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hFW t ht) (abs_nonneg y))
        (abs_sin_le_one _) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    exact ⟨(abs_sub _ _).trans (add_le_add hc hsy),(abs_add_le _ _).trans (add_le_add hs hcy)⟩

/-- The cofactor phase is retained by an exact two-component rotation.
The actual prime-error input and every Riesz crossing are already paid. -/
theorem exists_cosine_error_mean :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (F G : ℝ → ℝ) (a b y W V L : ℝ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      (∀ t, HasDerivAt F (G t) t) → Continuous G → T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ V →
      (∀ t ∈ Icc a b, |F t| ≤ W) → (∀ t ∈ Icc a b, |G t| ≤ V) →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (cosineError F a b y L (c n) n)^2) ≤
        E*X*b*(intervalError a b W (V+|y| * W))^2 := by
  obtain ⟨T,E,hT,hE,hmean⟩ := exists_response_error_mean
  refine ⟨T,2*E,hT,by positivity,fun F G a b y W V L c X S hF hG ha hab hW hV hFW hGV hS hSF => ?_⟩
  have ha0 : 0 < a := by linarith
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  obtain ⟨Gc,Gs,hFc',hGc,hFs',hGs,htrig,hderiv⟩ := oscillating_profile F G hF hG y hW hV hFW hGV
  have hc := hmean (fun t => F t*cos (y*t)) Gc a b W (V+|y| * W) L X S hFc' hGc
    ha hab hW (by positivity) (fun t ht => (htrig t ht).1) (fun t ht => (hderiv t ht).1) hS hSF
  have hs := hmean (fun t => F t*sin (y*t)) Gs a b W (V+|y| * W) L X S hFs' hGs
    ha hab hW (by positivity) (fun t ht => (htrig t ht).2) (fun t ht => (hderiv t ht).2) hS hSF
  have ht := Finset.sum_le_sum (fun n (_ : n ∈ S) => cosine_error_square F hFc ha0 hab y L (c n) n)
  rw [Finset.sum_add_distrib] at ht
  nlinarith only [ht,hc,hs]

private theorem factorial_data (j : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j);
    let S := factorialScore a (b-a) j;
    ∃ G : ℝ → ℝ, (∀ t, HasDerivAt (factorialAmplitude j) (G t) t) ∧ Continuous G ∧
      (∀ t ∈ Icc a b, |factorialAmplitude j t| ≤ W) ∧
      (∀ t ∈ Icc a b, |G t| ≤ W*S) := by
  dsimp only
  let G := fun t => exp (-t/2)*((j : ℝ)*t^(j-1)-t^j/2)
  have hderiv t : HasDerivAt (factorialAmplitude j) (G t) t := by
    apply ((((hasDerivAt_id t).neg.div_const 2).exp).mul ((hasDerivAt_id t).pow j)).congr_deriv
    simp only [G,Pi.pow_apply,Pi.neg_apply,id_eq]
    ring
  let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j)
  have hb : 0 ≤ b := ha.le.trans hab
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hbound t (ht : t ∈ Icc a b) : |factorialAmplitude j t| ≤ W := by
    have h := (factorialAmplitude_bounds j ha (sub_nonneg.mpr hab)
      (show t ∈ Icc a (a+(b-a)) by simpa only [add_sub_cancel] using ht)).1
    simp only [add_sub_cancel] at h
    exact le_min h (factorial_amplitude_global_bound j (ha.le.trans ht.1))
  refine ⟨G,hderiv,by dsimp [G]; fun_prop,hbound,?_⟩
  intro t ht
  rw [(hderiv t).unique (factorialAmplitude_deriv j (ha.trans_le ht.1)),abs_mul,mul_comm]
  exact mul_le_mul (hbound t ht) (factorial_score_bound j ha ht) (abs_nonneg _) hW

private theorem factorialError_nonneg {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
    0 ≤ factorialError a b y j := by
  have hb : 0 ≤ b := ha.le.trans hab
  have hba : 0 ≤ b-a := sub_nonneg.mpr hab
  dsimp [factorialError,factorialScore]
  positivity

/-- Every exact factorial order has an actual-prime discrepancy mean with
the correlated cofactor phase and both Riesz cutoffs retained. -/
theorem exists_factorial_error_mean :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (a b y L : ℝ) (j : ℕ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      T ≤ a → a ≤ b → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (cosineError (factorialAmplitude j) a b y L (c n) n)^2) ≤
        E*X*b*(factorialError a b y j)^2 := by
  obtain ⟨T,E,hT,hE,hmean⟩ := exists_cosine_error_mean
  refine ⟨T,E,hT,hE,fun a b y L j c X S ha hab hS hSF => ?_⟩
  have ha0 : 0 < a := by linarith
  have hb : 0 ≤ b := ha0.le.trans hab
  have hba : 0 ≤ b-a := sub_nonneg.mpr hab
  let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j)
  obtain ⟨G,hG,hGc,hGW,hGD⟩ := factorial_data j ha0 hab
  have hh := hmean (factorialAmplitude j) G a b y W (W*factorialScore a (b-a) j) L c X S
    hG hGc ha hab (by dsimp [W]; positivity) (by dsimp [W,factorialScore]; positivity)
    hGW hGD hS hSF
  have he : intervalError a b W (W*factorialScore a (b-a) j+|y| * W) =
      factorialError a b y j := by dsimp [intervalError,factorialError,W]; ring
  rw [he] at hh
  exact hh

/-- The entire reciprocal-cofactor energy is paid on a shell, without a
count ceiling. This gives both signs of every factorial-order discrepancy. -/
theorem exists_factorial_shell_error :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (a b y L V : ℝ) (j : ℕ) (c w : ℕ → ℝ) (M : ℕ) (S : Finset ℕ),
      T ≤ a → a ≤ b → 0 ≤ V → 1 ≤ M → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, |w n| ≤ V/n) →
      |∑ n ∈ S, w n*cosineError (factorialAmplitude j) a b y L (c n) n| ≤
        sqrt E*V*sqrt b*factorialError a b y j := by
  obtain ⟨T,E,hT,hE,hmean⟩ := exists_factorial_error_mean
  refine ⟨T,2*E,hT,by positivity,fun a b y L V j c w M S ha hab hV hM hS hSF hw => ?_⟩
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := ha0.le.trans hab
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hSI : S ⊆ Finset.Ioc 1 (2*M) := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Ioc.mpr ⟨by omega,h.2⟩
  have hcard : (S.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hS
    rw [Nat.card_Ioc,show 2*M-M=M by omega] at h
    exact_mod_cast h
  have hwE : (∑ n ∈ S, (w n)^2) ≤ V^2/M := by
    have hp n (hn : n ∈ S) : (w n)^2 ≤ (V/M)^2 := by
      have hnM : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1.le
      have h := (hw n hn).trans (div_le_div_of_nonneg_left hV hM0 hnM)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    calc
      _ ≤ ∑ _n ∈ S, (V/M)^2 := Finset.sum_le_sum hp
      _ = S.card*(V/M)^2 := by simp
      _ ≤ M*(V/M)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = V^2/M := by field_simp
  have hmean' := hmean a b y L j c (2*M) S ha hab hSI hSF
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => cosineError (factorialAmplitude j) a b y L (c n) n)).trans
      (mul_le_mul hwE hmean' (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have he : V^2/M*(E*(2*M)*b*(factorialError a b y j)^2) =
      2*E*V^2*b*(factorialError a b y j)^2 := by field_simp
  push_cast at hs
  rw [he] at hs
  have herr := factorialError_nonneg (y := y) ha0 hab j
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt hb0]
  nlinarith only [hs]

/-- A numerical joint arithmetic-error budget for the retained carrier on
one common prime interval and one cofactor shell.  The signed smooth term
is separate and remains unpaid. -/
def retainedErrorCost (N M : ℕ) (a b y L : ℝ) : ℝ :=
  exp (-log M/2)*sqrt b/(L*N.factorial)*
    (∑ j ∈ Finset.range (N+2), ((N+1).choose j : ℝ)*log (2*M : ℕ)^(N+1-j)*
      factorialError a b y j)

/-- Both signed comparisons for the ORIGINAL retained carrier, now with
its exact allocation, all factorial orders, full cofactor phase and BOTH
Riesz cutoffs. Only the arithmetic discrepancy is bounded; the explicit
smooth carrier, literal prime holes and total source budget remain open. -/
theorem exists_literal_retained_error :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (A : Finset ℕ) (N M : ℕ) (S : Finset ℕ) (a b y L : ℝ),
      1 ≤ M → T ≤ a → a ≤ b → 0 < L → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime;
      P ⊆ A → (∀ n ∈ S, ∀ p ∈ P, ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1, 0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j)) ∧
        (∀ n ∈ S, ∀ p ∈ P,
          (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*log p^j) ∧
        let J := (∑ n ∈ S, ∑ p ∈ P, residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
        let H := (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S,
          (exp (-log n/2)*B n j/(n : ℝ))*
            smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n);
        let K := sqrt E*retainedErrorCost N M a b y L;
        H-K ≤ J ∧ J ≤ H+K := by
  obtain ⟨T,E,hT,hE,hbound⟩ := exists_factorial_shell_error
  refine ⟨T,E,hT,hE,fun A N M S a b y L hM ha hab hL hS hSF hPA hcop => ?_⟩
  dsimp only at hPA hcop ⊢
  let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime
  have hex n (hn : n ∈ S) := exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let B' := fun n j => if hn : n ∈ S then B n hn j else 0
  have hcoef' n (hn : n ∈ S) j (hj : j ≤ N+1) :
      0 ≤ B' n j ∧ B' n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j) := by
    simpa only [B',dif_pos hn] using hcoef n hn j hj
  have hid' n (hn : n ∈ S) p (hp : p ∈ P) :
      (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
        ∑ j ∈ Finset.range (N+2), B' n j*log p^j := by
    simpa only [B',dif_pos hn] using
      hid n hn p (Finset.mem_filter.mp hp).2 (hPA hp) (hcop n hn p hp)
  refine ⟨B',hcoef',hid',?_⟩
  let w := fun j (n : ℕ) => exp (-log n/2)*B' n j/(n : ℝ)
  let V := fun j => exp (-log M/2)*((N+1).choose j : ℝ)*log (2*M : ℕ)^(N+1-j)
  have hw j (hj : j ∈ Finset.range (N+2)) n (hn : n ∈ S) : |w j n| ≤ V j/n := by
    have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
    have hMn := Finset.mem_Ioc.mp (hS hn)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : log M ≤ log n := log_le_log hM0 (by exact_mod_cast hMn.1.le)
    have hlog' : log n ≤ log (2*M : ℕ) := log_le_log hn0 (by exact_mod_cast hMn.2)
    have hb0 := (hcoef' n hn j hjN).1
    have hb := (hcoef' n hn j hjN).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (log_natCast_nonneg n) hlog' _) (Nat.cast_nonneg _))
    dsimp only [w,V]
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ hn0.le
    simpa only [mul_assoc] using
      (mul_le_mul (exp_le_exp.mpr (show -log n/2 ≤ -log M/2 by linarith))
        hb hb0 (exp_pos (-log M/2)).le)
  have hi n (hn : n ∈ S) :
      (∑ p ∈ P, residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
        (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), w j n*
          primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n) := by
    rw [Complex.re_sum]
    have he p (hp : p ∈ P) := atom_expansion A N L y (hSF n hn).1 (hSF n hn).2
      (Finset.mem_filter.mp hp).2 (hcop n hn p hp) (B' n) (hid' n hn p hp)
    rw [Finset.sum_congr rfl he,← Finset.mul_sum,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [primeResponse,w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htotal :
      (∑ n ∈ S, ∑ p ∈ P, residualCoefficient A L N (p*n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S, w j n*
        primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n) := by
    rw [Complex.re_sum,Finset.sum_congr rfl hi,← Finset.mul_sum,Finset.sum_comm]
  have hj j (hj : j ∈ Finset.range (N+2)) :
      |∑ n ∈ S, w j n*cosineError (factorialAmplitude j) a b y L (log n) n| ≤
        sqrt E*V j*sqrt b*factorialError a b y j :=
    hbound a b y L (V j) j (fun n => log n) (w j) M S ha hab
      (by dsimp [V]; positivity) hM hS (fun n hn => (hSF n hn).1) (hw j hj)
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun j => ∑ n ∈ S, w j n*cosineError (factorialAmplitude j) a b y L (log n) n)
    (Finset.range (N+2))).trans (Finset.sum_le_sum hj)
  have hdiff :
      (∑ n ∈ S, ∑ p ∈ P, residualCoefficient A L N (p*n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re-
        (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S, w j n*
          smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n) =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S,
        w j n*cosineError (factorialAmplitude j) a b y L (log n) n) := by
    rw [htotal]
    simp only [cosineError,mul_sub,Finset.sum_sub_distrib]
  have habs : |(-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S,
        w j n*cosineError (factorialAmplitude j) a b y L (log n) n)| ≤
      sqrt E*retainedErrorCost N M a b y L := by
    rw [abs_mul,abs_div,abs_neg,abs_one,abs_of_pos (show 0 < L*(N.factorial : ℝ) by positivity)]
    apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/(L*(N.factorial : ℝ)))).trans_eq
    dsimp only [V,retainedErrorCost]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hdiff] at habs
  obtain ⟨hl,hu⟩ := abs_le.mp habs
  constructor <;> linarith

/-- Arbitrary finite radial/count families retain their JOINT signed smooth
carrier. One constant pays the sum of the explicit arithmetic error costs;
there is no maximum-order, count or family-cardinality multiplier. -/
theorem exists_literal_family_error :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (I : Finset ℕ) (A S : ℕ → Finset ℕ) (N M : ℕ → ℕ) (a b y L : ℕ → ℝ),
      (∀ i ∈ I, 1 ≤ M i ∧ T ≤ a i ∧ a i ≤ b i ∧ 0 < L i) →
      (∀ i ∈ I, S i ⊆ Finset.Ioc (M i) (2*M i)) →
      (∀ i ∈ I, ∀ n ∈ S i, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := fun i => (Finset.Ioc ⌊exp (a i)⌋₊ ⌊exp (b i)⌋₊).filter Nat.Prime;
      (∀ i ∈ I, P i ⊆ A i) → (∀ i ∈ I, ∀ n ∈ S i, ∀ p ∈ P i, ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℕ → ℝ,
        (∀ i ∈ I, ∀ n ∈ S i, ∀ j ≤ N i+1,
          0 ≤ B i n j ∧ B i n j ≤ ((N i+1).choose j : ℝ)*log n^(N i+1-j)) ∧
        (∀ i ∈ I, ∀ n ∈ S i, ∀ p ∈ P i,
          (1-boundedShare (A i) (N i) (p*n))*log (p*n : ℕ)^(N i+1) =
            ∑ j ∈ Finset.range (N i+2), B i n j*log p^j) ∧
        let J := ∑ i ∈ I, (∑ n ∈ S i, ∑ p ∈ P i, residualCoefficient (A i) (L i) (N i) (p*n)*
          zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re;
        let H := ∑ i ∈ I, (-1/(L i*(N i).factorial))*(∑ j ∈ Finset.range (N i+2), ∑ n ∈ S i,
          (exp (-log n/2)*B i n j/(n : ℝ))*
            smoothResponse (fun t => factorialAmplitude j t*cos (y i*(t+log n))) (a i) (b i) (L i) n);
        let K := sqrt E*(∑ i ∈ I, retainedErrorCost (N i) (M i) (a i) (b i) (y i) (L i));
        H-K ≤ J ∧ J ≤ H+K := by
  obtain ⟨T,E,hT,hE,hbound⟩ := exists_literal_retained_error
  refine ⟨T,E,hT,hE,fun I A S N M a b y L hpar hS hSF hPA hcop => ?_⟩
  dsimp only at hPA hcop ⊢
  have hex i (hi : i ∈ I) := hbound (A i) (N i) (M i) (S i) (a i) (b i) (y i) (L i)
    (hpar i hi).1 (hpar i hi).2.1 (hpar i hi).2.2.1 (hpar i hi).2.2.2
    (hS i hi) (hSF i hi) (hPA i hi) (hcop i hi)
  choose B hcoef hid hb using hex
  let B' := fun i n j => if hi : i ∈ I then B i hi n j else 0
  refine ⟨B',?_,?_,?_⟩
  · intro i hi n hn j hj
    simpa only [B',dif_pos hi] using hcoef i hi n hn j hj
  · intro i hi n hn p hp
    simpa only [B',dif_pos hi] using hid i hi n hn p hp
  · let J := fun i => (∑ n ∈ S i,
        ∑ p ∈ (Finset.Ioc ⌊exp (a i)⌋₊ ⌊exp (b i)⌋₊).filter Nat.Prime,
          residualCoefficient (A i) (L i) (N i) (p*n)*
            zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re
    let H := fun i => (-1/(L i*(N i).factorial))*(∑ j ∈ Finset.range (N i+2), ∑ n ∈ S i,
      (exp (-log n/2)*B' i n j/(n : ℝ))*
        smoothResponse (fun t => factorialAmplitude j t*cos (y i*(t+log n))) (a i) (b i) (L i) n)
    have hbi i (hi : i ∈ I) :
        H i-sqrt E*retainedErrorCost (N i) (M i) (a i) (b i) (y i) (L i) ≤ J i ∧
        J i ≤ H i+sqrt E*retainedErrorCost (N i) (M i) (a i) (b i) (y i) (L i) := by
      simpa only [H,J,B',dif_pos hi] using hb i hi
    have hlow := Finset.sum_le_sum (fun i (hi : i ∈ I) => (hbi i hi).1)
    have hhigh := Finset.sum_le_sum (fun i (hi : i ∈ I) => (hbi i hi).2)
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hlow hhigh
    exact ⟨hlow,hhigh⟩

end RiemannGaussian.ZetaRieszRetainedDiscrepancy
