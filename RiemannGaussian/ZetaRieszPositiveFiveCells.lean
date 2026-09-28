/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFivePrimeTransfer

/-!
# Original positive-five labels in the checked angular cells

The ordered cofactor witnesses refer to the actual prime factors of each
label. The coefficient enclosure retains the moving total logarithm.
These cells are for a one-sided arithmetic debit with the original signed
complement, not a new completed carrier.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveCells
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators Classical
open ZetaRieszPositiveFiveCover ZetaRieszPrimeEndpoint

/-- The fixed root used by the exhaustive positive-five certificate. -/
def root : Cover.Box := ![(1079/2000,119/200),(49/1000,307/2000),(49/1000,307/2000)]

/-- The ordered cofactor shares come from the original integer. -/
def shares (n a b : ℕ) : Fin 3 → ℝ :=
  ![Real.log (largestPrime n)/Real.log n,Real.log b/Real.log n,Real.log a/Real.log n]

/-- A cell selects actual positive five-prime labels and keeps every
pre-existing mask through `S`. Its lower least-prime cutoff is explicit. -/
def population (B : Cover.Box) (S : Finset ℕ) (L t h δ : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 5 ∧
    t < Real.log n ∧ Real.log n ≤ t+h ∧
    0 < (SquarefreeVaughanLogSource.coefficient L n).re ∧
    ∃ q a b r : ℕ, n.primeFactors.erase (largestPrime n) = {q,a,b,r} ∧
      r < b ∧ b < a ∧ a < q ∧ δ*Real.log n < Real.log r ∧
      shares n a b ∈ Cover.region B)

/-- Every squarefree five-prime label has the ordered cofactor witness
used in the literal cells. No unproved prime factorization is assumed. -/
theorem exists_ordered_cofactor {n : ℕ} (hc : n.primeFactors.card = 5) :
    ∃ q a b r : ℕ, n.primeFactors.erase (largestPrime n) = {q,a,b,r} ∧
      r < b ∧ b < a ∧ a < q := by
  have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hP : largestPrime n ∈ n.primeFactors := by
    rw [largestPrime,dif_pos hne]
    exact Finset.max'_mem _ _
  have hcard : (n.primeFactors.erase (largestPrime n)).card = 4 := by
    rw [Finset.card_erase_of_mem hP,hc]
  let v := (n.primeFactors.erase (largestPrime n)).orderEmbOfFin hcard
  refine ⟨v 3,v 2,v 1,v 0,?_,v.strictMono (by decide),v.strictMono (by decide),
    v.strictMono (by decide)⟩
  have he := (n.primeFactors.erase (largestPrime n)).image_orderEmbOfFin_univ hcard
  rw [← he]
  ext p
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Fin.exists_fin_succ,
    Fin.exists_fin_zero,or_false,Finset.mem_insert,Finset.mem_singleton]
  dsimp [v]
  simp only [eq_comm]
  tauto

/-- Exact cofactor witnesses give genuine primes, their product and the
sum of their logarithms. -/
theorem cofactor_data {n q a b r : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5)
    (he : n.primeFactors.erase (largestPrime n) = {q,a,b,r})
    (hrb : r < b) (hba : b < a) (haq : a < q) :
    (largestPrime n).Prime ∧ q.Prime ∧ a.Prime ∧ b.Prime ∧ r.Prime ∧
    n = (largestPrime n*b*a)*r*q ∧
    Real.log n = Real.log (largestPrime n)+Real.log q+Real.log a+Real.log b+Real.log r := by
  have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hP : largestPrime n ∈ n.primeFactors := by
    rw [largestPrime,dif_pos hne]
    exact Finset.max'_mem _ _
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase (by rw [he]; simp))
  have hap : a.Prime := Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase (by rw [he]; simp))
  have hbp : b.Prime := Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase (by rw [he]; simp))
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_erase (by rw [he]; simp))
  have hq : q ≠ a := by omega
  have hqb : q ≠ b := by omega
  have hqr : q ≠ r := by omega
  have hab : a ≠ b := by omega
  have har : a ≠ r := by omega
  have hbr : b ≠ r := by omega
  have hp := Finset.prod_erase_mul n.primeFactors id hP
  have hl := Finset.sum_erase_add n.primeFactors (fun p : ℕ => Real.log p) hP
  dsimp only [id_eq] at hp
  rw [he,Nat.prod_primeFactors_of_squarefree hs] at hp
  rw [he,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hl
  simp only [Finset.prod_insert,Finset.prod_singleton,Finset.sum_insert,Finset.sum_singleton,
    Finset.mem_insert,Finset.mem_singleton,hq,hqb,hqr,hab,har,hbr,or_self,not_false_eq_true] at hp hl
  refine ⟨Nat.prime_of_mem_primeFactors hP,hqp,hap,hbp,hrp,?_,?_⟩
  · simpa only [id_eq,mul_comm,mul_left_comm,mul_assoc] using hp.symm
  · linarith only [hl]

private theorem scaled_hinge_le {lo hi : ℚ} {B : Cover.Box}
    {T L P a b r : ℝ} (hT : 0 < T)
    (hLlo : (lo : ℝ)*T ≤ L) (hLhi : L ≤ (hi : ℝ)*T)
    (hPl : (B 0).1*T ≤ P) (hPu : P ≤ (B 0).2*T)
    (hbu : b ≤ (B 1).2*T) (hau : a ≤ (B 2).2*T) :
    max 0 (min (r-max 0 (max (L-P-b) (2*L-2*P-b-a))) (min (L-P) (T+2*P-3*L))) ≤
      T*max 0 (min (r/T-(offset lo B : ℝ))
        (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))) := by
  let R := (offset lo B : ℝ)
  let C := max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ)))
  have hR : T*R ≤ max 0 (max (L-P-b) (2*L-2*P-b-a)) := by
    dsimp [R,offset]
    simp only [Rat.cast_max,Rat.cast_zero,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,
      mul_max_of_nonneg _ _ hT.le,mul_zero]
    apply max_le (le_max_left _ _)
    apply max_le
    · exact (by nlinarith : T*((lo : ℝ)-(B 0).2-(B 1).2) ≤ L-P-b).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (by nlinarith : T*(2*(lo : ℝ)-2*(B 0).2-(B 1).2-(B 2).2) ≤ 2*L-2*P-b-a).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  have hC : min (L-P) (T+2*P-3*L) ≤ T*C := by
    have hh : min (L-P) (T+2*P-3*L) ≤
        T*min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ)) := by
      rw [mul_min_of_nonneg _ _ hT.le]
      exact min_le_min (by nlinarith) (by nlinarith)
    exact hh.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le)
  calc
    _ ≤ max 0 (min (r-T*R) (T*C)) :=
      max_le_max le_rfl (min_le_min (by linarith) hC)
    _ = max (T*0) (T*min (r/T-R) C) := by
      have he : T*(r/T-R) = r-T*R := by rw [mul_sub,mul_div_cancel₀ _ hT.ne']
      rw [mul_zero,mul_min_of_nonneg _ _ hT.le,he]
    _ = T*max 0 (min (r/T-R) C) := (mul_max_of_nonneg _ _ hT.le).symm

/-- The checked translated cap bounds the original five-prime coefficient
at its actual total logarithm. It keeps the pair deficit and introduces
no factorial or incidence multiplier. -/
theorem coefficient_le_cell_cap {lo hi owner : ℚ} {B : Cover.Box}
    (hv : valid lo hi owner B) {n q a b r : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5)
    (he : n.primeFactors.erase (largestPrime n) = {q,a,b,r})
    (hrb : r < b) (hba : b < a) (haq : a < q)
    (hshare : shares n a b ∈ Cover.region B) {L : ℝ}
    (hLlo : (lo : ℝ)*Real.log n ≤ L) (hLhi : L ≤ (hi : ℝ)*Real.log n)
    (hchlo : 2*Real.log n ≤ 3*L) (hchhi : 4*L ≤ 3*Real.log n) :
    max 0 (SquarefreeVaughanLogSource.coefficient L n).re ≤
      (Real.log n/(lo : ℝ))*max 0 (min (Real.log r/Real.log n-(offset lo B : ℝ))
        (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))) := by
  obtain ⟨hp,hq,ha,hb,hr,_,hlog⟩ := cofactor_data hs hc he hrb hba haq
  have hT : 0 < Real.log n := by
    have hn : 1 < n := by
      have hne : n ≠ 1 := by intro hn; subst n; norm_num at hc
      exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hs.ne_zero) (Ne.symm hne)
    exact Real.log_pos (by exact_mod_cast hn)
  have hlo : (0 : ℝ) < lo := by exact_mod_cast hv.1
  have hL : 0 < L := (mul_pos hlo hT).trans_le hLlo
  have hx (i : Fin 3) := Set.mem_pi.mp hshare i (Set.mem_univ i)
  have hPlo : (B 0).1*Real.log n ≤ Real.log (largestPrime n) := by
    exact (le_div_iff₀ hT).mp (hx 0).1.le
  have hPhi : Real.log (largestPrime n) ≤ (B 0).2*Real.log n := by
    exact (div_le_iff₀ hT).mp (hx 0).2
  have hbhi : Real.log b ≤ (B 1).2*Real.log n := by
    exact (div_le_iff₀ hT).mp (hx 1).2
  have hahi : Real.log a ≤ (B 2).2*Real.log n := by
    exact (div_le_iff₀ hT).mp (hx 2).2
  have hcap := scaled_hinge_le (r := Real.log r) hT hLlo hLhi hPlo hPhi hbhi hahi
  rw [ZetaRieszPositiveFiveInterior.positive_coefficient_eq_cap hs hc he hrb hba haq hL hchlo hchhi]
  have hshape : Real.log n-Real.log (largestPrime n)-3*(L-Real.log (largestPrime n)) =
      Real.log n+2*Real.log (largestPrime n)-3*L := by ring
  have hoff : 2*(L-Real.log (largestPrime n))-Real.log b-Real.log a =
      2*L-2*Real.log (largestPrime n)-Real.log b-Real.log a := by ring
  rw [hshape,hoff]
  have hratio : Real.log n/L ≤ 1/(lo : ℝ) :=
    (div_le_div_iff₀ hL hlo).mpr (by linarith)
  calc
    _ ≤ (Real.log n/L)*(Real.log n*max 0
        (min (Real.log r/Real.log n-(offset lo B : ℝ))
          (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ)))))) :=
      mul_le_mul_of_nonneg_left hcap (div_nonneg hT.le hL.le)
    _ ≤ (1/(lo : ℝ))*(Real.log n*max 0
        (min (Real.log r/Real.log n-(offset lo B : ℝ))
          (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ)))))) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg hT.le (le_max_left _ _))
    _ = _ := by ring

open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows

/-- The literal weighted five-prime counting expression for one cell.
The final prime keeps its exact cofactor-dependent total-log interval. -/
def weightedPrimeMass (lo H : Fin 3 → ℝ) (a b r c t h : ℝ) : ℝ :=
  ∑ v ∈ Fintype.piFinset (fun i => logPrimes (lo i) (H i)),
    (∏ i, (v i : ℝ)⁻¹)*
      ∑ p ∈ logPrimes (t*a) (t*(b-a)),
        (max 0 (min (Real.log p/t-r) c)/(p : ℝ))*
          ∑ q ∈ logPrimes (t-Real.log ((∏ i, v i)*p : ℕ)) h, (q : ℝ)⁻¹

/-- All five literal prime sums are bounded jointly, preserving the
weighted least-prime fibre and the cofactor-dependent final endpoint.
No independent final-prime interval or absolute phase cost is substituted. -/
theorem eventually_weightedPrimeMass_upper {h α β a b Q r c ε : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 < a) (hab : a < b) (hbQ : b < Q) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 3 → ℝ) (t : ℝ),
      (N : ℝ) ≤ t → (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∑ i, (lo i+H i)) ≤ t*(1-Q) →
      weightedPrimeMass lo H a b r c t h ≤
        ((1001/1000 : ℝ)*(∏ i, H i/lo i))*((10001/10000 : ℝ)*h/t)*
          ((10003/10000 : ℝ)*
            (∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(Q-x)))+ε) := by
  filter_upwards [eventually_macro_tuple_bounds hα hβ (by norm_num : 3 ≤ 4),
    ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu (sub_pos.mpr hbQ),
    ZetaRieszPositiveFivePrimeTransfer.eventually_translated_fibre_upper ha hab hbQ hc hε,
    eventually_ge_atTop (1 : ℕ)] with N hmacro hlast hfibre hN lo H t ht hlo hwidth hsum
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith
  let V := Fintype.piFinset (fun i : Fin 3 => logPrimes (lo i) (H i))
  let R := logPrimes (t*a) (t*(b-a))
  let F := fun p : ℕ => max 0 (min (Real.log p/t-r) c)
  let D := (10001/10000 : ℝ)*h/t
  let I := (10003/10000 : ℝ)*
    (∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(Q-x)))+ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hI : 0 ≤ I := by
    have he : 0 ≤ ∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(Q-x)) := by
      apply intervalIntegral.integral_nonneg hab.le
      intro x hx
      exact div_nonneg (le_max_left _ _) (mul_nonneg (ha.le.trans hx.1) (by linarith [hx.2]))
    dsimp [I]
    positivity
  have hrow (v : Fin 3 → ℕ) (hv : v ∈ V) :
      (∑ p ∈ R, (F p/(p : ℝ))*
        ∑ q ∈ logPrimes (t-Real.log ((∏ i, v i)*p : ℕ)) h, (q : ℝ)⁻¹) ≤ D*I := by
    have hpoint (p : ℕ) (hp : p ∈ R) :
        (F p/(p : ℝ))*(∑ q ∈ logPrimes (t-Real.log ((∏ i, v i)*p : ℕ)) h, (q : ℝ)⁻¹) ≤
        D*(F p/((Q-Real.log p/t)*(p : ℝ))) := by
      have hvp (i : Fin 3) := logPrimes_bounds (Fintype.mem_piFinset.mp hv i)
      have hp' := logPrimes_bounds hp
      have hlog : Real.log ((∏ i, v i)*p : ℕ) = (∑ i, Real.log (v i))+Real.log p := by
        rw [Nat.cast_mul,Real.log_mul]
        · rw [Nat.cast_prod,Real.log_prod]
          exact fun i _ => by exact_mod_cast (hvp i).1.ne_zero
        · exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun i _ => (hvp i).1.ne_zero)
        · exact_mod_cast hp'.1.ne_zero
      have hlogs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hvp i).2.2)
      have hx : Real.log p/t ≤ b := (div_le_iff₀ ht0).mpr (by nlinarith [hp'.2.2])
      have hgap : 0 < Q-Real.log p/t := by linarith
      have hcenter : t*(Q-Real.log p/t) ≤ t-Real.log ((∏ i, v i)*p : ℕ) := by
        rw [hlog,mul_sub,mul_div_cancel₀ _ ht0.ne']
        nlinarith
      have hmin : (Q-b)*N ≤ t-Real.log ((∏ i, v i)*p : ℕ) := by
        have h₁ := mul_le_mul_of_nonneg_left ht (sub_pos.mpr hbQ).le
        have h₂ := mul_le_mul_of_nonneg_left (show Q-b ≤ Q-Real.log p/t by linarith) ht0.le
        nlinarith
      have hl := (hlast _ hmin).2
      have hden : 0 < t*(Q-Real.log p/t) := mul_pos ht0 hgap
      have hbound := hl.trans (div_le_div_of_nonneg_left
        (by positivity : (0 : ℝ) ≤ (10001/10000 : ℝ)*h) hden hcenter)
      have hf : 0 ≤ F p/(p : ℝ) := div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
      calc
        _ ≤ (F p/(p : ℝ))*((10001/10000 : ℝ)*h/(t*(Q-Real.log p/t))) :=
          mul_le_mul_of_nonneg_left hbound hf
        _ = _ := by dsimp [D]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
    have hs := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (hfibre t ht) hD)
  have hs := Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_left (hrow v hv) (by positivity : (0 : ℝ) ≤ ∏ i, (v i : ℝ)⁻¹))
  rw [← Finset.sum_mul] at hs
  have hbnd := mul_le_mul_of_nonneg_right (hmacro lo H hlo hwidth).2 (mul_nonneg hD hI)
  change weightedPrimeMass lo H a b r c t h ≤
    (∑ v ∈ V, ∏ i, (v i : ℝ)⁻¹)*(D*I) at hs
  exact hs.trans (by simpa only [mul_assoc] using hbnd)

/-- The positivity restrictions force every original interior label into
the complete checked root. These are exact prime logarithms, not limiting
shares or an assumed continuum support. -/
theorem shares_mem_root_of_positive {n q a b r : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5)
    (he : n.primeFactors.erase (largestPrime n) = {q,a,b,r})
    (hrb : r < b) (hba : b < a) (haq : a < q) {L : ℝ}
    (hLlo : (693/1000 : ℝ)*Real.log n ≤ L)
    (hLhi : L ≤ (1733/2500 : ℝ)*Real.log n)
    (howner : Real.log (largestPrime n) ≤ (119/200 : ℝ)*Real.log n)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re) :
    shares n a b ∈ Cover.region root := by
  obtain ⟨hp,hq,ha,hb,hr,_,hlog⟩ := cofactor_data hs hc he hrb hba haq
  have hT : 0 < Real.log n := by
    have hn : 1 < n := by
      have hne : n ≠ 1 := by intro hn; subst n; norm_num at hc
      exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hs.ne_zero) (Ne.symm hne)
    exact Real.log_pos (by exact_mod_cast hn)
  have hL : 0 < L := by linarith
  have hlr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  have hrblog : Real.log r ≤ Real.log b := Real.log_le_log
    (by exact_mod_cast hr.pos) (by exact_mod_cast hrb.le)
  have hbalog : Real.log b ≤ Real.log a := Real.log_le_log
    (by exact_mod_cast hb.pos) (by exact_mod_cast hba.le)
  have haqlog : Real.log a ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast ha.pos) (by exact_mod_cast haq.le)
  let d := L-Real.log (largestPrime n)
  let off := max 0 (max (d-Real.log b) (2*d-Real.log b-Real.log a))
  let F := max 0 (min (Real.log r-off) (min d
    (Real.log n-Real.log (largestPrime n)-3*d)))
  have hcoeff := ZetaRieszPositiveFiveInterior.positive_coefficient_eq_cap hs hc he hrb hba haq hL
    (by linarith) (by linarith)
  rw [max_eq_right hpos.le] at hcoeff
  change (SquarefreeVaughanLogSource.coefficient L n).re = (Real.log n/L)*F at hcoeff
  have hF : 0 < F := by
    by_contra hn
    have hn : F ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hT.le hL.le) hn
    rw [← hcoeff] at hm
    exact hpos.not_ge hm
  have hh : 0 < min (Real.log r-off) (min d (Real.log n-Real.log (largestPrime n)-3*d)) :=
    (lt_max_iff.mp hF).resolve_left (lt_irrefl _)
  have hsmall := (lt_min_iff.mp hh).1
  have hfull := (lt_min_iff.mp (lt_min_iff.mp hh).2).2
  have hoff : d-Real.log b ≤ off := (le_max_left _ _).trans (le_max_right _ _)
  have hpair : d < Real.log r+Real.log b := by linarith
  have hPlo : (1079/2000 : ℝ)*Real.log n < Real.log (largestPrime n) := by
    dsimp [d] at hfull
    linarith
  have hbLo : (49/1000 : ℝ)*Real.log n < Real.log b := by
    dsimp [d] at hpair
    linarith
  have hbHi : Real.log b ≤ (307/2000 : ℝ)*Real.log n := by linarith
  have haLo : (49/1000 : ℝ)*Real.log n < Real.log a := hbLo.trans_le hbalog
  have haHi : Real.log a ≤ (307/2000 : ℝ)*Real.log n := by
    dsimp [d] at hpair
    linarith
  apply Set.mem_pi.mpr
  intro i _
  fin_cases i
  · change ((1079/2000 : ℚ) : ℝ) < Real.log (largestPrime n)/Real.log n ∧
      Real.log (largestPrime n)/Real.log n ≤ ((119/200 : ℚ) : ℝ)
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    exact ⟨(lt_div_iff₀ hT).mpr hPlo,(div_le_iff₀ hT).mpr howner⟩
  · change ((49/1000 : ℚ) : ℝ) < Real.log b/Real.log n ∧
      Real.log b/Real.log n ≤ ((307/2000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    exact ⟨(lt_div_iff₀ hT).mpr hbLo,(div_le_iff₀ hT).mpr hbHi⟩
  · change ((49/1000 : ℚ) : ℝ) < Real.log a/Real.log n ∧
      Real.log a/Real.log n ≤ ((307/2000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    exact ⟨(lt_div_iff₀ hT).mpr haLo,(div_le_iff₀ hT).mpr haHi⟩

/-- The checked root contains the entire literal positive-five interior
left by the owner and least-prime payments, in the original window. -/
theorem mem_root_population {S : Finset ℕ} {n : ℕ} (hnS : n ∈ S)
    (hs : Squarefree n) (hc : n.primeFactors.card = 5) {L t h δ : ℝ}
    (ht : t < Real.log n) (hth : Real.log n ≤ t+h)
    (hLlo : (693/1000 : ℝ)*Real.log n ≤ L)
    (hLhi : L ≤ (1733/2500 : ℝ)*Real.log n)
    (howner : Real.log (largestPrime n) ≤ (119/200 : ℝ)*Real.log n)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
    (hsmall : ∀ p ∈ n.primeFactors, δ*Real.log n < Real.log p) :
    n ∈ population root S L t h δ := by
  obtain ⟨q,a,b,r,he,hrb,hba,haq⟩ := exists_ordered_cofactor hc
  apply Finset.mem_filter.mpr
  refine ⟨hnS,hs,hc,ht,hth,hpos,q,a,b,r,he,hrb,hba,haq,?_,?_⟩
  · exact hsmall r (Finset.mem_of_mem_erase (by rw [he]; simp))
  · exact shares_mem_root_of_positive hs hc he hrb hba haq hLlo hLhi howner hpos

/-- Cell subdivision covers the same original labels. Shared faces are
assigned by the original half-open convention and are never discarded. -/
theorem population_subset_split (B : Cover.Box) (i : Fin 3) (cut : ℚ)
    (S : Finset ℕ) (L t h δ : ℝ) :
    population B S L t h δ ⊆ population (CertifiedBoxCover.leftBox B i cut) S L t h δ ∪
      population (CertifiedBoxCover.rightBox B i cut) S L t h δ := by
  intro n hn
  obtain ⟨hnS,hs,hc,ht,hth,hpos,q,a,b,r,he,hrb,hba,haq,hsmall,hshare⟩ := Finset.mem_filter.mp hn
  by_cases hside : shares n a b i ≤ (cut : ℝ)
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hnS,hs,hc,ht,hth,hpos,q,a,b,r,he,hrb,hba,haq,hsmall,?_⟩
    apply Set.mem_pi.mpr
    intro j _
    have hj := Set.mem_pi.mp hshare j (Set.mem_univ j)
    by_cases hji : j = i
    · subst j
      simpa only [CertifiedBoxCover.leftBox,Function.update_self,Set.mem_Ioc] using And.intro hj.1 hside
    · simpa only [CertifiedBoxCover.leftBox,Function.update_of_ne hji] using hj
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hnS,hs,hc,ht,hth,hpos,q,a,b,r,he,hrb,hba,haq,hsmall,?_⟩
    apply Set.mem_pi.mpr
    intro j _
    have hj := Set.mem_pi.mp hshare j (Set.mem_univ j)
    by_cases hji : j = i
    · subst j
      simpa only [CertifiedBoxCover.rightBox,Function.update_self,Set.mem_Ioc] using And.intro (lt_of_not_ge hside) hj.2
    · simpa only [CertifiedBoxCover.rightBox,Function.update_of_ne hji] using hj

/-- The exact ordering bounds the least share by the same moving endpoint
used in the checked harmonic cap. -/
theorem least_share_le_cap_endpoint {lo hi : ℚ} {B : Cover.Box} (w : ℚ × ℚ)
    {n q a b r : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (he : n.primeFactors.erase (largestPrime n) = {q,a,b,r})
    (hrb : r < b) (hba : b < a) (haq : a < q)
    (hshare : shares n a b ∈ Cover.region B) (hT : 0 < Real.log n) :
    Real.log r/Real.log n ≤ ((cap lo hi B w.1 w.2).b : ℝ) := by
  obtain ⟨_,hq,ha,hb,hr,_,hlog⟩ := cofactor_data hs hc he hrb hba haq
  have hrlog : Real.log r ≤ Real.log b := Real.log_le_log
    (by exact_mod_cast hr.pos) (by exact_mod_cast hrb.le)
  have haqlog : Real.log a ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast ha.pos) (by exact_mod_cast haq.le)
  have hx (i : Fin 3) := Set.mem_pi.mp hshare i (Set.mem_univ i)
  have hPlo : (B 0).1*Real.log n ≤ Real.log (largestPrime n) :=
    (le_div_iff₀ hT).mp (hx 0).1.le
  have hbLo : (B 1).1*Real.log n ≤ Real.log b := (le_div_iff₀ hT).mp (hx 1).1.le
  have haLo : (B 2).1*Real.log n ≤ Real.log a := (le_div_iff₀ hT).mp (hx 2).1.le
  have hbHi : Real.log b ≤ (B 1).2*Real.log n := (div_le_iff₀ hT).mp (hx 1).2
  simp only [cap,Rat.cast_min,Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat]
  apply le_min
  · exact (div_le_iff₀ hT).mpr (hrlog.trans hbHi)
  · apply (div_le_iff₀ hT).mpr
    nlinarith only [hPlo,hbLo,haLo,haqlog,hlog]

/-- The coefficient bound can be evaluated at the original phase-window
scale t while its share masks continue to use the true total log n. -/
theorem coefficient_le_window_cap {lo hi owner : ℚ} {B : Cover.Box}
    (hv : valid lo hi owner B) {n q a b r : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5)
    (he : n.primeFactors.erase (largestPrime n) = {q,a,b,r})
    (hrb : r < b) (hba : b < a) (haq : a < q)
    (hshare : shares n a b ∈ Cover.region B) {L t h : ℝ}
    (ht : 0 < t) (htn : t ≤ Real.log n) (hnth : Real.log n ≤ t+h)
    (hLlo : (lo : ℝ)*Real.log n ≤ L) (hLhi : L ≤ (hi : ℝ)*Real.log n)
    (hchlo : 2*Real.log n ≤ 3*L) (hchhi : 4*L ≤ 3*Real.log n) :
    max 0 (SquarefreeVaughanLogSource.coefficient L n).re ≤
      ((t+h)/(lo : ℝ))*max 0 (min (Real.log r/t-(offset lo B : ℝ))
        (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))) := by
  have hlo : (0 : ℝ) < lo := by exact_mod_cast hv.1
  have hx := div_le_div_of_nonneg_left (Real.log_natCast_nonneg r) ht htn
  have hF : max 0 (min (Real.log r/Real.log n-(offset lo B : ℝ))
      (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))) ≤
      max 0 (min (Real.log r/t-(offset lo B : ℝ))
      (max 0 (min ((hi : ℝ)-(B 0).1) (1+2*(B 0).2-3*(lo : ℝ))))) :=
    max_le_max le_rfl (min_le_min (sub_le_sub_right hx _) le_rfl)
  exact (coefficient_le_cell_cap hv hs hc he hrb hba haq hshare hLlo hLhi hchlo hchhi).trans
    (mul_le_mul (div_le_div_of_nonneg_right hnth hlo.le) hF (le_max_left _ _)
      (div_nonneg (by linarith : 0 ≤ t+h) hlo.le))

end
end RiemannGaussian.ZetaRieszPositiveFiveCells
