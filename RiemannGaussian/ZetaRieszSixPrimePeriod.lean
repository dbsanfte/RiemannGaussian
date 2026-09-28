/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointTriplePayment
import RiemannGaussian.ZetaRieszSixPrimeSecondReflection

/-!
# Signed period payment for a literal six-prime population

Four middle primes have logarithms in `(14v/125,27v/200]`; the least
prime has logarithm at most `v/200`. Their complete largest-prime period
retains the exact coefficient, factorial weight and phase. No lower
cutoff is imposed on the least prime.
-/

namespace RiemannGaussian.ZetaRieszSixPrimePeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- The four-prime middle chamber is affine with exact slope three. -/
theorem four_difference_pairs {a b c e D v : ℝ} (hv : 0 ≤ v)
    (ha : (14/125 : ℝ)*v ≤ a) (hb : (14/125 : ℝ)*v ≤ b)
    (hc : (14/125 : ℝ)*v ≤ c) (he : (14/125 : ℝ)*v ≤ e)
    (hau : a ≤ (27/200 : ℝ)*v) (hbu : b ≤ (27/200 : ℝ)*v)
    (hcu : c ≤ (27/200 : ℝ)*v) (heu : e ≤ (27/200 : ℝ)*v)
    (hD : (27/100 : ℝ)*v ≤ D) (hDu : D ≤ (42/125 : ℝ)*v) :
    tripleDifference a b c D-tripleDifference a b c (D-e) =
      3*D-2*(a+b+c+e) := by
  simp only [tripleDifference,primePairTent]
  repeat' first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
  ring

/-- The five-prime cofactor keeps exactly three least-prime logarithms.
This equality is uniform through the whole last-prime period. -/
theorem riesz_five_plateau {r a b c e : ℕ} (hr : r.Prime) (ha : a.Prime)
    (hb : b.Prime) (hc : c.Prime) (he : e.Prime)
    (hs : Squarefree (r*(e*(a*(b*c))))) {v D : ℝ} (hv : 0 ≤ v)
    (hm : ∀ q ∈ ({a,b,c,e} : Finset ℕ),
      (14/125 : ℝ)*v ≤ Real.log q ∧ Real.log q ≤ (27/200 : ℝ)*v)
    (hrl : Real.log r ≤ v/200)
    (hD : (11/40 : ℝ)*v ≤ D) (hDu : D ≤ (42/125 : ℝ)*v) :
    VaughanLogAverage.riesz D (r*(e*(a*(b*c)))) = 3*Real.log r := by
  have hrd : ¬r ∣ e*(a*(b*c)) := hr.coprime_iff_not_dvd.mp
    (Nat.coprime_of_squarefree_mul hs)
  have hed : ¬e ∣ a*(b*c) := he.coprime_iff_not_dvd.mp
    (Nat.coprime_of_squarefree_mul hs.of_mul_right)
  have had : ¬a ∣ b*c := ha.coprime_iff_not_dvd.mp
    (Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right)
  have hbd : ¬b ∣ c := hb.coprime_iff_not_dvd.mp
    (Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right.of_mul_right)
  have hab : a ≠ b := by intro h; subst b; exact had (dvd_mul_right _ _)
  have hac : a ≠ c := by intro h; subst c; exact had (dvd_mul_left _ _)
  have hbc : b ≠ c := by intro h; subst c; exact hbd (dvd_refl _)
  have hma := hm a (by simp)
  have hmb := hm b (by simp)
  have hmc := hm c (by simp)
  have hme := hm e (by simp)
  have hfour (E : ℝ) (hl : (27/100 : ℝ)*v ≤ E) (hu : E ≤ (42/125 : ℝ)*v) :
      VaughanLogAverage.riesz E (e*(a*(b*c))) =
        3*E-2*(Real.log a+Real.log b+Real.log c+Real.log e) := by
    rw [riesz_prime_mul E he hed,
      riesz_three_primes_eq_difference E ha hb hc hab hac hbc,
      riesz_three_primes_eq_difference (E-Real.log e) ha hb hc hab hac hbc]
    exact four_difference_pairs hv hma.1 hmb.1 hmc.1 hme.1
      hma.2 hmb.2 hmc.2 hme.2 hl hu
  rw [riesz_prime_mul D hr hrd,hfour D (by linarith) hDu,
    hfour (D-Real.log r) (by linarith) (by linarith [Real.log_natCast_nonneg r])]
  ring

/-- Middle-prime choices; repeated factors are removed by the literal
squarefree condition, before forming the integer image. -/
def middlePrimes (v : ℝ) : Finset ℕ :=
  logPrimes ((14/125 : ℝ)*v) ((23/1000 : ℝ)*v)

/-- All small primes, including the fixed small primes, are retained. -/
def smallPrimes (v : ℝ) : Finset ℕ := logPrimes 0 (v/200)

/-- The five-prime cofactor before its unique largest prime is inserted. -/
def cofactor (rq : ℕ × (Fin 4 → ℕ)) : ℕ := rq.1 * ∏ i, rq.2 i

/-- The squarefree cofactor choices retain every small prime and all
distinct middle-prime choices in the specified interval. -/
def choices (v : ℝ) : Finset (ℕ × (Fin 4 → ℕ)) :=
  ((smallPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => middlePrimes v))).filter
    (fun rq => Squarefree (cofactor rq))

/-- Actual cofactor integers, without duplicate tuple incidences. -/
def cofactors (v : ℝ) : Finset ℕ := (choices v).image cofactor

/-- Literal integers, with one owner prime and its full phase period. -/
def population (v y : ℝ) : Finset ℕ := (cofactors v).biUnion (fun a =>
  (logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)).image (fun p => a*p))

private theorem choice_data {v : ℝ} {rq : ℕ × (Fin 4 → ℕ)}
    (hrq : rq ∈ choices v) :
    rq.1.Prime ∧ 0 < Real.log rq.1 ∧ Real.log rq.1 ≤ v/200 ∧
      (∀ i, (rq.2 i).Prime ∧ (14/125 : ℝ)*v < Real.log (rq.2 i) ∧
        Real.log (rq.2 i) ≤ (27/200 : ℝ)*v) ∧ Squarefree (cofactor rq) := by
  obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hrq
  obtain ⟨hr,hq⟩ := Finset.mem_product.mp hmem
  have hrb := logPrimes_bounds hr
  refine ⟨hrb.1,hrb.2.1,by simpa only [zero_add] using hrb.2.2,?_,hs⟩
  intro i
  have hq := logPrimes_bounds (Fintype.mem_piFinset.mp hq i)
  exact ⟨hq.1,hq.2.1,by linarith [hq.2.2]⟩

private theorem cofactor_log {v : ℝ} {rq : ℕ × (Fin 4 → ℕ)} (hrq : rq ∈ choices v) :
    Real.log (cofactor rq) = Real.log rq.1+∑ i, Real.log (rq.2 i) := by
  have hd := choice_data hrq
  rw [cofactor,Nat.cast_mul,Real.log_mul (by exact_mod_cast hd.1.ne_zero)
    (by exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun i _ => (hd.2.2.2.1 i).1.ne_zero)),
    Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hd.2.2.2.1 i).1.ne_zero)]

private theorem cofactor_factor {v : ℝ} {rq : ℕ × (Fin 4 → ℕ)}
    (hrq : rq ∈ choices v) {p : ℕ} (hp : p.Prime) (hd : p ∣ cofactor rq) :
    p = rq.1 ∨ ∃ i, p = rq.2 i := by
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (choice_data hrq).1).mp hd)
  · obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    exact Or.inr ⟨i,(Nat.prime_dvd_prime_iff_eq hp ((choice_data hrq).2.2.2.1 i).1).mp hi⟩

private theorem cofactor_data {v : ℝ} (_hv : 0 ≤ v) {a : ℕ} (ha : a ∈ cofactors v) :
    Squarefree a ∧ a.primeFactors.card = 5 ∧ Real.log a.minFac ≤ v/200 ∧
      (56/125 : ℝ)*v < Real.log a ∧ Real.log a ≤ (109/200 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ (27/200 : ℝ)*v) := by
  obtain ⟨rq,hrq,rfl⟩ := Finset.mem_image.mp ha
  have hd := choice_data hrq
  have hcount : ArithmeticFunction.cardFactors (cofactor rq) = 5 := by
    simp [cofactor,Fin.prod_univ_four,ArithmeticFunction.cardFactors_mul,
      hd.1.ne_zero,(hd.2.2.2.1 0).1.ne_zero,(hd.2.2.2.1 1).1.ne_zero,
      (hd.2.2.2.1 2).1.ne_zero,(hd.2.2.2.1 3).1.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hd.1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 0).1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 1).1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 2).1,
      ArithmeticFunction.cardFactors_apply_prime (hd.2.2.2.1 3).1]
  have hcard : (cofactor rq).primeFactors.card = 5 := by
    have he : (cofactor rq).primeFactors.card = (cofactor rq).primeFactorsList.length :=
      List.toFinset_card_of_nodup hd.2.2.2.2.nodup_primeFactorsList
    simpa only [ArithmeticFunction.cardFactors_apply,← he] using hcount
  have hne : cofactor rq ≠ 1 := by intro h; simp [h] at hcard
  have hmin : (cofactor rq).minFac = rq.1 := by
    apply le_antisymm (Nat.minFac_le_of_dvd hd.1.two_le (dvd_mul_right _ _))
    rcases cofactor_factor hrq (Nat.minFac_prime hne) (Nat.minFac_dvd _) with h | ⟨i,h⟩
    · exact h.ge
    · change rq.1 ≤ (cofactor rq).minFac
      rw [h]
      exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hd.1.pos : (0 : ℝ) < rq.1)
        (by exact_mod_cast (hd.2.2.2.1 i).1.pos : (0 : ℝ) < rq.2 i)).mp
        (by linarith [hd.2.2.1,(hd.2.2.2.1 i).2.1])
  have hlog := cofactor_log hrq
  rw [Fin.sum_univ_four] at hlog
  refine ⟨hd.2.2.2.2,hcard,by simpa only [hmin] using hd.2.2.1,?_,?_,?_⟩
  · linarith [hd.2.1,(hd.2.2.2.1 0).2.1,(hd.2.2.2.1 1).2.1,
      (hd.2.2.2.1 2).2.1,(hd.2.2.2.1 3).2.1]
  · linarith [hd.2.2.1,(hd.2.2.2.1 0).2.2,(hd.2.2.2.1 1).2.2,
      (hd.2.2.2.1 2).2.2,(hd.2.2.2.1 3).2.2]
  · intro p hp
    rcases cofactor_factor hrq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp) with h | ⟨i,h⟩
    · rw [h]; linarith [hd.2.2.1]
    · simpa only [h] using (hd.2.2.2.1 i).2.2

/-- The selected six-prime integers have unique largest-prime ownership,
all original radial bounds, and no prime beyond the allocation-safe share. -/
theorem fibre_geometry {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ Squarefree (p*a) ∧
      (p*a).primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/|y| ∧
      (∀ q ∈ (p*a).primeFactors, Real.log q ≤ (9/16 : ℝ)*Real.log (p*a : ℕ)) := by
  obtain ⟨hs,hc,hr,hal,hau,ham⟩ := cofactor_data (by linarith) ha
  have hb := logPrimes_bounds hp
  have hπ : 0 < Real.pi/|y| := div_pos Real.pi_pos (by linarith)
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  have hl : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.1.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hbu := hb.2.2
  rw [mul_div_assoc] at hbu
  have howner (q : ℕ) (hq : q ∈ a.primeFactors) : q < p := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos : (0 : ℝ) < q)
      (by exact_mod_cast hb.1.pos : (0 : ℝ) < p)).mp (by linarith [ham q hq,hb.2.1])
  have hpd : ¬p ∣ a := by
    intro hd
    exact (howner p (hb.1.mem_primeFactors hd hs.ne_zero)).false
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hb.1.coprime_iff_not_dvd.mpr hpd,hb.1.squarefree,hs⟩
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hb.1.ne_zero hs.ne_zero,hb.1.primeFactors,Finset.singleton_union]
  have hpm : p ∉ a.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
  have hpmax : Real.log p ≤ (9/16 : ℝ)*Real.log (p*a : ℕ) := by
    rw [hl]; linarith
  refine ⟨hb.1,howner,hsf,by rw [hpf,Finset.card_insert_of_notMem hpm,hc],
    by rw [hl]; linarith [hb.2.1],by rw [hl]; linarith,?_⟩
  intro q hq
  rw [hpf] at hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact hpmax
  · exact (Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast (howner q hq).le)).trans hpmax

private theorem choice_minFac {v : ℝ} (hv : 0 ≤ v) {rq : ℕ × (Fin 4 → ℕ)}
    (hrq : rq ∈ choices v) : (cofactor rq).minFac = rq.1 := by
  have hd := choice_data hrq
  have hc := (cofactor_data hv (Finset.mem_image.mpr ⟨rq,hrq,rfl⟩)).2.1
  have hne : cofactor rq ≠ 1 := by intro h; simp [h] at hc
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hd.1.two_le (dvd_mul_right _ _)
  · rcases cofactor_factor hrq (Nat.minFac_prime hne) (Nat.minFac_dvd _) with h | ⟨i,h⟩
    · exact h.ge
    · rw [h]
      exact_mod_cast (Real.log_le_log_iff
        (by exact_mod_cast hd.1.pos : (0 : ℝ) < rq.1)
        (by exact_mod_cast (hd.2.2.2.1 i).1.pos : (0 : ℝ) < rq.2 i)).mp
        (by linarith [hd.2.2.1,(hd.2.2.2.1 i).2.1])

/-- Exact coefficient on the selected literal six-prime population. -/
theorem coefficient_plateau {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hLl : (67/100 : ℝ)*v ≤ L) (hLu : L ≤ (18/25 : ℝ)*v)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    SquarefreeVaughanLogSource.coefficient L (p*a) =
      ((-(Real.log (p*a : ℕ)/L)*(3*Real.log a.minFac) : ℝ) : ℂ) := by
  obtain ⟨hpp,howner,hs,hc,hlo,hhi,hmax⟩ := fibre_geometry hv hy ha hp
  have hadata := cofactor_data (by linarith) ha
  have hpd : ¬p ∣ a := by
    intro h
    exact (howner p (hpp.mem_primeFactors h hadata.1.ne_zero)).false
  have hn1 : p*a ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬(p*a).Prime := by intro h; simp [h.primeFactors] at hc
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hadata.1.ne_zero)]
  have hD : (11/40 : ℝ)*v ≤ Real.log (p*a : ℕ)-L := by linarith
  have hDu : Real.log (p*a : ℕ)-L ≤ (42/125 : ℝ)*v := by linarith
  have houter : Real.log (p*a : ℕ)-L-Real.log p ≤ 0 := by
    rw [hlog]; linarith [hadata.2.2.2.2.1]
  have hR : VaughanLogAverage.riesz (Real.log (p*a : ℕ)-L) a = 3*Real.log a.minFac := by
    obtain ⟨rq,hrq,rfl⟩ := Finset.mem_image.mp ha
    have hd := choice_data hrq
    have he : cofactor rq = rq.1*(rq.2 0*(rq.2 1*(rq.2 2*rq.2 3))) := by
      simp [cofactor,Fin.prod_univ_four,mul_assoc]
    rw [choice_minFac (by linarith) hrq,he]
    exact riesz_five_plateau hd.1 (hd.2.2.2.1 1).1 (hd.2.2.2.1 2).1
      (hd.2.2.2.1 3).1 (hd.2.2.2.1 0).1 (he ▸ hd.2.2.2.2) (by linarith)
      (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl <;>
            exact ⟨(hd.2.2.2.1 _).2.1.le,(hd.2.2.2.1 _).2.2⟩)
      hd.2.2.1 (by simpa only [← he] using hD) (by simpa only [← he] using hDu)
  have href := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc] at href
  norm_num only [Int.cast_pow,Int.cast_neg,Int.cast_one,one_mul] at href
  rw [riesz_prime_mul (Real.log (p*a : ℕ)-L) hpp hpd,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos houter,sub_zero,hR] at href
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,← href]
  congr 1
  ring

private theorem small_log_mass {v : ℝ} (hv : 1000 ≤ v) :
    (∑ r ∈ smallPrimes v, Real.log r*(r : ℝ)⁻¹) ≤ v/50 := by
  have hb := ZetaRieszCoreExtensions.prime_log_mass_le (smallPrimes v)
    (show 0 ≤ v/200 by linarith) (by
      intro r hr
      have hd := logPrimes_bounds hr
      exact ⟨hd.1,by simpa only [zero_add] using hd.2.2⟩)
  have he : (∑ r ∈ smallPrimes v, Real.log r*Real.exp (-Real.log r)) =
      ∑ r ∈ smallPrimes v, Real.log r*(r : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Real.exp_neg,Real.exp_log (by exact_mod_cast (logPrimes_bounds hr).1.pos)]
  rw [he] at hb
  have hl : Real.log 4 ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1
    norm_num
  nlinarith [mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+v/200 by linarith)]

/-- An actual cofactor population bound, retaining the least-prime log
weight. The harmless tuple overcount is used only after prime-period
cancellation, never on individual oscillatory prime atoms. -/
theorem eventually_cofactor_mass :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v →
      (∑ a ∈ cofactors v, Real.log a.minFac*(a : ℝ)⁻¹) ≤ v/25000 := by
  filter_upwards [eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/100) (by norm_num : (0 : ℝ) < 1/100),
    eventually_ge_atTop (1000 : ℕ)] with N hN hlarge v hv
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 ≤ v := by linarith
  have hq := (hN ((14/125 : ℝ)*v) ((23/1000 : ℝ)*v) (by linarith) (by linarith)).2
  have hqu : (∑ q ∈ middlePrimes v, (q : ℝ)⁻¹) ≤ 207/1000 := by
    apply hq.trans
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < (14/125)*v)).mpr
    nlinarith
  have hcover : (∑ a ∈ cofactors v, Real.log a.minFac*(a : ℝ)⁻¹) ≤
      ∑ rq ∈ (smallPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => middlePrimes v)),
        Real.log rq.1*(cofactor rq : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ rq ∈ choices v, Real.log (cofactor rq).minFac*(cofactor rq : ℝ)⁻¹ :=
        Finset.sum_image_le_of_nonneg (fun a _ => mul_nonneg (Real.log_natCast_nonneg _) (by positivity))
      _ = ∑ rq ∈ choices v, Real.log rq.1*(cofactor rq : ℝ)⁻¹ :=
        Finset.sum_congr rfl (fun rq hrq => by rw [choice_minFac hv0 hrq])
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun rq _ _ => mul_nonneg (Real.log_natCast_nonneg _) (by positivity))
  have he : (∑ rq ∈ (smallPrimes v).product (Fintype.piFinset (fun _ : Fin 4 => middlePrimes v)),
        Real.log rq.1*(cofactor rq : ℝ)⁻¹) =
      (∑ r ∈ smallPrimes v, Real.log r*(r : ℝ)⁻¹)*
        (∑ q ∈ middlePrimes v, (q : ℝ)⁻¹)^4 := by
    rw [Finset.product_eq_sprod,Finset.sum_product]
    have hpoint (r : ℕ) (q : Fin 4 → ℕ) :
        Real.log r*(cofactor (r,q) : ℝ)⁻¹ =
          (Real.log r*(r : ℝ)⁻¹)*(∏ i, (q i : ℝ)⁻¹) := by
      simp only [cofactor,Nat.cast_mul,Nat.cast_prod,Finset.prod_inv_distrib,mul_inv_rev]
      ring
    simp_rw [hpoint,← Finset.mul_sum]
    rw [← Finset.sum_mul]
    congr 1
    exact (Finset.sum_pow' (middlePrimes v) (fun q : ℕ => (q : ℝ)⁻¹) 4).symm
  rw [he] at hcover
  have hpow := pow_le_pow_left₀
    (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))) hqu 4
  have hprod := mul_le_mul (small_log_mass (by linarith)) hpow
    (by positivity) (by linarith : 0 ≤ v/50)
  apply hcover.trans (hprod.trans _)
  nlinarith

/-- The whole largest-prime period is summed before any absolute value. -/
theorem sum_population {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) (f : ℕ → ℂ) :
    (∑ n ∈ population v y, f n) = ∑ a ∈ cofactors v,
      ∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|), f (p*a) := by
  rw [population,ZetaRieszCoupledWindow.sum_owned_products _ _ f
    (fun a ha => (cofactor_data (by linarith) ha).1.ne_zero) (by
      intro a ha p hp
      have hg := fibre_geometry hv hy ha hp
      exact ⟨hg.1,fun q hq hd => hg.2.1 q
        (hq.mem_primeFactors hd (cofactor_data (by linarith) ha).1.ne_zero)⟩)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.mul_comm]

private theorem re_plateau_atom {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (hLl : (67/100 : ℝ)*v ≤ L) (hLu : L ≤ (18/25 : ℝ)*v)
    {a p : ℕ} (ha : a ∈ cofactors v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) (N : ℕ) :
    (SquarefreeVaughanLogSource.coefficient L (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      -(3*Real.log a.minFac/L/a)*
        ((Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
          (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a))) := by
  have hpp := (logPrimes_bounds hp).1
  have ha0 := (cofactor_data (by linarith) ha).1.ne_zero
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast ha0)]
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*a : ℕ)) =
      Real.exp (-Real.log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*a : ℕ) =
      -Real.log (p*a : ℕ)/2-Real.log (p*a : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hpp.pos (Nat.pos_of_ne_zero ha0)),
      Nat.cast_mul]
    ring
  rw [← ZetaRieszJointAllocation.filter_one_eq,ZetaRieszCosineCarrier.re_coefficient_filter_one,
    coefficient_plateau hv hy hLl hLu ha hp,Complex.ofReal_re,hex,hlog,pow_succ]
  ring

/-- Independent signed cancellation of the entire selected six-prime
population. The constant is proved using actual prime counts, with every
least prime retained and no zero hypothesis. -/
theorem eventually_raw_population_bound {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ N : ℕ in atTop, ∀ (v L : ℝ),
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (67/100 : ℝ)*v ≤ L → L ≤ (18/25 : ℝ)*v →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |(∑ n ∈ population v y, SquarefreeVaughanLogSource.coefficient L n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          (m : ℝ)/100000*V*(Real.pi/(4*m*|y|)) := by
  filter_upwards [ZetaRieszPrimePeriodCancellation.eventually_factorial_prime_period
      hm hy (by norm_num : (0 : ℝ) < 1/2) hsmall hphase,
    eventually_cofactor_mass,eventually_ge_atTop (1000 : ℕ)] with N hN hmass hlarge v L hv hlo hhi hLl hLu
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hy0 : 0 < |y| := by linarith
  have hπ : 0 < Real.pi/|y| := by positivity
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨V,hV,hbaseLower,hbase,hbound⟩ := hN v hv hlo hhi
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  let h := Real.pi/(4*m*|y|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < h := by dsimp [h]; positivity
  have hrow (a : ℕ) (ha : a ∈ cofactors v) :
      |(∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        SquarefreeVaughanLogSource.coefficient L (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re| ≤
        ((m : ℝ)*V*h/(5*v))*(Real.log a.minFac*(a : ℝ)⁻¹) := by
    have hd := cofactor_data hv0.le ha
    have ha0 : 0 < v-Real.log a := by linarith [hd.2.2.2.2.1]
    have hperiod := hbound (Real.log a) (by linarith [hd.2.2.2.2.1])
    rw [← ZetaRieszPrimePeriodCancellation.sum_prime_period _ hm v (Real.log a) y hy0] at hperiod
    have he : (∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
        SquarefreeVaughanLogSource.coefficient L (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
        -(3*Real.log a.minFac/L/a)*
          (∑ p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|),
            (Real.exp (-(Real.log p+Real.log a)/2)*(Real.log p+Real.log a)^(N+1)/N.factorial)*
              (p : ℝ)⁻¹*Real.cos (y*(Real.log p+Real.log a))) := by
      rw [Complex.re_sum,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p hp => re_plateau_atom hv100 hy hLl hLu ha hp N)
    rw [he,abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ 3*Real.log a.minFac/L/a by
      exact div_nonneg (div_nonneg (by positivity) hL.le) (Nat.cast_nonneg _))]
    apply (mul_le_mul_of_nonneg_left hperiod (by positivity)).trans
    have hl : 3/L ≤ 9/(2*v) := by
      apply (div_le_div_iff₀ hL (by positivity)).mpr
      linarith
    have ht : (v-Real.pi/|y|)/(v-Real.log a) ≤ 9/4 := by
      apply (div_le_iff₀ ha0).mpr
      linarith [hd.2.2.2.2.1]
    have ht0 : 0 ≤ (v-Real.pi/|y|)/(v-Real.log a) := by
      apply div_nonneg _ ha0.le
      linarith
    have hc := mul_le_mul hl ht ht0 (by positivity : 0 ≤ 9/(2*v))
    have hc' : (3/L)*((v-Real.pi/|y|)/(v-Real.log a)) ≤ 25/(2*v) := by
      apply hc.trans
      have hp : (9/(2*v))*(9/4) = (81/8)/v := by ring
      rw [hp]
      apply (div_le_div_iff₀ hv0 (by positivity)).mpr
      linarith
    have hs := mul_le_mul_of_nonneg_right hc'
      (show 0 ≤ (1/500 : ℝ)*(8*m)*V*h*(Real.log a.minFac*(a : ℝ)⁻¹) by positivity)
    convert hs using 1 <;> dsimp only [h] <;> ring
  rw [sum_population hv100 hy,Complex.re_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum hrow).trans
  rw [← Finset.mul_sum]
  have hb := mul_le_mul_of_nonneg_left (hmass v (by linarith))
    (show 0 ≤ (m : ℝ)*V*h/(5*v) by positivity)
  apply hb.trans
  have he : (m : ℝ)*V*h/(5*v)*(v/25000) = (m : ℝ)*V*h/125000 := by
    field_simp
    ring
  rw [he]
  change (m : ℝ)*V*h/125000 ≤ (m : ℝ)/100000*V*h
  nlinarith only [mul_nonneg (mul_nonneg hmR.le hV.le) hh.le]

/-- Every selected integer is squarefree, has exactly six prime factors,
and satisfies the unchanged radial and allocation-safe share conditions. -/
theorem population_data {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) {n : ℕ}
    (hn : n ∈ population v y) :
    Squarefree n ∧ n.primeFactors.card = 6 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      (∀ a ∈ n.primeFactors, Real.log a ≤ (9/16 : ℝ)*Real.log n) := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  simpa only [Nat.mul_comm a p] using (fibre_geometry hv hy ha hp).2.2
/-- All original core masks are discharged on the concrete rectangle.
The phase-period selection does not enlarge the arithmetic support. -/
theorem population_subset_core (j : ℕ) (hj : 32 ≤ j) {u v y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hv : 100 ≤ v)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ v-Real.pi/|y|)
    (hhi : v+Real.pi/|y| ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) :
    population v y ⊆ ZetaRieszParityPacket.coreBand u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨hs,hcount,htl,htu,hmax⟩ := population_data hv hy hn
  apply ZetaRieszCoupledWindow.mem_core_of_prime_share_le j hj hu hU hL hs
    (by omega) ?_ (hlo.trans_lt htl) (htu.trans hhi) hmax
  rw [hcount]
  have hk : 8 ≤ ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    change 2^3 ≤ 2^(j+3)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Independent two-sided cancellation inside the WHOLE actual core.
The selected rectangle is arithmetically counted, every original mask
is checked, and the entire complementary response remains signed. -/
theorem eventually_core_joint_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |((u : ℂ)^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|)))+ZetaRieszTriplePeriod.allocationBound N := by
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 137/200) hroom
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_raw_population_bound hm hy hsmall hphase),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hraw hLlow hlarge hj
  intro v
  dsimp only
  intro hv hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hN : 2 ≤ N := by omega
  have hy0 : 0 < |y| := by linarith
  have hπ : 0 ≤ Real.pi/|y| := by positivity
  have hv100 : 100 ≤ v := by change (39/20 : ℝ)*N ≤ _ at hlo; linarith
  have hLhi : L ≤ (7/5 : ℝ)*N := by
    have he := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    change SquarefreeVaughanLogSource.length u N ≤ _ at he
    dsimp only [L]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  change 2*(137/200 : ℝ)*N ≤ L at hLlow
  change (39/20 : ℝ)*N ≤ _ at hlo
  change _ ≤ (203/100 : ℝ)*N at hhi
  obtain ⟨V,hV,hbaseLower,hbase,hB⟩ := hraw v L hv hlo hhi (by linarith) (by linarith)
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  have hD := population_subset_core j hj hu hU hy hv100 (by change (5/4 : ℝ)*N ≤ L; linarith) hlo hhi
  apply ZetaRieszTriplePeriod.scaled_joint_bound_of_raw _ _ _ (SquarefreeVaughanLogSource.length_pos u N) N hD ?_ ?_ y
    (by linarith : 0 ≤ u) hU hB
  · intro n hn
    have hb := (population_data hv100 hy hn).2.2
    apply (ZetaRieszJointAllocation.mem_literalWindow N n).mpr
    constructor <;> linarith [hb.1,hb.2.1]
  · intro n hn p hp _ _
    have hb := (population_data hv100 hy hn).2.2.2.2 p hp
    nlinarith [Real.log_natCast_nonneg n]

/-- The cancellation reaches the SAME whole J+C used by the source
contradiction. Both a lower and an upper comparison follow, with a proved
vanishing error and the exact signed complement. The local radial debit
is explicit; it is not asserted to vanish at source scale. -/
theorem eventually_whole_joint_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
        |((u : ℂ)^(N+1)*(J-
          ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\population v y,
            ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
              (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|)))+err j := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount
  let J := fun j => ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y (N j) (K j)-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y (N j) (K j)+
      ZetaRieszLeastBoundary.rest u y (N j) (K j)
  let E := fun j => (u : ℂ)^(N j+1)*(ZetaRieszParityPacket.coreResponse u y (N j) (K j)-J j)
  have hu0 : 0 ≤ u := by linarith
  have he : Tendsto E atTop (𝓝 0) := by
    have hh := (ZetaRieszJointFloor.tendsto_nondominant_sub_joint hu0 hU y).sub
      (ZetaRieszJointFloor.tendsto_nondominant_sub_core hu0 hU y)
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [] with j
    dsimp only [E,J,N,K]
    ring
  let err := fun j => ZetaRieszTriplePeriod.allocationBound (N j)+‖E j‖
  refine ⟨err,fun j => add_nonneg (ZetaRieszTriplePeriod.allocationBound_nonneg _) (norm_nonneg _),?_,?_⟩
  · have ht := (ZetaRieszTriplePeriod.tendsto_allocationBound.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add he.norm
    simpa only [norm_zero,add_zero,err,N,Function.comp_def] using ht
  filter_upwards [eventually_core_joint_bound hu hU hm hy hsmall hphase] with j hj
  intro v
  dsimp only
  intro hv hlo hhi
  obtain ⟨V,hV,hbaseLower,hbase,hbound⟩ := hj v hv hlo hhi
  refine ⟨V,hV,hbaseLower,hbase,?_⟩
  let rest := ∑ n ∈ ZetaRieszParityPacket.coreBand u (N j) (K j)\population v y,
    ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (N j))
      (SquarefreeVaughanLogSource.length u (N j)) (N j) n*zetaPrimeLogKernel (N j) (3/2+Complex.I*y) n
  have hid : (u : ℂ)^(N j+1)*(J j-rest) =
      (u : ℂ)^(N j+1)*(ZetaRieszParityPacket.coreResponse u y (N j) (K j)-rest)-E j := by
    dsimp only [E]
    ring
  change |((u : ℂ)^(N j+1)*(J j-rest)).re| ≤ _
  rw [hid,Complex.sub_re]
  have hs := (abs_sub _ _).trans (add_le_add hbound (Complex.abs_re_le_norm (E j)))
  dsimp only [err]
  simpa only [add_assoc] using hs

/-- The actual coupled residual sum, including its old allocation, has
the proved signed cost. This is the payment used in the combined ledger. -/
theorem eventually_signed_population_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m)
    {y : ℝ} (hy : 54 ≤ |y|)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      population v y ⊆ ZetaRieszParityPacket.coreBand u N K ∧
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        |u^(N+1)*(∑ n ∈ population v y,
          ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
          u^(N+1)*((m : ℝ)/100000*V*(Real.pi/(4*m*|y|)))+ZetaRieszTriplePeriod.allocationBound N := by
  filter_upwards [eventually_core_joint_bound hu hU hm hy hsmall hphase,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)), eventually_ge_atTop (32 : ℕ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent (by linarith : 0 < u)
        (by norm_num : (0 : ℝ) ≤ 137/200)
        (hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
          (Real.exp_lt_exp.mpr (by norm_num)))))] with j hbound hN hj hL
  intro v
  dsimp only
  intro hv hlo hhi
  have hNR : (1000 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
  have hpi : 0 ≤ Real.pi/|y| := by positivity
  have hQ := population_subset_core j hj hu hU hy (by linarith) (by linarith) hlo hhi
  obtain ⟨V,hV,hbase,_,hc⟩ := hbound v hv hlo hhi
  refine ⟨hQ,V,hV,hbase,?_⟩
  have he := Finset.sum_sdiff hQ (f := fun n =>
    ZetaRieszJointAllocation.residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n*
        zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (3/2+Complex.I*y) n)
  unfold ZetaRieszParityPacket.coreResponse at hc
  rw [← he,add_sub_cancel_left] at hc
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using hc
/-- The new squarefree six-prime population cannot overlap any supply cell,
without adding an ordering or numerical-cover premise. -/
theorem disjoint_supply {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (t h z : ℝ) (lo H : Fin 4 → ℝ) :
    Disjoint (population v y) (ZetaRieszJointPrimeCells.supplyCell t h z lo H) := by
  apply Finset.disjoint_left.mpr
  intro n hn hs
  have hd := population_data hv hy hn
  have hcard : n.primeFactors.card = n.primeFactorsList.length :=
    List.toFinset_card_of_nodup hd.1.nodup_primeFactorsList
  have hc := ZetaRieszJointTriplePayment.supply_count hs
  rw [ArithmeticFunction.cardFactors_apply,← hcard,hd.2.1] at hc
  omega

/-- Four-prime payments and the new six-prime payment have distinct labels. -/
theorem disjoint_adverse {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L t h z a : ℝ) :
    Disjoint (population v y) (ZetaRieszFourBoundaryCover.adversePopulation S L t h z a) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hf).2.2.1
  omega

/-- Full positive-five interior payments have no six-prime labels. -/
theorem disjoint_interior {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z δ : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v' z m δ) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- The small-prime five-factor boundary is disjoint from the six-primes. -/
theorem disjoint_head {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (L v' z : ℝ) (m : ℕ) :
    Disjoint (population v y)
      (ZetaRieszPositiveFiveBoundary.periodPopulation S L v' z m) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  have hc := (population_data hv hy hn).2.1
  have hf := (Finset.mem_filter.mp hi).2.2.1
  omega

/-- Every prime share of the new rectangle is below the paid owner band. -/
theorem disjoint_owner {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S A : Finset ℕ) :
    Disjoint (population v y) (ZetaRieszJointOwnerPayment.population S A) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨_,_,hn1,_,p,hp,_,_,hlo,_⟩ := Finset.mem_filter.mp hf
  have hc := (population_data hv hy hn).2.2.2.2 p hp
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  nlinarith


/-- The new six-prime period has no labels in the previously paid
balanced-triple population. -/
theorem disjoint_balanced {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    (S : Finset ℕ) (t h : ℝ) :
    Disjoint (population v y) (ZetaRieszBroadTripleBudget.population S t h) := by
  apply Finset.disjoint_left.mpr
  intro n hn hb
  have hc := (population_data hv hy hn).2.1
  have hb := (Finset.mem_filter.mp hb).2.2.1
  omega

/-- Nor can it overlap the previously paid unbalanced-triple period. -/
theorem disjoint_triple {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|) :
    Disjoint (population v y) (ZetaRieszTriplePeriod.population v y) := by
  apply Finset.disjoint_left.mpr
  intro n hn ht
  have hc := (population_data hv hy hn).2.1
  have ht := (ZetaRieszTriplePeriod.population_data hv hy ht).2.1
  omega

/-- The payment is nonvacuous: every sufficiently late period contains
actual six-prime labels, already with the fixed least prime two. -/
theorem eventually_population_nonempty {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, (N : ℝ) ≤ v → (population v y).Nonempty := by
  have hy0 : 0 < |y| := by linarith
  have hH : 0 < 2*Real.pi/|y| := by positivity
  have hpi : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hne (S : Finset ℕ) (f : ℕ → ℝ) (hp : 0 < ∑ p ∈ S, f p) : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  filter_upwards [eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/1000) (by norm_num : (0 : ℝ) < 1/1000),
    ZetaRieszSharpPrimeWindows.eventually_log_mass_bounds hH
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1000 : ℕ)] with N hmacro hlast hlarge v hv
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hv0 : 0 < v := by linarith
  have hex (i : Fin 4) : ∃ q, q ∈ logPrimes (((14/125 : ℝ)+(i : ℕ)/200)*v) (v/200) := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hm := (hmacro (((14/125 : ℝ)+(i : ℕ)/200)*v) (v/200)
      (by nlinarith) (by linarith)).1
    exact hne _ _ ((by positivity : 0 < (4999/5000 : ℝ)*(v/200)/
      (((14/125 : ℝ)+(i : ℕ)/200)*v+v/200)).trans_le hm)
  choose q hq using hex
  have hqp (i : Fin 4) := (logPrimes_bounds (hq i)).1
  have hqb (i : Fin 4) := (logPrimes_bounds (hq i)).2
  have hmono : StrictMono q := by
    intro i j hij
    have hijR : ((i : ℕ) : ℝ)+1 ≤ (j : ℕ) := by exact_mod_cast (show (i : ℕ)+1 ≤ j by omega)
    have hlog : Real.log (q i) < Real.log (q j) := by
      nlinarith [hqb i,hqb j,mul_nonneg (show (0 : ℝ) ≤ (j : ℕ)-(i : ℕ)-1 by linarith) hv0.le]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (hqp i).pos : (0 : ℝ) < q i)
      (by exact_mod_cast (hqp j).pos : (0 : ℝ) < q j)).mp hlog
  have hqm (i : Fin 4) : q i ∈ middlePrimes v := by
    have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hiu : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (i : ℕ) ≤ 3 by omega)
    apply (mem_logPrimes_iff _ _ _).mpr
    exact ⟨hqp i,by nlinarith [hqb i],by nlinarith [hqb i]⟩
  have h2q (i : Fin 4) : 2 ≠ q i := by
    intro h
    have hh := (logPrimes_bounds (hqm i)).2.1
    rw [← h] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_lt_d9]
  have hsprod : Squarefree (∏ i, q i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      change IsRelPrime (q i) (q j)
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hqp i) (hqp j)).mpr (fun h => hij (hmono.injective h))
    · intro i _
      exact (hqp i).squarefree
  have h2d : ¬2 ∣ ∏ i, q i := by
    intro hd
    obtain ⟨i,_,hi⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp hd
    exact h2q i ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hqp i)).mp hi)
  have hrq : (2,q) ∈ choices v := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,Fintype.mem_piFinset.mpr hqm⟩,
      Nat.squarefree_mul_iff.mpr ⟨Nat.prime_two.coprime_iff_not_dvd.mpr h2d,
        Nat.prime_two.squarefree,hsprod⟩⟩
    exact (mem_logPrimes_iff _ _ _).mpr ⟨Nat.prime_two,by norm_num; positivity,
      by norm_num only [Nat.cast_ofNat,zero_add]; linarith [Real.log_two_lt_d9]⟩
  have ha : cofactor (2,q) ∈ cofactors v := Finset.mem_image.mpr ⟨(2,q),hrq,rfl⟩
  have hd := cofactor_data hv0.le ha
  have hpa : (1/4 : ℝ)*N ≤ v-Real.pi/|y|-Real.log (cofactor (2,q)) := by
    linarith [hd.2.2.2.2.1]
  have hpmass := (hlast _ hpa).1
  have he : 0 < Real.exp (2*Real.pi/|y|)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hH)
  obtain ⟨p,hp⟩ := hne _ _ ((by positivity : 0 < (1-1/2 : ℝ)*(Real.exp (2*Real.pi/|y|)-1)*
    Real.exp (v-Real.pi/|y|-Real.log (cofactor (2,q)))).trans_le hpmass)
  exact ⟨cofactor (2,q)*p,Finset.mem_biUnion.mpr ⟨cofactor (2,q),ha,
    Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩

end
end RiemannGaussian.ZetaRieszSixPrimePeriod
