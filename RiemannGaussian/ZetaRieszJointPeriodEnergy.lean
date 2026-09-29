/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRetainedFactorial

/-!
# Joint prime-period cutoff energy

At a fixed divisor cutoff only one of a separated family of prime intervals
can be partially active. Combine all signed periods before the quadratic
mean: the partial-tail budget is paid once, not once per period.
-/

noncomputable section
open scoped BigOperators Classical
open Set
namespace RiemannGaussian.ZetaRieszJointPeriodEnergy
open ZetaRieszPrimeTailEnergy ZetaRieszWeightedPrimeTail

private theorem tail_outside_transition (P : Finset ℕ) (c x : ℕ → ℝ)
    (L t a b : ℝ) (hx : ∀ p ∈ P, a ≤ x p ∧ x p ≤ b)
    (ht : t ∉ Ioc (L-b) (L-a)) :
    tail P c x L t = 0 ∨ tail P c x L t = ∑ p ∈ P, c p := by
  by_cases hlow : t ≤ L-b
  · left
    apply Finset.sum_eq_zero
    intro p hp
    apply indicator_of_notMem
    intro hh
    linarith [(hx p hp).2,hh.1]
  · have hhigh : L-a < t := by
      by_contra hh
      exact ht ⟨lt_of_not_ge hlow,le_of_not_gt hh⟩
    by_cases htL : t ≤ L
    · right
      apply Finset.sum_congr rfl
      intro p hp
      exact indicator_of_mem (show t ∈ Ioc (L-x p) L from
        ⟨by linarith [(hx p hp).1],htL⟩) _
    · left
      apply Finset.sum_eq_zero
      intro p _
      apply indicator_of_notMem
      exact fun h => htL h.2

/-- Only one separated prime interval can meet the moving cutoff. All
other intervals contribute their complete SIGNED moment, or zero. -/
theorem joint_tail_bound (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (c x : ℕ → ℕ → ℝ) (lo hi : ℕ → ℝ) (L t B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ i ∈ I, ∀ p ∈ P i, lo i ≤ x i p ∧ x i p ≤ hi i)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hpartial : ∀ i ∈ I, t ∈ Ioc (L-hi i) (L-lo i) →
      |tail (P i) (c i) (x i) L t| ≤ B) :
    |∑ i ∈ I, tail (P i) (c i) (x i) L t| ≤
      (∑ i ∈ I, |∑ p ∈ P i, c i p|)+B := by
  let T := I.filter (fun i => t ∈ Ioc (L-hi i) (L-lo i))
  have hcard : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi' j hj'
    obtain ⟨hiI,hti⟩ := Finset.mem_filter.mp hi'
    obtain ⟨hjI,htj⟩ := Finset.mem_filter.mp hj'
    by_contra hne
    rcases hsep i hiI j hjI hne with h | h <;> linarith [hti.1,hti.2,htj.1,htj.2]
  have hp i (hiI : i ∈ I) :
      |tail (P i) (c i) (x i) L t| ≤
        |∑ p ∈ P i, c i p|+(if t ∈ Ioc (L-hi i) (L-lo i) then B else 0) := by
    by_cases ht : t ∈ Ioc (L-hi i) (L-lo i)
    · rw [if_pos ht]
      exact (hpartial i hiI ht).trans (by linarith [abs_nonneg (∑ p ∈ P i, c i p)])
    · rw [if_neg ht,add_zero]
      rcases tail_outside_transition (P i) (c i) (x i) L t (lo i) (hi i) (hx i hiI) ht with he | he
      · rw [he,abs_zero]; exact abs_nonneg _
      · rw [he]
  calc
    _ ≤ ∑ i ∈ I, |tail (P i) (c i) (x i) L t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, (|∑ p ∈ P i, c i p|+
        if t ∈ Ioc (L-hi i) (L-lo i) then B else 0) := Finset.sum_le_sum hp
    _ = (∑ i ∈ I, |∑ p ∈ P i, c i p|)+(T.card : ℝ)*B := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (by
      have hc : (T.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hB)

/-- The entire separated family pays only one partial-tail amplitude.
The total signed moment stays inside its square. No norm is taken separately
for each period's cutoff response. -/
theorem joint_profile_energy (I : Finset ℕ) (P : ℕ → Finset ℕ)
    (c x : ℕ → ℕ → ℝ) (lo hi : ℕ → ℝ) (L : ℝ) {a b B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hedges : ∀ i ∈ I, a ≤ lo i ∧ hi i ≤ b)
    (hx : ∀ i ∈ I, ∀ p ∈ P i, lo i ≤ x i p ∧ x i p ≤ hi i)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hpartial : ∀ i ∈ I, ∀ t ∈ Ioc (L-hi i) (L-lo i),
      |tail (P i) (c i) (x i) L t| ≤ B) (R : ℕ) :
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*
      ((∑ i ∈ I, profile (P i) (c i) (x i) L k)-
        (∑ i ∈ I, profile (P i) (c i) (x i) L (k+1)))^2) ≤
      a*(∑ i ∈ I, ∑ p ∈ P i, c i p)^2+
        (b-a)*((∑ i ∈ I, |∑ p ∈ P i, c i p|)+B)^2 := by
  let U := I.sigma P
  let C := fun ip : (i : ℕ) × ℕ => c ip.1 ip.2
  let X := fun ip : (i : ℕ) × ℕ => x ip.1 ip.2
  have hp k : profile U C X L k = ∑ i ∈ I, profile (P i) (c i) (x i) L k := by
    simp only [profile,U,C,X,Finset.sum_sigma]
  have ht t : tail U C X L t = ∑ i ∈ I, tail (P i) (c i) (x i) L t := by
    simp only [tail,U,C,X,Finset.sum_sigma]
  have hu : ∀ ip ∈ U, a ≤ X ip ∧ X ip ≤ b := by
    intro ip hip
    obtain ⟨hiI,hpi⟩ := Finset.mem_sigma.mp hip
    exact ⟨(hedges ip.1 hiI).1.trans (hx ip.1 hiI ip.2 hpi).1,
      (hx ip.1 hiI ip.2 hpi).2.trans (hedges ip.1 hiI).2⟩
  have hbound (t : ℝ) (_ : t ∈ Ioc (L-b) (L-a)) :
      |tail U C X L t| ≤ (∑ i ∈ I, |∑ p ∈ P i, c i p|)+B := by
    rw [ht]
    exact joint_tail_bound I P c x lo hi L t B hB hx hsep
      (fun i hiI hti => hpartial i hiI t hti)
  have h := profile_energy_bound U C X L ha hab
    (by positivity : 0 ≤ (∑ i ∈ I, |∑ p ∈ P i, c i p|)+B) hu hbound R
  simpa only [hp,U,C,Finset.sum_sigma] using h

/-- A literal clipped weighted prime period has an explicit tail budget.
The interval's actual endpoints and arbitrary phase shift are retained. -/
theorem weighted_tail_bound {a y W D : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (G : ℝ → ℝ) (c L : ℝ) (hD : 0 ≤ D)
    (hG : ∀ t ∈ Icc a (a+2*Real.pi/|y|), |G t| ≤ W)
    (hLip : ∀ t ∈ Icc a (a+2*Real.pi/|y|), ∀ z ∈ Icc a (a+2*Real.pi/|y|),
      |G t-G z| ≤ D*|t-z|) {t : ℝ}
    (ht : t ∈ Ioc (L-(a+2*Real.pi/|y|)) (L-a)) :
    |tail ((Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime)
      (fun p => G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ))
      (fun p => Real.log p) L t| ≤
      (W+D*(2*Real.pi/|y|))*(2/(|y| *a)+4/a^2) := by
  let h := 2*Real.pi/|y|
  let v := L-t
  have hav : a ≤ v := by dsimp [v]; linarith [ht.2]
  have hvb : v ≤ a+h := by dsimp [v,h]; linarith [ht.1]
  have hv0 : 0 < v := by linarith
  have he : t=L-v := by dsimp [v]; ring
  rw [he,tail_eq_prime_interval hav hv0.le]
  have hsub : Icc v (a+h) ⊆ Icc a (a+h) := fun _ hx => ⟨hav.trans hx.1,hx.2⟩
  have hb := weighted_cosine_interval (ha.trans hav) hvb hy (by dsimp [h] at hvb ⊢; linarith)
    G c hD (fun x hx => hG x (hsub hx))
    (fun x hx z hz => hLip x (hsub hx) z (hsub hz))
  apply hb.trans
  apply mul_le_mul
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith : a+h-v ≤ h) hD)
  · apply add_le_add
    · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hav (by positivity))
    · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by linarith : 0 ≤ a) hav 2)
  · positivity
  · have hW : 0 ≤ W := (abs_nonneg (G a)).trans
      (hG a ⟨le_rfl,le_add_of_nonneg_right (by positivity)⟩)
    positivity

/-- Quantitative joint energy for actual separated prime periods. The
single partial-tail price B is an explicit maximum of the individual
numerical caps; all prime-counting premises are discharged. -/
theorem joint_weighted_profile_energy (I : Finset ℕ) (a W D : ℕ → ℝ)
    (G : ℝ → ℝ) (c L y lo hi B : ℝ)
    (hlo : 5000 ≤ lo) (hlh : lo ≤ hi) (hy : 54 ≤ |y|) (hB : 0 ≤ B)
    (hedges : ∀ i ∈ I, lo ≤ a i ∧ a i+2*Real.pi/|y| ≤ hi)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      a i+2*Real.pi/|y| ≤ a j ∨ a j+2*Real.pi/|y| ≤ a i)
    (hW : ∀ i ∈ I, 0 ≤ W i) (hD : ∀ i ∈ I, 0 ≤ D i)
    (hG : ∀ i ∈ I, ∀ t ∈ Icc (a i) (a i+2*Real.pi/|y|), |G t| ≤ W i)
    (hLip : ∀ i ∈ I, ∀ t ∈ Icc (a i) (a i+2*Real.pi/|y|),
      ∀ z ∈ Icc (a i) (a i+2*Real.pi/|y|), |G t-G z| ≤ D i*|t-z|)
    (hcap : ∀ i ∈ I, (W i+D i*(2*Real.pi/|y|))*(2/(|y| *a i)+4/(a i)^2) ≤ B)
    (R : ℕ) :
    let h := 2*Real.pi/|y|;
    let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊ ⌊Real.exp (a i+h)⌋₊).filter Nat.Prime;
    let f := fun k => ∑ i ∈ I, profile (P i)
      (fun p => G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)) (fun p => Real.log p) L k;
    let C := ∑ i ∈ I, (W i*(4/(a i)^2)+D i*h*(2/(|y| *a i)+4/(a i)^2));
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2) ≤
      lo*C^2+(hi-lo)*(C+B)^2 := by
  dsimp only
  let h := 2*Real.pi/|y|
  let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊ ⌊Real.exp (a i+h)⌋₊).filter Nat.Prime
  let z := fun p : ℕ => G (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ)
  let C := ∑ i ∈ I, (W i*(4/(a i)^2)+D i*h*(2/(|y| *a i)+4/(a i)^2))
  have hai i (hiI : i ∈ I) : 5000 ≤ a i := hlo.trans (hedges i hiI).1
  have hm i (hiI : i ∈ I) : |∑ p ∈ P i, z p| ≤
      W i*(4/(a i)^2)+D i*h*(2/(|y| *a i)+4/(a i)^2) :=
    weighted_cosine_period (hai i hiI) hy G c (hD i hiI) (hG i hiI) (hLip i hiI)
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro i hiI
    have hw := hW i hiI
    have hd := hD i hiI
    have ha := hai i hiI
    dsimp [h]
    positivity
  have hsum : (∑ i ∈ I, |∑ p ∈ P i, z p|) ≤ C := Finset.sum_le_sum hm
  have htotal : |∑ i ∈ I, ∑ p ∈ P i, z p| ≤ C := (Finset.abs_sum_le_sum_abs _ _).trans hsum
  have hh := joint_profile_energy I P (fun _ => z) (fun _ p => Real.log p) a
    (fun i => a i+h) L (by linarith : 0 ≤ lo) hlh hB hedges
    (fun i _ p hp => ⟨(prime_interval_logs hp).1.le,(prime_interval_logs hp).2⟩) hsep
    (fun i hiI t ht => (weighted_tail_bound (hai i hiI) hy G c L (hD i hiI)
      (hG i hiI) (hLip i hiI) ht).trans (hcap i hiI)) R
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ lo)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) htotal 2
  · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hlh)
    exact pow_le_pow_left₀ (by positivity) (add_le_add hsum le_rfl) 2

/-- Numerical full-moment cap for one factorial prime period. -/
def factorialMomentCap (a y : ℝ) (j : ℕ) : ℝ :=
  let h := 2*Real.pi/|y|
  let W := Real.exp (-a/2)*(a+h)^j
  W*(4/a^2)+(W*factorialScore a h j)*h*(2/(|y| *a)+4/a^2)

/-- Numerical partial-tail cap for one factorial prime period. -/
def factorialTailCap (a y : ℝ) (j : ℕ) : ℝ :=
  let h := 2*Real.pi/|y|
  let W := Real.exp (-a/2)*(a+h)^j
  (W+(W*factorialScore a h j)*h)*(2/(|y| *a)+4/a^2)

/-- An explicit joint cost: one maximum partial tail and the complete
moment budget. There is no sum of individual square-root energies. -/
def factorialJointEnergy (I : Finset ℕ) (hI : I.Nonempty) (a : ℕ → ℝ)
    (lo hi y : ℝ) (j : ℕ) : ℝ :=
  let C := ∑ i ∈ I, factorialMomentCap (a i) y j
  let B := I.sup' hI (fun i => factorialTailCap (a i) y j)
  lo*C^2+(hi-lo)*(C+B)^2

/-- Every factorial prime order has the joint separated-period energy
bound. All amplitude, derivative and prime-discrepancy inputs are discharged. -/
theorem joint_factorial_profile_energy (I : Finset ℕ) (hI : I.Nonempty) (a : ℕ → ℝ)
    (lo hi y L c : ℝ) (j R : ℕ) (hlo : 5000 ≤ lo) (hlh : lo ≤ hi) (hy : 54 ≤ |y|)
    (hedges : ∀ i ∈ I, lo ≤ a i ∧ a i+2*Real.pi/|y| ≤ hi)
    (hsep : ∀ i ∈ I, ∀ k ∈ I, i ≠ k →
      a i+2*Real.pi/|y| ≤ a k ∨ a k+2*Real.pi/|y| ≤ a i) :
    let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊
      ⌊Real.exp (a i+2*Real.pi/|y|)⌋₊).filter Nat.Prime;
    let f := fun k => ∑ i ∈ I, profile (P i)
      (fun p => factorialAmplitude j (Real.log p)*Real.cos (y*(Real.log p+c))/(p : ℝ))
      (fun p => Real.log p) L k;
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2) ≤
      factorialJointEnergy I hI a lo hi y j := by
  let h := 2*Real.pi/|y|
  let W := fun i => Real.exp (-a i/2)*(a i+h)^j
  let D := fun i => W i*factorialScore (a i) h j
  have hai i (hiI : i ∈ I) : 0 < a i := by have := (hedges i hiI).1; linarith
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hW i (hiI : i ∈ I) : 0 ≤ W i := by have := hai i hiI; dsimp [W]; positivity
  have hD i (hiI : i ∈ I) : 0 ≤ D i := by
    have := hW i hiI
    dsimp only [D,factorialScore]
    positivity
  have hcap i (hiI : i ∈ I) : factorialTailCap (a i) y j ≤
      I.sup' hI (fun i => factorialTailCap (a i) y j) :=
    Finset.le_sup' (fun k => factorialTailCap (a k) y j) hiI
  have hB : 0 ≤ I.sup' hI (fun i => factorialTailCap (a i) y j) := by
    obtain ⟨i,hiI⟩ := hI
    apply (show 0 ≤ factorialTailCap (a i) y j from ?_).trans (hcap i hiI)
    have := hai i hiI
    dsimp [factorialTailCap,factorialScore]
    positivity
  exact joint_weighted_profile_energy I a W D (factorialAmplitude j) c L y lo hi _ hlo hlh hy hB
    hedges hsep hW hD
    (fun i hiI t ht => (factorialAmplitude_bounds j (hai i hiI) hh ht).1)
    (fun i hiI t ht z hz => factorialAmplitude_lipschitz j (hai i hiI) hh ht hz)
    hcap R

private theorem joint_phase_square (I : Finset ℕ) (G : ℝ → ℝ) (a : ℕ → ℝ)
    (y L v : ℝ) (hy : y ≠ 0) (n : ℕ) :
    (∑ i ∈ I, weightedResponse G (a i) y L v n)^2 ≤
      (∑ i ∈ I, weightedResponse G (a i) y L 0 n)^2+
        (∑ i ∈ I, weightedResponse G (a i) y L (Real.pi/(2*y)) n)^2 := by
  have he : (∑ i ∈ I, weightedResponse G (a i) y L v n) =
      Real.cos (y*v)*(∑ i ∈ I, weightedResponse G (a i) y L 0 n)+
        Real.sin (y*v)*(∑ i ∈ I, weightedResponse G (a i) y L (Real.pi/(2*y)) n) := by
    simp_rw [weighted_phase G _ y L hy v n]
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  rw [he]
  let C := ∑ i ∈ I, weightedResponse G (a i) y L 0 n
  let D := ∑ i ∈ I, weightedResponse G (a i) y L (Real.pi/(2*y)) n
  have hs : (Real.cos (y*v)*C+Real.sin (y*v)*D)^2+
      (Real.sin (y*v)*C-Real.cos (y*v)*D)^2 = C^2+D^2 := by
    calc
      _ = (Real.sin (y*v)^2+Real.cos (y*v)^2)*(C^2+D^2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq,one_mul]
  nlinarith only [hs,sq_nonneg (Real.sin (y*v)*C-Real.cos (y*v)*D)]

/-- All neighbouring factorial prime periods are combined before the
squarefree mean. Arbitrary cofactor phases remain correlated with them. -/
theorem exists_joint_factorial_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (hI : I.Nonempty) (a : ℕ → ℝ)
      (lo hi y L : ℝ) (j X : ℕ) (S : Finset ℕ) (c : ℕ → ℝ),
      5000 ≤ lo → lo ≤ hi → 54 ≤ |y| →
      (∀ i ∈ I, lo ≤ a i ∧ a i+2*Real.pi/|y| ≤ hi) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k →
        a i+2*Real.pi/|y| ≤ a k ∨ a k+2*Real.pi/|y| ≤ a i) →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L (c n) n)^2) ≤
        E*X*factorialJointEnergy I hI a lo hi y j := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_divisor_profile_mean
  refine ⟨2*E,by positivity,fun I hI a lo hi y L j X S c hlo hlh hy hedges hsep hS hSF => ?_⟩
  let R := ⌊Real.exp L⌋₊
  have hR : Real.exp L < R+1 := Nat.lt_floor_add_one (Real.exp L)
  let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊
    ⌊Real.exp (a i+2*Real.pi/|y|)⌋₊).filter Nat.Prime
  have hconst v : (∑ n ∈ S,
      (∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L v n)^2) ≤
        E*X*factorialJointEnergy I hI a lo hi y j := by
    let f := fun k => ∑ i ∈ I, profile (P i)
      (fun p => factorialAmplitude j (Real.log p)*Real.cos (y*(Real.log p+v))/(p : ℝ))
      (fun p => Real.log p) L k
    have hf : f (R+1)=0 := Finset.sum_eq_zero (fun i _ =>
      profile_endpoint (P i) _ _ L R hR (fun p _ => Real.log_natCast_nonneg p))
    have he n (hn : n ∈ S) : (∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L v n) =
        ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
      simp_rw [weighted_response_profile (factorialAmplitude j) _ y L v R hR
        (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega : 0 < n)]
      rw [Finset.sum_comm]
      simp only [f,Finset.sum_mul,P]
    rw [Finset.sum_congr rfl (fun n hn => congrArg (fun x : ℝ => x^2) (he n hn))]
    exact (hmean X R S f hS hSF hf).trans (mul_le_mul_of_nonneg_left
      (joint_factorial_profile_energy I hI a lo hi y L v j R hlo hlh hy hedges hsep) (by positivity))
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ S) =>
    joint_phase_square I (factorialAmplitude j) a y L (c n) (abs_pos.mp (by linarith : 0 < |y|)) n)
  rw [Finset.sum_add_distrib] at hs
  nlinarith only [hs,hconst 0,hconst (Real.pi/(2*y))]

/-- Reciprocal cofactor weights pay their energy after combining all
periods. Both signed sides use the square root of one joint energy. -/
theorem exists_joint_factorial_shell_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (hI : I.Nonempty) (a : ℕ → ℝ)
      (lo hi y L V : ℝ) (j M : ℕ) (S : Finset ℕ) (c w : ℕ → ℝ),
      5000 ≤ lo → lo ≤ hi → 54 ≤ |y| → 0 ≤ V → 1 ≤ M →
      (∀ i ∈ I, lo ≤ a i ∧ a i+2*Real.pi/|y| ≤ hi) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k →
        a i+2*Real.pi/|y| ≤ a k ∨ a k+2*Real.pi/|y| ≤ a i) →
      S ⊆ Finset.Ioc M (2*M) → (∀ n ∈ S, Squarefree n) →
      (∀ n ∈ S, |w n| ≤ V/n) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L (c n) n);
      let K := Real.sqrt E*V*Real.sqrt (factorialJointEnergy I hI a lo hi y j);
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_joint_factorial_mean
  refine ⟨2*E,by positivity,fun I hI a lo hi y L V j M S c w hlo hlh hy hV hM hedges hsep hS hSF hw => ?_⟩
  dsimp only
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
  let Q := factorialJointEnergy I hI a lo hi y j
  have hQ : 0 ≤ Q := by
    have hlo0 : 0 ≤ lo := by linarith
    have hlen : 0 ≤ hi-lo := sub_nonneg.mpr hlh
    dsimp [Q,factorialJointEnergy]
    positivity
  have hm := hmean I hI a lo hi y L j (2*M) S c hlo hlh hy hedges hsep hSI hSF
  change _ ≤ E*(2*M : ℕ)*Q at hm
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => ∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L (c n) n)).trans
      (mul_le_mul hwE hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have he : V^2/M*(E*(2*M)*Q) = 2*E*V^2*Q := by field_simp
  push_cast at hs
  rw [he] at hs
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hQ]
  nlinarith only [hs]

/-- A joint signed bound for the ORIGINAL retained carrier over a separated
family of prime periods. Its single cofactor population, all factorial orders,
allocation and complex product phase are retained. The numerical square root
is taken only after all periods have been combined. -/
theorem exists_literal_joint_period_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (hI : I.Nonempty) (A : Finset ℕ)
      (N M : ℕ) (S : Finset ℕ) (a : ℕ → ℝ) (lo hi y L : ℝ),
      1 ≤ M → 5000 ≤ lo → lo ≤ hi → 54 ≤ |y| → 0 < L →
      (∀ i ∈ I, lo ≤ a i ∧ a i+2*Real.pi/|y| ≤ hi) →
      (∀ i ∈ I, ∀ k ∈ I, i ≠ k →
        a i+2*Real.pi/|y| ≤ a k ∨ a k+2*Real.pi/|y| ≤ a i) →
      S ⊆ Finset.Ioc M (2*M) → (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊
        ⌊Real.exp (a i+2*Real.pi/|y|)⌋₊).filter Nat.Prime;
      (∀ i ∈ I, P i ⊆ A) → (∀ n ∈ S, ∀ i ∈ I, ∀ p ∈ P i, ¬p ∣ n) →
      let J := (∑ n ∈ S, ∑ i ∈ I, ∑ p ∈ P i,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let K := Real.sqrt E/(L*N.factorial)*Real.exp (-Real.log M/2)*
        (∑ j ∈ Finset.range (N+2), ((N+1).choose j : ℝ)*Real.log (2*M : ℕ)^(N+1-j)*
          Real.sqrt (factorialJointEnergy I hI a lo hi y j));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_factorial_shell_bounds
  refine ⟨E,hE,fun I hI A N M S a lo hi y L hM hlo hlh hy hL hedges hsep hS hSF hPA hcop => ?_⟩
  dsimp only
  let P := fun i => (Finset.Ioc ⌊Real.exp (a i)⌋₊
    ⌊Real.exp (a i+2*Real.pi/|y|)⌋₊).filter Nat.Prime
  have hex n (hn : n ∈ S) :=
    ZetaRieszRetainedFactorial.exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let w := fun j n => if hn : n ∈ S then Real.exp (-Real.log n/2)*B n hn j/(n : ℝ) else 0
  let V := fun j => Real.exp (-Real.log M/2)*((N+1).choose j : ℝ)*Real.log (2*M : ℕ)^(N+1-j)
  let Q := factorialJointEnergy I hI a lo hi y
  have hw j (hj : j ∈ Finset.range (N+2)) n (hn : n ∈ S) : |w j n| ≤ V j/n := by
    have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
    have hMn := Finset.mem_Ioc.mp (hS hn)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log M ≤ Real.log n := Real.log_le_log hM0 (by exact_mod_cast hMn.1.le)
    have hlog' : Real.log n ≤ Real.log (2*M : ℕ) := Real.log_le_log hn0 (by exact_mod_cast hMn.2)
    have hb0 := (hcoef n hn j hjN).1
    have hb := (hcoef n hn j hjN).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hlog' _) (Nat.cast_nonneg _))
    dsimp only [w,V]
    rw [dif_pos hn,abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ hn0.le
    simpa only [mul_assoc] using mul_le_mul
      (Real.exp_le_exp.mpr (show -Real.log n/2 ≤ -Real.log M/2 by linarith))
      hb hb0 (Real.exp_pos (-Real.log M/2)).le
  have hi' n (hn : n ∈ S) i (hiI : i ∈ I) :
      (∑ p ∈ P i, ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
        w j n*weightedResponse (factorialAmplitude j) (a i) y L (Real.log n) n) := by
    rw [Complex.re_sum]
    have he p (hp : p ∈ P i) := ZetaRieszRetainedFactorial.atom_expansion A N L y
      (hSF n hn).1 (hSF n hn).2 (Finset.mem_filter.mp hp).2 (hcop n hn i hiI p hp)
      (B n hn) (hid n hn p (Finset.mem_filter.mp hp).2 (hPA i hiI hp) (hcop n hn i hiI p hp))
    rw [Finset.sum_congr rfl he,← Finset.mul_sum,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [weightedResponse,w]
    rw [dif_pos hn,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htotal :
      (∑ n ∈ S, ∑ i ∈ I, ∑ p ∈ P i,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2),
        ∑ n ∈ S, w j n*(∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L (Real.log n) n)) := by
    simp only [Complex.re_sum]
    have hn n (hn : n ∈ S) := Finset.sum_congr rfl (hi' n hn)
    simp only [Complex.re_sum] at hn
    rw [Finset.sum_congr rfl hn]
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hj j (hj : j ∈ Finset.range (N+2)) :
      |∑ n ∈ S, w j n*(∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L (Real.log n) n)| ≤
        Real.sqrt E*V j*Real.sqrt (Q j) :=
    abs_le.mpr (hbound I hI a lo hi y L (V j) j M S (fun n => Real.log n) (w j)
      hlo hlh hy (by dsimp [V]; positivity) hM hedges hsep hS (fun n hn => (hSF n hn).1) (hw j hj))
  have hs := (Finset.abs_sum_le_sum_abs
    (fun j => ∑ n ∈ S, w j n*(∑ i ∈ I, weightedResponse (factorialAmplitude j) (a i) y L (Real.log n) n))
    (Finset.range (N+2))).trans (Finset.sum_le_sum hj)
  apply abs_le.mp
  rw [htotal,abs_mul,abs_div,abs_neg,abs_one,abs_of_pos (show 0 < L*(N.factorial : ℝ) by positivity)]
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1/(L*(N.factorial : ℝ)))).trans_eq
  dsimp only [V]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RiemannGaussian.ZetaRieszJointPeriodEnergy
