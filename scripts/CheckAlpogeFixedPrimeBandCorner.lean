import CheckAlpogeFixedPrimeBandCentered
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! # Möbius cancellation across the changes of cofactor in the fixed prime band -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Finset Real
open scoped ArithmeticFunction.Moebius

private theorem telescope {D U : ℕ} (hDU : D < U) (w : ℕ → ℝ) :
    ∑ j ∈ Ioc D U, (w j-w (j+1)) = w (D+1)-w (U+1) := by
  rw [show Ioc D U = Ico (D+1) (U+1) by ext j; simp only [mem_Ioc,mem_Ico]; omega]
  simpa only [← sum_neg_distrib,neg_sub] using
    congrArg Neg.neg (sum_Ico_sub w (by omega : D+1 ≤ U+1))

private theorem by_prefix (D U : ℕ) (c w : ℕ → ℝ) (hz : w (U+1)=0) :
    ∑ a ∈ Ioc D U, c a*w a =
      ∑ i ∈ Ioc D U, (∑ a ∈ Ioc D i, c a)*(w i-w (i+1)) := by
  let I := Ioc D U
  have htel (a : ℕ) (ha : a ∈ I) :
      (∑ i ∈ I, if a ≤ i then w i-w (i+1) else 0) = w a := by
    rw [← sum_filter,show I.filter (fun i => a ≤ i)=Ioc (a-1) U by
      ext i; have := mem_Ioc.mp ha; simp only [I,mem_filter,mem_Ioc]; omega,
      telescope (by have := mem_Ioc.mp ha; omega),hz,sub_zero,
      Nat.sub_add_cancel (by have := mem_Ioc.mp ha; omega : 1 ≤ a)]
  have hp (i : ℕ) (hi : i ∈ I) : (∑ a ∈ I, if a ≤ i then c a else 0)=∑ a ∈ Ioc D i, c a := by
    rw [← sum_filter,show I.filter (fun a => a ≤ i)=Ioc D i by
      ext a; have := mem_Ioc.mp hi; simp only [I,mem_filter,mem_Ioc]; omega]
  change (∑ a ∈ I, _) = ∑ i ∈ I, _
  calc
    _ = ∑ a ∈ I, ∑ i ∈ I, if a ≤ i then c a*(w i-w (i+1)) else 0 := by
      apply sum_congr rfl
      intro a ha
      rw [← htel a ha,mul_sum]
      exact sum_congr rfl fun i _ => by split_ifs <;> simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [← hp i hi,sum_mul]
      exact sum_congr rfl fun a _ => by split_ifs <;> simp

private def cornerSum (D U : ℕ) (x y : ℕ → ℝ) (K : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Ioc D U, x a*∑ b ∈ Ioc D U, y b*K a b

private def localSum (D : ℕ) (x : ℕ → ℝ) (i : ℕ) := ∑ a ∈ Ioc D i, x a

private def mixedDiff (K : ℕ → ℕ → ℝ) (i j : ℕ) :=
  (K i j-K (i+1) j)-(K i (j+1)-K (i+1) (j+1))

private theorem corner_expand {D U : ℕ} (x y : ℕ → ℝ) {K : ℕ → ℕ → ℝ}
    (ha : ∀ j, K (U+1) j=0) (hb : ∀ i, K i (U+1)=0) :
    cornerSum D U x y K = ∑ i ∈ Ioc D U, ∑ j ∈ Ioc D U,
      (localSum D x i*localSum D y j)*mixedDiff K i j := by
  let I := Ioc D U
  let R (i j : ℕ) := K i j-K (i+1) j
  unfold cornerSum
  rw [by_prefix D U x (fun a => ∑ b ∈ I, y b*K a b) (by simp [ha])]
  apply sum_congr rfl
  intro i _
  have hr : (∑ b ∈ I, y b*K i b)-(∑ b ∈ I,y b*K (i+1) b)=∑ b ∈ I,y b*R i b := by
    simp only [R,mul_sub,sum_sub_distrib]
  rw [hr,by_prefix D U y (R i) (by simp [R,hb]),mul_sum]
  exact sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

private theorem corner_abel {D U : ℕ} (hDU : D < U) {x y : ℕ → ℝ} {K : ℕ → ℕ → ℝ}
    (ha : ∀ j, K (U+1) j=0) (hb : ∀ i, K i (U+1)=0)
    (hm : ∀ i ∈ Ioc D U, ∀ j ∈ Ioc D U,
      K i (j+1)-K (i+1) (j+1) ≤ K i j-K (i+1) j)
    {X Y : ℝ} (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ X)
    (hy : ∀ j ∈ Ioc D U, |∑ b ∈ Ioc D j, y b| ≤ Y) :
    |cornerSum D U x y K| ≤ X*Y*K (D+1) (D+1) := by
  let I := Ioc D U
  let P (i : ℕ) := ∑ a ∈ Ioc D i, x a
  let S (j : ℕ) := ∑ b ∈ Ioc D j, y b
  let R (i j : ℕ) := K i j-K (i+1) j
  let Δ (i j : ℕ) := R i j-R i (j+1)
  have he : cornerSum D U x y K = ∑ i ∈ I, ∑ j ∈ I, (P i*S j)*Δ i j := by
    exact corner_expand x y ha hb
  have hmass : (∑ i ∈ I, ∑ j ∈ I, Δ i j) = K (D+1) (D+1) := by
    dsimp only [I,Δ]
    simp_rw [telescope hDU,show ∀ i, R i (U+1)=0 by intro i; simp [R,hb],sub_zero]
    dsimp only [R]
    rw [telescope hDU (fun i => K i (D+1)),ha,sub_zero]
  rw [he,← hmass,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  rw [mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j hj
  have hΔ : 0 ≤ Δ i j := sub_nonneg.mpr (hm i hi j hj)
  rw [abs_mul,abs_mul,abs_of_nonneg hΔ]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hx i hi) (hy j hj) (abs_nonneg _) ((abs_nonneg _).trans (hx i hi))) hΔ

private def cornerHinge (s t : ℝ) : ℝ := max (s*t-1) 0

private theorem hinge_diff {s t v : ℝ} (hst : t ≤ s) (hv : 0 ≤ v) :
    cornerHinge s v-cornerHinge t v = min (cornerHinge s v) ((s-t)*v) := by
  have hts := mul_le_mul_of_nonneg_right hst hv
  unfold cornerHinge
  by_cases h₁ : 0 ≤ t*v-1
  · rw [max_eq_left h₁,max_eq_left (by linarith),min_eq_right (by nlinarith)]
    ring
  · rw [max_eq_right (by linarith : t*v-1 ≤ 0),sub_zero,min_eq_left (max_le (by nlinarith)
      (mul_nonneg (sub_nonneg.mpr hst) hv))]

private theorem hinge_mixed {u v : ℕ → ℝ} {i j : ℕ}
    (hu : u (i+1) ≤ u i) (hv : v (j+1) ≤ v j) (h₀ : 0 ≤ v (j+1)) :
    cornerHinge (u i) (v (j+1))-cornerHinge (u (i+1)) (v (j+1)) ≤
      cornerHinge (u i) (v j)-cornerHinge (u (i+1)) (v j) := by
  rw [hinge_diff hu h₀,hinge_diff hu (h₀.trans hv)]
  by_cases hp : 0 ≤ u i
  · exact min_le_min (max_le_max_right _ (by nlinarith only [mul_le_mul_of_nonneg_left hv hp]))
      (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hu))
  · have h (z : ℝ) (hz : 0 ≤ z) : cornerHinge (u i) z=0 :=
      max_eq_right (by linarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) hz])
    rw [h _ h₀,h _ (h₀.trans hv),min_eq_left (mul_nonneg (sub_nonneg.mpr hu) h₀),
      min_eq_left (mul_nonneg (sub_nonneg.mpr hu) (h₀.trans hv))]

/-- Summing positive mixed differences against squared running sums allows isolated
large prefixes. Symmetry identifies the two one-dimensional marginals. -/
private theorem corner_energy {D U : ℕ} (hDU : D < U) (x y : ℕ → ℝ) {K : ℕ → ℕ → ℝ}
    (ha : ∀ j, K (U+1) j=0) (hb : ∀ i, K i (U+1)=0)
    (hs : ∀ i j, K i j=K j i) (hm : ∀ i ∈ Ioc D U, ∀ j ∈ Ioc D U, 0 ≤ mixedDiff K i j)
    {d : ℝ} (hd : ∀ i ∈ Ioc D U, K i (D+1)-K (i+1) (D+1) ≤ d) :
    |cornerSum D U x y K| ≤ (∑ i ∈ Ioc D U, ((localSum D x i)^2+(localSum D y i)^2))*d/2 := by
  let I := Ioc D U
  let Δ := mixedDiff K
  let P := localSum D x
  let S := localSum D y
  have hsym (i j : ℕ) : Δ i j=Δ j i := by
    dsimp only [Δ,mixedDiff]
    rw [hs i j,hs (i+1) j,hs i (j+1),hs (i+1) (j+1)]
    ring
  have hrow (i : ℕ) : ∑ j ∈ I, Δ i j=K i (D+1)-K (i+1) (D+1) := by
    change (∑ j ∈ Ioc D U, ((fun j => K i j-K (i+1) j) j-(fun j => K i j-K (i+1) j) (j+1)))=_
    rw [telescope hDU,hb,hb]; ring
  have hbnd (w : ℕ → ℝ) : (∑ i ∈ I, ∑ j ∈ I, w i^2*Δ i j) ≤ (∑ i ∈ I, w i^2)*d := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    rw [← mul_sum,hrow]
    exact mul_le_mul_of_nonneg_left (hd i hi) (sq_nonneg _)
  have hswap : (∑ i ∈ I, ∑ j ∈ I, S j^2*Δ i j) = ∑ i ∈ I, ∑ j ∈ I, S i^2*Δ i j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hsym]
  rw [corner_expand x y ha hb]
  change |∑ i ∈ I, ∑ j ∈ I, (P i*S j)*Δ i j| ≤ _
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, (P i^2*Δ i j+S j^2*Δ i j)/2 := by
      apply sum_le_sum
      intro i hi
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro j hj
      rw [abs_mul,abs_mul,abs_of_nonneg (hm i hi j hj)]
      have h : |P i| * |S j| ≤ (P i^2+S j^2)/2 := by
        nlinarith only [sq_nonneg (|P i|-|S j|),sq_abs (P i),sq_abs (S j)]
      exact (mul_le_mul_of_nonneg_right h (hm i hi j hj)).trans_eq (by ring)
    _ ≤ _ := by
      simp only [← sum_div,sum_add_distrib,hswap]
      exact (div_le_div_of_nonneg_right (add_le_add (hbnd P) (hbnd S)) (by norm_num : (0:ℝ) ≤ 2)).trans_eq
        (by dsimp only [I,P,S]; rw [add_mul])

private def cornerCoord (U a : ℕ) : ℝ := if a ≤ U then (U:ℝ)/a else 0

private theorem coord_nonneg (U a : ℕ) : 0 ≤ cornerCoord U a := by
  unfold cornerCoord; split <;> positivity

private theorem coord_anti {U i : ℕ} (hi : 0 < i) : cornerCoord U (i+1) ≤ cornerCoord U i := by
  by_cases h : i+1 ≤ U
  · simp only [cornerCoord,ite_eq_left h,ite_eq_left (by omega : i ≤ U)]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr hi) (by norm_num)
  · simp only [cornerCoord,ite_eq_right h]
    split <;> positivity

private theorem coord_bounds {D U H a : ℕ} (ha : a ∈ Ioc D U) (hscale : U ≤ H*(D+1)) :
    1 ≤ cornerCoord U a ∧ cornerCoord U a ≤ H := by
  obtain ⟨hD,hU⟩ := mem_Ioc.mp ha
  rw [cornerCoord,ite_eq_left hU]
  have ha₀ : 0 < (a:ℝ) := Nat.cast_pos.mpr (by omega)
  exact ⟨(one_le_div ha₀).mpr (by exact_mod_cast hU), (div_le_iff₀ ha₀).mpr
    (by exact_mod_cast hscale.trans (Nat.mul_le_mul_left H hD))⟩

private theorem corner_hinge_exact {D U : ℕ} (hDU : D < U)
    {r X Y : ℝ} (hr : 0 < r) {x y : ℕ → ℝ}
    (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ X)
    (hy : ∀ j ∈ Ioc D U, |∑ b ∈ Ioc D j, y b| ≤ Y) :
    |cornerSum D U x y (fun a b => max (cornerCoord U a*cornerCoord U b/r-1) 0)| ≤
      X*Y*max (cornerCoord U (D+1)*cornerCoord U (D+1)/r-1) 0 := by
  let u := cornerCoord U
  have hform (a b : ℕ) : max (u a*u b/r-1) 0=cornerHinge (u a/r) (u b) := by
    unfold cornerHinge; rw [div_mul_eq_mul_div]
  simp_rw [show ∀ a b, max (cornerCoord U a*cornerCoord U b/r-1) 0=cornerHinge (u a/r) (u b) from hform]
  have hz : u (U+1)=0 := by simp [u,cornerCoord]
  exact corner_abel hDU (fun _ => by simp [cornerHinge,hz]) (fun _ => by simp [cornerHinge,hz])
    (fun i hi j hj => hinge_mixed (u := fun i => u i/r) (v := u)
      (div_le_div_of_nonneg_right (coord_anti (by have := mem_Ioc.mp hi; omega)) hr.le)
      (coord_anti (by have := mem_Ioc.mp hj; omega)) (coord_nonneg _ _)) hx hy

private theorem corner_hinge_bound {D U H : ℕ} (hDU : D < U) (hscale : U ≤ H*(D+1))
    {r X Y : ℝ} (hr : 0 < r) {x y : ℕ → ℝ}
    (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ X)
    (hy : ∀ j ∈ Ioc D U, |∑ b ∈ Ioc D j, y b| ≤ Y) :
    |cornerSum D U x y (fun a b => max (cornerCoord U a*cornerCoord U b/r-1) 0)| ≤
      X*Y*((H:ℝ)^2/r) := by
  let u := cornerCoord U
  have hi : D+1 ∈ Ioc D U := mem_Ioc.mpr ⟨by omega,hDU⟩
  have h := (coord_bounds hi hscale).2
  apply (corner_hinge_exact hDU hr hx hy).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg ((abs_nonneg _).trans (hx _ hi)) ((abs_nonneg _).trans (hy _ hi)))
  have hs : u (D+1)*u (D+1) ≤ (H:ℝ)^2 := by
    rw [pow_two]; exact mul_le_mul h h (coord_nonneg _ _) (Nat.cast_nonneg _)
  exact max_le ((sub_le_self _ zero_le_one).trans (div_le_div_of_nonneg_right hs hr.le)) (by positivity)

private theorem weighted_prefix {D U : ℕ} {x w : ℕ → ℝ} {E : ℝ}
    (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ E)
    (hw : ∀ i ∈ Ioc D U, 0 ≤ w i)
    (ha : ∀ i ∈ Ioc D U, i < U → w (i+1) ≤ w i)
    {j : ℕ} (hj : j ∈ Ioc D U) :
    |∑ a ∈ Ioc D j, x a*w a| ≤ E*w (D+1) := by
  let v (a : ℕ) := if a ≤ j then w a else 0
  have hDj := (mem_Ioc.mp hj).1
  have hjU := (mem_Ioc.mp hj).2
  have hz : v (j+1)=0 := by simp [v]
  have he (i : ℕ) (hi : i ∈ Ioc D j) : v i=w i := ite_eq_left (mem_Ioc.mp hi).2
  have hd (i : ℕ) (hi : i ∈ Ioc D j) : 0 ≤ v i-v (i+1) := by
    rw [he i hi]
    by_cases hij : i+1 ≤ j
    · exact sub_nonneg.mpr ((ite_eq_left hij : v (i+1)=w (i+1)).trans_le
        (ha _ (Ioc_subset_Ioc_right hjU hi) (by omega)))
    · rw [show v (i+1)=0 from ite_eq_right hij,sub_zero]
      exact hw _ (Ioc_subset_Ioc_right hjU hi)
  rw [sum_congr rfl (fun a ha => congrArg (x a*·) (he a ha).symm),by_prefix D j x v hz]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ Ioc D j, E*(v i-v (i+1)) := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (hd i hi)]
      exact mul_le_mul_of_nonneg_right (hx _ (Ioc_subset_Ioc_right hjU hi)) (hd i hi)
    _ = _ := by rw [← mul_sum,telescope hDj,hz,sub_zero,he _ (mem_Ioc.mpr ⟨by omega,hDj⟩)]

private theorem corner_log_prefix {D U H : ℕ} (hscale : U ≤ H*(D+1)) {x : ℕ → ℝ} {E : ℝ}
    (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ E) {j : ℕ} (hj : j ∈ Ioc D U) :
    |∑ a ∈ Ioc D j, x a*log (cornerCoord U a)| ≤ E*log H := by
  have hi : D+1 ∈ Ioc D U := mem_Ioc.mpr ⟨by omega,(mem_Ioc.mp hj).1.trans_le (mem_Ioc.mp hj).2⟩
  apply (weighted_prefix hx (fun i h => log_nonneg (coord_bounds h hscale).1)
    (fun i h hl => log_le_log (zero_lt_one.trans_le (coord_bounds (a := i+1)
      (mem_Ioc.mpr ⟨by have := (mem_Ioc.mp h).1; omega,hl⟩) hscale).1)
      (coord_anti (by have := (mem_Ioc.mp h).1; omega))) hj).trans
  exact mul_le_mul_of_nonneg_left (log_le_log (zero_lt_one.trans_le (coord_bounds hi hscale).1)
    (coord_bounds hi hscale).2) ((abs_nonneg _).trans (hx j hj))

private theorem centered_zero {z : ℝ} (hz : 0 ≤ z) (h₁ : z ≤ 1) : fixedBandCenteredKernel z=0 := by
  have h {r : ℝ} (hr : 0 ≤ r) (h : r ≤ 1) : fixedBandUnitRamp r=0 := by
    rw [← fixedBandUnitRamp_sum hr h]
    norm_num [max_eq_right (sub_nonpos.mpr h)]
  rw [fixedBandCenteredKernel,fixedBandLattice_ramps hz,h hz h₁,
    h (by positivity : 0 ≤ z/2) (by linarith),h (by positivity : 0 ≤ z/4) (by linarith)]
  ring

private theorem product_multiples {N a b J : ℕ} (hp : 0 < a*b) (hcap : N/(a*b) ≤ J) :
    fixedBandProductEntry N a b = ∑ j ∈ Ioc 0 J, fixedBandCenteredKernel ((N:ℝ)/(a*b)/j) := by
  let p := a*b
  let f (k : ℕ) := fixedBandCenteredKernel ((N:ℝ)/k)
  let g (j : ℕ) := f (p*j)
  have h : (∑ j ∈ Ioc 0 (N/p), g j) = ∑ k ∈ (Ioc 0 N).filter (fun k => p ∣ k), f k := by
    apply sum_bij (fun j _ => p*j)
    · intro j hj
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hp (mem_Ioc.mp hj).1,?_⟩,dvd_mul_right _ _⟩
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp (mem_Ioc.mp hj).2
    · exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp h
    · intro k hk
      obtain ⟨hk,⟨j,rfl⟩⟩ := mem_filter.mp hk
      refine ⟨j,mem_Ioc.mpr ⟨Nat.pos_of_ne_zero (fun he => by simp [he] at hk),?_⟩,rfl⟩
      exact (Nat.le_div_iff_mul_le hp).mpr (by simpa only [mul_comm] using (mem_Ioc.mp hk).2)
    · intros; rfl
  change (∑ k ∈ Ioc 0 N, if p ∣ k then f k else 0) = _
  rw [← sum_filter,← h]
  calc
    _ = ∑ j ∈ Ioc 0 J, g j := by
      apply sum_subset (Ioc_subset_Ioc_right hcap)
      intro j hj hout
      have hj₀ := (mem_Ioc.mp hj).1
      have hjg : N/p < j := lt_of_not_ge (fun h => hout (mem_Ioc.mpr ⟨hj₀,h⟩))
      have hjp : N < p*j := by simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul hp).mp hjg
      exact centered_zero (by positivity)
        ((div_le_one (Nat.cast_pos.mpr (Nat.mul_pos hp hj₀))).mpr (by exact_mod_cast hjp.le))
    _ = _ := sum_congr rfl fun j _ => by simp only [g,f,p,Nat.cast_mul,div_div]

private theorem corner_congr {D U : ℕ} {x y : ℕ → ℝ} {f g : ℕ → ℕ → ℝ}
    (he : ∀ a ∈ Ioc D U, ∀ b ∈ Ioc D U, f a b=g a b) :
    cornerSum D U x y f=cornerSum D U x y g :=
  sum_congr rfl fun a ha => congrArg (x a*·) (sum_congr rfl fun b hb => congrArg (y b*·) (he a ha b hb))

private theorem corner_sum {D U : ℕ} (x y : ℕ → ℝ) {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℕ → ℝ) :
    cornerSum D U x y (fun a b => ∑ i ∈ S, f i a b) = ∑ i ∈ S, cornerSum D U x y (f i) := by
  simp only [cornerSum,mul_sum]
  rw [sum_comm (s := S)]
  apply sum_congr rfl
  intro a _
  rw [sum_comm (s := S)]

private def rampBox (D U : ℕ) (x y : ℕ → ℝ) (k : ℝ) :=
  cornerSum D U x y (fun a b => fixedBandUnitRamp (cornerCoord U a*cornerCoord U b/k))

private theorem rampBox_bound {D U H : ℕ} (hDU : D < U) (hscale : U ≤ H*(D+1))
    {k X Y : ℝ} (hk : 1 ≤ k) {x y : ℕ → ℝ}
    (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ X)
    (hy : ∀ j ∈ Ioc D U, |∑ b ∈ Ioc D j, y b| ≤ Y) :
    |rampBox D U x y k| ≤ X*Y*(H:ℝ)^2*(1+log (H^2:ℕ))/k := by
  let J := H^2
  let u := cornerCoord U
  let Z := X*Y*(H:ℝ)^2/k
  have hi : D+1 ∈ Ioc D U := mem_Ioc.mpr ⟨by omega,hDU⟩
  have hX := (abs_nonneg _).trans (hx _ hi)
  have hY := (abs_nonneg _).trans (hy _ hi)
  have hk₀ := zero_lt_one.trans_le hk
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have he : rampBox D U x y k=∑ d ∈ Ioc 0 J, cornerSum D U x y
      (fun a b => max (u a*u b/(k*d)-1) 0) := by
    rw [← corner_sum]
    apply corner_congr
    intro a ha b hb
    have h₀ := coord_nonneg U a
    have h₁ := coord_nonneg U b
    have hcap : u a*u b/k ≤ (J:ℝ) := by
      apply (div_le_iff₀ hk₀).mpr
      have hh := mul_le_mul (coord_bounds ha hscale).2 (coord_bounds hb hscale).2 h₁ (Nat.cast_nonneg _)
      have hk' := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (α := ℝ) J)
      dsimp only [J] at hk' ⊢
      push_cast at hk' ⊢
      nlinarith only [hh,hk']
    change fixedBandUnitRamp (u a*u b/k) = _
    rw [← fixedBandUnitRamp_sum (div_nonneg (mul_nonneg h₀ h₁) hk₀.le) hcap,Nat.floor_natCast]
    exact sum_congr rfl fun d _ => by rw [div_div]
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 J, Z*(d:ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      apply (corner_hinge_bound hDU hscale (mul_pos hk₀ (Nat.cast_pos.mpr (mem_Ioc.mp hd).1)) hx hy).trans_eq
      dsimp [Z]; ring
    _ ≤ Z*(1+log J) := by
      have hh := harmonic_le_one_add_log J
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hh
      rw [← mul_sum,show Ioc 0 J=Icc 1 J by ext d; simp only [mem_Ioc,mem_Icc]; omega]
      exact mul_le_mul_of_nonneg_left hh hZ
    _ = _ := by dsimp [J,Z]; ring

private def latticeBox (D U : ℕ) (x y : ℕ → ℝ) (j : ℝ) :=
  rampBox D U x y j-3*rampBox D U x y (j*2)+2*rampBox D U x y (j*4)

private def logWeight (U : ℕ) (x : ℕ → ℝ) (a : ℕ) := x a*log (cornerCoord U a)

private theorem corner_term {D U H j : ℕ} (hscale : U ≤ H*(D+1)) (hj : 0 < j) (x y : ℕ → ℝ) :
    cornerSum D U x y (fun a b => fixedBandCenteredKernel (cornerCoord U a*cornerCoord U b/j)) =
      log 2*(rampBox D U x y j-rampBox D U x y (j*2))-
      (fixedBandLogConstant-log j)*latticeBox D U x y j-
      latticeBox D U (logWeight U x) y j-latticeBox D U x (logWeight U y) j := by
  let u := cornerCoord U
  let z (a b : ℕ) := u a*u b/j
  let A (a b : ℕ) (h : ℝ) := fixedBandUnitRamp (z a b/h)
  let W (a b : ℕ) := A a b 1-3*A a b 2+2*A a b 4
  have he (a : ℕ) (ha : a ∈ Ioc D U) (b : ℕ) (hb : b ∈ Ioc D U) :
      fixedBandCenteredKernel (z a b)=log 2*(A a b 1-A a b 2)-
      (fixedBandLogConstant-log j)*W a b-log (u a)*W a b-log (u b)*W a b := by
    have ha₀ := zero_lt_one.trans_le (coord_bounds ha hscale).1
    have hb₀ := zero_lt_one.trans_le (coord_bounds hb hscale).1
    have hz : 0 ≤ z a b := div_nonneg (mul_nonneg ha₀.le hb₀.le) (Nat.cast_nonneg _)
    rw [fixedBandCenteredKernel,fixedBandLattice_ramps hz]
    dsimp only [W,A,z,u,div_one]
    rw [log_div (mul_pos ha₀ hb₀).ne' (Nat.cast_pos.mpr hj).ne',log_mul ha₀.ne' hb₀.ne']
    ring
  change cornerSum D U x y (fun a b => fixedBandCenteredKernel (z a b)) = _
  rw [corner_congr he]
  simp only [cornerSum,latticeBox,rampBox,logWeight,mul_sum,← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  dsimp only [W,A,z,u,div_one,div_div]
  ring

private theorem corner_term_bound {D U H j : ℕ} (hDU : D < U) (hscale : U ≤ H*(D+1))
    (hj : j ∈ Ioc 0 (H^2)) {x y : ℕ → ℝ} {X Y : ℝ}
    (hx : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, x a| ≤ X)
    (hy : ∀ i ∈ Ioc D U, |∑ b ∈ Ioc D i, y b| ≤ Y) :
    |cornerSum D U x y (fun a b => fixedBandCenteredKernel (cornerCoord U a*cornerCoord U b/j))| ≤
      (2*log 2+6*(|fixedBandLogConstant|+log (H^2:ℕ)+2*log H))*
      (X*Y*(H:ℝ)^2*(1+log (H^2:ℕ))/j) := by
  let J := H^2
  let B := (H:ℝ)^2*(1+log J)/j
  have hJ := log_natCast_nonneg J
  have hH := log_natCast_nonneg H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi : D+1 ∈ Ioc D U := mem_Ioc.mpr ⟨by omega,hDU⟩
  have hj₀ := (mem_Ioc.mp hj).1
  have hj₁ : 1 ≤ (j:ℝ) := by exact_mod_cast hj₀
  have hjpos : 0 < (j:ℝ) := Nat.cast_pos.mpr hj₀
  have hb {f g : ℕ → ℝ} {P Q : ℝ} (hf : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, f a| ≤ P)
      (hg : ∀ i ∈ Ioc D U, |∑ b ∈ Ioc D i, g b| ≤ Q) {s : ℝ} (h : (j:ℝ) ≤ s) :
      |rampBox D U f g s| ≤ P*Q*B := by
    have hP := (abs_nonneg _).trans (hf _ hi)
    have hQ := (abs_nonneg _).trans (hg _ hi)
    apply (rampBox_bound hDU hscale (hj₁.trans h) hf hg).trans
    apply (div_le_div_of_nonneg_left (by positivity) hjpos h).trans_eq
    dsimp [B,J]; ring
  have hlat {f g : ℕ → ℝ} {P Q : ℝ} (hf : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, f a| ≤ P)
      (hg : ∀ i ∈ Ioc D U, |∑ b ∈ Ioc D i, g b| ≤ Q) :
      |latticeBox D U f g j| ≤ 6*(P*Q*B) := by
    unfold latticeBox
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_sub _ _) le_rfl).trans
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hb hf hg le_rfl,hb hf hg (by linarith : (j:ℝ) ≤ j*2),hb hf hg (by linarith : (j:ℝ) ≤ j*4)]
  have hXl (i : ℕ) (hi' : i ∈ Ioc D U) := corner_log_prefix hscale hx hi'
  have hYl (i : ℕ) (hi' : i ∈ Ioc D U) := corner_log_prefix hscale hy hi'
  have hlog : |fixedBandLogConstant-log j| ≤ |fixedBandLogConstant|+log J := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (log_natCast_nonneg j)]
    exact add_le_add_right (log_le_log hjpos (Nat.cast_le.mpr (show j ≤ J from (mem_Ioc.mp hj).2) : (j:ℝ) ≤ J)) _
  have h₂ := log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have hdiff := (abs_sub _ _).trans (add_le_add (hb hx hy le_rfl) (hb hx hy (by linarith : (j:ℝ) ≤ j*2)))
  rw [corner_term hscale hj₀ x y]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  apply (add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl).trans
  rw [abs_mul,abs_mul,abs_of_nonneg h₂]
  have hp := mul_le_mul_of_nonneg_left hdiff h₂
  have hq := mul_le_mul hlog (hlat hx hy) (abs_nonneg _) (by positivity : 0 ≤ |fixedBandLogConstant|+log J)
  have hr := hlat (f := logWeight U x) hXl hy
  have hs := hlat (g := logWeight U y) hx hYl
  change _ ≤ (2*log 2+6*(|fixedBandLogConstant|+log J+2*log H))*(X*Y*(H:ℝ)^2*(1+log J)/j)
  exact (add_le_add (add_le_add (add_le_add hp hq) hr) hs).trans_eq (by dsimp only [B]; ring)

/-- Complete contribution to the original square form with both Möbius indices
in (D,U]. All multiples in each selected matrix entry are retained. -/
def fixedBandCorner (D U : ℕ) : ℝ :=
  cornerSum D U (fun a => (μ a : ℝ)) (fun b => (μ b : ℝ)) (fixedBandProductEntry (U^2))

/-- A two-coordinate summation by parts controls a full corner by the square
of its local Möbius prefix bound. H bounds the ratio between its endpoints. -/
theorem fixedBandCorner_local_prefix {D U H : ℕ} (hDU : D < U) (hscale : U ≤ H*(D+1))
    {E : ℝ} (hp : ∀ i ∈ Ioc D U, |∑ a ∈ Ioc D i, (μ a : ℝ)| ≤ E) :
    |fixedBandCorner D U| ≤
      (2*log 2+6*(|fixedBandLogConstant|+log (H^2:ℕ)+2*log H))*
      (H:ℝ)^2*(1+log (H^2:ℕ))^2*E^2 := by
  let J := H^2
  let C := 2*log 2+6*(|fixedBandLogConstant|+log J+2*log H)
  let B := C*(E*E*(H:ℝ)^2*(1+log J))
  let x (a : ℕ) := (μ a : ℝ)
  have he : fixedBandCorner D U=∑ j ∈ Ioc 0 J, cornerSum D U x x
      (fun a b => fixedBandCenteredKernel (cornerCoord U a*cornerCoord U b/j)) := by
    rw [← corner_sum]
    apply corner_congr
    intro a ha b hb
    have ha₀ : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp ha).1
    have hb₀ : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hb).1
    have hprod := Nat.mul_pos ha₀ hb₀
    have h₁ := hscale.trans (Nat.mul_le_mul_left H (mem_Ioc.mp ha).1)
    have h₂ := hscale.trans (Nat.mul_le_mul_left H (mem_Ioc.mp hb).1)
    have hcap : U^2/(a*b) ≤ J := Nat.div_le_of_le_mul (by
      have h := Nat.mul_le_mul h₁ h₂
      dsimp [J]; nlinarith only [h])
    rw [product_multiples hprod hcap]
    apply sum_congr rfl
    intro j _
    rw [cornerCoord,ite_eq_left (mem_Ioc.mp ha).2,cornerCoord,ite_eq_left (mem_Ioc.mp hb).2,Nat.cast_pow]
    congr 2
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  have hi : D+1 ∈ Ioc D U := mem_Ioc.mpr ⟨by omega,hDU⟩
  have hE := (abs_nonneg _).trans (hp _ hi)
  have hJ := log_natCast_nonneg J
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ j ∈ Ioc 0 J, B*(j:ℝ)⁻¹ := by
      apply sum_le_sum
      intro j hj
      apply (corner_term_bound hDU hscale hj hp hp).trans_eq
      dsimp [B,C,J]; ring
    _ ≤ B*(1+log J) := by
      have hh := harmonic_le_one_add_log J
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hh
      rw [← mul_sum,show Ioc 0 J=Icc 1 J by ext d; simp only [mem_Ioc,mem_Icc]; omega]
      exact mul_le_mul_of_nonneg_left hh hB
    _ = _ := by dsimp [B,C,J]; ring

private theorem outer_restrict {N V T : ℕ} (hT : T ≤ N) (hcap : N < (V+1)*(T+1)) :
    fixedBandOuter N V=cornerSum V T (fun a => (μ a : ℝ)) (fun b => (μ b : ℝ)) (fixedBandProductEntry N) := by
  let I := Ioc V T
  let J := Ioc V N
  let g (a b : ℕ) := ((μ a : ℝ)*(μ b : ℝ))*fixedBandProductEntry N a b
  have hz {a b : ℕ} (ha : V < a) (hb : T < b) : N < a*b :=
    hcap.trans_le (Nat.mul_le_mul ha hb)
  have he (a : ℕ) (ha : a ∈ J) : ∑ b ∈ I, g a b=∑ b ∈ J, g a b := by
    apply sum_subset (Ioc_subset_Ioc_right hT)
    intro b hb hout
    have h := hz (mem_Ioc.mp ha).1 (lt_of_not_ge (fun h => hout (mem_Ioc.mpr ⟨(mem_Ioc.mp hb).1,h⟩)))
    simp [g,fixedBandProductEntry_zero h]
  change (∑ a ∈ J, ∑ b ∈ J, g a b)=_
  calc
    _ = ∑ a ∈ J, ∑ b ∈ I, g a b := sum_congr rfl fun a ha => (he a ha).symm
    _ = ∑ a ∈ I, ∑ b ∈ I, g a b := by
      symm
      apply sum_subset (Ioc_subset_Ioc_right hT)
      intro a ha hout
      apply sum_eq_zero
      intro b hb
      have h := hz (mem_Ioc.mp hb).1 (lt_of_not_ge (fun h => hout (mem_Ioc.mpr ⟨(mem_Ioc.mp ha).1,h⟩)))
      rw [mul_comm b] at h
      simp [g,fixedBandProductEntry_zero h]
    _ = _ := by simp only [I,cornerSum,g,mul_sum,mul_assoc]

/-- On the far side of a cutoff just below the square root, summation by parts
keeps the height of the first ramp, which vanishes at the product boundary. -/
private theorem outer_first_expansion {N V T : ℕ} (hN : 0 < N) (hVT : V < T) (hTN : T ≤ N)
    (hcap : N < (V+1)*(T+1)) (hfirst : N < 2*(V+1)^2) (hwidth : T ≤ 2*(V+1))
    :
    let r := (T:ℝ)^2/N
    let u := cornerCoord T
    let x := fun a : ℕ => (μ a : ℝ)
    let K := fun a b => max (u a*u b/r-1) 0
    fixedBandOuter N V=(1-eulerMascheroniConstant+log r)*cornerSum V T x x K-
      cornerSum V T (logWeight T x) x K-cornerSum V T x (logWeight T x) K := by
  intro r u x K
  have hN₀ : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hT₀ : 0 < (T:ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 0 < r := by dsimp [r]; positivity
  have he (a : ℕ) (ha : a ∈ Ioc V T) (b : ℕ) (hb : b ∈ Ioc V T) :
      fixedBandProductEntry N a b=(1-eulerMascheroniConstant+log r)*K a b-
        log (u a)*K a b-log (u b)*K a b := by
    have ha₀ : 0 < (a:ℝ) := Nat.cast_pos.mpr (by have := (mem_Ioc.mp ha).1; omega)
    have hb₀ : 0 < (b:ℝ) := Nat.cast_pos.mpr (by have := (mem_Ioc.mp hb).1; omega)
    have hy : u a*u b/r=(N:ℝ)/(a*b) := by
      simp only [u,cornerCoord,ite_eq_left (mem_Ioc.mp ha).2,ite_eq_left (mem_Ioc.mp hb).2,r]
      field_simp
    have hab₀ : 0 < a*b := Nat.mul_pos (Nat.cast_pos.mp ha₀) (Nat.cast_pos.mp hb₀)
    have hpR := mul_pos ha₀ hb₀
    by_cases hab : a*b ≤ N
    · have h₁ : 1 ≤ u a*u b/r := by rw [hy]; exact (one_le_div hpR).mpr (by exact_mod_cast hab)
      have h₂ : N < 2*(a*b) := hfirst.trans_le (Nat.mul_le_mul_left 2 (by
        simpa only [pow_two] using Nat.mul_le_mul (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1))
      have h := fixedBandProductEntry_first hab₀ hab h₂
      rw [h,← hy,log_div (mul_pos (zero_lt_one.trans_le (coord_bounds ha hwidth).1)
        (zero_lt_one.trans_le (coord_bounds hb hwidth).1)).ne' hr.ne',
        log_mul (zero_lt_one.trans_le (coord_bounds ha hwidth).1).ne'
          (zero_lt_one.trans_le (coord_bounds hb hwidth).1).ne']
      dsimp only [K]
      rw [max_eq_left (sub_nonneg.mpr h₁)]
      ring
    · have h₁ : u a*u b/r ≤ 1 := by rw [hy]; exact (div_le_one hpR).mpr (by exact_mod_cast (lt_of_not_ge hab).le)
      simp only [fixedBandProductEntry_zero (lt_of_not_ge hab),K,max_eq_right (sub_nonpos.mpr h₁),mul_zero,sub_zero]
  rw [outer_restrict hTN hcap,corner_congr he]
  simp only [cornerSum,logWeight,x,u,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  ring

private theorem outer_hinge_bound {N V T : ℕ} (hN : 0 < N) (hVT : V < T) (hTN : T ≤ N)
    (hcap : N < (V+1)*(T+1)) (hfirst : N < 2*(V+1)^2) (hwidth : T ≤ 2*(V+1))
    (hscale : N ≤ T^2) {E : ℝ} (hp : ∀ i ∈ Ioc V T, |∑ a ∈ Ioc V i, (μ a : ℝ)| ≤ E) :
    |fixedBandOuter N V| ≤ (1+log ((T:ℝ)^2/N)+2*log 2)*E^2*max ((N:ℝ)/(V+1:ℝ)^2-1) 0 := by
  let r := (T:ℝ)^2/N
  let u := cornerCoord T
  let x (a : ℕ) := (μ a : ℝ)
  let K (a b : ℕ) := max (u a*u b/r-1) 0
  have hN₀ : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hT₀ : 0 < (T:ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₁ : 1 ≤ r := (one_le_div hN₀).mpr (by exact_mod_cast hscale)
  have hγ : 0 ≤ 1-eulerMascheroniConstant := by linarith only [eulerMascheroniConstant_lt_two_thirds]
  have hγ' : 1-eulerMascheroniConstant ≤ 1 := by linarith only [one_half_lt_eulerMascheroniConstant]
  have hs := outer_first_expansion hN hVT hTN hcap hfirst hwidth
  have htop : u (V+1)*u (V+1)/r=(N:ℝ)/(V+1:ℝ)^2 := by
    simp only [u,cornerCoord,ite_eq_left (show V+1 ≤ T from hVT),r,Nat.cast_add,Nat.cast_one]
    field_simp
  have hlog (i : ℕ) (hi : i ∈ Ioc V T) := corner_log_prefix hwidth hp hi
  have h₀ := corner_hinge_exact hVT hr hp hp
  have h₁ := corner_hinge_exact hVT hr (x := logWeight T x) hlog hp
  have h₂ := corner_hinge_exact hVT hr (y := logWeight T x) hp hlog
  change |cornerSum V T x x K| ≤ E*E*max (u (V+1)*u (V+1)/r-1) 0 at h₀
  change |cornerSum V T (logWeight T x) x K| ≤ (E*log (2:ℕ))*E*max (u (V+1)*u (V+1)/r-1) 0 at h₁
  change |cornerSum V T x (logWeight T x) K| ≤ E*(E*log (2:ℕ))*max (u (V+1)*u (V+1)/r-1) 0 at h₂
  rw [htop] at h₀ h₁ h₂
  rw [hs]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  rw [abs_mul,abs_of_nonneg (add_nonneg hγ (log_nonneg hr₁))]
  have hpre := add_le_add (add_le_add (mul_le_mul (add_le_add_left hγ' (log r)) h₀
    (abs_nonneg _) (by linarith only [log_nonneg hr₁] : 0 ≤ 1+log r)) h₁) h₂
  exact hpre.trans_eq (by push_cast; dsimp only [r]; ring)

/-- Moving the cutoff L places below the square root costs the square of the
largest Möbius sum on (V,V+3L], multiplied by the relative width L/(V+L). -/
theorem fixedBandOuter_near_prefix {V L : ℕ} (hL : 0 < L) (hsize : 3*L ≤ V) {E : ℝ}
    (hp : ∀ i ∈ Ioc V (V+3*L), |∑ a ∈ Ioc V i, (μ a : ℝ)| ≤ E) :
    |fixedBandOuter ((V+L)^2) V| ≤ 24*((L:ℝ)/(V+L))*E^2 := by
  let U := V+L
  let T := V+3*L
  have hVT : V < T := by dsimp [T]; omega
  have hU : 0 < U := by dsimp [U]; omega
  have hTU : T ≤ 2*U := by dsimp [T,U]; omega
  have hTN : T ≤ U^2 := by
    have h₂ : 2 ≤ U := by dsimp [U]; omega
    exact hTU.trans (by simpa only [pow_two] using Nat.mul_le_mul_right U h₂)
  have hcap : U^2 < (V+1)*(T+1) := by
    dsimp [U,T]
    nlinarith only [Nat.mul_le_mul_right L hsize]
  have hfirst : U^2 < 2*(V+1)^2 := by
    dsimp [U]
    nlinarith only [Nat.mul_le_mul_right V hsize,Nat.mul_le_mul_right L hsize]
  have hT : U^2 ≤ T^2 := Nat.pow_le_pow_left (by dsimp [U,T]; omega) 2
  have hb := outer_hinge_bound (pow_pos hU 2) hVT hTN hcap hfirst (by dsimp [T]; omega) hT hp
  have hv : 0 < (V:ℝ) := Nat.cast_pos.mpr (by omega)
  have hl : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have hs : 3*(L:ℝ) ≤ V := by exact_mod_cast hsize
  have hu : 0 < (U:ℝ) := Nat.cast_pos.mpr hU
  have hTu : (T:ℝ) ≤ 2*U := by exact_mod_cast hTU
  have hUT : (U:ℝ) = V+L := by exact_mod_cast (rfl : U=V+L)
  have hlog : log ((T:ℝ)^2/(U:ℝ)^2) ≤ 3 := by
    have h₀ : 0 < (T:ℝ)^2/(U:ℝ)^2 := by have : 0 < (T:ℝ) := Nat.cast_pos.mpr (by omega); positivity
    apply (log_le_sub_one_of_pos h₀).trans
    have hh : (T:ℝ)^2/(U:ℝ)^2 ≤ 4 := (div_le_iff₀ (sq_pos_of_pos hu)).mpr
      (by nlinarith only [sq_le_sq' (by have := Nat.cast_nonneg (α := ℝ) T; linarith : -(2*(U:ℝ)) ≤ T) hTu])
    linarith
  have hamp : max ((U:ℝ)^2/(V+1:ℝ)^2-1) 0 ≤ 4*((L:ℝ)/(V+L)) := by
    apply max_le _ (by positivity)
    have h₁ : (U:ℝ)^2/(V+1:ℝ)^2 ≤ (U:ℝ)^2/(V:ℝ)^2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hv) (by nlinarith)
    have hr : (L:ℝ)/V ≤ 1 := (div_le_one hv).mpr (by linarith)
    calc
      _ ≤ (U:ℝ)^2/(V:ℝ)^2-1 := sub_le_sub_right h₁ _
      _ = ((L:ℝ)/V)*(2+L/V) := by rw [hUT]; field_simp; ring
      _ ≤ ((L:ℝ)/V)*3 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := by
        rw [show ((L:ℝ)/V)*3=(3*L)/V by ring,show 4*((L:ℝ)/(V+L))=(4*L)/(V+L) by ring]
        exact (div_le_div_iff₀ hv (add_pos hv hl)).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hs hl.le])
  rw [Nat.cast_pow] at hb
  apply hb.trans
  have hcoeff : 1+log ((T:ℝ)^2/(U:ℝ)^2)+2*log 2 ≤ 6 := by
    linarith only [hlog,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg E)) hamp (le_max_right _ _) (by positivity)).trans_eq (by ring)

/-- The trivial bound for the local Möbius sums already removes a boundary
layer of cube-root width in the original sample at square-root error. -/
theorem fixedBandOuter_near {V L : ℕ} (hsize : 3*L ≤ V) :
    |fixedBandOuter ((V+L)^2) V| ≤ 216*(L:ℝ)^3/(V+L) := by
  by_cases hL : 0 < L
  · apply (fixedBandOuter_near_prefix hL hsize (E := 3*L) (fun i hi => ?_)).trans_eq
    · ring
    · apply (abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ _a ∈ Ioc V i, (1:ℝ) := sum_le_sum fun a _ => by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
        _ ≤ _ := by simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]; exact_mod_cast (by have := (mem_Ioc.mp hi).2; omega : i-V ≤ 3*L)
  · have hz : L=0 := by omega
    rw [hz,Nat.add_zero]
    have he : fixedBandOuter (V^2) V=0 := by
      apply sum_eq_zero; intro a ha; apply sum_eq_zero; intro b hb
      have h := Nat.mul_lt_mul_of_lt_of_lt (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
      rw [← pow_two] at h
      rw [fixedBandProductEntry_zero h,mul_zero]
    simp [he]

/-- At any cutoff below the square root the outer square is the only error
beyond the prime-power and small-row allowance. -/
theorem fixedBand_prime_outer_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n V : ℕ}, 2 ≤ n → V ≤ n^2 →
      |dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) V-fixedBandOuter (n^4) V| ≤ C*(n:ℝ)^2 := by
  obtain ⟨K,hK,hp⟩ := dyadicPrimeDeficit_power_cost
  let B := 72+60*|fixedBandLogConstant|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K+10*B,by positivity,fun {n V} hn hV => ?_⟩
  let N := n^4
  have hN : 4 ≤ N := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have hU : 2 ≤ n^2 := (by decide : 2 ≤ 2^2).trans (Nat.pow_le_pow_left hn 2)
  have hU₂ : 2*n^2 ≤ N := (Nat.mul_le_mul_right (n^2) hU).trans_eq (by dsimp [N]; ring)
  have hV₂ : 2*V ≤ N := (Nat.mul_le_mul_left 2 hV).trans hU₂
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hn₁ : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hNr : (N:ℝ)=(n:ℝ)^4 := Nat.cast_pow _ _
  have hVr : (V:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hV

  have hsmall := fixedBand_small_rows hN hV₂
  rw [hNr,log_pow,Nat.cast_ofNat] at hsmall
  have hlog := log_natCast_nonneg n
  have hpre : B*(V:ℝ)^2*(1+4*log n)/(n:ℝ)^4 ≤ B*(1+4*log n) := by
    apply (div_le_iff₀ (pow_pos hn₀ 4)).mpr
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg V) hVr 2)
      (mul_nonneg hB (by linarith : 0 ≤ 1+4*log n))
    linarith only [hh]
  have he := fixedBand_quadratic_split hN (by omega : V ≤ N)
  have hcont : |dyadicContrast N+fixedBandQuadratic N V-fixedBandOuter N V| ≤ 2*(B*(1+4*log n)) := by
    rw [he,add_sub_cancel_right,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),hNr]
    exact mul_le_mul_of_nonneg_left (hsmall.trans hpre) (by norm_num)
  obtain ⟨hlo,hhi⟩ := hp (pow_pos hn₀ 4)
  rw [show sqrt ((n:ℝ)^4)=(n:ℝ)^2 by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _)]] at hhi
  rw [← hNr]
  rw [show dyadicPrimeDeficit (N:ℝ)+fixedBandQuadratic N V-fixedBandOuter N V =
    (dyadicPrimeDeficit (N:ℝ)-dyadicContrast N)+(dyadicContrast N+fixedBandQuadratic N V-fixedBandOuter N V) by ring]
  apply (abs_add_le _ _).trans
  · rw [abs_of_nonneg (by simpa only [hNr] using hlo)]
    have hlog' : 1+4*log n ≤ 5*(n:ℝ)^2 := by
      nlinarith only [log_le_sub_one_of_pos hn₀,mul_le_mul_of_nonneg_left hn₁ hn₀.le,hn₁]
    rw [← hNr] at hhi
    linarith only [hhi,hcont,mul_le_mul_of_nonneg_left hlog' hB]

/-- Uniformly in the choice of the shorter cutoff V, an outer width L with
L³ ≤ n⁴ costs at most a square-root error in the original prime shortfall. -/
theorem fixedBand_prime_below_root :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n V L : ℕ}, 2 ≤ n → V+L=n^2 → 3*L ≤ V → L^3 ≤ n^4 →
      |dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) V| ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_outer_error
  refine ⟨C+216,by positivity,fun {n V L} hn hVL hsize hcube => ?_⟩
  have hbase := h hn (show V ≤ n^2 by omega)
  have ho := fixedBandOuter_near hsize
  rw [show (V+L)^2=n^4 by rw [hVL]; ring,show (V:ℝ)+L=(n:ℝ)^2 by exact_mod_cast hVL] at ho
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hforce : |fixedBandOuter (n^4) V| ≤ 216*(n:ℝ)^2 := by
    apply ho.trans
    apply (div_le_iff₀ (sq_pos_of_pos hn₀)).mpr
    have h : (L:ℝ)^3 ≤ (n:ℝ)^4 := by exact_mod_cast hcube
    linarith only [mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 216)]
  have he := abs_add_le (dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) V-fixedBandOuter (n^4) V)
    (fixedBandOuter (n^4) V)
  rw [sub_add_cancel] at he
  linarith only [he,hbase,hforce]

/-- Short input length for the quartic evaluation. Squaring it gives the
quadratic cutoff whose boundary error is controlled at every fourth power. -/
def fixedBandShortRoot (n : ℕ) : ℕ := n-Nat.nthRoot 3 (n/8)

private theorem shortRoot_geometry (n : ℕ) :
    let V := (fixedBandShortRoot n)^2
    let L := n^2-V
    V+L=n^2 ∧ 3*L ≤ V ∧ L^3 ≤ n^4 := by
  let k := Nat.nthRoot 3 (n/8)
  let s := n-k
  change s^2+(n^2-s^2)=n^2 ∧ 3*(n^2-s^2) ≤ s^2 ∧ (n^2-s^2)^3 ≤ n^4
  have h₀ : k^3 ≤ n/8 := Nat.pow_nthRoot_le (.inl (by decide))
  have hk₃ : 8*k^3 ≤ n := by omega
  have hk : k ≤ k^3 := Nat.le_self_pow (by decide : (3:ℕ) ≠ 0) k
  have h8 : 8*k ≤ n := by omega
  have hsn : s+k=n := Nat.sub_add_cancel (by omega)
  have hL : n^2-s^2 = k*(2*s+k) := by rw [← hsn,show (s+k)^2=s^2+k*(2*s+k) by ring]; omega
  have hL' : n^2-s^2 ≤ 2*n*k := by rw [hL,← hsn]; nlinarith
  have h4L : 4*(n^2-s^2) ≤ n^2 := by
    calc
      _ ≤ 4*(2*n*k) := Nat.mul_le_mul_left _ hL'
      _ ≤ _ := by nlinarith only [Nat.mul_le_mul_left n h8]
  have hVs : s^2 ≤ n^2 := Nat.pow_le_pow_left (by omega) 2
  refine ⟨by omega,by omega,?_⟩
  calc
    _ ≤ (2*n*k)^3 := Nat.pow_le_pow_left hL' 3
    _ ≤ _ := by nlinarith only [Nat.mul_le_mul_left (n^3) hk₃]

/-- The trimmed divisor cutoff stays between the half-product threshold and
the square root. -/
theorem fixedBandShortRoot_square_bounds (n : ℕ) :
    ((fixedBandShortRoot n)^2)^2 ≤ n^4 ∧ n^4 ≤ 2*((fixedBandShortRoot n)^2)^2 := by
  let V := (fixedBandShortRoot n)^2
  have h := shortRoot_geometry n
  change V+(n^2-V)=n^2 ∧ 3*(n^2-V) ≤ V ∧ _ at h
  have hV : V ≤ n^2 := by omega
  have h₃ : 3*n^2 ≤ 4*V := by omega
  constructor
  · rw [show n^4=(n^2)^2 by ring]
    exact Nat.pow_le_pow_left hV 2
  · have hr : 3*((n:ℝ)^2) ≤ 4*(V:ℝ) := by exact_mod_cast h₃
    have hpow := pow_le_pow_left₀ (by positivity) hr 2
    exact_mod_cast (show (n:ℝ)^4 ≤ 2*(V:ℝ)^2 by nlinarith only [hpow,pow_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ)) 4])

theorem fixedBand_prime_shortRoot_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 2 ≤ n →
      |dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) ((fixedBandShortRoot n)^2)| ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_below_root
  refine ⟨C,hC,fun {n} hn => ?_⟩
  obtain ⟨he,hs,hL⟩ := shortRoot_geometry n
  exact h hn he hs hL

/-- Negative-part mass with the shortened square cutoff on every sample. -/
def fixedBandTrimmedMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (-fixedBandQuadratic (n^4) ((fixedBandShortRoot n)^2)) 0/(n:ℝ)^3

theorem fixedBandTrimmedMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandTrimmedMass m b| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_shortRoot_error
  exact ⟨C,hC,fun hm => fixedBand_mass_sqrt_error (x := fun n => dyadicPrimeDeficit ((n:ℝ)^4))
    (y := fun n => -fixedBandQuadratic (n^4) ((fixedBandShortRoot n)^2))
    hC (fun hn => by simpa only [sub_neg_eq_add] using h hn) hm⟩

theorem rh_of_fixedBandTrimmedMass_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandTrimmedMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) : RiemannHypothesis := by
  apply rh_of_fixedBandMass_powerWindows
  intro α hα
  obtain ⟨δ,hδ,hδ₁,hw⟩ := h (α/2) (by linarith)
  obtain ⟨C,hC,he⟩ := fixedBandTrimmedMass_error
  refine ⟨δ,hδ,hδ₁,fixedBand_cofinal_mass_transfer fixedBandMass fixedBandTrimmedMass hC
    (fun {m b} hm => (abs_le.mp (he hm)).2.trans (mul_le_mul_of_nonneg_left
      (by nlinarith only [log_natCast_nonneg b,sq_nonneg (log b)]) hC)) (by linarith)
      (by linarith : α/2 < α) hδ₁ hw⟩

/-- Energy of the actual local Möbius sums. A large isolated prefix is charged
at only its own index. -/
def fixedBandPrefixEnergy (D T : ℕ) : ℝ :=
  ∑ i ∈ Ioc D T, (localSum D (fun a => (μ a : ℝ)) i)^2

/-- The first-multiple remainder is bounded by a one-dimensional mean square
of local Möbius sums, uniformly in the width below the square root. -/
theorem fixedBandOuter_near_energy {V L : ℕ} (hL : 0 < L) (hsize : 3*L ≤ V) :
    |fixedBandOuter ((V+L)^2) V| ≤ 27*fixedBandPrefixEnergy V (V+3*L)/V := by
  let U := V+L
  let T := V+3*L
  let I := Ioc V T
  let r := (T:ℝ)^2/((U^2:ℕ):ℝ)
  let x (a : ℕ) := (μ a : ℝ)
  let u := cornerCoord T
  let w (a : ℕ) := log (u a)
  let K (a b : ℕ) := max (u a*u b/r-1) 0
  let Z (a b : ℕ) := (w a+w b)*K a b
  let e := fixedBandPrefixEnergy V T
  have hVT : V < T := by dsimp [T]; omega
  have hU : 0 < U := by dsimp [U]; omega
  have hTU : T ≤ 2*U := by dsimp [T,U]; omega
  have hTN : T ≤ U^2 := hTU.trans (by
    have h₂ : 2 ≤ U := by dsimp [U]; omega
    simpa only [pow_two] using Nat.mul_le_mul_right U h₂)
  have hwidth : T ≤ 2*(V+1) := by dsimp [T]; omega
  have hcap : U^2 ≤ (V+1)*T := by dsimp [U,T]; nlinarith only [Nat.mul_le_mul_right L hsize]
  have hfirst : U^2 < 2*(V+1)^2 := by
    dsimp [U]; nlinarith only [Nat.mul_le_mul_right V hsize,Nat.mul_le_mul_right L hsize]
  have hUT : U ≤ T := by dsimp [U,T]; omega
  have hv : 0 < (V:ℝ) := Nat.cast_pos.mpr (by omega)
  have ht : 0 < (T:ℝ) := Nat.cast_pos.mpr (by omega)
  have hn : 0 < ((U^2:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos hU _)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₁ : 1 ≤ r := (one_le_div hn).mpr (by exact_mod_cast Nat.pow_le_pow_left hUT 2)
  have hr₄ : r ≤ 4 := (div_le_iff₀ hn).mpr (by
    have hh := Nat.pow_le_pow_left hTU 2
    have hh' : (T:ℝ)^2 ≤ (2*(U:ℝ))^2 := by exact_mod_cast hh
    push_cast; linarith only [hh'])
  have he : 0 ≤ e := sum_nonneg fun _ _ => sq_nonneg _
  have hi₀ : V+1 ∈ I := mem_Ioc.mpr ⟨by omega,hVT⟩
  have hu₀ (i : ℕ) : 0 ≤ u i := coord_nonneg T i
  have hu₁ (i : ℕ) (hi : i ∈ I) := coord_bounds hi hwidth
  have hw (i : ℕ) (hi : i ∈ I) : 0 ≤ w i ∧ w i ≤ 1 := by
    obtain ⟨hl,hh⟩ := hu₁ i hi
    exact ⟨log_nonneg hl,(log_le_sub_one_of_pos (zero_lt_one.trans_le hl)).trans (by norm_num at hh; linarith)⟩
  have hz : u (T+1)=0 := by simp [u,cornerCoord]
  have hwa (i : ℕ) (hi : i ∈ I) : w (i+1) ≤ w i := by
    by_cases ha : i < T
    · exact log_le_log (zero_lt_one.trans_le (hu₁ _ (mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hi).1; omega,ha⟩)).1)
        (coord_anti (by have := (mem_Ioc.mp hi).1; omega))
    · have h : i=T := by have := (mem_Ioc.mp hi).2; omega
      simpa only [h,w,hz,log_zero] using (hw i hi).1
  have hKsym (i j : ℕ) : K i j=K j i := by dsimp [K]; rw [mul_comm (u i)]
  have hKz (i : ℕ) : K i (T+1)=0 := by simp [K,hz]
  have hKa (i : ℕ) (hi : i ∈ I) (j : ℕ) : K (i+1) j ≤ K i j := by
    apply max_le_max_right
    apply sub_le_sub_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (coord_anti (by have := (mem_Ioc.mp hi).1; omega)) (hu₀ j)) hr.le
  have hmix (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) : 0 ≤ mixedDiff K i j := by
    apply sub_nonneg.mpr
    have hh := hinge_mixed (u := fun a => u a/r) (v := u) (i := i) (j := j)
      (div_le_div_of_nonneg_right (coord_anti (by have := (mem_Ioc.mp hi).1; omega)) hr.le)
      (coord_anti (by have := (mem_Ioc.mp hj).1; omega)) (hu₀ _)
    simpa only [cornerHinge,K,div_mul_eq_mul_div] using hh
  have hZmix (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) : 0 ≤ mixedDiff Z i j := by
    have h₀ := mul_nonneg (add_nonneg (hw i hi).1 (hw j hj).1) (hmix i hi j hj)
    have h₁ := mul_nonneg (sub_nonneg.mpr (hwa i hi)) (sub_nonneg.mpr (hKa j hj (i+1)))
    rw [hKsym (j+1) (i+1),hKsym j (i+1)] at h₁
    have h₂ := mul_nonneg (sub_nonneg.mpr (hwa j hj)) (sub_nonneg.mpr (hKa i hi (j+1)))
    dsimp only [mixedDiff,Z] at h₀ ⊢
    linarith only [h₀,h₁,h₂]
  have hlast : K T (V+1)=0 := by
    dsimp only [K,u,cornerCoord]
    rw [ite_eq_left le_rfl,ite_eq_left (show V+1 ≤ T from hVT),div_self ht.ne']
    apply max_eq_right
    apply sub_nonpos.mpr
    apply (div_le_one hr).mpr
    have h : ((U^2:ℕ):ℝ) ≤ ((V:ℝ)+1)*T := by exact_mod_cast hcap
    dsimp only [r]
    simp only [one_mul,Nat.cast_pow,Nat.cast_succ] at h ⊢
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left h ht.le]
  have hedge (i : ℕ) (hi : i ∈ I) :
      K i (V+1)-K (i+1) (V+1) ≤ 4/V ∧ Z i (V+1)-Z (i+1) (V+1) ≤ 11/V := by
    by_cases ha : i < T
    · have hiR : (V:ℝ) < i := by exact_mod_cast (mem_Ioc.mp hi).1
      have hi₀R := hv.trans hiR
      have hi' : i+1 ∈ I := mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hi).1; omega,ha⟩
      have hu₂ : u (V+1) ≤ 2 := (hu₁ _ hi₀).2
      have hdiff : u i-u (i+1) ≤ 2/V := by
        have h : u i-u (i+1)=u i/(i+1:ℝ) := by
          simp only [u,cornerCoord,ite_eq_left (mem_Ioc.mp hi).2,ite_eq_left (show i+1 ≤ T from ha),Nat.cast_add,Nat.cast_one]
          field_simp; ring
        rw [h]
        exact div_le_div₀ (by norm_num) (hu₁ i hi).2 hv (by linarith)
      have hKdiff : K i (V+1)-K (i+1) (V+1) ≤ 4/V := by
        have h := hinge_diff (div_le_div_of_nonneg_right (coord_anti (U := T) (by have := (mem_Ioc.mp hi).1; omega : 0 < i)) hr.le) (hu₀ (V+1))
        change cornerHinge (u i/r) (u (V+1))-cornerHinge (u (i+1)/r) (u (V+1)) = _ at h
        simp only [cornerHinge,div_mul_eq_mul_div] at h
        change max _ 0-max _ 0 ≤ _
        rw [h]
        apply (min_le_right _ _).trans
        rw [← sub_div]
        have hdif₀ := sub_nonneg.mpr (coord_anti (U := T) (by have := (mem_Ioc.mp hi).1; omega : 0 < i))
        exact (mul_le_mul ((div_le_self hdif₀ hr₁).trans hdiff) hu₂ (hu₀ _) (by positivity)).trans_eq (by ring)
      have hwΔ : w i-w (i+1) ≤ 1/V := by
        have hw₁ : w i=log ((T:ℝ)/i) := congrArg log (ite_eq_left (mem_Ioc.mp hi).2)
        have hw₂ : w (i+1)=log ((T:ℝ)/((i:ℝ)+1)) := by
          simp only [w,u,cornerCoord,ite_eq_left (show i+1 ≤ T from ha),Nat.cast_succ]
        rw [hw₁,hw₂,
          ← log_div (by positivity) (by positivity),show (T:ℝ)/i/(T/(i+1))=((i:ℝ)+1)/i by field_simp]
        apply (log_le_sub_one_of_pos (by positivity)).trans
        rw [show ((i:ℝ)+1)/i-1=1/i by field_simp; ring]
        exact one_div_le_one_div_of_le hv hiR.le
      have hK₃ : K (i+1) (V+1) ≤ 3 := by
        apply max_le _ (by norm_num)
        have h := (div_le_self (mul_nonneg (hu₀ _) (hu₀ _)) hr₁).trans
          (mul_le_mul (hu₁ (i+1) hi').2 hu₂ (hu₀ _) (by norm_num))
        norm_num at h; linarith
      refine ⟨hKdiff,?_⟩
      have h₁ := mul_le_mul (add_le_add (hw i hi).2 (hw _ hi₀).2) hKdiff
        (sub_nonneg.mpr (hKa i hi _)) (by norm_num)
      have h₂ := mul_le_mul hwΔ hK₃ (le_max_right _ _) (by positivity)
      dsimp only [Z]
      simp only [div_eq_mul_inv] at h₁ h₂ ⊢
      linarith only [h₁,h₂]
    · have hit : i=T := by have := (mem_Ioc.mp hi).2; omega
      rw [hit]
      simp only [Z,hlast,hKsym (T+1) _,hKz,mul_zero,sub_zero]
      constructor <;> positivity
  have energy {F : ℕ → ℕ → ℝ} (hz : ∀ i,F i (T+1)=0) (hs : ∀ i j,F i j=F j i)
      (hm : ∀ i ∈ I, ∀ j ∈ I, 0 ≤ mixedDiff F i j) {d : ℝ}
      (hd : ∀ i ∈ I, F i (V+1)-F (i+1) (V+1) ≤ d) :
      |cornerSum V T x x F| ≤ e*d := by
    apply (corner_energy hVT x x (fun j => (hs _ _).trans (hz j)) hz hs hm hd).trans_eq
    dsimp only [e,fixedBandPrefixEnergy,x]
    rw [sum_add_distrib]; ring
  have hk := energy hKz hKsym hmix (fun i hi => (hedge i hi).1)
  have hZs (i j : ℕ) : Z i j=Z j i := by dsimp only [Z]; rw [hKsym i j,add_comm]
  have hl := energy (F := Z) (fun i => by simp [Z,hKz]) hZs hZmix (fun i hi => (hedge i hi).2)
  have hcorr : cornerSum V T (logWeight T x) x K+cornerSum V T x (logWeight T x) K=cornerSum V T x x Z := by
    simp only [cornerSum,logWeight,w,u,Z,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    ring
  have hrep := outer_first_expansion (pow_pos hU 2) hVT hTN (hcap.trans_lt (by nlinarith : (V+1)*T < (V+1)*(T+1))) hfirst hwidth
  change fixedBandOuter (U^2) V=(1-eulerMascheroniConstant+log r)*cornerSum V T x x K-
    cornerSum V T (logWeight T x) x K-cornerSum V T x (logWeight T x) K at hrep
  rw [← sub_add_eq_sub_sub,hcorr] at hrep
  rw [hrep]
  apply (abs_sub _ _).trans
  have hC : |1-eulerMascheroniConstant+log r| ≤ 4 := abs_le.mpr ⟨by linarith only [eulerMascheroniConstant_lt_two_thirds,log_nonneg hr₁],
    by linarith only [one_half_lt_eulerMascheroniConstant,log_le_sub_one_of_pos hr,hr₄]⟩
  rw [abs_mul]
  exact (add_le_add (mul_le_mul hC hk (abs_nonneg _) (by norm_num)) hl).trans_eq (by dsimp only [e,T]; ring)

/-- Prefix energy allowed for the outer corner at the chosen divisor cutoff. -/
def fixedBandCutEnergy (n L : ℕ) : ℝ :=
  let V := n^2-L
  27*fixedBandPrefixEnergy V (V+3*L)/V

/-- The energy pays for both large-divisor indices at a chosen truncation. -/
def fixedBandCutScore (n L : ℕ) : ℝ :=
  fixedBandCutEnergy n L-fixedBandQuadratic (n^4) (n^2-L)

private theorem cutScore_zero (n : ℕ) :
    fixedBandCutScore n 0 = -fixedBandQuadratic (n^4) (n^2) := by
  simp [fixedBandCutScore,fixedBandCutEnergy,fixedBandPrefixEnergy]

theorem fixedBand_prime_cut_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n L : ℕ}, 2 ≤ n → 4*L ≤ n^2 →
      dyadicPrimeDeficit ((n:ℝ)^4) ≤ fixedBandCutScore n L+C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_outer_error
  obtain ⟨K,hK,hq⟩ := fixedBand_prime_quadratic_error
  refine ⟨max C K,le_max_of_le_left hC,fun {n L} hn hL₄ => ?_⟩
  by_cases hL : 0 < L
  · let V := n^2-L
    have hsize : 3*L ≤ V := by dsimp [V]; omega
    have he := fixedBandOuter_near_energy hL hsize
    have hVL : V+L=n^2 := by dsimp [V]; omega
    rw [show (V+L)^2=n^4 by rw [hVL]; ring] at he
    have hmain := (abs_le.mp (h (V := V) hn (Nat.sub_le _ _))).2
    change _ ≤ 27*fixedBandPrefixEnergy V (V+3*L)/V-fixedBandQuadratic (n^4) V+_
    linarith only [hmain,(abs_le.mp he).2,mul_le_mul_of_nonneg_right (le_max_left C K) (sq_nonneg (n:ℝ))]
  · rw [show L=0 by omega,cutScore_zero]
    linarith only [(abs_le.mp (hq hn)).2,mul_le_mul_of_nonneg_right (le_max_right C K) (sq_nonneg (n:ℝ))]

/-- Keeping three quarters of the square-root cutoff charges one local prefix energy. -/
def fixedBandQuarterMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandCutScore n (n^2/4)) 0/(n:ℝ)^3

/-- The ordinary prime mass has a one-sided logarithmic error from the
quarter-truncated statistic on every window. -/
theorem fixedBandQuarterMass_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      fixedBandMass m b-fixedBandQuarterMass m b ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_cut_upper
  let d (n : ℕ) := dyadicPrimeDeficit ((n:ℝ)^4)
  let f (n : ℕ) := max (d n) (fixedBandCutScore n (n^2/4))
  have he {n : ℕ} (hn : 2 ≤ n) : |f n-fixedBandCutScore n (n^2/4)| ≤ C*(n:ℝ)^2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (le_max_right _ _))]
    exact sub_le_iff_le_add.mpr (max_le (by linarith only [h hn (by omega : 4*(n^2/4) ≤ n^2)] : d n ≤ _) (by have := mul_nonneg hC (sq_nonneg (n:ℝ)); linarith))
  refine ⟨C,hC,fun {m b} hm => ?_⟩
  apply le_trans _ (abs_le.mp (fixedBand_mass_sqrt_error (b := b) hC he hm)).2
  apply sub_le_sub_right
  apply sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (max_le_max_right _ (le_max_left (d n) _)) (by positivity)

/-- Choose a different arithmetic cutoff at each fourth-power sample. The
uncut quadratic form is one of the finitely many choices. -/
def fixedBandMinScore (n : ℕ) : ℝ :=
  (Icc 0 (n^2/4)).inf' (nonempty_Icc.mpr (Nat.zero_le _)) (fixedBandCutScore n)

def fixedBandMinMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandMinScore n) 0/(n:ℝ)^3

theorem fixedBandMinScore_le {n L : ℕ} (h : L ≤ n^2/4) :
    fixedBandMinScore n ≤ fixedBandCutScore n L :=
  inf'_le _ (mem_Icc.mpr ⟨Nat.zero_le _,h⟩)

theorem fixedBandMinMass_le_quadratic (m b : ℕ) :
    fixedBandMinMass m b ≤ fixedBandQuadraticMass m b := by
  apply sum_le_sum
  intro n _
  have h := fixedBandMinScore_le (n := n) (Nat.zero_le (n^2/4))
  rw [cutScore_zero] at h
  exact div_le_div_of_nonneg_right (max_le_max_right _ h) (by positivity)

theorem fixedBandMinMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandMinMass m b| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_cut_upper
  obtain ⟨K,hK,hq⟩ := fixedBand_prime_quadratic_error
  refine ⟨max C K,le_max_of_le_left hC,fun {m b} hm => fixedBand_mass_sqrt_error
    (x := fun n => dyadicPrimeDeficit ((n:ℝ)^4)) (y := fixedBandMinScore)
    (le_max_of_le_left hC) (fun {n} hn => ?_) hm⟩
  have hlo : dyadicPrimeDeficit ((n:ℝ)^4)-C*(n:ℝ)^2 ≤ fixedBandMinScore n := by
    refine (le_inf'_iff (nonempty_Icc.mpr (Nat.zero_le (n^2/4))) (fixedBandCutScore n)).mpr ?_
    intro L hL
    have h4 : 4*L ≤ n^2 := by have := (mem_Icc.mp hL).2; omega
    linarith only [h hn h4]
  have hhi := fixedBandMinScore_le (n := n) (Nat.zero_le (n^2/4))
  rw [cutScore_zero] at hhi
  exact abs_le.mpr ⟨by linarith only [hhi,(abs_le.mp (hq hn)).1,mul_le_mul_of_nonneg_right (le_max_right C K) (sq_nonneg (n:ℝ))],
    by linarith only [hlo,mul_le_mul_of_nonneg_right (le_max_left C K) (sq_nonneg (n:ℝ))]⟩

/-- The energy-corrected score formed using only the late multiples. -/
def fixedBandLateCutScore (n L : ℕ) : ℝ :=
  fixedBandCutEnergy n L-fixedBandQuadraticAfter (n^4) (n^2-L) (fixedBandMultipleCutoff n)

/-- The cutoff can still be chosen separately at every sample. -/
def fixedBandLateMinScore (n : ℕ) : ℝ :=
  (Icc 0 (n^2/4)).inf' (nonempty_Icc.mpr (Nat.zero_le _)) (fixedBandLateCutScore n)

def fixedBandLateMinMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandLateMinScore n) 0/(n:ℝ)^3

/-- For every allowed cut the late score is the single Möbius tail plus the
energy reserve left after paying the exact outer corner. -/
theorem fixedBandLateCutScore_eq {n L : ℕ} (hn : 2 ≤ n) (hL : L ≤ n^2/4) :
    fixedBandLateCutScore n L =
      fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n) +
        (fixedBandCutEnergy n L-fixedBandOuter (n^4) (n^2-L)) := by
  obtain ⟨h₁,h₂,h₃⟩ := fixedBandMultipleCutoff_bounds (V := n^2-L) hn
    (Nat.sub_le _ _) (by omega)
  have hN : 4 ≤ n^4 := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  rw [fixedBandLateCutScore,fixedBandQuadraticAfter_eq hN h₁ h₂ (by omega)]
  ring

private theorem fixedBandCutEnergy_pays_outer {n L : ℕ} (hL : L ≤ n^2/4) :
    fixedBandOuter (n^4) (n^2-L) ≤ fixedBandCutEnergy n L := by
  obtain rfl | hpos := Nat.eq_zero_or_pos L
  · rw [Nat.sub_zero,fixedBandOuter_zero (le_of_eq (by ring))]
    simp [fixedBandCutEnergy,fixedBandPrefixEnergy]
  · let V := n^2-L
    have hsize : 3*L ≤ V := by dsimp [V]; omega
    have hsum : V+L=n^2 := by dsimp [V]; omega
    have he := fixedBandOuter_near_energy hpos hsize
    rw [show (V+L)^2=n^4 by rw [hsum]; ring] at he
    exact (abs_le.mp he).2

/-- For late multiples the uncut square already attains the minimum. -/
theorem fixedBandLateMinScore_eq_tail {n : ℕ} (hn : 2 ≤ n) :
    fixedBandLateMinScore n = fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n) := by
  refine le_antisymm ?_ ?_
  · apply (inf'_le _ (mem_Icc.mpr ⟨le_rfl,Nat.zero_le (n^2/4)⟩)).trans_eq
    rw [fixedBandLateCutScore_eq hn (Nat.zero_le _),Nat.sub_zero,fixedBandOuter_zero (le_of_eq (by ring))]
    simp [fixedBandCutEnergy,fixedBandPrefixEnergy]
  · apply (le_inf'_iff (nonempty_Icc.mpr (Nat.zero_le _)) _).mpr
    intro L hL
    have h := (mem_Icc.mp hL).2
    rw [fixedBandLateCutScore_eq hn h]
    linarith only [fixedBandCutEnergy_pays_outer h]

/-- Evaluating the adaptive late-multiple mass only needs the single tail. -/
theorem fixedBandLateMinMass_eq_tail {m b : ℕ} (hm : 2 ≤ m) :
    fixedBandLateMinMass m b = fixedBandCriticalTailMass m b := by
  apply sum_congr rfl
  intro n hn
  rw [fixedBandLateMinScore_eq_tail (hm.trans (mem_Icc.mp hn).1)]

theorem fixedBandLateMinMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandLateMinMass m b| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBandCriticalTailMass_error
  refine ⟨C,hC,fun {m b} hm => ?_⟩
  rw [fixedBandLateMinMass_eq_tail hm]
  exact h hm

/-- The trimmed square-window estimate alone suffices for RH. -/
theorem rh_of_fixedBandTrimmed_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandTrimmedMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBand_upper_log_squareWindows _ _ h
  obtain ⟨K,hK,he⟩ := fixedBandTrimmedMass_error
  exact ⟨K,hK,fun {_ _} hm => (abs_le.mp (he hm)).2⟩

/-- A different energy-corrected cutoff may be chosen at every sample. -/
theorem rh_of_fixedBandMin_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMinMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBand_upper_log_squareWindows _ _ h
  obtain ⟨K,hK,he⟩ := fixedBandMinMass_error
  exact ⟨K,hK,fun {_ _} hm => (abs_le.mp (he hm)).2⟩

/-- A fixed quarter-width removal also suffices by a one-sided estimate. -/
theorem rh_of_fixedBandQuarter_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandQuarterMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis :=
  rh_of_fixedBand_upper_log_squareWindows _ fixedBandQuarterMass_upper h

/-- A logarithmic bound on the late-multiple scores suffices for RH. -/
theorem rh_of_fixedBandLateMin_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandLateMinMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBand_upper_log_squareWindows _ _ h
  obtain ⟨K,hK,he⟩ := fixedBandLateMinMass_error
  exact ⟨K,hK,fun {_ _} hm => (abs_le.mp (he hm)).2⟩

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandCorner_local_prefix,
      ``RiemannGaussian.AlpogeMined.fixedBandOuter_near_prefix,
      ``RiemannGaussian.AlpogeMined.fixedBand_prime_shortRoot_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandTrimmedMass_powerWindows,
      ``RiemannGaussian.AlpogeMined.fixedBandOuter_near_energy,
      ``RiemannGaussian.AlpogeMined.fixedBandQuarterMass_upper,
      ``RiemannGaussian.AlpogeMined.fixedBandMinMass_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandTrimmed_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandMin_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.fixedBandLateMinScore_eq_tail,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandLateMin_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandQuarter_log_squareWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  let imports := (← getEnv).header.moduleNames
  logInfo m!"Forward arithmetic implication uses {imports.size + 1} Lean modules including this module."
