import CheckAlpogeMinedBounds

/-! # Quadratic sign assignments for all sampled cutoffs at once -/

namespace RiemannGaussian.QuadraticPrefix
noncomputable section
open Finset Real RiemannGaussian.AlpogeMined

private def running (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => running g n + (if running g n ≤ 0 then g n else -g n)

/-- Greedy signs keep every initial sum within the largest allowed term. -/
theorem prefix_signs {g L : ℕ → ℝ} (h0 : 0 ≤ L 0) (hL : Monotone L)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ L (n+1)) :
    ∃ s : ℕ → ℤ, (∀ n, s n = 1 ∨ s n = -1) ∧
      ∀ n, |∑ p ∈ range n, (s p:ℝ)*g p| ≤ L n := by
  let s (n : ℕ) : ℤ := if running g n ≤ 0 then 1 else -1
  refine ⟨s,fun n => by dsimp [s]; split <;> simp,fun n => ?_⟩
  have he (k : ℕ) : ∑ p ∈ range k, (s p:ℝ)*g p = running g k := by
    induction k with
    | zero => simp [running]
    | succ k ih =>
      rw [sum_range_succ,ih,running]
      dsimp [s]
      split <;> simp
  rw [he]
  induction n with
  | zero => simpa [running] using h0
  | succ n ih =>
    obtain ⟨ha,hb⟩ := abs_le.mp ih
    have hm := hL (Nat.le_succ n)
    obtain ⟨hc,hd⟩ := hg n
    rw [running,abs_le]
    split <;> constructor <;> linarith

private theorem four_class_identity (a b α β : ℤ) (w : ℝ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) :
    ((if a = α ∧ b = β then (4:ℝ) else 0)-1)*w =
      (α:ℝ)*((a:ℝ)*w) + (2*β)*((b:ℝ)*(if a = α then w else 0)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> norm_num <;> ring

/-- Split each of the two signed classes once more. All four class discrepancies
then have prefix norm at most three times the largest allowed atom. -/
theorem prefix_four_classes {g L : ℕ → ℝ} (h0 : 0 ≤ L 0) (hL : Monotone L)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ L (n+1)) :
    ∃ s t : ℕ → ℤ, (∀ p, s p = 1 ∨ s p = -1) ∧ (∀ p, t p = 1 ∨ t p = -1) ∧
      ∀ α β : ℤ, (α = 1 ∨ α = -1) → (β = 1 ∨ β = -1) → ∀ j : ℕ,
        |∑ p ∈ range j, ((if s p = α ∧ t p = β then (4:ℝ) else 0)-1)*g p| ≤ 3*L j := by
  classical
  obtain ⟨s,hs,h1⟩ := prefix_signs h0 hL hg
  let group (α : ℤ) (p : ℕ) := if s p = α then g p else 0
  have hgroup (α : ℤ) (p : ℕ) : 0 ≤ group α p ∧ group α p ≤ L (p+1) := by
    dsimp [group]
    split
    · exact hg p
    · exact ⟨le_rfl,(hg p).1.trans (hg p).2⟩
  choose u hu h2 using fun α => prefix_signs h0 hL (hgroup α)
  let t (p : ℕ) := u (s p) p
  refine ⟨s,t,hs,fun p => hu _ p,fun α β hα hβ j => ?_⟩
  have identify (p : ℕ) :
      ((if s p = α ∧ t p = β then (4:ℝ) else 0)-1)*g p =
        (α:ℝ)*((s p:ℝ)*g p) + (2*β)*((u α p:ℝ)*group α p) := by
    have he : (s p = α ∧ t p = β) ↔ (s p = α ∧ u α p = β) := by
      constructor <;> rintro ⟨ha,hb⟩ <;> exact ⟨ha,by simpa [t,ha] using hb⟩
    simp only [he]
    exact four_class_identity _ _ _ _ _ (hs p) (hu α p) hα hβ
  have hαabs : |(α:ℝ)| = 1 := by rcases hα with rfl | rfl <;> norm_num
  have hβabs : |2*(β:ℝ)| = 2 := by rcases hβ with rfl | rfl <;> norm_num
  simp_rw [identify]
  rw [sum_add_distrib,← mul_sum,← mul_sum]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_mul,hαabs,hβabs,one_mul]
  linarith only [h1 j,h2 α j]

private theorem weighted_antitone {a b : ℕ} (hab : a < b) (f g : ℕ → ℝ) {L : ℝ}
    (hf : ∀ p ≥ a, 0 ≤ f p) (hdec : ∀ p ≥ a, f (p+1) ≤ f p)
    (hg : ∀ k ≤ b, |∑ p ∈ range k, g p| ≤ L) :
    |∑ p ∈ Ico a b, f p*g p| ≤ 2*L*f a := by
  let G k := ∑ p ∈ range k, g p
  have h := sum_Ico_by_parts f g hab
  simp only [smul_eq_mul] at h
  change (∑ p ∈ Ico a b, f p*g p) = f (b-1)*G b - f a*G a -
    ∑ p ∈ Ico a (b-1), (f (p+1)-f p)*G (p+1) at h
  have hb := hf (b-1) (by omega)
  have htail : |∑ p ∈ Ico a (b-1), (f (p+1)-f p)*G (p+1)| ≤ (f a-f (b-1))*L := by
    calc _ ≤ ∑ p ∈ Ico a (b-1), |(f (p+1)-f p)*G (p+1)| := abs_sum_le_sum_abs _ _
         _ ≤ ∑ p ∈ Ico a (b-1), (f p-f (p+1))*L := by
           apply sum_le_sum
           intro p hp
           obtain ⟨ha,hb'⟩ := mem_Ico.mp hp
           have hd := hdec p ha
           rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr hd),neg_sub]
           exact mul_le_mul_of_nonneg_left (hg _ (by omega)) (sub_nonneg.mpr hd)
         _ = _ := by
           rw [← sum_mul,sum_Ico_eq_sub _ (by omega),sum_range_sub',sum_range_sub']
           ring
  have hb' : |f (b-1)*G b| ≤ f (b-1)*L := by
    rw [abs_mul,abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (hg _ le_rfl) hb
  have ha' : |f a*G a| ≤ f a*L := by
    rw [abs_mul,abs_of_nonneg (hf a le_rfl)]
    exact mul_le_mul_of_nonneg_left (hg _ hab.le) (hf a le_rfl)
  rw [h]
  linarith only [abs_sub (f (b-1)*G b - f a*G a) (∑ p ∈ Ico a (b-1), (f (p+1)-f p)*G (p+1)),
    abs_sub (f (b-1)*G b) (f a*G a),htail,hb',ha']

/-- A bounded prefix discrepancy transfers to the reciprocal residue weights on
the band above the square root. The two monotone quotient terms each cost O(k). -/
theorem reciprocal_weight_bound {k : ℕ} (hk : 2 ≤ k) (g : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ j ≤ k^2+1, |∑ p ∈ range j, g p| ≤ L) :
    |∑ p ∈ Ioc k (k^2), weight (k^2) p*g p| ≤ 2*L*(1+2*k) := by
  let F (p : ℕ) : ℝ := 1+((k^2/p:ℕ):ℝ)
  let H (p : ℕ) : ℝ := (k:ℝ)^2/p
  have hlt : k+1 < k^2+1 := by
    have hkk : k < k^2 := by simpa [pow_two] using Nat.mul_lt_mul_of_pos_left (show 1 < k by omega) (show 0 < k by omega)
    omega
  have hF := weighted_antitone hlt F g (fun p _ => by dsimp [F]; positivity)
    (fun p hp => by
      dsimp [F]
      exact add_le_add_right (Nat.cast_le.mpr (Nat.div_le_div_left (Nat.le_succ p) (by omega))) _) h
  have hH := weighted_antitone hlt H g (fun p _ => by dsimp [H]; positivity)
    (fun p hp => by
      dsimp [H]
      apply div_le_div_of_nonneg_left (sq_nonneg _)
      · exact_mod_cast (show 0 < p by omega)
      · exact_mod_cast Nat.le_succ p) h
  rw [Ico_add_one_add_one_eq_Ioc] at hF hH
  have hw (p : ℕ) (hp : p ∈ Ioc k (k^2)) : weight (k^2) p = F p-H p := by
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by have := (mem_Ioc.mp hp).1; omega)
    have he : ((k^2%p:ℕ):ℝ)+(p:ℝ)*((k^2/p:ℕ):ℝ) = (k:ℝ)^2 := by exact_mod_cast Nat.mod_add_div (k^2) p
    unfold weight F H
    field_simp
    linarith only [he]
  have hq : k^2/(k+1) ≤ k := by
    by_contra! hh
    have he := (Nat.le_div_iff_mul_le (by omega : 0 < k+1)).mp (show k+1 ≤ k^2/(k+1) by omega)
    nlinarith only [he]
  have hf1 : F (k+1) ≤ 1+(k:ℝ) := by dsimp [F]; exact add_le_add_right (Nat.cast_le.mpr hq) _
  have hh1 : H (k+1) ≤ k := by
    dsimp [H]
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  rw [sum_congr rfl (fun p hp => by rw [hw p hp,sub_mul]),sum_sub_distrib]
  linarith only [abs_sub (∑ p ∈ Ioc k (k^2), F p*g p) (∑ p ∈ Ioc k (k^2), H p*g p),hF,hH,
    mul_le_mul_of_nonneg_left hf1 (show 0 ≤ 2*L by positivity),
    mul_le_mul_of_nonneg_left hh1 (show 0 ≤ 2*L by positivity)]

end
end RiemannGaussian.QuadraticPrefix
