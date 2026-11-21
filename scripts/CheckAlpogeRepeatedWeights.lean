import CheckAlpogeResidueAverage

/-! # Repeated averaging of reciprocal prime weights -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real AlpogeZetaSamples

private def blockMap (W : ℕ) : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f a := blockMean a W f
  map_add' f g := by
    ext a
    simp only [blockMean,Pi.add_apply,Finset.sum_add_distrib,add_div]
  map_smul' c f := by
    ext a
    simp only [blockMean,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,← Finset.mul_sum]
    ring

/-- The mean after k independent integer shifts uniform on the range from zero to W−1. -/
def repeatedMean (W : ℕ) : ℕ → (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ)
  | 0 => LinearMap.id
  | k+1 => (blockMap W).comp (repeatedMean W k)

private theorem block_const (A : ℕ) {W : ℕ} (hw : 0 < W) (c : ℝ) :
    blockMean A W (fun _ => c) = c := by simp [blockMean, (Nat.cast_pos.mpr hw : (0:ℝ) < W).ne']

private theorem block_sub (A W : ℕ) (f g : ℕ → ℝ) :
    blockMean A W (fun t => f t-g t) = blockMean A W f-blockMean A W g := by
  simp only [blockMean,Finset.sum_sub_distrib,sub_div]

private theorem block_mono {A W : ℕ} {f g : ℕ → ℝ}
    (h : ∀ j ∈ range W, f (A+j) ≤ g (A+j)) : blockMean A W f ≤ blockMean A W g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private theorem block_zero_period {d W : ℕ} {f : ℕ → ℝ}
    (hz : ∀ A, ∑ j ∈ range d, f (A+j)=0) (A : ℕ) :
    ∑ j ∈ range d, blockMean (A+j) W f=0 := by
  simp only [blockMean,← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [show ∀ j i : ℕ, A+i+j=A+j+i by intros; omega,hz,Finset.sum_const_zero,zero_div]

private theorem short_remainder {d W : ℕ} (hd : 0 < d) {f : ℕ → ℝ}
    (hz : ∀ A, ∑ j ∈ range d, f (A+j)=0) {K : ℝ}
    (hb : ∀ a, |f a| ≤ K) (A : ℕ) :
    |∑ j ∈ range W, f (A+j)| ≤ (min (W%d) (d-W%d):ℕ)*K := by
  have full (q r : ℕ) (a : ℕ) :
      ∑ j ∈ range (q*d+r), f (a+j) = ∑ j ∈ range r, f (a+q*d+j) := by
    induction q generalizing a with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul,show q*d+d+r=d+(q*d+r) by omega,Finset.sum_range_add,hz,zero_add]
      simpa only [← Nat.add_assoc,show a+d+q*d=a+(q*d+d) by omega] using ih (a+d)
  have he : W/d*d+W%d=W := Nat.div_add_mod' W d
  have hh := full (W/d) (W%d) A
  rw [he] at hh
  rw [hh]
  let r := W%d
  let B := A+(W/d)*d
  have bound (t a : ℕ) : |∑ j ∈ range t, f (a+j)| ≤ (t:ℝ)*K :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hb (a+j)).trans_eq
      (by simp [nsmul_eq_mul]))
  change |∑ j ∈ range r, f (B+j)| ≤ (min r (d-r):ℕ)*K
  by_cases h : r ≤ d-r
  · rw [min_eq_left h]
    exact bound r B
  · rw [min_eq_right (by omega : d-r ≤ r)]
    have hr : r ≤ d := (Nat.mod_lt W hd).le
    have hzero := hz B
    conv at hzero => lhs; rw [show d=r+(d-r) by omega, sum_range_add]
    have heq : (∑ j ∈ range r, f (B+j)) = -(∑ j ∈ range (d-r), f (B+r+j)) := by
      simp only [← Nat.add_assoc] at hzero
      linarith only [hzero]
    rw [heq, abs_neg]
    exact bound _ _

/-- Full periods cancel at every pass. The shorter of the remaining interval
and its complement bounds the oscillation. -/
theorem repeated_weight_residue_error {d W : ℕ} (hd : 0 < d) (hw : 0 < W) (k A : ℕ) :
    |repeatedMean W k (fun M => weight M d) A-(1/2+1/(2*(d:ℝ)))| ≤
      (((min (W%d) (d-W%d):ℕ):ℝ)/W)^k := by
  let r := min (W%d) (d-W%d)
  let c : ℝ := 1/2+1/(2*(d:ℝ))
  have hz (a : ℕ) : ∑ j ∈ range d, (weight (a+j) d-c)=0 := by
    rw [Finset.sum_sub_distrib,weight_block_identity _ _ hd]
    simp [c,residueTerm]
    ring
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hr : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hdiv : 1/(2*(d:ℝ)) ≤ 1/2 := by apply (div_le_iff₀ (by positivity)).mpr; linarith
    linarith
  have hb (a : ℕ) : |weight a d-c| ≤ 1 := by
    have hr : ((a%d:ℕ):ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt a hd).le
    have hp : (0:ℝ) < d := by exact_mod_cast hd
    have hm := (div_le_one hp).mpr hr
    unfold weight
    exact abs_le.mpr ⟨by linarith,by linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) (a%d)) hp.le]⟩
  suffices ht : (∀ a, |repeatedMean W k (fun M => weight M d) a-c| ≤ ((r:ℝ)/W)^k) ∧
      ∀ a, ∑ j ∈ range d, (repeatedMean W k (fun M => weight M d) (a+j)-c)=0 from ht.1 A
  induction k with
  | zero => exact ⟨by simpa [repeatedMean] using hb,by simpa [repeatedMean] using hz⟩
  | succ k ih =>
    let f := repeatedMean W k (fun M => weight M d)
    have he (a : ℕ) : repeatedMean W (k+1) (fun M => weight M d) a-c =
        blockMean a W (fun t => f t-c) := by rw [block_sub,block_const a hw]; rfl
    constructor
    · intro a
      rw [he,blockMean,abs_div,show |(W:ℝ)| = W from abs_of_nonneg (Nat.cast_nonneg W)]
      apply (div_le_iff₀ (Nat.cast_pos.mpr hw : (0:ℝ)<W)).mpr
      apply (short_remainder hd ih.2 ih.1 a).trans_eq
      rw [pow_succ]
      dsimp only [r]
      field_simp
    · intro a
      simp_rw [he]
      exact block_zero_period ih.2 a

/-- Each averaging pass saves at least the ratio of the period to the block width. -/
theorem repeated_weight_error {d W : ℕ} (hd : 0 < d) (hw : 0 < W) (k A : ℕ) :
    |repeatedMean W k (fun M => weight M d) A-(1/2+1/(2*(d:ℝ)))| ≤ ((d:ℝ)/W)^k := by
  apply (repeated_weight_residue_error hd hw k A).trans
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg W)
  exact_mod_cast (min_le_left (W%d) (d-W%d)).trans (Nat.mod_lt W hd).le

private theorem block_add_const (A : ℕ) {W : ℕ} (hw : 0 < W) (f : ℕ → ℝ) (c : ℝ) :
    blockMean A W (fun x => f x+c)=blockMean A W f+c := by
  have hh := congrFun ((blockMap W).map_add f (fun _ => c)) A
  change blockMean A W (fun x => f x+c)=blockMean A W f+blockMean A W (fun _ => c) at hh
  rwa [block_const A hw] at hh

/-- Each repeated average fixes every constant function. -/
theorem repeat_const {W : ℕ} (hw : 0 < W) (k A : ℕ) (c : ℝ) :
    repeatedMean W k (fun _ => c) A=c := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
    change blockMean A W (repeatedMean W k (fun _ => c))=c
    rw [show repeatedMean W k (fun _ => c) = fun _ => c by funext a; exact ih a,block_const A hw]

/-- Pointwise order on the support of the shifts is preserved by the repeated mean. -/
theorem repeat_mono (W k A : ℕ) {f g : ℕ → ℝ}
    (h : ∀ M, A ≤ M → M ≤ A+k*(W-1) → f M ≤ g M) :
    repeatedMean W k f A ≤ repeatedMean W k g A := by
  induction k generalizing A with
  | zero => exact h A le_rfl (by simp)
  | succ k ih =>
    apply block_mono
    intro j hj
    apply ih
    intro M hl hu
    have hj' := mem_range.mp hj
    apply h M (by omega)
    rw [Nat.succ_mul]
    omega

/-- The mean cutoff increases by H for each shift of width 2H+1. -/
theorem repeat_first_moment (H k A : ℕ) :
    repeatedMean (2*H+1) k (fun t => (t:ℝ)) A = A+(k:ℝ)*H := by
  induction k generalizing A with
  | zero => simp [repeatedMean]
  | succ k ih =>
    change blockMean A (2*H+1) (repeatedMean (2*H+1) k (fun t => (t:ℝ)))=_
    rw [funext ih,block_add_const A (by omega)]
    have hh := mean_center (N := A+H) (H := H) (by omega)
    rw [Nat.add_sub_cancel] at hh
    unfold blockMean
    rw [hh]
    push_cast
    field_simp
    ring

/-- After k passes the entire prime contribution up to D differs on the lower side
from half its mass by at most theta(D) times (D/W) to the kth power. -/
theorem repeated_low_prime_lower {W : ℕ} (hw : 0 < W) (D k A : ℕ) :
    Chebyshev.theta D*(1/2-((D:ℝ)/W)^k) ≤
      repeatedMean W k (fun M => lowPrimeSum M D) A := by
  let s := (Ioc 0 D).filter Nat.Prime
  have htheta : Chebyshev.theta D = ∑ p ∈ s, log p := by simp [Chebyshev.theta,s]
  have he : (fun M => lowPrimeSum M D) = ∑ p ∈ s, (log p) • (fun M => weight M p) := by
    ext M
    simp [s,lowPrimeSum,Finset.sum_apply]
  rw [he,map_sum,Finset.sum_apply,htheta,Finset.sum_mul]
  simp only [map_smul,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpD,hp'⟩ := mem_filter.mp hp
  have hle : (p:ℝ) ≤ D := by exact_mod_cast (mem_Ioc.mp hpD).2
  have hh := (abs_le.mp (repeated_weight_error hp'.pos hw k A)).1
  have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg W))
    (div_le_div_of_nonneg_right hle (Nat.cast_nonneg W)) k
  apply mul_le_mul_of_nonneg_left _ (log_natCast_nonneg p)
  linarith only [hh,hpow,show 0 ≤ 1/(2*(p:ℝ)) by positivity]

/-- Repeated averaging still controls the actual central sample. The accumulated
convexity error is at most k times the squared radius divided by the smallest cutoff. -/
theorem G_le_repeatedMean {A : ℕ} (hA : 0 < A) (H k : ℕ) :
    G (A+k*H : ℕ) ≤ repeatedMean (2*H+1) k (fun M => G M) A+(k:ℝ)*H^2/A := by
  induction k generalizing A with
  | zero => simp [repeatedMean]
  | succ k ih =>
    let f := repeatedMean (2*H+1) k (fun M => G M)
    have hh := G_le_blockMean (N := A+(k+1)*H) (H := H) (by rw [Nat.succ_mul]; omega)
    rw [show A+(k+1)*H-H=A+k*H by rw [Nat.succ_mul]; omega] at hh
    have hav : blockMean (A+k*H) (2*H+1) (fun M => G M) ≤
        blockMean A (2*H+1) f+(k:ℝ)*H^2/A := by
      rw [← block_add_const A (by omega)]
      change (∑ j ∈ range (2*H+1), G (A+k*H+j:ℕ))/(2*H+1:ℕ) ≤ _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      have ht := ih (A := A+j) (by omega)
      rw [show A+j+k*H=A+k*H+j by omega] at ht
      have he := div_le_div_of_nonneg_left (show 0 ≤ (k:ℝ)*H^2 by positivity)
        (Nat.cast_pos.mpr hA) (show (A:ℝ) ≤ (A+j:ℕ) by exact_mod_cast Nat.le_add_right A j)
      exact ht.trans (add_le_add le_rfl he)
    have hd := div_le_div_of_nonneg_left (sq_nonneg (H:ℝ)) (Nat.cast_pos.mpr hA)
      (show (A:ℝ) ≤ (A+(k+1)*H:ℕ) by exact_mod_cast Nat.le_add_right A ((k+1)*H))
    change G _ ≤ blockMean A (2*H+1) f+_
    rw [Nat.cast_succ,add_mul (k:ℝ) 1,one_mul,add_div]
    linarith only [hh,hav,hd]

/-- A finite-sample bound at any averaging order. The remaining summand uses only
ordinary primes above D, with all smoothing and endpoint costs explicit. -/
theorem G_le_repeated_prime_tail {A D : ℕ} (hA : 0 < A) (hD : D ≤ A) (H k : ℕ) :
    G (A+k*H : ℕ) ≤ eulerMascheroniConstant*((A:ℝ)+(k:ℝ)*H)-Chebyshev.theta D/2-
      repeatedMean (2*H+1) k (fun M => upperPrimeSum M D) A+
      (1+log (A+k*(2*H):ℕ)/2)+(k:ℝ)*H^2/A+Chebyshev.theta D*((D:ℝ)/(2*(H:ℝ)+1))^k := by
  let W := 2*H+1
  let T := A+k*(2*H)
  let c := 1+log T/2
  have hw : 0 < W := by dsimp [W]; omega
  have hh := @repeat_mono W k A (fun M => G M+lowPrimeSum M D+upperPrimeSum M D)
    (fun M => eulerMascheroniConstant*M+c) (by
      intro M hmin hmax
      have hpos := hA.trans_le hmin
      have hm : M ≤ T := by simpa [W,T] using hmax
      have hs := (integer_sample_bounds hpos).2
      rw [split_primeSum (D := D) (hD.trans hmin)] at hs
      have hl := log_le_log (Nat.cast_pos.mpr hpos) (show (M:ℝ) ≤ T by exact_mod_cast hm)
      dsimp [c]
      linarith)
  let L := repeatedMean W k
  change L ((fun M : ℕ => G M) + (fun M => lowPrimeSum M D) + (fun M => upperPrimeSum M D)) A ≤
    L (eulerMascheroniConstant • (fun M : ℕ => (M:ℝ)) + (fun _ => c)) A at hh
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hh
  have ha := repeat_first_moment H k A
  change L (fun t : ℕ => (t:ℝ)) A = _ at ha
  rw [ha,show L (fun _ => c) A=c from repeat_const hw k A c] at hh
  have hlow := repeated_low_prime_lower hw D k A
  have hg := G_le_repeatedMean hA H k
  change G _ ≤ L (fun M => G M) A+_ at hg
  change _ ≤ L (fun M => lowPrimeSum M D) A at hlow
  have hW : (W:ℝ)=2*(H:ℝ)+1 := by dsimp [W]; push_cast; ring
  rw [hW] at hlow
  change G _ ≤ _-_-L (fun M => upperPrimeSum M D) A+c+_+_
  linarith only [hg,hh,hlow]

/-- At order k the endpoint in terms of n is the floor of n to the power 3−1/(k+1). -/
def repeatedCutoff (k n : ℕ) : ℕ := ⌊(n:ℝ)^(3-1/((k:ℝ)+1))⌋₊

/-- Only primes strictly beyond the order-dependent cutoff have an oscillatory weight
in this deficit at the fourth power n^4. -/
def repeatedTailAt (k n D : ℕ) : ℝ :=
  eulerMascheroniConstant*(n:ℝ)^4-Chebyshev.theta D/2-
    repeatedMean (2*n^3+1) k (fun M => upperPrimeSum M D) (n^4-k*n^3)

/-- The deficit at the fixed-order cutoff. -/
def repeatedDeficit (k n : ℕ) : ℝ := repeatedTailAt k n (repeatedCutoff k n)

/-- The geometric residue bound summed over ordinary primes costs at most square-root
scale when the displayed power inequality for the cutoff holds. -/
theorem repeated_endpoint_cost {k n D : ℕ}
    (hsize : (D:ℝ)^(k+1) ≤ (n:ℝ)^2*(2*(n:ℝ)^3+1)^k) :
    Chebyshev.theta D*((D:ℝ)/(2*(n:ℝ)^3+1))^k ≤ (log 4+4)*(n:ℝ)^2 := by
  have htheta := (Chebyshev.theta_le_psi D).trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg D))
  let L := log 4+4
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hW : 0 < 2*(n:ℝ)^3+1 := by positivity
  apply (mul_le_mul_of_nonneg_right htheta (pow_nonneg (by positivity) k)).trans
  rw [div_pow,← mul_div_assoc,div_le_iff₀ (pow_pos hW k)]
  have hm := mul_le_mul_of_nonneg_left hsize hL
  rw [pow_succ] at hm
  dsimp [L] at hm
  linarith only [hm]

private theorem fourth_at_cutoff {k n D : ℕ} (hn : 2 ≤ n) (hk : 2*k ≤ n)
    (hD3 : D ≤ n^3) (hsize : (D:ℝ)^(k+1) ≤ (n:ℝ)^2*(2*(n:ℝ)^3+1)^k) :
    G ((n:ℝ)^4) ≤ repeatedTailAt k n D+(2*(k:ℝ)+8+log 4)*(n:ℝ)^2 := by
  let A := n^4-k*n^3
  have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hhalf : 2*(k*n^3) ≤ n^4 := by
    simpa only [← Nat.mul_assoc,show n^4=n*n^3 by ring] using Nat.mul_le_mul_right (n^3) hk
  have hH : 2*n^3 ≤ n^4 := (Nat.mul_le_mul_right (n^3) hn).trans_eq (by ring)
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < n^4 := by positivity
    omega
  have hA2 : (n:ℝ)^4 ≤ 2*(A:ℝ) := by exact_mod_cast (show n^4 ≤ 2*A by dsimp [A]; omega)
  have hc : A+k*n^3=n^4 := by dsimp [A]; omega
  have hcut : D ≤ A := by
    dsimp [A]; omega
  have hmid : (A:ℝ)+(k:ℝ)*(n:ℝ)^3=(n:ℝ)^4 := by exact_mod_cast hc
  have hh := G_le_repeated_prime_tail hA hcut (n^3) k
  rw [hc] at hh
  push_cast at hh
  rw [hmid] at hh
  have hquad : (k:ℝ)*((n:ℝ)^3)^2/A ≤ 2*k*(n:ℝ)^2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hA)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hA2 (show 0 ≤ (k:ℝ)*(n:ℝ)^2 by positivity)]
  have herr := repeated_endpoint_cost hsize
  have hsum : (A:ℝ)+k*(2*(n:ℝ)^3) ≤ 2*(n:ℝ)^4 := by linarith only [hmid,Nat.cast_nonneg (α := ℝ) A]
  have hl := log_le_log (show 0 < (A:ℝ)+k*(2*(n:ℝ)^3) by positivity) hsum
  rw [log_mul (by norm_num) (by positivity),log_pow] at hl
  have hlog : 1+log ((A:ℝ)+k*(2*(n:ℝ)^3))/2 ≤ 4*(n:ℝ)^2 := by
    norm_num at hl
    nlinarith only [hl,log_le_sub_one_of_pos hn0,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),
      sq_nonneg ((n:ℝ)-1),hnR]
  unfold repeatedTailAt
  linarith only [hh,herr,hquad,hlog]

/-- The order-k prime tail gives a square-root-error bound on the actual fourth-power sample. -/
theorem G_fourth_le_repeated_deficit (k n : ℕ) (hn : 2 ≤ n) (hk : 2*k ≤ n) :
    G ((n:ℝ)^4) ≤ repeatedDeficit k n+(2*(k:ℝ)+8+log 4)*(n:ℝ)^2 := by
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 := zero_lt_one.trans_le hn1
  have hk1 : 0 < (k:ℝ)+1 := by positivity
  have hr := Nat.floor_le (Real.rpow_nonneg hn0.le (3-1/((k:ℝ)+1)))
  change ((repeatedCutoff k n:ℕ):ℝ) ≤ _ at hr
  have hD3 := hr.trans (Real.rpow_le_rpow_of_exponent_le hn1
    (show 3-1/((k:ℝ)+1) ≤ 3 by linarith [one_div_nonneg.mpr hk1.le]))
  rw [Real.rpow_ofNat] at hD3
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (repeatedCutoff k n)) hr (k+1)
  rw [← Real.rpow_mul_natCast hn0.le,show (3-1/((k:ℝ)+1))*((k+1:ℕ):ℝ)=((3*k+2:ℕ):ℝ) by
    push_cast; field_simp; ring,Real.rpow_natCast,pow_add (n:ℝ) (3*k) 2,pow_mul (n:ℝ) 3 k] at hs
  have hWpow := pow_le_pow_left₀ (pow_nonneg hn0.le 3)
    (show (n:ℝ)^3 ≤ 2*(n:ℝ)^3+1 by linarith [pow_nonneg hn0.le 3]) k
  exact fourth_at_cutoff hn hk (by exact_mod_cast hD3)
    (hs.trans ((mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left hWpow (sq_nonneg (n:ℝ)))))

/-- For n at least eight, one more pass than the binary logarithm keeps every
observation positive and bounds the residues of all primes through n cubed. -/
theorem cubic_tail_parameters {n : ℕ} (hn : 8 ≤ n) :
    let k := Nat.log 2 n+1
    2*k ≤ n ∧ ((n^3:ℕ):ℝ)^(k+1) ≤ (n:ℝ)^2*(2*(n:ℝ)^3+1)^k := by
  let k := Nat.log 2 n+1
  have hl : 3 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega : n ≠ 0)).mpr hn
  have hp (j : ℕ) (hj : 3 ≤ j) : 2*(j+1) ≤ 2^j := by
    induction j, hj using Nat.le_induction with
    | base => decide
    | succ j _ ih => rw [pow_succ]; omega
  have hk : 2*k ≤ n := (hp _ hl).trans (Nat.pow_log_le_self 2 (by omega))
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hbig : (n:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hs : (((n^3:ℕ):ℝ))^(k+1) ≤ (n:ℝ)^2*(2*(n:ℝ)^3+1)^k := by
    push_cast
    rw [pow_succ]
    calc ((n:ℝ)^3)^k*(n:ℝ)^3 ≤ (n:ℝ)^2*(2*(n:ℝ)^3)^k := by
           rw [mul_pow]
           nlinarith only [mul_le_mul_of_nonneg_left hbig (show 0 ≤ (n:ℝ)^2*((n:ℝ)^3)^k by positivity)]
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity)
  exact ⟨hk,hs⟩

/-- With logarithmically many shifts the entire band through n cubed has only a
logarithmic loss in the square-root cost at the central sample. -/
theorem G_fourth_le_cubic_tail (n : ℕ) (hn : 8 ≤ n) :
    G ((n:ℝ)^4) ≤ repeatedTailAt (Nat.log 2 n+1) n (n^3)+
      (2*((Nat.log 2 n:ℕ):ℝ)+10+log 4)*(n:ℝ)^2 := by
  obtain ⟨hk,hs⟩ := cubic_tail_parameters hn
  have hg := fourth_at_cutoff (by omega : 2 ≤ n) hk (le_refl (n^3)) hs
  push_cast at hg
  convert hg using 1
  ring

end
end RiemannGaussian.AlpogeMined
