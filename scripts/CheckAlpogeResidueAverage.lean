import CheckAlpogeMinedBounds

/-! # Square-root-cost removal of small primes by averaging adjacent cutoffs -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real AlpogeZetaSamples

/-- The weighted ordinary primes up to a fixed cutoff at observation M. -/
def lowPrimeSum (M D : ℕ) : ℝ :=
  ∑ p ∈ (Ioc 0 D).filter Nat.Prime, log p * weight M p

/-- The weighted ordinary primes strictly above D and up to the observation M. -/
def upperPrimeSum (M D : ℕ) : ℝ :=
  ∑ p ∈ (Ioc D M).filter Nat.Prime, log p * weight M p

/-- Split the ordinary-prime contribution at a fixed integer cutoff. -/
theorem split_primeSum {M D : ℕ} (hD : D ≤ M) :
    primeSum M = lowPrimeSum M D + upperPrimeSum M D := by
  unfold primeSum lowPrimeSum upperPrimeSum
  simp only [sum_filter]
  exact (Finset.sum_Ioc_consecutive (f := fun p : ℕ => if p.Prime then log p*weight M p else 0)
    (Nat.zero_le D) hD).symm

/-- Mean over W consecutive integer cutoffs, beginning with A. -/
def blockMean (A W : ℕ) (f : ℕ → ℝ) : ℝ := (∑ j ∈ range W, f (A+j))/W

/-- The quadratic boundary correction of a partial residue period. -/
def residueTerm (M d : ℕ) : ℝ :=
  ((M % d : ℕ):ℝ)*(d-((M % d : ℕ):ℝ))/(2*d)

/-- Sharp continuous bounds on the quadratic residue correction. -/
theorem residue_bounds (M : ℕ) {d : ℕ} (hd : 0 < d) :
    0 ≤ residueTerm M d ∧ residueTerm M d ≤ (d:ℝ)/8 := by
  have hp : (0:ℝ) < d := by exact_mod_cast hd
  have hr : ((M%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt M hd
  unfold residueTerm
  constructor
  · positivity [sub_nonneg.mpr hr.le]
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg ((d:ℝ)-2*((M%d:ℕ):ℝ))]

private theorem residue_diff (M : ℕ) {d : ℕ} (hd : 0 < d) :
    weight M d = 1/2 + 1/(2*(d:ℝ)) + residueTerm (M+1) d - residueTerm M d := by
  have hpos : (0:ℝ) < d := by exact_mod_cast hd
  have hr := Nat.mod_lt M hd
  unfold residueTerm weight
  rw [← Nat.mod_add_mod M d 1]
  rcases lt_or_eq_of_le (show M%d+1 ≤ d by omega) with h|h
  · rw [Nat.mod_eq_of_lt h, Nat.cast_add_one]
    field_simp
    ring
  · have he : ((M%d:ℕ):ℝ)+1 = d := by exact_mod_cast h
    rw [h,Nat.mod_self,Nat.cast_zero]
    field_simp
    nlinarith only [he,congrArg (fun x : ℝ => x*((M%d:ℕ):ℝ)) he]

/-- Every full residue period has mean one half plus one over twice the denominator.
Only the two end residues affect a finite block. -/
theorem weight_block_identity (A W : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ j ∈ range W, weight (A+j) d) =
      W*(1/2+1/(2*(d:ℝ)))+residueTerm (A+W) d-residueTerm A d := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [sum_range_succ,ih,residue_diff _ hd,Nat.cast_succ]
    rw [Nat.add_assoc A W 1]
    ring

/-- Averaging bounds the contribution of every prime through D from below with an explicit
endpoint error at most D times Chebyshev theta(D) divided by eight times the block length. -/
theorem mean_low_prime_lower (A W D : ℕ) (hW : 0 < W) :
    Chebyshev.theta D/2 - D*Chebyshev.theta D/(8*W) ≤ blockMean A W (fun M => lowPrimeSum M D) := by
  let s := (Ioc 0 D).filter Nat.Prime
  have htheta : Chebyshev.theta D = ∑ p ∈ s, log p := by simp [Chebyshev.theta,s]
  have hp (d : ℕ) (hd : d ∈ s) : 0 < d := (mem_filter.mp hd).2.pos
  have hl (d : ℕ) (hd : d ∈ s) : 0 ≤ log d := log_nonneg (by exact_mod_cast hp d hd)
  have hweight (d : ℕ) (hd : d ∈ s) :
      (W:ℝ)/2 - D/8 ≤ ∑ j ∈ range W, weight (A+j) d := by
    have hdD : (d:ℝ) ≤ D := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hd).1).2
    rw [weight_block_identity A W (hp d hd)]
    linarith only [(residue_bounds (A+W) (hp d hd)).1,(residue_bounds A (hp d hd)).2,
      hdD,mul_nonneg (Nat.cast_nonneg (α := ℝ) W) (show 0 ≤ 1/(2*(d:ℝ)) by positivity)]
  have hs := Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hweight d hd) (hl d hd))
  rw [← Finset.sum_mul, ← htheta] at hs
  have hW' : (0:ℝ) < W := by exact_mod_cast hW
  unfold blockMean lowPrimeSum
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  apply (le_div_iff₀ hW').mpr
  convert hs using 1
  field_simp

private theorem midpoint_upper {x a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : a+b=2*x)
    (hda : -h ≤ a-x) (hda' : a-x ≤ h) :
    2*G x ≤ G a+G b+2*h^2/x := by
  have hx0 : 0 < x := by linarith
  have hconv {u v : ℝ} (hu : 0 < u) (hv : u ≤ v) (he : u+v=2*x) :
      2*ramp x ≤ ramp u+ramp v := by
    have hc := ramp_le_chord hu.le (by linarith : u ≤ x) (by linarith : x ≤ v)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num) (by linarith : x=(1/2)*u+(1/2)*v)
    linarith
  have hc : 2*ramp x ≤ ramp a+ramp b := by
    rcases le_total a b with hh|hh
    · exact hconv ha hh hx
    · linarith only [hconv hb hh (by linarith : b+a=2*x)]
  have hlog (t : ℝ) (ht : 0 < t) :
      t*log t-t*log x ≤ t-x+(t-x)^2/x := by
    calc _ = t*log (t/x) := by rw [Real.log_div ht.ne' hx0.ne']; ring
         _ ≤ t*(t/x-1) := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht hx0)) ht.le
         _ = _ := by field_simp; ring
  have hs := div_le_div_of_nonneg_right (sq_le_sq' hda hda') hx0.le
  have he : (b-x)^2/x = (a-x)^2/x := by rw [show b-x=-(a-x) by linarith]; ring
  have hh := hlog b hb
  rw [he] at hh
  have hl := hlog a ha
  have heL := congrArg (fun z : ℝ => z*log x) hx
  have heC := congrArg (fun z : ℝ => (1+Real.eulerMascheroniConstant)*z) hx
  unfold G
  ring_nf at hc hl hh hs hx heL heC ⊢
  linarith only [hc,hl,hh,hs,hx,heL,heC]

/-- The average over a symmetric block controls its central sample at quadratic cost. -/
theorem G_le_blockMean {N H : ℕ} (hH : H < N) :
    G N ≤ blockMean (N-H) (2*H+1) (fun M => G M)+(H:ℝ)^2/N := by
  let A := N-H
  let W := 2*H+1
  have hW : 0 < W := by dsimp [W]; omega
  have hW' : (0:ℝ) < W := by exact_mod_cast hW
  have hA : 0 < A := by dsimp [A]; omega
  have hpair (j : ℕ) (hj : j ∈ range W) :
      2*G N-2*(H:ℝ)^2/N ≤ G (A+j : ℕ) + G (A+(W-1-j) : ℕ) := by
    have hj' := mem_range.mp hj
    have he : (A+j)+(A+(W-1-j))=2*N := by dsimp [A,W] at *; omega
    have hsum : ((A+j : ℕ):ℝ)+((A+(W-1-j) : ℕ):ℝ) = 2*N := by exact_mod_cast he
    have h1 : N ≤ (A+j)+H := by dsimp [A]; omega
    have h2 : A+j ≤ N+H := by dsimp [A,W] at *; omega
    have hl : (N:ℝ) ≤ ((A+j : ℕ):ℝ)+H := by exact_mod_cast h1
    have hr : ((A+j : ℕ):ℝ) ≤ (N:ℝ)+H := by exact_mod_cast h2
    linarith only [midpoint_upper (by positivity : (0:ℝ) < (A+j : ℕ))
      (by positivity : (0:ℝ) < (A+(W-1-j) : ℕ)) hsum (by linarith : -(H:ℝ) ≤ (A+j : ℕ)-(N:ℝ)) (by linarith : ((A+j : ℕ):ℝ)-N ≤ H)]
  have hh := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, Finset.sum_range_reflect (fun j : ℕ => G (A+j : ℕ)) W] at hh
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  change G N ≤ (∑ j ∈ range W, G (A+j : ℕ))/W+(H:ℝ)^2/N
  rw [← sub_le_iff_le_add,le_div_iff₀ hW']
  ring_nf at hh ⊢
  linarith only [hh]

/-- A symmetric block of integer observations has first moment equal to its center times its length. -/
theorem mean_center {N H : ℕ} (hH : H ≤ N) :
    (∑ j ∈ range (2*H+1), (((N-H+j : ℕ):ℝ))) = (2*(H:ℝ)+1)*N := by
  let A := N-H
  let W := 2*H+1
  have he : ∀ j ∈ range W, ((A+j : ℕ):ℝ)+((A+(W-1-j) : ℕ):ℝ)=2*N := by
    intro j hj
    have hj' := mem_range.mp hj
    exact_mod_cast (show (A+j)+(A+(W-1-j)) = 2*N by dsimp [A,W] at *; omega)
  have hh := Finset.sum_congr rfl he
  rw [Finset.sum_add_distrib,Finset.sum_range_reflect (fun j : ℕ => ((A+j:ℕ):ℝ)) W] at hh
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  change (∑ j ∈ range W, ((A+j:ℕ):ℝ)) = _
  have hw : (W:ℝ)=2*(H:ℝ)+1 := by dsimp [W]; push_cast; ring
  rw [hw] at hh
  linarith only [hh]

/-- A single centered-ramp sample is bounded by the average tail above D. The primes
through D contribute half their actual mass with a finite endpoint cost. -/
theorem G_le_mean_upper_primes {N H D : ℕ} (hH : H < N) (hD : D ≤ N-H) :
    G N ≤ Real.eulerMascheroniConstant*N - Chebyshev.theta D/2
      - blockMean (N-H) (2*H+1) (fun M => upperPrimeSum M D)
      + (1+log (N+H : ℕ)/2) + (H:ℝ)^2/N + D*Chebyshev.theta D/(8*(2*(H:ℝ)+1)) := by
  let A := N-H
  let W := 2*H+1
  have hW : 0 < W := by dsimp [W]; omega
  have hW' : (0:ℝ) < W := by exact_mod_cast hW
  have hw : (W:ℝ)=2*(H:ℝ)+1 := by dsimp [W]; push_cast; ring
  have hc := mean_center hH.le
  change (∑ j ∈ range W, ((A+j:ℕ):ℝ)) = _ at hc
  rw [← hw] at hc
  have hpoint (j : ℕ) (hj : j ∈ range W) :
      G (A+j : ℕ)+lowPrimeSum (A+j) D+upperPrimeSum (A+j) D ≤
      Real.eulerMascheroniConstant*(A+j : ℕ)+(1+log (N+H : ℕ)/2) := by
    have hmax : A+j ≤ N+H := by have hj' := mem_range.mp hj; dsimp [W,A] at *; omega
    have hmin : 1 ≤ A+j := by dsimp [A]; omega
    have hh := (integer_sample_bounds hmin).2
    rw [split_primeSum (D := D) (by dsimp [A]; omega)] at hh
    have hlog := Real.log_le_log (show (0:ℝ) < (A+j:ℕ) by exact_mod_cast hmin)
      (show ((A+j:ℕ):ℝ) ≤ (N+H:ℕ) by exact_mod_cast hmax)
    linarith
  have hh := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,hc] at hh
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have hmean : blockMean A W (fun M => G M)+blockMean A W (fun M => lowPrimeSum M D)+
      blockMean A W (fun M => upperPrimeSum M D) ≤ Real.eulerMascheroniConstant*N+(1+log (N+H:ℕ)/2) := by
    unfold blockMean
    rw [← add_div,← add_div,div_le_iff₀ hW']
    exact hh.trans_eq (by ring)
  have hcenter := G_le_blockMean hH
  have hlow := mean_low_prime_lower A W D hW
  rw [hw] at hlow
  change G N ≤ blockMean A W (fun M => G M)+_ at hcenter
  change G N ≤ _-_-blockMean A W (fun M => upperPrimeSum M D)+_+_+_
  linarith only [hcenter,hlow,hmean]

/-- The endpoint correction is at square-root scale whenever D squared is at most n to the fifth. -/
theorem fourth_endpoint_cost {n D : ℕ} (hsize : (D:ℝ)^2 ≤ (n:ℝ)^5) :
    D*Chebyshev.theta D/(8*(2*(n:ℝ)^3+1)) ≤ (log 4+4)*(n:ℝ)^2 := by
  have hch := (Chebyshev.theta_le_psi D).trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg D))
  have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg D
  have hk : 0 ≤ log 4+4 := by positivity
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hch hd,mul_le_mul_of_nonneg_left hsize hk,
      mul_nonneg hk (sq_nonneg (n:ℝ)),mul_nonneg hk (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 5)]

/-- At a fourth-power observation the averaging width is n cubed. For every cutoff
D with D squared at most n to the fifth, all deterministic costs are at square-root scale. -/
theorem G_fourth_le_mean_upper_primes {n D : ℕ} (hn : 2 ≤ n) (hD : D ≤ n^4-n^3)
    (hsize : (D:ℝ)^2 ≤ (n:ℝ)^5) :
    G ((n:ℝ)^4) ≤ Real.eulerMascheroniConstant*(n:ℝ)^4 - Chebyshev.theta D/2
      - blockMean (n^4-n^3) (2*n^3+1) (fun M => upperPrimeSum M D)
      + (8+log 4)*(n:ℝ)^2 := by
  have hn' : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ) := by linarith
  have hH : n^3 < n^4 := by
    exact Nat.pow_lt_pow_right (by omega) (by decide)
  have hh := G_le_mean_upper_primes hH hD
  push_cast at hh
  have hlog' : log ((n:ℝ)^4+(n:ℝ)^3) ≤ log 2 + 4*log n := by
    have h34 : (n:ℝ)^3 ≤ (n:ℝ)^4 := by exact_mod_cast hH.le
    have ht := Real.log_le_log (show 0 < (n:ℝ)^4+(n:ℝ)^3 by positivity)
      (show (n:ℝ)^4+(n:ℝ)^3 ≤ 2*(n:ℝ)^4 by linarith)
    rwa [log_mul (by norm_num) (by positivity),log_pow] at ht
  have hcost := fourth_endpoint_cost hsize
  have quadratic : ((n:ℝ)^3)^2/(n:ℝ)^4 = (n:ℝ)^2 := by field_simp
  rw [quadratic] at hh
  have hn2 : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1)]
  linarith only [hh,hcost,hlog',log_le_sub_one_of_pos hpos,log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2),hn2,
    show 1 ≤ (n:ℝ)^2 by nlinarith]

end
end RiemannGaussian.AlpogeMined
