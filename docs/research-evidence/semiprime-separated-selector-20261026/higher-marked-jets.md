# Marked higher Macdonald jets: acquired responses and a direct pairing test

26 October 2026. Derived extension of higher-macdonald.md; scratch only. **Result:** every fixed-order, fixed-number marked jet of its entire degree-J response polynomial is acquired in soft J after the same gates. These jets are regular through an interior physical collision. One natural normalized marker pairing is explicitly evaluated below and is not a hit projection. This is not a general obstruction to processing the acquired jets.

## 1. Exact marked construction and startup

Let C be any fixed-rank truncated multivariate jet algebra over the prepared B, for example B[delta,epsilon]/(delta²,delta epsilon,epsilon²). Supply public row marks w_j. Choose the physical row deformation

T_j(delta,epsilon)=T_j-delta-epsilon w_j,
D_(delta,epsilon)(X)=prod_j(X-T_j+delta+epsilon w_j).

The constant-rank coefficient arrays of D are acquired by a product tree in soft J; no tag interpolation, inverse of a target value, or unknown hit index is used. More fixed marks or fixed higher precision change the constant rank only. Precision growing with h is NOT included in this claim.

Retain all actual base conventions and gates of higher-macdonald.md: node differences T_i-T_j, both endpoint differences T_i-b and T_i-q^-1, b=q^(h-1), are certified units, with actual mixed-label factor/extractor branches charged at soft K once. A jet with unit constant has a unique fixed-precision inverse by finite series arithmetic. Hence these same denominators are units in C. In particular D_(delta,epsilon)(b) is invertible. No qT_i-T_j is inverted; its constant may be zero.

Formula (3) therefore holds literally over C:

chi_(delta,epsilon)(u)
 =D_(delta,epsilon)(b)^-1 sum_(s=0)^J d_s(delta,epsilon)b^s
          (u;q)_s (u q^(h+s);q)_(J-s).               (1)

The supplied balanced two-Newton conversion works in C using the same product tree of O(J) unit-base linear factors. It returns ALL J+1 coefficients, including every fixed marked jet, in soft J base-ring operations times the fixed rank. The denominator inverse is acquired from its actual unit constant, not from a physical leaf at the hit. The matrix interpretation uses the deformed interpolation matrix and deformed row-shift ratios, whose denominators are the already certified jet units.

This is an actual acquired all-orders marked response. It is not merely formal differentiation of an unavailable determinant.

## 2. What is regular, and which residue is absent

At an interior physical collision T_(j*)=q^I, D(q^I)=0, every coefficient of (1) is still regular in delta and epsilon. Its only denominator is D_(delta,epsilon)(b), which is a global unit by the endpoint gate. Thus it has no delta^-1 coefficient at all. The same is true of its fixed jets and polynomial combinations; any additional rational combination has this guarantee ONLY if its denominator constant has actually been certified a unit.

This does NOT imply that all rational processing of chi must be regular or uninformative: a new choice of singular denominator, selected eigenvalue or another map could encode the hit. Such a construction needs its own acquisition, nonzero-amplitude and component gates. It cannot claim the physical residue from (1) without explaining that additional step. In particular one cannot replace its matrix by W_h(C_row), or conjugate with the unknown singular diagonal of clock products, merely because both are derived from the same roots.

## 3. Execute the simplest logarithmic marked pairing

At u=1 the acquired formula specializes to

chi_(delta,epsilon)(1)
 =d_0(delta,epsilon) (q^h;q)_J / D_(delta,epsilon)(b).

Both its constant and the q-factorial factor are units under the actual doubled short-gap footprint. Consequently logarithmic differentiation is legal and gives exactly

V = partial_delta log chi(1)|_0
  =sum_j a_j,
U = partial_epsilon log chi(1)|_0
  =sum_j w_j a_j,

a_j=b/[T_j(T_j-b)].                               (2)

All a_j are supplied UNIT amplitudes, including those from NONHITTING rows. Their derivation uses T_j'= -1 or -w_j: -w_j/T_j+w_j/(T_j-b)=w_j b/[T_j(T_j-b)]. This is a finite all-row barycentric-like sum, not a Dirac mass at the clock hit.

A precise diagnostic of this particular pairing: for two separated endpoint-unit rows, w_1=1,w_2=2 and a hit in row1, U-V=a_2 is a unit. Thus if V is also a unit, U/V cannot equal the required hit mark1. The conclusion holds algebraically regardless of which interior clock point equals T_1. This two-row calculation tests the proposed universal formula; it is NOT claimed as an attained full native unique-cover counterexample or a lower bound for other marker pairings. For a full bank, sums of the other rows can cancel or not; no promised projection follows from (2). An additive zero of V is not an actual mixed label and cannot use that decoder.

The derivative of chi itself rather than its log has the same issue: both U,V are multiplied by the known unit chi_0(1), so the ratio and the nonhit amplitudes are unchanged.

## 4. Exact conditional handoff that would project the row

The short D jet already shows what a successful pairing must accomplish. If the actual hitting clock node theta=q^I were supplied, then

partial_epsilon D_(delta,epsilon)(theta)|_0
  =w_(j*) partial_delta D_(delta,epsilon)(theta)|_0,
partial_delta D_(delta,epsilon)(theta)|_0=D'(theta)!=0

at the good field. Other leave-one-out terms vanish there. This yields the desired weak row-index pair with soft J evaluation and its existing guards. The missing data are theta, or an equivalent selected linear functional that singles out this clock-intersection branch without listing h values.

The finite Newton transformation (1) is a paid short basis change of the entire marked D data. Inverting it and performing the preceding evaluation is constructive once theta is known, but does not acquire theta. No computational separation is proved by saying the same short data occur in both bases. A new singular pairing of the acquired higher jets that supplies that selection would be real progress; equations (1)–(2) do not yet provide it.

All claims are finite and derived from the already reviewed formula. No new external theorem, numerical campaign, implementation, source alteration or repository edit is used. All acquisition costs here are soft J AFTER inherited preparation/gates, with a once-only terminating extractor still charged at original soft K.
