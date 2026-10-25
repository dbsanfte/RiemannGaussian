# Independent native reciprocal-pairing and gap-complement review

2026-10-24. Reviewed `/tmp/semiprime-shared-triangles-20261024/native-row-pairing.md`, SHA256 `2b0c3715072e3c6edb40986982dd64fcdeacbbb92a2d99aa072a8ef2add5c769`.

Verdict: **PASS**, including the added precise interval condition for the unit screen. No required fixes remain. No repository edits. The earlier version hash `065f059145872aa7cf84e54575a560794109fd28993a8348163a6fa4666b97c2` had a sign error in t_j; it is not approved. The reviewed version correctly uses t_j=(b_j*j+v_j)/m. This is divisible by m because b_j*j=-v_j modulo m, and gives j*c_j=H*t_j-N. Subsequent carry identities (2),(3) are consistent with this corrected sign.

## Exact transport and the entire normalizable class

Write A=a_j, B=a_(j*), c=c_j, c*=c_(j*), eta=(Bc-c*)/m and rho=(AB-1)/m. All exact divisions follow from the stated residue identities, and j->j*=N/j modulo the prime m is an involution. Since AB=1 modm,
  B L_j(h,k)=c*+m(h+eta)+H(rho*h+Bk).
The acquired h'=[A(h+eta)]_m satisfies h+eta=B h' modm. Consequently sigma=(h+eta-Bh')/m is an integer and k'=rho*h+Bk+sigma gives the exact integer identity B L_j(h,k)=L_(j*)(h',k'). No original hit factor is inverted.

The stronger class assertion is also correct for EVERY original h and k, not merely selected rows. Expanding k' gives
  m k'=B(Ah-h')+eta+mBk.
Also m(b*+eta)=B(c+j*). Thus m(b*+mk') is divisible by B; gcd(m,B)=1 proves b*+mk'=0 modB. The unique k0 in [0,B) satisfying that congruence is acquired, and ell=(k'-k0)/B is an integer. With z*=(b*+m k0)/B, division of the integer transport equality by B yields
  L_j(h,k)=m(h'+z*)-j*+H ell.
This integer division is an algebraic identity; when used as a modular computation B is a separately certified unit. The map increments ell by one as k increments by one, while the h-dependent carries remain.

## Exact scope of the unit envelope

This distinction must govern the report's phrase 'short-menu unit screening':

- For the single original normalizing representative k'=k0 (ell=0), centered b* and 0<=k0<B imply -m/2<z*<m. Since 0<=h'<m and 1<=j*<m, the normalized leaf m(h'+z*)-j* has absolute value <2H+m<3H. It is nonzero modulo m. Under the actual prepared native promise P,Q>16H, it is a unit modulo N. This implication needs that factor cutoff; the opening weaker assumption that 1,...,m are units alone does not imply it.
- A bounded ell extension has |leaf|<(abs(ell)+3)H; the cutoff must be compared with this actual constant. Arbitrary O(1) is not itself a certificate below 16H.
- The FULL original public menu k' in [-m-2,m+2], even restricted to the normalizable class, gives abs(ell)=O(m/B), not uniformly O(1). Its normalized leaf envelope is O(m³/B), so a blanket unit claim for that entire menu would be false without an additional inequality. The source's wording is accepted only as referring to the actually certified small representative/submenu, not all public K labels.
- For the enlarged transported indices, k'=O(Bm+m), so ell=O(m). In fact the normalized leaf is EXACTLY the original L_j(h,k), and inherits its O(m³) envelope, not an O(H) unit bound. The transport therefore cannot erase original nonunit support. The unscaled transported leaf can be larger; localization must return to original labels as the report prescribes.

The reviewed final version explicitly adds this interval distinction. It also correctly supplies the sufficient condition B>=m/4 for the FULL original public menu: the inherited original bound divided by B is at most 8H+10m<16H for odd m>=3. Nonzero residue modulo m excludes literal zero; this strict bound below P,Q proves units. This sufficient condition does not apply to the enlarged transported menu. The earlier wording ambiguity is resolved; a stronger unconditional full-menu unit claim remains unapproved.

## Algorithm and cost scope

Tagged copies avoid unsafe removal of hit-bearing overlap factors. Exact support deduplication can keep one acquired copy. Multiplication by B preserves support because B is a certified unit. A transported k progression has known-unit step HB and an explicitly paid length. Subdivision can use original physical labels, whose nonzero and abs<N envelope yields proper-factor leaves. The literal all-h overlap computation across O(m) rows emits Theta(m²) metadata in this implementation. Nothing in the class normalization or scalar carry identity supplies a faster whole-family product or a smaller covered menu.

## Root gap-complement theorem

For coprime a,M>1, let C be the positive gap set of <a,M>, g=(a-1)(M-1)/2, F=aM-a-M=2g-1, and S(z)=prod_(n in C)(z+n). The exact identity is
  S(z) S(-z-F)=(-1)^g B_(2g)(z),
  B_(2g)(z)=prod_(r=0)^(2g-1)(z+r).

Proof: F is not representable. For each r in [0,F], r and F-r cannot both belong to the semigroup, since their sum would represent F. There are 2g integers in this interval and exactly g gaps. The involution r->F-r has no fixed integer because F is odd. Therefore each pair has exactly one gap: C and F-C partition [0,F]. Expanding S(-z-F)=(-1)^g prod_(n in C)(z+F-n) gives the identity immediately. It is a polynomial identity over Z, hence remains valid over Z/N without any unit hypothesis or denominator. If a=1 or M=1, g=0,F=-1 and the empty-product identity also holds.

This is precisely the familiar symmetry of a two-generator numerical semigroup (Sylvester gap symmetry), expressed multiplicatively. It is useful as a denominator-free contraction when the two reflected arguments are actually acquired from the native family. The symmetry alone does not prove that a chosen native row pairing realizes the needed shifts or that the paired blocks cover a native hit; those are separate arithmetic/coverage requirements. No new factoring exponent follows from this review.
