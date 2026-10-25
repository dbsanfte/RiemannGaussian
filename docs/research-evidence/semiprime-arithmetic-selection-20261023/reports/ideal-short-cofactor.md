# Short-cofactor ideals: acquired relation, recognition target, SQUFOF scope

23 October 2026. Read the frozen 256-entry checkpoint, structured coefficient proof, and inherited discriminant/conic audit. This is a new scratch applicability check. No frozen or repository file was edited.

**Outcome.** There is an exact, uniformly affordable public ideal relation with fully factored cofactor aC. The true short sigma gives a stronger *hidden-prime* ideal relation, stated below. I did not acquire the all-input recognition/selection step in total soft r. Every negative-C row is proved nonprincipal for the particular square-form transfer below. Tiny true sigma does **not** force a positive-C row's supplied square form into the principal class either: one inherited prepared witness gives a complete exact countercheck. This single positive-C check does not exclude a different principal positive-C row in that or another catalog. The report does not promote restricted ambiguity screens or selected input classes as overall progress.

## 1. Exact ideal ledger, including the public factored norm

Use one structured window, H=r^2, M=H^2, g(h)=a h^2+b h+d, and

    B=Hb-2as,   CN=M d-Hbs+as^2,
    D=b^2-4ad,  B^2-M D=4aCN.

First perform the already valid gcd and integer-square discriminant screens. A square D in a nonzero-a row factors N. In the remaining case D is nonsquare and gcd(D,N)=1. Divide out primitive content k=gcd(a,b,d), if necessary. This k also divides B,C because gcd(k,N)=1; dividing (a,b,d,B,C) by k replaces D by D/k^2 and true sigma by sigma/k. Thus the same identities hold with primitive g and 0<|sigma|<4r. This is an O(log N)-bit gcd/division operation per row, not a factorization of D.

In the quadratic order O=Z[theta] of discriminant D, put

    theta=(-b+sqrt(D))/2,    I=(a,theta),
    R=B/H modulo N,         n_R=(N,sqrt(D)-R).

I is an invertible ideal of norm a for primitive g. Since gcd(D,N)=1 and R^2=D modulo N, n_R is invertible of norm N, with one fixed orientation above each of P,Q. All these ideals have public rank-two integer bases of O(log N)-bit height.

The completely public element

    alpha0=(B-H sqrt(D))/2=-(as+H theta)

is integral and has norm aCN. It lies in I and n_R; their norms are coprime. Consequently

    (alpha0)=I*n_R*J_C,        Norm(J_C)=|C|.             (1)

J_C is obtained directly by exact ideal quotient in fixed dimension. Every a and C is fully factored in total soft r: |a|<r, |C|<r^2; sieve primes through r, use batched smooth-part/prime-product refinement, and observe that a remaining cofactor of |C| cannot contain two primes >r. Thus (1) has an acquired fully factored **rational** cofactor norm. Its local ideal blocks can be computed from the given alpha0 and ideal bases; the supplied orientation does not require an oracle for a fresh modular square root. At primes dividing D, retain exact prime-power ideal blocks: a factorization into Dedekind prime ideals of a nonmaximal order is not silently assumed. No maximal-order/conductor computation is required for (1).

Here is a concrete charge for the complete integer factorizations, independent of any smoothness heuristic. Sieve the primes p<=r and form their balanced product tree, whose total prime bit length is O(r). At the root assign all nonunit |C_i|. For an active node with assigned moduli |C_i|, compute each child's prime product modulo all those moduli using a modulus product/remainder tree; a gcd selects which indices pass to that child. A surviving index at one depth is assigned to at most omega(|C_i|) nodes, because their disjoint prime sets each contain a divisor of C_i. Hence at every depth the trial lists for both children have total bit size

    O(sum_i omega(|C_i|)*log |C_i|)=O(r*(log r)^2).

The prime-product node values at that depth have total bit length O(r). Batched remainder trees, gcds, and their modulus-tree construction therefore cost soft r for the depth; there are O(log r) depths. At a prime leaf repeatedly divide its assigned C_i to obtain the full valuation. The total number of prime factors with multiplicity is O(r log r), so this also costs soft r. Every residual cofactor is 1 or a prime >r: a composite residual would have two prime factors >r and exceed |C_i|<r^2. This is a certified consequence of the size bound, not an uncharged primality or factoring oracle. The a_i are factored by the same sieve (or tree). Signed C_i keep a separate sign bit. The argument applies to all O(log N) windows with only polylogarithmic overhead and never scans the rectangle of a,C possibilities.

Now at the true witness g(h)=P sigma define

    alpha_h=a h-theta,       Norm(alpha_h)=aP sigma.

The P-ideal p_R in n_R contains alpha_h because

    sqrt(D)=2ah+b=B/H modulo P,

using Hh=cP-s. Since P exceeds a and |sigma|, its norm occurs to exactly the first power. There is an integral invertible ideal J with

    (alpha_h)=I*p_R*J,       Norm(J)=|sigma|<4r.          (2)

Thus in the ordinary ideal class group

    [p_R]=[I*J]^{-1}.                                    (3)

For real D, a narrow-class/infrastructure implementation must also carry the sign of Norm(alpha_h)=aP sigma. Replacing it by an unsigned narrow relation is invalid. For D<0, sigma is positive. Equations (1)-(3) are exact and strengthen the generic smoothness discussion: C is factored, and the true residual ideal has a genuinely short norm.

## 2. What recognition would have to compute, and its charge

Equation (3) is not an already acquired class collision: p_R is an unknown prime factor of the public ideal n_R. Reducing n_R, I, and J_C only reduces their known product relation (1); it does not isolate the unknown P-component. P and Q are unramified split primes in O, so their ideal classes need not be ambiguous or have order two.

A concrete sufficient arithmetic target is to isolate a proper norm divisor of n_R under the promise (2), using the acquired factorization of aC and the row bounds. It must find the oriented short-cofactor relation, or its generator, without using P, h, or sigma as input. The straightforward construction crosses O(r) rows with O(r) possible nonzero sigma labels, before constructing possible ideal orientations and testing equivalence. It already has a soft-r^2 descriptor charge. This is the charge of that construction, not a lower bound against compression using the C progression.

Class-group setup is not free. A known form can be reduced in polynomial time in its bit length, so all supplied reductions are affordable. Full class-group tables are a different operation: the classical general scale is |D|^(1/2+o(1)), up to r^(2+o(1)) for a row, and no source theorem bounds these groups by polylog N. For real D, two reduced forms need not be equal when their classes are equal; class recognition includes cycle/equivalence work. Even granting a fourth-root equivalence method independently for each row would have scale r per row, hence r^2 across the family. Neither the source nor tiny sigma supplies the needed amortization across its varying discriminants.

These distinctions follow from Lenstra's primary order/form dictionary and reduction/equivalence analysis: sections 1-5, printed pp.125-131 (PDF pp.3-9), and section 13. He works with arbitrary quadratic orders, explains the real-cycle equality issue, and states the hypothesis dependence of the faster class/regulator algorithms at the beginning. The ordinary/narrow distinction above is retained explicitly. [Lenstra, *On the calculation of regulators and class numbers of quadratic fields* (1982)](https://public.csusm.edu/ssharif/crypto/Lenstra82-QuadraticRegulators.pdf).

## 3. Exact SQUFOF transfer and its missing premise

Working at discriminant D with |D|=O(r^4) gives the nominal fourth-root scale r **for factoring D**, not N. Ambiguous forms there yield divisors of D; after gcd(D,N)=1 those divisors do not split N. The small-norm relation (2) concerns a split P-ideal, not a ramified ambiguous P-ideal.

One can instead build, directly from the acquired row,

    Delta=16aCN,
    F=(D,2B,H^2),       G=(H,2B,DH).                     (4)

Both have discriminant Delta, and gcd(H,2B)=1. Composition gives

    G^2 equivalent to (H^2,2B,D) equivalent to F^{-1}.   (5)

Here equivalence and principality mean proper SL2(Z) equivalence, hence narrow ideal classes when Delta>0.

So F is an explicit square form, but that does not prove it principal. SQUFOF's inverse-square-root return reaches an ambiguous cycle because its square form is equivalent to a principal form. For (4), that premise is precisely [G]^2=1. It is an additional arithmetic claim, not a consequence of the visible square H^2. If C<0 the form is definite; if C>0 its real cycle/equivalence must be paid. The factorization of aC permits computing the fundamental discriminant underlying Delta without factoring N, but does not establish (5) is principal. A generic run on a discriminant containing N also has fourth-root scale at least N^(1/4)=Theta(r^(3/2)), and up to Theta(r^2), before row-family charges; this is only a nominal average scale, not an unconditional guarantee.

**Uniform negative-C exclusion (root's refinement, independently checked).** For every C<0 descriptor, translate G's middle coefficient to b'=center(2B modulo 2H), leaving leading coefficient H. Since H is odd and r does not divide B=-2a modulo r,

    0<|b'|<H,
    c'=(b'^2-Delta)/(4H)>4a|C|N/H>=4N/H>1024H.

The last inequality uses P,Q>16H. Thus G'=(H,b',c') is primitive and strictly reduced positive definite. The inverse has the distinct strictly reduced representative (H,-b',c'). By uniqueness of definite reduced representatives, [G] is not equal to its inverse, so [G]^2!=1 and F is nonprincipal. Equivalently, the definite ambiguity cases b'=0, |b'|=H, or H=c' are all excluded. This uses the arbitrary-order conventions in Lenstra section 5, printed p.130 (PDF p.8), so no fundamental-discriminant assumption is needed. Consequently the previously suggested optional negative-C ambiguity screen has no successes anywhere in this source and is withdrawn. It is not a pending acquisition algorithm.

The relevant exact condition is in Gower-Wagstaff section 3.2, Proposition 3.1 (PDF p.10); their sections 4.2 and 4.6 (PDF pp.16,26) explicitly base the average analysis on additional assumptions and omit inputs with no proper square form in the chosen principal cycle. Therefore their Theorem 4.22 is not a uniform deterministic soft-r guarantee for these rows. [Gower-Wagstaff, *Square Form Factorization*](https://www.cerias.purdue.edu/assets/pdf/bibtex_archive/S0025-5718-07-02010-8.pdf).

The later SQUFOF2 construction preserves the principal-class premise when it manufactures square forms from principal-form values; it does not accept arbitrary square forms as that input. Its theorem is explicitly conditional on four hypotheses, including smooth-value supply, return distance, and useful ambiguous-form distribution. It therefore cannot be applied as an unconditional replacement for the missing recognition operation. See section 6, PDF pp.10-11; section 8.2 and Theorem 4, PDF pp.13-16. [Bradford-Wagstaff, *Square Form Factorization, II*](https://homes.cerias.purdue.edu/~ssw/squfof2.pdf).

## 4. A true short-cofactor witness does not force principality

The adjacent pure-integer replay uses only the already recorded prepared instance, not a new search:

    r=43, N=59447*59747=3551779909,
    a=1, C=331, s=345, c=41, B=1082824,
    b=586, d=343984, h=1318, sigma=48<4r,
    D=-1032540, Delta=18810226398064.

It checks the original row/witness identities and prime/order premises, then uses the exact standard indefinite reduction permutation. For G in (4), its reduced form is

    (1849,4336374,-823003).

Its complete cycle returns after 152120 steps and contains no ambiguous form. Independently, F reduces to

    (-1032540,4230728,220613),

whose complete cycle returns after 151318 steps and contains no principal form. Thus F is not principal even with an actual true sigma=48. This directly refutes the proposed implication that every true short-cofactor row supplies the principal-square-form premise. It does **not** prove that this whole catalog lacks a different principal positive-C row, or exclude a different recognition algorithm using the additional small-ideal information in (2). The finite cycle check is a countercheck of the stated implication, not a performance certificate, family coverage experiment, or asymptotic obstruction.

### Exact remaining positive-C class target

There is a precise public small-prime ideal underlying this transfer. Put delta=4aCN, so O_Delta=Z[sqrt(delta)]. The acquired simple root B defines

    r_B=(r,sqrt(delta)-B),       Norm(r_B)=r.

Because B^2-delta=r^4 D and r does not divide B, the ideal whose oriented norm form is G^{-1}=(H,-2B,DH) is exactly

    (H,sqrt(delta)-B)=r_B^2.

Consequently the positive-C target is

    F principal iff [r_B]^4=1 in the narrow class group. (6)

Equivalently, there must be an oriented primitive norm generator

    u^2-delta*v^2=r^4,
    r does not divide v,     u+Bv=0 modulo r^4.          (7)

Indeed a generator of r_B^4 has positive norm r^4; the conjugate r-ideal cannot divide it, giving r not dividing v. Conversely (7) and the norm force its principal ideal to equal r_B^4. This characterization is in the public order and retains the actual orientation, without an unknown-P input.

For C<0, (7) gives a second direct proof of exclusion: its left side is u^2+4a|C|N*v^2, and v!=0 makes it greater than 4N>1024r^4. If v=0, the norm equation instead gives u=+/-r^2; its rational principal ideal is (r^2)=r_B^2*conjugate(r_B)^2, not the oriented r_B^4. The two prime ideals are distinct because r is unramified and split. Thus there is no generator even after dropping the primitive-v condition. In this imaginary order every nonzero element has positive norm, so ordinary and narrow principal ideals coincide; there is no sign convention escape. For C>0 it is an actual Pell-type norm-generator problem: (7) uses positive norm for the narrow class, whereas a merely negative-norm generator would prove only ordinary principality. A simple local root modulo r^4 does not constitute its solution; the fixed true-row countercheck above distinguishes these two conditions.

The all-row existence question remains: does the clipped positive-C catalog force (6) for at least one descriptor, with a generator or return computation whose TOTAL cost is soft r? No such implication was derived from the circular-gap proof, the factored aC relation (1), or the hidden small norm (2). Relation (2) lives in O_D, whereas (6) lives in O_Delta; replacing one by the other is the unproved transfer. Even proving a positive-C principal row exists would still require paying recognition and the infrastructure return distance. The one positive-C counterexample does not answer this all-row existence question. No additional selected instances were tested.

## 5. CFRAC does not supply the missing recognition theorem

For this application, CFRAC still needs a sufficient supply of useful relations in a fixed discriminant/order. Running it at D creates relations for D, while running it at a discriminant divisible by N changes the size and retains the principal-cycle/proper-relation conditions. The fully factored aC pays relation (1), but no theorem in the checked sources converts that one relation and the unknown-prime promise (2) into a guaranteed family-wide selection in soft r.

Shanks's primary manuscript gives the exact CFRAC square-product criterion and distinguishes proper from global-sign square relations in its section 1, PDF pp.2-6; it also describes both practical and absolute failures of an unmultiplied continued-fraction period. It provides no theorem that a short cofactor in the varying source discriminants forces a useful relation within the requested budget. This is an applicability conclusion, not a new smoothness argument. [Shanks, *SQUFOF*, unfinished manuscript, transcribed 2003](https://homes.cerias.purdue.edu/~ssw/shanks.pdf).

The remaining positive target is (2)-(3) as a constrained ideal-factor recognition problem with an already factored public cofactor relation (1). It has not been solved here, and no new all-input factorizer follows.

## Local sources and replay

The four primary PDFs were downloaded into `sources/` and read locally. `source-hashes.txt` records their SHA256 fingerprints. Morrison-Brillhart's primary AMS PDF returned HTTP 403; no theorem was attributed to unread contents of that paper. The CFRAC claims above use Shanks's readable primary account.

Run `python3 -B replay_principal_square_premise.py`. It performs one fixed identity/class-cycle check, without row enumeration or semiprime searches.
