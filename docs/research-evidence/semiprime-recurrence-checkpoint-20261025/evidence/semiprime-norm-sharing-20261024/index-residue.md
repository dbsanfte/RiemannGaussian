# Acquire the native index-residue map and its exact catalog consumer

24 October 2026. Scratch research. This initializes the exact quadratic residue map, including the repaired Hensel vertex, and a soft-k algorithm for every supplied constant-size index-residue palette. It does not supply such a palette covering every semiprime. The arithmetic missing from a constant number of terminal evaluations is stated exactly, rather than supplied by a group-order projection.

## Paid input and credit

Use native-pairing.md SHA256 06548c974c61d9922a4ec6c2f41ba1c95d7dfcbb92442b3b2e5ceff984cd8016, the corrected native-moments source 6fabb876e618ba1a5fafbda304f95d43c1b8d785e56de6062254b0ae63f3b20d, and the independently reviewed composed-terminal.md 6ad4b2e3206dec95673013b34f9a0ee52d77f134b89af9f21bd450902ad264e8. All beta/W preparation, q screen, original leaf consumer and supplied-root single-resultant algorithm are actually paid.

H=k², N=PQ<=k^6, 16H<P<Q, P<=k³. The controlled even k has at most two distinct odd prime factors, each to exponent one, and v2(k) in {1,3,4}; phi(k)=Theta(k). Its public factorization and modular inverses are known or acquired within soft k. The original and repaired own-row identities hold. No hidden factor information or q logarithm is supplied.

The primitive relation below is credited to native-lattice.md and its second-content calculation. The prior journal's sparse-residue/quotient-catalog consumers already process explicit factor-residue catalogs. The new initialized interface here is specifically the conversion of an INDEX palette into such a catalog, with the exact repaired shift. Neither a quadratic rewriting nor the classical catalog product tree is claimed as a new unconditional acquisition rate. The separate complete cubic-cover construction aligns a stronger divisibility at its fully charged N^(2/9) cost; that algorithm is not replaced by a free congruence choice here.

## 1. The exact index residue, before and after repair

For a unit tag j set

 a=[Nj^-2]_k, d=(N-aj²)/k,
 b=center_k(-d j^-1), ell=kb-2aj,
 c=(d+jb)/k.

All integers are public and acquired. Write the unknown own prime P=j+kx. The exact primitive identity is

 (j+kx)I=a x²+b x+c.

Consequently

 I = j^-1(a x²+b x+c) modulo k.                 (1)

For parity repair epsilon=b mod2, put a'=a+epsilon k, b'=b+epsilon j-k zeta, ell'=ell-epsilon kj-Hzeta and c'=(d-epsilon j²+jb')/k=c-j zeta. The TRUE integer index changes by

 I'=I+epsilon x-zeta.                            (2)

In particular its residue is not obtained by changing a alone. It is

 I'=j^-1(a' x²+b' x+c') modulo k.                (3)

Acquire the supplied Hensel t, 0<=t<k/2, with 2a't+b'=0 modulo k, and let X=x-t. Expanding (3) gives the genuinely centered quadratic

 I'=lambda X²+gamma modulo k,
 lambda=[a'j^-1]_k=[Nj^-3]_k,
 gamma=[j^-1(a't²+b't+c')]_k.                   (4)

Thus lambda is a public unit, and gamma,t are public. These arrays for ALL tags cost soft k. The unknown parameter in (4) is precisely [(P-j)/k-t]_k, i.e. the next prime digit modulo H with its known Hensel shift. It has not been acquired by forming the quadratic.

For the negative fundamental character with conductor dividing k, chi(N)=-1 gives chi(lambda)=-chi(j). If X is a unit modulo k, then

 chi(I'-gamma)=-chi(j).                          (5)

When X is not a unit, one must retain the actual character value; (5) is not asserted universally. This is at most a quadratic-image restriction, not a determined residue or an additive character formula.

## 2. Fibers, public inversion and what lifts actually change

For this controlled modulus every congruence Z²=w modulo k has at most16 solutions. At an odd prime factor there are at most two solutions (one at w=0), and the bounded 2-primary component contributes at most four; CRT gives the claim. In particular the image of (4) has at least k/16 values as X ranges over ALL residues. Restricting to unit X still gives at least phi(k)/16=Theta(k) values. This is an exact image count for this public map, not a lower bound on factoring algorithms or a proof that actual prime lifts fill its whole domain.

Acquire an inverse lookup for the square map by enumerating Z=0,...,k-1 once, storing Z in the bucket [Z²]_k. This costs soft k and stores exactly k entries in total. No modular square-root oracle or assumed cheap nonresidue search is required. Given an index r and tag j, retrieve the at most16 solutions to

 X²=lambda^-1(r-gamma) modulo k,
 x=X+t modulo k.                               (6)

Thus index-palette inversion is a truly initialized O(1)-size-per-tag operation, after soft-k preprocessing.

For comparison any legal positive lift a_s=a+ks and recomputed b_s has the already proved exact change I_s=I+s x-z_s, z_s=(b+sj-center_k(b+sj))/k. Its quadratic coefficient modulo k remains a j^-1, a UNIT. Public s moves the linear and constant terms; it does not make the polynomial in the unknown x constant. A universal identity I_s=r for ALL x modulo k is impossible for this particular lift family: its second finite difference is 2a j^-1, nonzero modulo k on the continuing k>16 branch. This is only a test of universal polynomial flattening; it does not prove that public lifts cannot exploit the actual divisors of N. Nor does it guarantee that a short lift menu attains a chosen residue at the actual unknown x.

## 3. Execute a complete supplied-palette factor algorithm

Let A be an explicitly supplied subset of residues modulo k, of size s. Construct for EVERY public unit tag j and EVERY r in A the roots (6), retaining labels (j,r,X), and form the integer catalog

 S_A={j+kx : x=[X+t]_k from (6)} subset [1,H).

This is acquired in soft(k+ks) time, has at most16ks entries, and contains P modulo H whenever the actual repaired own I' modulo k belongs to A. The implication uses (2)--(4), with no independent prime digit assumed. Duplicate catalog values may be removed or retained. All residues are units modulo k.

The catalog has an elementary complete factor consumer. Acquire

 D_A(T)=product_(v in S_A)(T-v),

then evaluate it at the k+1 actual nodes -Hn, 0<=n<=k, by monic MPE. If P modulo H is in the catalog, P=v+Hn for one queried n since P<=k³. A proper row gcd factors. A saturated row is descended in its retained root product tree until obtaining a nonunit leaf gcd. Every integer v+Hn is positive and less than k³+H<N (N>256k^4 and k>16), so ANY such nonunit leaf has a proper gcd; there is no zero-annihilator or saturated-leaf ambiguity. The complete conditional-class algorithm costs soft(k+ks), including all starts, row outputs, localization and integer metadata. It uses no beta query at all once this explicit catalog is built.

For a fixed or polylogarithmic palette this is soft k. This is a genuine sufficient factor-class theorem: if the own repaired residue belongs to A, it factors. It is not a proof that a fixed small A covers every N. Taking ALL k residues covers every possible own residue but acquires O(k²) catalog entries before optional deduplication; indeed the union becomes all unit residues modulo H. The classical explicit full catalog then costs soft k². No free small sufficient palette is inferred from the at-most16 fibers.

The alternate terminal consumer is also fully initialized: split the repaired horizon into main3H and its acquired last two factors, use m=k,G=3k and the supplied original roots, without reciprocal augmentation in this residue-class consumer. For each r in A, one actual scalar resultant R(q^-r) costs soft(J+G)=soft k, with original MAIN indices kg+r. Original tail hits are handled separately. Its prime support is exactly the corresponding index-residue class. Existing original leaf localization and consumer therefore give the same soft(ks+k) conditional guarantee. This does not take individual R values free and does not decode an auxiliary moment sum. It is not needed by the simpler integer catalog consumer above.

## 4. Why a rough-order quotient has not supplied the residue

Actual q component orders are k-rough. Therefore a cyclic component generated by q has no nontrivial homomorphism into the additive group Z/k: its order is coprime to k. In particular the map q^i -> i modulo k is not well-defined on that WHOLE cyclic group, because i and i+ord(q) represent the same element and have different residues modulo k. This disproves the specific proposed quotient-character extraction; it is not a general lower bound on bounded discrete logarithms. On the short actual interval the index may be unique, but using its interval promise is precisely additional work, not an ordinary subgroup quotient.

Beta/W norm and Frobenius identities remain valid own-prime equalities, but taking norms or k-th roots in those rough subgroups does not by itself acquire the integer lift in (4). No character of order k, cyclotomic phase, or local-order inverse is silently supplied. Distinct choices of an integer representative for the same unrestricted group exponent still alter its residue modulo k.

## Outcome

All quadratic coefficients, Hensel shifts, inverse square-map buckets and index-palette catalogs are actually acquired. A supplied soft-1 palette gives a complete soft-k sufficient query with safe recovery by either an integer catalog or a constant number of initialized scalar terminal evaluations. The missing uniform input is a publicly acquired small palette containing the actual own I' modulo k, or some proved different alignment covering all inputs. Neither the large quadratic image, its character restriction nor the lift formula acquires that input. No unconditional improvement over the current full query or complete cubic-cover alternative is asserted.
