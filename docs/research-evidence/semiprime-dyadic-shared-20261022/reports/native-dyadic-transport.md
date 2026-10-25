# Native dyadic half-tag transport, exact carries, and phase queries

Work over dyadic m>=8 with the established canonical rows: odd j in [1,m), a=Nj^-2 mod m in [1,m), b centered in [-m/2,m/2), b congruent ((aj^2-N)/m)j^-1 modulo m, ell=mb-2aj, E=N+a+ell. All statements concern the original scalar target gamma^E and seed q^I, q=gamma^(m^2).

## Exact half-tag shift

Pair the lower representative 1<=j<m/2 with j'=j+m/2, so no wrapping occurs in this orientation. Since (j+m/2)^2=j^2 mod m, a'=a exactly. Put d=m/2. Expanding the defining congruence, or multiplying by j+d and using its inverse modulo m, gives

 b'-b = a - (m/4) j^-1(a+2b) modulo m.

For example this follows directly from (j+d)(b'-b)=am/4+aj-db modulo m; after substitution the difference from the displayed expression is a multiple of m (m>=8). Thus b'-b-a is an ODD multiple of m/4. Keeping the actual centered representatives defines an exact odd integer

 h=4(b'-b-a)/m,
 E'-E=ell'-ell=h*m^2/4.

The bounds -m<b'-b<m and 1<=a<m imply -8<h<4, hence

 h in {-7,-5,-3,-1,1,3}.

For an arbitrary canonical starting j, use the lower member of its pair; reversing orientation negates h. This handles wrapping without importing an uncentered b'. In particular this pairing is a statement about native TAGS, not the unrelated substitution X->-X in a cyclic algebra.

With q0=gamma^(m^2/4), the two targets satisfy x'=x q0^h, while q=q0^4. This identity is acquired from O(m) integer row descriptors and O(m) modular operations, up to logarithmic bit factors. It is a real whole-family scalar cancellation.

## Exact product transport retains a phase

For any interval [A,B), define the scalar collision product

 F_r(x;A,B)=prod_(A<=i<B)(x-q0^(4i+r)), r modulo4.

It is only a notation unless a startup product has actually been computed. Let h=4v+r with r in {0,1,2,3}. Then the paired target query has the exact transport

 prod_(A<=i<B)(x q0^h-q0^(4i))
 =q0^(h(B-A)) prod_(A<=i<B)(x-q0^(4i-h)).

The right side has phase -r, and interval translated by -v (with the corresponding canonical phase carry). Because h is odd, it is an ODD phase, never the original phase0. Therefore this is not a same-phase interval shift with only a few endpoints. An endpoint formula becomes available AFTER the new phase's startup has been acquired. No division by an endpoint value should be used without a gcd guard; products can instead be maintained by ordered-subset product/MPE constructions.

One may acquire all four phase products at a representative x. This covers both native targets using bounded endpoint adjustments and known unit scales; endpoints and their original leaf labels are explicit. It is a valid sufficient augmented query. Computing four startups independently is a constant-factor cost at that level, not a free startup. Replacing them by one full interval of q0 exponents also multiplies the interval length by four and adds extra leaves; those extra leaves require the original scalar nonzero-gap/recovery ledger before being accepted.

## Four-root grouping is real but does not yet give a speed exponent

For m>=8, the equation j^2=u among odd residues has exactly four solutions whenever soluble: j,-j,j+m/2,-j+m/2. Consequently each occurring a has four native tags, and there are m/8 distinct a values. The half-tag relation pairs their targets by odd q0 shifts; antipodal pairing additionally has E_j+E_-j=2(N+a)-m^2 s. These are paid four-target descriptors. The antipodal operation is reciprocal around a-dependent gamma^(N+a), not generally an integer q0 shift between all four targets.

Even in the optimistic case that four tags could be replaced by one representative with four seed phases, the target-count/interval-length product in the existing block bound would remain J*L: (J/4)*(4L)=J L. Thus that particular implementation supplies useful sharing/constants, but not a 1/6 exponent. This is a charge for the explicit transport implementation, not a lower bound against a more effective shared algorithm.

## Why this does not automatically recurse to canonical lower rows

Let n=m/2, j=r+eta*n, a=a0+epsilon*n, with r the canonical lower tag and a0 the canonical row coefficient modulo n. Let b0 be its independently centered lower-row coefficient. Exact subtraction gives

 E_m-E_n = n[epsilon(1-2r)-2a*eta+2b-b0].

There is no general divisibility by n^2 here; if epsilon=1, the bracket has an uncontrolled odd contribution. Moreover the lower-row seed is gamma^(n^2), whereas the inherited original seed is its FOURTH power. Thus a recursive call needs inherited target offsets, phase restrictions and the original I interval, not just the fresh canonical lower-row problem. Describing each offset is cheap; acquiring all its phase startups is the missing operation. The explicit half-tag bounded shifts alone do not establish bounded branching under this canonical descent.

## Constructive next interface and status

A sufficient advance would be a shared constructor for all phase-startup products attached to these inherited representatives, with restriction/localization support, in soft O(m) total rather than paying a new geometric-interval startup per representative. The exact phase transport above would then pay only O(m) boundary factors and known scales at each logarithmic level. It must also control the accumulated offset phases in the lower-row formula and retain the original seed index, so a detected leaf has a nonzero scalar gap with the established decoder conditions.

I verified the bounded odd half-tag shift and derived the phase-preserving transport, but did not obtain that shared startup constructor or a telescoping identity across the distinct a representatives. The half-tag symmetry is stronger than an arbitrary target list; its currently proved implementation does not close the all-input near-linear collision query. No numerical coverage evidence, generic lower bound, or change to the frozen packet is asserted.
