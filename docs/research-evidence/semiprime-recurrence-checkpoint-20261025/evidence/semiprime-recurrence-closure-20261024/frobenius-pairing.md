# A paid quadratic quotient that makes saturated norm leaves recoverable

24 October 2026. Scratch construction; no repository changes or numerical examples. The positive result is a uniformly acquired rank-two covered family whose scalar norm has a complete original-beta factor/witness consumer. A public Jacobi-minus-one discriminant makes ONE unknown local algebra a field. This is sufficient: proper norm gcds factor, and a saturated norm LEAF forces the original-beta equality at that field side. No large-order survival for the norm-one torus seed is assumed. The initialized long query remains soft k^(3/2), not soft k.

## Inputs, credited contracts, and the change of constructor

N=P Q is a distinct odd semiprime. The previously paid scalar setup at a sixth-root size parameter k either factors or supplies the hard branch

    N<=k^6, P,Q>16k²,
    beta in (Z/N)^*,
    ord_P(beta),ord_Q(beta) odd, coprime, and >C=16k²,
    ord_P(beta^H),ord_Q(beta^H)>C, H=k².

The H-power screen is part of that paid setup; it does not follow merely from the beta order bound for composite k. Global beta order is consequently >C². The setup accepts composite even k and includes the old exact-common-order/short-annihilator consumers. Its cost is soft k bits, not a supplied hidden-order oracle.

This construction chooses k after a small quadratic conductor. It does NOT require k+1 prime, does NOT construct the previous full-order Gauss vectors, and does NOT claim to compress those already defined vectors. It uses the same integer native row metadata and original-beta bounded decoder in a different, explicitly initialized quadratic algebra.

Read/pinned predecessors:

* composite-row-contract.md, SHA256 66795af6eae4e0cde23b6e84a6beb7ae18a656e41bdf9f94d739c83f3cbccb74;
* character-acquisition.md, SHA256 83bd40ae27d975320566827bba50ae73d63464218d2993bfc5b226e60e7749a7;
* preserved unbalanced-extractor.md, SHA256 a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be.

The last report already pays the deterministic Jacobi nonresidue scan used below. Root supplied the simpler Cayley seed and the short-seed-screen observation; the discriminant synchronization and native quadratic family are the present attempt.

## 1. Discover the Frobenius alignment without knowing either factor

If N=3 modulo 4, take D=-4. Otherwise N=1 modulo 4. Scan positive a<=ceil(N^(5/32)), computing gcd(a,N) first and then its Jacobi symbol. A proper gcd factors. Stop at a unit with (a/N)=-1. Factor this PUBLIC a by trial division and take its positive squarefree core d. Set

    D=-d if d=3 modulo 4; D=-4d otherwise.

This is a negative fundamental discriminant, gcd(D,N)=1, and (D/N)=-1: removing squares preserves the Jacobi value, the factor 4 is a square, and (-1/N)=1 in this branch. In the first branch (-4/N)=-1 immediately. Put c=|D| and r=ceil(N^(1/6)), and acquire

    k=2c ceil(r/(2c)).                            (1)

Thus k is even, c divides k, k>=r, and k<r+2c. For sufficiently large N, c<=4ceil(N^(5/32))=o(r), so k=Theta(r). No prime in a growing prescribed progression is sought. Factoring a costs at most soft sqrt(a), below the scan budget; factoring public k and enumerating its unit tags costs soft k.

The scan's uniform existence is the already accepted cubefree-modulus least-character-nonresidue bound. Lau--Wu, Theorem 1, gives exponent 1/(4 sqrt(e))+epsilon, strictly below 5/32 for a fixed sufficiently small epsilon. The Jacobi character of squarefree N is nonprincipal and primitive. Primary author preprint: [On the least quadratic non-residue](https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf), printed page 2 and Section 2. The same primary source recalls that a fundamental discriminant D gives a primitive quadratic character chi_D of conductor |D|. Therefore the bounded scan succeeds for every sufficiently large input. If it fails, execute trial division. This is the exact finite-input/asymptotic convention already accepted in the pinned extractor: the fallback occurs on only finitely many inputs and is absorbed by a fixed asymptotic constant. No effective Burgess threshold or practical constant is claimed.

The entire discovery costs soft N^(5/32), strictly inside the N^(1/6) budget. It is paid before the scalar setup, whose size parameter is the actual k from (1). Check gcd(kD,N), returning any proper factor; on the continuing hard branch k,D are units. For all unit tags j modulo k, acquire e_j=chi_D(j) in {+1,-1} by Kronecker/Jacobi arithmetic. Since c divides k, at the own tag j=P modulo k we have e_j=(D/P). This is an ordinary PUBLIC character table, not evaluation at a known factor.

## 2. Explicit algebra, involution, and the aligned local side

Let R=Z/N and

    B=R[tau]/(tau²-D), bar(tau)=-tau,
    Norm(A+B1*tau)=A²-D*B1².

The unit discriminant 4D makes B finite etale of rank two. For a local prime p in {P,Q}, Euler's criterion gives tau^p=(D/p)tau. Thus B modulo p is F_(p²) when (D/p)=-1, and F_p x F_p when (D/p)=+1. In the field case bar is exactly the nontrivial p-Frobenius. The product of the two signs is (D/N)=-1, so EXACTLY ONE local side is a field. We do not determine which one.

This is the required Frobenius-orbit alignment in a quadratic quotient: complex conjugation is the nontrivial automorphism of the negative quadratic conductor, and a nonsplit Frobenius generates it. No full cyclotomic embedding or chosen primitive root is needed to compute in B. One may identify the quotient with the quadratic subfield of conductor c, but that interpretation is not an initialization step.

Acquire the norm-one seed

    W=(1+tau)/(1-tau)=(1+D+2tau)/(1-D).           (2)

The denominator has norm 1-D=1+c. On the prepared hard branch 1+c<P,Q, because c<=k/2 and P,Q>16k². Hence it is a unit, also directly certified by gcd(1-D,N). Formula (2) computes the inverse explicitly with scalar extended gcd. Norm(W)=1; W is a unit. Its local order divides p-(D/p), with no lower bound asserted. In particular W can have small orders, and this does not invalidate either coverage or recovery below.

## 3. Acquire ALL native rank-two rows

For every j in (Z/k)^*, represented by 1<=j<k, compute the INTEGER data

    a_j=[N j^-2]_k,
    D_j=(N-a_j j²)/k,
    b_j=center_k(-j^-1 D_j),
    ell_j=k b_j-2a_j j,
    delta_j=a_j+ell_j,
    E_j=N+delta_j,
    Texp_j=ell_j+e_j*(N+a_j).

A fixed tie convention centers b in [-k/2,k/2). Each exponent has O(log N) bits. Define the actual acquired targets and seed

    V_j=beta^E_j * W^Texp_j,
    z=(beta W)^H, H=k².                         (3)

All negative powers are of explicit units. Binary powering each constant-rank element costs polylog N bits; there are at most k tags. Hence ALL actual coordinate pairs V_j and z are acquired in soft k bits, rather than O(k) vectors of length k.

Coverage is exact. At the own tag j=P modulo k, the native tangent calculation supplies the integer

    HI=a_j P+Q+ell_j, 0<=I<L=2H+2.

The inequalities and integrality are the composite-row predecessor's proof and do not require k prime. For the scalar exponent,

    E_j-HI=(P-1)(Q-a_j).                         (4)

At this tag e_j=(D/P). If e_j=+1, Texp_j-HI=(P-1)(Q-a_j); if e_j=-1,

    Texp_j-HI=-(P+1)(Q+a_j).                    (5)

The local order of W divides P-e_j. Thus W^Texp_j=W^(HI), while beta^E_j=beta^(HI) by (4). Consequently V_j=z^I modulo P as a WHOLE quadratic-algebra equality, on either the split or field side. This proves a covered family without a period-survival assumption. The old native horizon has not decreased.

Retain ALL raw unit tags. Deduplicating merely by delta is unsafe here: equal scalar exponents need not give equal W powers, and deleting the own row could delete its quadratic hit. Repeated actual targets are harmless to the monic product/restriction algorithm. No target-difference inverse, discriminant, simple-root claim, or root-gradient recovery is used.

## 4. Actual short-seed unit screen, including BOTH local sides

Although W itself has no order certificate, the COUPLED seed z can be safely screened. Its norm is

    Norm(z)=beta^(2H).

Fix the unknown nonsplit prime p*. If z^d=1 in B modulo p*, taking norms gives beta^(2Hd)=1. The order of beta^H modulo p* is odd and >C. Hence this is impossible for every 1<=d<=C. Since B modulo p* is a FIELD, Norm(z^d-1) is nonzero there for all these d. At the other, split side z^d-1 may be nonunit; any such event gives a proper factor, not a saturated obstruction.

Here is an initialized soft-k certificate. Put b=4k, so b²=C exactly. Acquire the monic polynomial

    A(X)=product_(v=1)^b (X-z^v)

and evaluate it by monic multipoint evaluation at z^(-bu), 0<=u<b. Its u-th value is a known unit times the product of z^(bu+v)-1 over 1<=v<=b. Compute the rank-two norm of each value and gcd with N. The exponent blocks cover exactly 1,...,C, with no overhang. Every block norm is nonzero at p*, so gcd N is impossible; a nonunit block immediately gives a PROPER factor. If all gcds are one, EVERY z^d-1, 1<=d<=C, is a unit in B: a product is a unit in a commutative ring only if each factor is a unit, and an element of B is a unit iff its explicit norm is a unit in R. Polynomial construction/evaluation has cost soft b=soft k, using monic arithmetic over B even before the screen has certified node differences.

Thus all short geometric-node inverses required by the old blocked query are available, or a factor has already been found. The standard blocks use exponents bounded by L<C and degrees at most soft k^(3/2)<C for sufficiently large k; the fixed small endpoint cases can use direct multiplication. No large-order assertion about each split coordinate is silently inherited from beta. The screen establishes the needed unit conditions directly on BOTH local sides.

## 5. Same-leaf beta recovery from scalar norms

For an actual leaf f=V_j-z^i, define the original scalar condition

    G=beta^(2E_j)-beta^(2Hi).

Because Norm(V_j)=beta^(2E_j), the exact identity is

    G=bar(V_j)*f+z^i*bar(f),
    (f,bar(f))=(f,G).                            (6)

The reverse inclusion uses only the explicit unit (z^i)^-1. For an arbitrary split component, Norm(f)=0 alone need not give G=0. We do NOT make that false claim. Instead:

* If gcd(Norm(f),N) is proper, it already factors N, regardless of pairing.
* If this gcd is N, then Norm(f)=0 at p*. Since B modulo p* is a FIELD, f=0 there, hence bar(f)=0 there, and (6) gives G=0 modulo p*.

Now compute g=gcd(G,N). This cannot be one. A proper g factors. If g=N, odd beta orders remove the squaring, giving beta^(E_j-Hi)=1 modulo BOTH primes. This is exactly an original bounded native scalar leaf, using the retained j,i labels, so its old decoder applies. More explicitly, coprime beta orders make their product divide K=E_j-Hi. Comparing this multiple with N-P-Q+1 by the original short-index bound forces K=N-P-Q+1; equivalently

    P+Q=1+Hi-delta_j.

The fixed predecessor decoder checks the resulting integer quadratic before output. Its hypotheses are the already prepared scalar margins and i<L<4H, not any order of W. Thus saturated norms cannot get stuck in an unpaired or shared torus kernel.

For a product over ANY supplied row/index restriction, compute the norm of the product in B and its gcd with N. Multiplicativity gives the usual product-tree localization: a proper gcd factors; a unit discards the restriction; a saturated node can be split, returning a proper factor or a saturated child, until reaching an ORIGINAL leaf. At least one saturated child exists whenever all children have gcd only 1 or N and the parent is saturated. Therefore every nonunit norm restriction has a complete factor/original-witness consumer. Different leaves at the two primes do not cause a cross-leaf error: localization precedes (6), and the single surviving leaf is paired at p* automatically.

Own coverage from (4)--(5) guarantees the full family's norm is nonunit. All conclusions hold without knowing p*, its sign, either prime, or any torus order. There is no required global equality for W and no use of an unpaired norm leaf as a scalar witness.

## 6. Paid terminal computation and its unchanged bottleneck

Form, over B, the MONIC target polynomial

    F(X)=product_j (X-V_j), J=phi(k)<=k.

It is acquired in soft k bit operations by a product tree. The exact family product is

    E_B=product_(0<=i<L) F(z^i),
    E_scalar=Norm(E_B).                          (7)

Constant rank makes each B operation a fixed number of R operations; polynomial multiplication, monic remainder/MPE, and the original geometric blocked product therefore retain their old cost. With the paid seed screen, a complete computation including restriction descent costs

    soft(J+sqrt(JL)) <= soft k^(3/2).

All targets, seed, character values, guards and norm evaluations are charged. The usual geometric monic implementation does not invert differences of target roots. If a different implementation requires target separation or simple-root AD, that additional contract is NOT supplied by this report. Even distinct delta targets only prove absence of field-side collisions via their beta norms; equal delta tags require separate care. We retain all rows and use the older zero-safe product/controller instead.

The elementary all-row norm expansion is also explicit: for a supplied i,

    Norm(V_j-z^i)
      = beta^(2E_j)+beta^(2Hi)
        - beta^(E_j+Hi)*Tr(W^(Texp_j-Hi)).        (8)

Each value costs polylog N, hence all rows at ONE i cost soft k. Formula (8) is not a fast acquisition for all L indices. It shows exactly what scalar mixed trace remains after the unit phases have been normalized. Nor does multiplicativity turn (7) into a shorter original scalar polynomial. The degree and horizon are still J and L; no soft-k endpoint routine has been obtained.

## 7. Original primitive cyclotomic one-leaf test versus the family issue

For comparison, in a primitive cyclotomic algebra over F_p, a conjugation-stable Frobenius orbit has -1 in the subgroup generated by p modulo k. A norm zero on such an orbit is conjugate paired; a general orbit need not have that property. This criterion alone is not a paid discovery algorithm because p is unknown. The public Jacobi sign above deliberately forces a usable quadratic quotient at at least one side, avoiding classification of all primitive orbits.

Root's one-leaf joint-support test is valid separately. For a SUPPLIED degree<phi(k) primitive vector f, use guarded polynomial half-GCD on Phi_k,f,bar(f) over R. Unit leading coefficients permit ordinary monic normalization; a proper leading-coefficient gcd factors N; a globally zero leading coefficient is dropped. A successful monic gcd of positive degree supplies common support at both local fields, and degree zero means no paired support. Fast gcd costs soft k for this supplied input, with every inversion guarded. If local gcd degrees would disagree, the common monic Euclidean execution must encounter a nonunit pivot first. This does not acquire f itself for free.

Applying that test to a FAMILY product is unsafe as a same-leaf detector: f_(j,i) can vanish at one component while a DIFFERENT conjugated leaf vanishes at its conjugate. The polynomial gcd then detects cross-leaf support. No native orbit symmetry aligning those labels has been proved here. The quadratic constructor's recovery does not use a gcd of family products: it uses scalar norm localization and the field-side implication for the selected original leaf.

## Ledger and exact contribution

| Operation | Worst-case bit work | Output/qualification |
|---|---:|---|
| Public Jacobi-minus-one D, factoring small public a | soft N^(5/32) | factor or negative fundamental D; accepted finite-input convention |
| Conductor-synchronized k, public units/characters | soft k | k=Theta(N^(1/6)), c divides k |
| Original composite-k beta setup | soft k | factor or BOTH local beta and H-power margins |
| W and ALL actual quadratic V_j | soft k | explicit rank-two coordinates; no torus order promise |
| Coupled-seed short-difference screen | soft k | factor or all z^d-1 units for 1<=d<=16k² |
| Supplied original leaf norm/recovery | polylog N | proper factor or original beta bounded witness |
| Supplied rank-k primitive vector joint gcd | soft k after input | separate one-leaf test, not family acquisition |
| Complete covered quadratic query and recovery | soft(J+sqrt(JL)) | old worst-case soft k^(3/2) |

This is a positive uniform paired-recovery constructor, with discovery and both-side guards paid. It removes the need to certify survival/large order of a Gauss-period or norm-one seed before using beta-coupled norm hits. It changes the source to a publicly aligned quadratic quotient; it does not solve the original full-order Gauss acquisition or the scalar terminal recurrence. The whole-query sixth-rate target remains open in this attempt.
