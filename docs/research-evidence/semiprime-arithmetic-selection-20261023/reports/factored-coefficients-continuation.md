# Factored coefficients and the joint short-seed root query

23 October 2026. Scratch only. No all-input soft-r acquisition algorithm was found. This note uses the now acquired full factorizations of a and |C|, derives the exact global polynomial splitting and its cost, and identifies the missing reconstruction input. It does not reuse the earlier residue-universal menu obstruction or assert a lower bound for an N-dependent selector.

## 1. What the factorizations do and do not select

For a true source row, M=r^4, H=r^2 and

    M sigma=a c^2P+B c+C Q,
    delta=gcd(c,sigma)=gcd(c,C).

Factoring C provides the possible delta values. Writing c=delta*v and sigma=delta*u reduces the ratio to u/v with gcd(u,v)=1 and bounds v<r/delta, |u|<3.5r/delta. It does not identify delta, v, or u. Even if delta were supplied free, the primitive ratio remains unknown when delta is small. The delta=1 case is actually present in the retained prepared example, not an empty algebraic branch.

An explicit loop over every c consistent with the divisor groups gains no multiplier-count saving:

    sum_(delta|C) #{1<=c<r : gcd(c,C)=delta}=r-1.

Factoring a and refining this partition by gcd(c,a) does not change its union. Processing every group in every acquired descriptor therefore still costs O(Jr), J=O(r) per window, before any reconstruction inside a group. A proof identifying a successful thin collection of groups would be substantive new input; coefficient factorization alone has not provided one. This is the exact cost of that enumeration, not a universal-menu or algorithmic impossibility claim.

The companion `ideal-short-cofactor.md`, Section1, now proves total soft-r acquisition of these complete factorizations by a prime-product refinement, including the residual prime >r when present; this is more than extraction of smooth parts. The argument below grants the resulting factorizations as supplied data, so it remains valid even without charging their already proved acquisition again. The remaining selection is unresolved despite this favorable input.

## 2. Both modular roots are already computable

Write the integer source polynomial as

    g(h)=a h^2+b h+d0,
    b=(2as+B)/H,
    d0=(as^2+Bs+CN)/M.

Since a<r<P,Q and H is a unit modulo N, its monicization

    F(z)=z^2+bz+a*d0=a*g(z/a)

splits modulo N with the TWO explicit roots

    z0=-a*s/H modN,
    z1=-(a*s+B)/H modN.                                (1)

Their difference is -B/H. Since B^2=M*D0 modulo N and M is a unit modulo N, the existing gcd(D0,N)=1 screening branch already implies gcd(B,N)=1. This root-collision gcd is therefore not an additional detector. No factorization of a or C is needed for (1).

At the true witness z=a h is a nonnegative integer and

    z<a*X<=2sqrt(N)/r<=2H,
    F(z)=a*sigma*P.                                    (2)

Thus all windows map into a common small-integer-lift problem: find some row root z_i and integer 0<=z<L=ceil(2sqrt(N)/r) such that gcd(N,z-z_i)>1. The actual first-root witness is included. This forgets the short-sigma condition; it is an overcover, not a new sparse selector.

These integer leaves have particularly clean recovery. After multiplication by the unit H they are

    Hz+as, or Hz+as+B.

They are nonzero because their residues modulo r are a and -a. Their absolute values are <3H^2<N, using |B|<=H^2/2, a<r/16, L<=2H and N=P Q>256H^2. Therefore an individual nonunit leaf always gives a PROPER gcd, with no saturated-annihilator case. Product-tree localization handles a saturated aggregate.

For J=O(r) supplied descriptors, a standard additive block/product-tree acquisition is explicit. Choose block width q, build the degree-q polynomial product_(i=0)^(q-1)(X+i), and evaluate it at the O(J*ceil(L/q)) shifted root points. The total cost is

    soft O(q+J+JL/q),

hence soft O(sqrt(JL)+J)=soft O(r^(3/2)) in the largest windows. Performing a separate length-L search per row costs soft O(J*sqrt L)=soft O(r^2). Factoring a,C does not lower these costs without an additional source-specific contraction.

## 3. Exact transfer to the inherited linear AP in the monic case

For A=1, the signed interval |C|<=floor(H/2) and CN=1 modulo r has exactly r C values. The map C->s is bijective onto s=1+rt, 0<=t<r. Thus the first-root part of (1) has exactly the original full AP family.

For any common integer length L,

    product_(t=0)^(r-1) product_(z=0)^(L-1) (Hz+1+rt)
      =product_(v=0)^(rL-1) (rv+1),                    (3)

by v=rz+t. The normalized root-difference product differs only by the known unit H^(-rL). At L of order r^2 this is a single AP of length of order r^3, with the inherited soft-r^(3/2) ordinary product acquisition. This exact source transfer prevents presenting monicization as search thinning. It is not a lower bound for a different integer algorithm, nor does it show that the added second roots cannot help. No faster use of those roots was obtained.

## 4. The precise rational-reconstruction input is absent

A supplied residue of the true ratio mu=sigma/c modulo M WOULD be enough for a cheap test. Denominators c<r are units modulo M. Two reduced fractions with |numerator|<=4r and denominator<=r that agree modulo M have cross-difference of absolute value <=8r^2<M, so are equal. Extended-Euclidean rational reconstruction and then the integer quadratic v*g(h)-u*(Hh+s) recover/check the witness in polynomial log N work. This is a concrete missing input, not an assertion that a low-height ratio can be reconstructed without an image.

The source supplies no such ratio residue. With Y=Hh+s its exact identity is

    M*g(h)=aY^2+BY+CN,
    M*g(h)/Y=aY+B+CN/Y.                                (4)

Modulo N the polynomials g and Y share their public linear factor, giving M*g=Y(aY+B). Cancelling Y as if it were a unit at the hidden witness would produce the wrong quotient: at Y=cP the missing term in (4) is exactly

    CN/Y=CQ/c.

Factoring C, or inverting it modulo N, does not supply Q/c. The pole cancellation in the polynomial ring is not evaluation of the ordinary rational value at this nonunit input. Equivalently, one can compute mu modulo M from g(h)/(Hh+s) IF h is supplied, since Y is a unit modulo M; h is precisely the unknown small lift.

Primary algorithm reference for the supplied-image operation: Collins–Encarnacion, *Efficient Rational Number Reconstruction*, Journal of Symbolic Computation20(1995), author-affiliated publication page https://www.microsoft.com/en-us/research/publication/efficient-rational-number-reconstruction/ . The uniqueness bound above is elementary and uses the actual source sizes. No reconstruction oracle is assumed.

## 5. Discriminants and the paired equation retain the same unknown

The source-specific discriminant is

    D0=b^2-4a*d0=(B^2-4aCN)/M,
    (2ah+b)^2=D0+4a*sigma*P.                            (5)

The prime factor P cannot be deleted from the last term. Alternatively the quadratic in P has square discriminant

    (Bc-M sigma)^2-4aC*c^2*N.                           (6)

Knowing the factors of aC factors the small coefficient of N in (6), but does not supply c, sigma, or its integer square root. Completing (6) as a difference of squares gives the split factors 2a*c^2*P and 2C*Q; stripping known small factors leaves the same hidden N factors. No fixed per-row integer-root polynomial independent of the ratio was obtained.

In the all-input paired formulation, t=dQ modH, b_t=center(-N/t modH), and ell=(s+b_t*c*d)/H, one has the exact short-seed equation

    g(c*tau-ell)=sigma*(H*tau-b_t*d),
    P_candidate=H*tau-b_t*d.                            (7)

Both seeds are O(r), even in unbalanced windows. Factoring a,C does not acquire the candidate multiplier c, its coupled d=N^(-1)/c modr, or the phase/carry ell. For a specified candidate, tau is restricted further to an interval of length P0/H by its factor window. Finding the solutions separately still expands J(r-1) labeled candidates per window; full divisor-group enumeration in section1 does not reduce this count.

Every integer solution of (7) in the genuine factor window gives a proper factor: P_candidate divides CN by (4), P_candidate>|C|, and P_candidate<N. This divisibility needs no division by H. Moreover P_candidate is a unit modulo H since it is -b_t*d modulo r. Thus recovery is fully paid; the missing input is acquisition of ONE successful bounded integer lift or its ratio image across the source, not another decoder assumption.

## 6. Exact remaining constructive problem

Granting factored a,C, all global roots (1), all divisor partitions, and all coupled multipliers d(c) still leaves one source-specific operation: acquire a small local lift obeying (7), or equivalently a true low-height value of g(h)/(Hh+s), in TOTAL soft O(r) across the O(r) descriptors and logarithmically many size windows. The explicit batch gcd algorithm is soft r^(3/2), and separate reconstruction by multiplier is soft r^2. An acquired ratio image modulo r^4 would collapse each selected row to one cheap integer-root test, but no method to obtain that image without the unknown lift/cofactor has been proved here.

This is not claimed irreducible in complexity theory. The actual N-dependent selector remains open. No restricted class, more additive statistics, or known-root descriptor is being counted as overall factoring progress. No repository files were changed.
