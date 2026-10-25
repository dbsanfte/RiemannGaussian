# Quadratic period norm-one controller: paid branch and preparation gap

2026-10-24. Scratch only; repository read only. No examples, numerical claims or new all-input rate. Read proposal.txt, the preserved quadratic colour journal, SemiprimeOrderSeparation.lean, the quadratic extraction probe, and the torus-Frobenius report. Coordinate with recurrence_review: that constructor audit certifies the quadratic cyclotomic period point, but finds no period-specific long-order transfer from beta.

## Correct carrier and acquired constructor

Let m be the prepared odd prime, H=m², D=chi_m(-1)m, and B=R[tau]/(tau²-D), R=Z/N. The quadratic Gauss period belongs to the NONTRIVIAL CYCLOTOMIC component, not to a rank-two subalgebra with tau²=D in the full cyclic algebra. In the full cyclic algebra the corresponding Gauss sum has square D(1-e0); the quadratic-invariant algebra also has an augmentation summand. This controller uses only B, with the independently justified cyclotomic embedding/Frobenius action.

The proposed fast Newton/power-sum construction acquires U in B in soft m residue arithmetic with all small integer divisions certified. Its conjugate norm is
  n_U=U*bar(U)=(beta^m+1)/(beta+1).
Both displayed scalars are units under the prepared odd-local-order beta promise. Hence U^(-1)=bar(U)/n_U, W0=U/bar(U), and Norm(W0)=1 are actually acquired. No hidden local square root or field decomposition is needed. This report imports the reviewed constructor rather than claiming a new proof of its Gaussian embedding.

## Existing public setup and exact local collision theorem

The repository already supplies the relevant group arithmetic:

- `RiemannGaussian/SemiprimeOrderSeparation.lean`, `colour_gcd_separator` and `coloured_projected_orders_coprime` (around lines 99 and 109), prove the signed-cardinality separator and projected coprimality under local order divisibility.
- The same file's `quadratic_norm_one_collision` (around line 308) proves Norm(x-y)=0 iff x=y for norm-one elements over a field with D!=0 and 2!=0, INCLUDING split quadratic algebras.
- `scripts/probe_semiprime_quadratic_extraction.py` implements rank-two arithmetic and geometric collision trees. Its finite discriminant/parameter menu can report kernel-unresolved; this is explicitly not a uniform source theorem.
- `docs/research-evidence/semiprime-collision-representation-20261022/reports/torus-frobenius.md` records paid Cayley/Dickson coordinates and cautions that a compressed trace is an OR of direct/inverse matches, not an oriented collision by itself.

For p|N, write eps_p=(D/p)=chi_m(p), using reciprocity for this D. The norm-one group in B modp has size p-eps_p: it is F_p^* in the split case and the kernel of the norm F_(p²)^*->F_p^* in the nonsplit case. These local colours are proof variables, not algorithm inputs. D is a unit because m is coprime to N.

For norm-one x,y, let z=x*bar(y). Norm(x-y)=2-Tr(z). If that norm vanishes locally, z has real coordinate 1; Norm(z)=1 then forces D times its imaginary-coordinate square to vanish, hence that coordinate is zero. Thus x=y even in the split case. Zero norm of an arbitrary split-algebra element would NOT imply zero; the norm-one hypothesis is indispensable.

## Charged separator and complete short-order screen

Compute s=Jacobi(D,N), Esep=N-s, and W1=W0^Esep. Let A=P-eps_P and C=Q-eps_Q. Modulo A, Esep is eps_P*(Q-eps_Q), so gcd(A,Esep)=gcd(A,C), and symmetrically for C. Therefore the two orders of W1 are coprime, as the cited Lean theorem establishes.

First compute g1=gcd(Norm(W1-1),N). A proper gcd returns a factor. If g1=N, local norm-one collision equivalence forces W1=1 globally: this is the genuine separator-kernel UNRESOLVED branch, not a successful certificate. If g1=1, both coprime local orders are greater than one.

Odd orders are not needed by the collision or signed decoder, but they can now be acquired WITHOUT an extra unresolved case. Raise W1 to 2^v, v=ceil(log2(N+1)), and call the result W. Since the two preprojection orders are coprime and both >1, at most one is even, and the other has a nontrivial odd order and survives. Thus W cannot be globally one. Testing gcd(Norm(W-1),N) either returns a proper factor (one side died) or is a unit; gcd=N is mathematically excluded. The work is O(log N) rank-two operations. On the unit branch W has coprime odd local orders >1.

Next form q=W^H. Its two orders remain coprime. They cannot BOTH be one: that would require both nontrivial coprime orders of W to divide the prime power H=m². Test gcd(Norm(q-1),N); a proper factor returns immediately, and otherwise the gcd is a unit. A saturated gcd is again excluded by the proved group arithmetic. Therefore both q orders are nontrivial before the following single order screen. No original-beta order promise was transferred to q.

Take T=16H. A complete rank-two geometric screen of q through exponents 1,...,T costs soft sqrt T=soft m:

1. Let b=ceil sqrt T. Build the degree-b polynomial with roots 1,q,...,q^(b-1) over B.
2. Evaluate it at q^(b j), 1<=j<=ceil(T/b), by geometric MPE or monic general MPE. The differences cover the consecutive positive exponents b j-i. The last block may be trimmed or conservatively extended.
3. Take scalar norms of the acquired block values and gcd with N. If all are units, both local q orders exceed T (hence both W orders do too).
4. In the first nonunit block descend its acquired product tree, evaluating node polynomials at that block point. A proper norm gcd gives a factor. A saturated leaf is not itself a factor; continue into other relevant leaves.

Why this screen has a proper-factor witness whenever a short order exists: if the coprime local q orders sP,sQ are both greater than one, exponent min(sP,sQ) annihilates precisely the smaller side. The preceding guards established both are greater than one. The first nonunit exponent block therefore contains a proper witness. Complete descent within that one block costs soft b: the sum of node degrees on each fully traversed tree level is b, with O(b) gcds. This avoids assuming that the reference probe's early 'shared-order' outcome is a complete controller for this branch. The rigorous controller returns either a proper factor, W1=1 unresolved, or certified coprime odd W orders rP,rQ>T together with coprime q orders >T, all with paid soft-m preparation including the period constructor.

The q-order certificate was obtained by an actual q-screen after the charged guards; it was not inferred merely from the W-order bound. The direct monic product/MPE query below would not itself need q-node separation, but the stronger guard is now lawfully available.

## Native row coverage in the rank-two group

Let e=chi_m(j), a=a_j, ell=ell_j. Since inverse tags have the same quadratic character, the actual normalized row is
  Y_j=W^(E_j), E_j=ell+e(N+a), q=W^H.
All Y_j are acquired in soft m total rank-two scalar-power work. At the own tag j=P modm, e=eps_P and the original native integer relation is n=HI=aP+Q+ell. The exponent differences are exactly
  E_j-HI=(P-1)(Q-a) if e=+1,
  E_j-HI=-(P+1)(Q+a) if e=-1.
Thus Y_j=q^I modulo P. Raising W0 to the public preparation exponent preserves this own hit. Use a conservative inherited public horizon h<=4H+4 if needed; it contains the originally supplied index convention.

For any restriction of rows/seeds, form the explicit degree-J polynomial F(Z)=prod_j(Z-Y_j) over B and acquire prod_(i<h)F(q^i) by ordinary scalar polynomial blocking in B. Norm of the product vanishes at p exactly when one difference Y_j-q^i vanishes there, by the local norm-one collision theorem and norm multiplicativity. The cost is soft(J+sqrt(Jh))=soft m^1.5, since B has fixed rank two. Product-tree/seed descent finds a proper norm gcd or one saturated leaf. No arbitrary split-algebra norm-zero implication or trace orientation is used.

This is a complete covered query AFTER the paid preparation returns its large-order certificate, but its cost remains the existing scale. It is not an unconditional controller because the period point may die under the separator.

## Exact recovery from a saturated GLOBAL torus collision

Assume preparation returned rP,rQ>16H, coprime. If a leaf is saturated, norm-one collision equivalence in BOTH local algebras gives W^K=1 globally, where
  K=ell+e(N+a)-Hi.
Set the proof-only common group exponent
  lambda=(P-eps_P)(Q-eps_Q).
Both local orders divide lambda, and rP*rQ divides K and lambda. Let t=e*eps_P in {+1,-1}. A direct expansion gives
  K-e*lambda = C0+t*(Q+sP),
  C0=ell+e*a-Hi-e*s.
C0 uses only public j,i,N,m metadata and s. Neither lambda nor either private character is an algorithm input.

The native centered bounds give abs(ell)<(5/2)H, a<m and i<4H+4, hence abs(C0)<5m^4 for m>=17. Also P<=m³ and Q<N/(16H)<=m^4/16, so P+Q<m^4/8 for m>=17. Therefore
  abs(C0+t*(Q+sP))<6m^4<256m^4<rP*rQ.
As rP*rQ divides this integer, it must be zero. Thus
  abs(C0)=P+Q when s=+1,
  abs(C0)=Q-P when s=-1 (P<=Q).
This is a valid saturated decoder for ANY acquired saturated row/seed leaf in the stated horizon, not only the own tag.

Execute it using integer square roots and verification:
- s=+1: S=abs(C0), R=isqrt(S²-4N); verify the radicand is a square, then candidates (S±R)/2.
- s=-1: D0=abs(C0), S=isqrt(D0²+4N); verify the square, then candidates (S±D0)/2.
Check parity, strict nontriviality and divisibility by N before output. Under the proved hypotheses these checks succeed and recover P,Q. Bit work is soft log N. This decoder uses the known Jacobi PRODUCT and avoids pretending that a beta-specific annihilator decoder automatically applies to W.

## Primary Gauss/Aurifeuilian and group literature

Richard Brent, *On computing factors of cyclotomic polynomials*, Math. Comp. 61 (1993), [author primary record and files](https://maths-people.anu.edu.au/brent/pub/pub135.html), [preprint](https://arxiv.org/abs/1004.5466). It gives Gauss identities 4Phi_n=A_n²-(-1)^((n-1)/2)n B_n² and generating-function/Newton-sum algorithms, stated at O(n²) integer arithmetic in the abstract. These support classical algebraic structure; they do not certify the order of a specialized norm-one point over unknown prime fields. Fast modular series arithmetic in the reviewed constructor has its own paid unit ledger.

Allombert–Belabas, *Practical Aurifeuillian factorization*, JTNB 20 (2008), [primary article](https://www.numdam.org/articles/10.5802/jtnb.641/). Its stated deterministic soft(d² L) bound assumes a suitable Riemann Hypothesis and concerns special cyclotomic VALUES admitting Aurifeuilian factors. It neither supplies an unconditional long-order period point nor replaces the arbitrary-semiprime query.

H. C. Williams, *A p+1 method of factoring*, Math. Comp. 39 (1982), [primary DOI](https://doi.org/10.1090/S0025-5718-1982-0658227-7). It uses the smoothness of a local p+1-type group order. The norm-one group and Lucas machinery are classical; a smoothness-dependent route is not a uniform bound for the present branch.

## Root palette follow-up and generic Cayley comparison

Root supplies a further positive raw-palette theorem, checked here. Write h=(m-1)/2 and U(Z)=A(Z)+tau B(Z). The coefficient of Z^(h-1) in U is the first quadratic period (-1+tau)/2. Therefore B has EXACT degree h-1 and leading coefficient 1/2, a unit in each residue field. Acquire the m-2=2h-1 nodes beta^t, 1<=t<=m-2; the prepared beta order makes these nodes distinct in each hidden field. Ordinary monic MPE evaluates both degree-O(m) polynomials at all these nodes in soft m.

In either field B vanishes at at most h-1 nodes. The union of the two local bad-node sets therefore has size at most 2h-2, less than the 2h-1 supplied nodes. A complete list of gcd(B(beta^t),N) thus returns either a proper factor, or a node with gcd=1. At that node U has norm (beta^(tm)+1)/(beta^t+1), a certified unit. Separately U-bar(U)=2tau B is a unit, with norm -4D B². Hence W0=U/bar(U) is nonidentity in BOTH local fields. All point values, guards and the successful choice are acquired in soft m. This is an actual guaranteed RAW nonidentity supplier, not just a possible adaptive benefit.

It does NOT force this selected point, or the whole palette, to survive projection. The equation
  (U(beta^t)/bar(U(beta^t)))^(N-s)=1
has a large exponent and can have many roots; the low degree of B controls only exponent one. No bounded-degree root-count proof that the projected palette survives is available here, and no full-torus generation assertion is inferred from the raw polynomial's nonidentity.

A preliminary public twin screen eliminates the extreme case in which the separator kills the ENTIRE local norm-one groups on both sides. Indeed this would mean A|Esep and C|Esep. The gcd identity then forces A=C; since P<Q this is possible only when Q=P+2, eps_P=-1 and eps_Q=+1. Then N+1=(P+1)^2, recognized by one integer square root and verified factor division. This observation concerns the whole groups. It does not exclude a particular period point or the entire finite period palette lying in smaller separator kernels when A!=C.

The known public Cayley parametrization (a+tau)/(a-tau) supplies arbitrary explicit norm-one points when a²-D is a unit. A proper gcd of that denominator factors N; a saturated denominator needs separate handling. The existing repository prototype checks only a finite parameter menu and explicitly returns kernel-unresolved when necessary. Its colour and order-separator theorems prove what happens AFTER a surviving point is supplied; they do not certify a universally successful short Cayley interval. A new character-sum or short-generator theorem would require its own exact hypotheses and full preparation cost. No Burgess-type bound or torus-short-interval transfer is assumed in this report.

Thus the period palette guarantees a raw nonidentity point on both sides in soft m, but its all-input projected-order supply remains unresolved. This is a stronger raw supplier than the finite prototype menu; it is not a long-order supplier after separation.

## Outcome and exact remaining gap

Acquired: a rank-two period point, its norm-one quotient, public Jacobi separation, guarded odd projection and q construction, complete short-order screening, a valid covered rank-two query on the surviving branch, and an independently derived signed sum/difference decoder for saturated global collisions. Preparation costs soft m, surviving query costs soft m^1.5, and saturated recovery costs soft log N.

Unacquired: a guarantee that the actual period point survives the public separator, or a paid rule choosing replacement period data that always supplies a surviving point in soft m. The period construction gives a special explicit torus point, but no checked theorem improves this controller's order supply beyond the generic torus-point setup. Original scalar beta preparation remains available as a fallback; it does not establish the missing W certificate. No all-input rate gain is claimed.
