# Minimal dangling-node gauges are paid; a few telescoping q-products do not replace their residue packet

2026-10-16. Actual-source gauge construction and two precisely scoped route obstructions. No nearlinear whole-query or residue acquisition algorithm was found. A linear number of poles or gauge blocks is NOT called a superlinear operation bound.

## 1. Literal graph and a minimal explicit gauge

Use the retained actual first-current nodes z_i=gamma^(-N-delta_i), q=gamma^d, d=m^2, after public exact-offset deduplication. There are J=Theta(m) nodes, their differences are units, their integer offsets lie in [-3d,d], and their low-digit fibers have size at most two. Both local gamma orders exceed 16d. The source successor relation is therefore exactly

    qz_i=z_j iff delta_i-delta_j=d as an integer.

It is identical in both fields. Its components are one- or two-node directed chains. Let D be the dangling terminals, so |D|>=ceil(J/2), and define

    G(t)=product_(i in D)(t-qz_i).                 (1)

This gauge has a simple zero at every dangling successor and is a UNIT at EVERY original source node. The latter follows because a dangling successor belongs to neither field's source set. All differences qz_i-z_j used in G(z_j), and qz_i-qz_k used in G'(qz_i), are consequently units modulo N. A polynomial vanishing at all these distinct successors must have degree at least |D| in either field, so (1) is a minimal-degree polynomial with these required zeros.

Everything in (1) is public and paid in soft O(J) metadata work: sort/deduplicate the literal offsets and look up delta_i-d, build G by a product tree, evaluate G at the source nodes and G' at its roots by monic multipoint trees, and batch-invert the unit values if needed. There is no factoring/order oracle or long F value in this setup.

Take a=q^L and the additional delta-unit branch

    Delta=product_j(1-a z_j) is a unit modulo N.

This is the same normalized-operator branch as before; a proper gcd of Delta already factors N, and saturated failure is outside this branch. Set w=(1-t)/(1-a t) and w_G=w G(qt)/G(t). Formula (1) kills every dangling source value of w_G, so H divides its regular numerator times H(qt). Thus this gauge DOES repair homogeneous quotient descent. It is not excluded by the earlier regular-weight obstruction: its zeros remove the missing information from the homogeneous source operator.

On a two-node chain, a remaining nonzero transition leads directly to its dangling terminal, where the new weight vanishes. Hence the descended value operator is nilpotent of index at most two. Its homogeneous fixed-point equation contains no nonzero source payload. The actual rational payload F/G instead requires the residues described next. This is a valid cheap gauge/operator construction, not a cheap evaluation of that payload.

## 2. Exact residue packet and finite parts

At every dangling successor qz_i, the ordinary formal residue is

    rho_i=F(qz_i)/G'(qz_i), i in D.                (2)

This is well defined modulo N because the derivative denominator is a unit. In each field a residue may vanish and the corresponding pole cancel; on the many unit rows it is a genuine pole. If 1-z_i is also a unit, the exact q-difference identity gives

    rho_i=[(1-a z_i)/((1-z_i)G'(qz_i))]F(z_i).    (3)

All displayed prefactors are public and paid units on that two-endpoint-unit row. Formula (3) is not applied at z_i=1. Indeed F(1)=0 while F(q) is a unit, so that endpoint cannot be propagated through an invalid division.

The finite-part cancellation at a dangling node is explicit: near t=z_i,

    w_G(t)=w(z_i) qG'(qz_i)(t-z_i)/G(z_i)+O((t-z_i)^2),
    (F/G)(qt)=rho_i/[q(t-z_i)]+O(1).

Their regular product has value w(z_i)G'(qz_i)rho_i/G(z_i), exactly F(z_i)/G(z_i) where (3) applies. At a nondangling node its successor is another original node and the rational payload is regular there. Thus the one-/two-node chain equations reconstruct the source payload from the terminal residues with soft O(J) postprocessing on the appropriate regular branch. The residues themselves have not been acquired.

A weighted residue sum is a legitimate remaining escape. It may avoid a full packet, and sums of units can reveal a factor. No cost lower bound for such aggregates follows from (2), the pole count, or the packet size. The paid selected coefficients of F and the one-binomial oracle do not presently supply (2) or an adequate factor-selective aggregate of it at soft O(J).

## 3. The residue packet retains both exclusive proper-factor supports

This claim uses the prior actual exclusive-own-row family and the Delta-unit branch, but does NOT assume 1-z_j is a unit at every OTHER source node.

The own P row has known proof-side true index

    i_P=(a_P P+Q+ell_P)/d,  0<=i_P<L,

and analogously for Q. On the balanced source a_P>=1, ell_P>=-3d, and P,Q=Theta(m^3). Thus i_P>=(P+Q)/d-3=Omega(m), in particular i_P>=2 for sufficiently large m; the same holds for i_Q. This is a lower bound on the existing native true index, not a newly acquired private index.

In its P field the own row is q^(-i_P), and its value has gcd exactly P. Following a source chain takes at most one q-step to a dangling terminal. At the own row and that terminal the P-field exponent remains at least one; hence 1-z is nonzero there. In the Q field the value stays nonzero: initially it is nonzero by exclusive ownership; the Delta-unit promise makes 1-a z a unit, and a nonzero F(z) excludes z=1. Therefore the q-step multiplies F by a unit in both fields. At the terminal, the further q-step in (2) still has a unit ratio because its source P exponent is at least one. Its residue has proper gcd P.

The Q own row similarly reaches a residue with proper gcd Q. These two terminals must be distinct, since along these chains the proper support has been preserved. Thus the minimal gauge residue packet contains BOTH a P-only and a Q-only value, with cheap unit normalizations. Endpoint behavior of unrelated rows is irrelevant to this argument.

It follows that this whole residue packet cannot be represented by ONE common prefix-product stream with unit denominators and rowwise unit prefactors, even with advised index assignments and arbitrarily large horizons. Prime-zero support is nested along such a stream. If the P-only residue has the earlier index, its P zero persists at the Q-only value, a contradiction; reversing the order gives the analogous Q contradiction. A single common Gaussian-coefficient stream has precisely that prefix-ratio form when its denominators are units. Ratios between separately selected stream values, sums, nonunit prefactors and multiple streams are outside this theorem. This is an actual residue-packet representation obstruction, not a scalar factor-query lower bound.

## 4. Few contiguous q-product gauges cannot repair the actual carrier

There is a second obstruction that does not depend on the residue-support argument or on global units of 1-z. Let a gauge be ANY rational product of r contiguous q-products,

    G(t)=C product_(nu=1)^r P_(T_nu)(g_nu t;q)^(epsilon_nu),

with C nonzero, T_nu>=0, nonzero integer epsilon_nu, and arbitrary nonzero origins g_nu. Origins, horizons and signs may depend on the full input or private advice. Assume the reduced G is regular and unit at source nodes, and the resulting w_G is regular there. The formal identity is

    G(qt)/G(t)=product_nu [(1-g_nu q^(T_nu)t)/(1-g_nu t)]^(epsilon_nu).  (4)

Thus w_G has at most r+1 DISTINCT finite zero locations: one from 1-t and at most one numerator endpoint per signed block. Integer powers change multiplicities, not this distinct-location bound. Cancellations can remove zeros or poles but cannot create a zero away from those numerator endpoints. Arbitrarily huge horizons do not enlarge the endpoint count.

Actual quotient descent requires w_G(z_i)=0 at every dangling node, at least ceil(J/2) of them. Therefore

    r>=ceil(J/2)-1.                               (5)

ONE or polylogarithmically many such telescoping q-product gauges cannot repair the carrier. This remains true even if the long gauge descriptions, their coefficients and all scalar metadata are granted for free. It is a zero-location/endpoint representation statement, not an algorithmic lower bound. A linear number of blocks could conceivably be shared or aggregated at the desired clock. Additive gauges, other q-step bases, nonregular/finite-part constructions and general multi-stream residue methods are not excluded.

## Outcome and scope

The minimal gauge (1), its coefficient and normalization data, and its descended nilpotent source operator are genuinely cheap. They do not acquire the long residue packet. The actual exclusive residues defeat the proposed ONE-common-coefficient-stream shortcut; equation(5) separately defeats a polylog-block telescoping-gauge shortcut. Neither rules out a scalar residue aggregate, an additive/multi-stream representation, an implicit rational algorithm, or a whole-query method with different observables. No improved query exponent, all-input controller theorem or Lean result is claimed. No repository edits, examples or builds were made.
