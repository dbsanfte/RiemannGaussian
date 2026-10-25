# Character nontriviality audit of the lifted relations

22 October2026. There is a paid strengthening of the TWO-row screen: test every SINGLETON square relation m z_j. Under the native exact integer relation and size bounds, EVERY such positive singleton gives proper factors unconditionally; no Jacobi mismatch is needed. A single public sentinel incorporates all singleton tests into the existing pair controller. Existence of a singleton or actionable native pair is not forced by the current identities. Two-row m z relations are exactly the previously acquired z-pair relations. No new universal existence theorem follows.

Retain the checked no-factor branch: N=P Q odd squarefree, gcd(m,N)=1, every v_j and z_j unit modulo N, and v_j²=m³ z_j. All descriptors have O(log N) bits and there are O(m) rows. The existing coprime-base decomposition and sparse parity signatures are acquired; earlier reviews are unchanged.

## An actual additional singleton consumer

For each row test whether z_j is positive and z_j/m is an exact integer square (first require integer divisibility by m). If so acquire its positive square root s_j. This is equivalent to m z_j being a positive integer square: since m is prime, its m-adic valuation in z_j must be odd, and all other valuations even. The exact representation is

    z_j=m s_j²,
    v_j²=(m² s_j)² mod N.

Set y_j=m² s_j mod N. Check gcd(s_j,N) before use; it is1 by the unit z contract, or any proper result already factors. Compute gcd(v_j−y_j,N) and gcd(v_j+y_j,N). Return a proper result; saturated results are trivial signs and are not called an annihilator. This adds O(m) integer divisions, exact square tests and modular gcds, hence soft O(m) native bit work. It needs no refinement of the existing base at all. Equivalently one may add the public m to the coprime-base input and select the positive square class of m, but that is unnecessary for singleton acquisition.

**Native size strengthening: every positive singleton succeeds.** Use the exact integer identity, not merely its reduction modulo N. For a positive native multiplier a_j>0 and z_j=m s_j² with s_j>0, put w=m²s_j. Then

    (v_j−w)(v_j+w)=v_j²−w²=4a_j N>0.

Therefore 0<w<|v_j|. Both absolute factors are strictly between0 and2|v_j|. Under the sharpened native bound |v_j|<=2m³ and N>256m⁴, one has2|v_j|<=4m³<N. Neither factor is zero or divisible by N. Since squarefree N divides their product, at least one hidden prime divides each factor: if a factor were coprime to N, both primes would have to divide the other, contradicting its size<N. Thus BOTH gcd(v_j−w,N) and gcd(v_j+w,N) are proper, without any character assumption. In particular no saturated root comparison is possible in this native positive-singleton case.

The conclusion also follows from the weaker bound |v_j|<=m³+3m² used in the preceding independent audit: 2m³+6m²<N follows from N>256m⁴ for m>=1. Thus the sharpened constant2 is not needed for the proof. Positivity a_j>0 IS needed for w<|v_j|; the modular-root comparison alone is still valid for other input contracts but does not carry this size guarantee.

**One public sentinel unifies singleton and pair acquisition.** Append the record

    v_*=m², z_*=m, a_*=0.

It satisfies the exact common-root equation v_*²=M z_* and both entries are units modulo N. It is nonzero and has O(log N) bits. A native row and the sentinel have positive integer square-product exactly when m z_j is a square, equivalently z_j=m s_j². In that signature class the sentinel and row normalization compare roots of the same unit M sigma D. Their mixed-sign comparison is, up to units, the already proved v_j±m²s_j test. Consequently the complete pair controller applied to the augmented list acquires ALL native singleton cases together with ALL native two-row cases in the same soft O(m) budget. Its representative completeness theorem remains valid even if the sentinel is not selected as representative.

The sentinel bypasses only the *native-row validation* step that used m not dividing v: it is not asserted to be a canonical native row or to have positive a. Instead its common-root equation and unit properties are explicitly checked as above. The generic pair theorem needs exactly those properties, so a_*=0 is harmless. Duplicate z=m rows and a possible globally signed sentinel copy are handled by the existing sparse decomposition/representative algorithm; for a positive native singleton the exact size proof rules out a trivial sentinel comparison.

This is a genuine strengthened factor guarantee GIVEN an acquired positive singleton. It does not prove that one exists. In regimes where all native z_j are negative the singleton branch is empty; the two-row screen remains available.

## Acquired Jacobi certificate, with the exact sign condition

Write J(a)=Jacobi(a,N), and eta=J(−1). All compared arguments here are units. In a singleton let t=v_j/y_j mod N. Then t²=1. If eta=1 and

    J(v_j) != J(y_j)=J(s_j),

then t cannot be either global +1 or global −1: both have Jacobi value1. Therefore t has opposite local signs and both scalar gcd comparisons above are proper. This certificate uses only O(log N)-bit public inputs and classical Jacobi evaluation. It is stronger than merely restating an unknown local-sign condition: it is an efficiently acquired, directly checkable sufficient condition. It does not improve the cost of the gcd consumer, which already detects all useful singleton roots irrespective of Jacobi.

The arithmetic meaning of eta=1 has two cases. If P,Q are both3 mod4, the two nontrivial roots of1 have Jacobi value−1, so the certificate is equivalent to nontriviality. If both are1 mod4, ALL four roots have Jacobi value1 and the mismatch never occurs. The algorithm knows eta but does not know which case holds. Thus a missing mismatch cannot certify triviality. If eta=−1, the global signs +1 and−1 already have different Jacobi values; a mismatch alone is not sufficient and must not be advertised as a factor certificate.

Exactly the same certificate applies to a normalized pair-class comparison r_i,r_j from the prior consumer: if eta=1 and J(r_i)≠J(r_j), a proper factor is guaranteed. These J values are acquired in O(m) work, but their mismatch gives a SUBCASE of the already complete pair gcd screen. It is not a new independent existence guarantee. When eta=−1, choosing a canonical global sign from Jacobi would mix the two possible local-sign patterns and does not justify a stronger test.

## Why multiplying every row by the common m does not add pair dependencies

For any two rows,

    (m z_i)(m z_j)=m² z_i z_j.

This is a positive integer square exactly when z_i z_j is a positive integer square. With z_i=sigma D s_i² and z_j=sigma D s_j² in one existing signature class, the standard roots built from w_j=v_j/m satisfy

    (w_i w_j)²=(m D s_i s_j)² mod N.

Multiplying both compared roots by the unit m² gives the old v_i v_j versus m³ D s_i s_j construction. Their scalar gcds with N are unchanged. Thus ALL actionable two-row m z dependencies have already been acquired by the z-pair consumer, including unequal a and unequal signs of v. Refactoring m z values cannot introduce a missed pair.

For odd-size dependencies the common m can matter, as the singleton test shows. Higher odd subsets need their own selected dependency construction and nontriviality proof; the available sparse exponent decomposition is not a free nearlinear general binary nullspace algorithm.

## Public colours of individual bases: exact constraints, no extra witness proved

Applying either local Legendre character to v_j²=m³ z_j gives

    Legendre(z_j,P)=Legendre(m,P),
    Legendre(z_j,Q)=Legendre(m,Q).

Consequently every public row satisfies J(z_j)=J(m). This is an identity, not a colour separation among rows. Writing |z_j| in the coprime base translates it to sparse linear constraints on the UNKNOWN local base characters. Public Jacobi values reveal only the products of those two local characters. They do not select either local vector. A mismatch J(z_j)≠J(m) would contradict the checked input/unit identities, rather than be a legitimate new dependency witness.

The row parameter a_j enters the exact integer equality v_j²−m³ z_j=4a_j N. Taking a multiplicative character modulo either factor removes the right side entirely. No character relation containing a_j survives from this equality without a further nonvanishing/nonlinear argument. Thus no additional public colour of a_j is silently substituted for a local root sign.

Shared-base incidence components by themselves do not supply a square dependency: a component consisting of a single nonsquare-class row, or a chain of independent parity signatures, has none. Even a parity cycle producing a square relation need not have mixed local root signs. The coprime-base output genuinely acquires the incidence data, but a graph interpretation does not establish rank deficiency or nontriviality for the native family. No stronger nearlinear incidence-based factor guarantee was proved here.

## Paid conclusion and remaining theorem

The resulting deterministic controller is: run the retained unit screens, append the public sentinel, and run the already paid complete pair consumer. Alternatively the O(m) exact singleton tests may be run explicitly before the pair consumer. Every positive native singleton is guaranteed useful by the size proof above. Jacobi mismatches with eta=1 remain valid optional nontriviality certificates for more general comparisons, but add no requirement to the native singleton theorem; pair gcd comparisons remain necessary for completeness when such certificates are absent. Total additional work remains soft O(m), including every square root, Jacobi value, division and gcd.

A universal factoring consequence would still require proving that the native supplied family always contains an actionable singleton, actionable pair, or another constructible useful dependency. No such existence theorem follows from the cubic lift, shared-base incidence, or the public Jacobi identities above. This is an acquired augmented-list consumer with guaranteed recovery for every supplied positive native singleton, plus a scoped character certificate; it is not a claim of improved all-input factoring rate.

All arguments are elementary exact integer and finite-field arithmetic, using the previously reviewed coprime-base acquisition only for the prior pair consumer. No new literature theorem, hidden-field oracle, numerical example or backend was used. Only this new audit file was written; earlier reviews and source reports remain intact.
