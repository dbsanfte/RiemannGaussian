# Independent exact-byte audit of period recovery

2026-10-24. **PASS** for the final reviewed report. Scratch only; no source or repository edits.

Reviewed source: `/tmp/semiprime-gauss-period-20261024/period-recovery.md`

SHA256: `bb8fd816c969e00061192201e88c97d0d8e0ed0993dced370f1e7ea670408e3d`

The author froze these bytes after adding guarded projection/q screening and correcting a norm-pronoun ambiguity. The review independently checked the cited separator and norm-one collision declarations in `RiemannGaussian/SemiprimeOrderSeparation.lean`; no Lean build or new backend theorem is asserted. The imported period constructor is reviewed separately. This audit uses the inherited hard branch: distinct odd P<Q, m>=17, N<=m^6, P,Q>16m^2 and original prepared beta.

## Separator and all guard branches

For A=P-epsP, C=Q-epsQ, s=epsP epsQ and E=N-s, the congruence E=epsP*C modulo A is correct, and gives gcd(A,E)=gcd(A,C). The analogous identity holds at C. Prime-adic valuations then show that orders after exponent E divide A/g and C/g, respectively, where g=gcd(A,C); these quotients are coprime. Thus projected local orders are coprime without supplying either private colour.

Norm-one collision equivalence makes the first gcd guard exact: proper Norm(W1-1) gcd factors; saturated gcd means W1 is globally one; unit gcd means both projected local orders exceed one. In the unit branch, raising to 2^v kills all 2-parts. Coprimality prevents both nontrivial local orders being 2-primary, so both cannot die. A proper next gcd factors; saturation is excluded. The remaining W orders are odd, nontrivial and coprime.

Raising W to H=m^2 cannot kill both sides either, because two nontrivial coprime orders cannot both divide a prime power. The q guard is therefore valid and adds no unresolved branch. No large original-beta order is transferred to W or q; the actual q screen supplies that certificate.

## Complete short-order screen and cost

The baby/giant difference leaves q^(bj)-q^i cover consecutive positive exponents bj-i. They are differences of norm-one elements, so vanishing scalar norm in a local field is exactly local equality, including split algebras. Polynomial/MPE construction uses monic divisors and no cross-difference inverses.

If either q order is <=T, their coprimality and nontriviality make the minimum order a one-sided annihilator. This occurs in the FIRST nonunit exponent block. Thus that block has an actual proper-factor leaf even if other leaves saturate. Complete descent through that block is paid: summed polynomial degrees per traversed tree level are O(b), and O(b) scalar gcds suffice. The report correctly continues past saturated leaves instead of treating them as factors. Soft sqrt(T)=soft m screening is therefore justified. Unit blocks certify both q orders>T and hence both W orders>T.

## Split norm-one equivalence

For norm-one x,y, z=x*bar(y) has norm one and Norm(x-y)=2-Tr(z). Zero difference norm gives Re(z)=1; then D*Im(z)^2=0 in the BASE field. Since D!=0 this forces Im(z)=0, so z=1 and x=y. No domain hypothesis on the split quadratic algebra is used. The report correctly confines this inference to norm-one inputs and applies norm multiplicativity to products.

## Native coverage, acquired query and signed saturated decoder

The native exponent differences are exactly

    E_j-HI=(P-1)(Q-a) for e=+1,
    E_j-HI=-(P+1)(Q+a) for e=-1.

At own j, e=epsP, so the local norm-one group cardinality divides the difference. All public projections preserve the resulting hit. The row values are actual rank-two powers, acquired in soft m total; the stated common-interval product/query constructor retains soft(J+sqrt(Jh)). Repeated nodes and split zero divisors do not invalidate monic MPE or norm-based localization. No faster query is asserted.

For a saturated leaf, the two local collision equivalences give W^K=1. Coprime W orders therefore have product dividing both K and lambda=(P-epsP)(Q-epsQ). Direct expansion verifies

    K-e*lambda=C0+t*(Q+sP),
    C0=ell+e*a-Hi-e*s, t=e*epsP.

The public quantity C0 has the correct minus sign on e*s. From |ell|<2.5m^2, a<m, i<4m^2+4, one obtains |C0|<5m^4 for m>=17. Also P+Q<m^4/8 follows from P<=m^3 and Q<m^4/16 at m>=17. Thus the signed difference is strictly smaller than 6m^4, whereas rP*rQ>256m^4. Divisibility forces it to vanish.

Consequently |C0| is the sum for s=+1 and the difference for s=-1. The two integer-square-root formulas, parity checks and factor verification recover P,Q. This is an independently proved torus decoder, not an illicit reuse of the beta-specific decoder. It applies to any acquired saturated bounded leaf, not just the private own row. Its cost is polylogarithmic.

## Raw palette and exact unresolved scope

The degree-h period polynomial's next coefficient is (-1+tau)/2. Hence its tau coefficient B has exact degree h-1 and leading 1/2, a unit modulo both primes. The m-2=2h-1 acquired beta^t nodes are locally distinct. The two local B-zero sets have union of size <=2h-2, so the complete acquired gcd list gives a proper factor or a node with B a scalar unit.

At that node Norm(U) is the stated beta^t specialization, while Norm(U-bar U)=-4D B^2. The final bytes correctly distinguish these two norms. It follows that W0-1 is a unit and raw W0 is nonidentity in both local quadratic algebras. This raw supplier and its soft-m MPE cost are genuinely established.

The report does NOT extend that degree argument through exponent N-s. It allows every selected/palette point to lie in separator kernels. The preliminary whole-group kernel screen is correct: A|E and C|E force A=C, then P<Q forces Q=P+2 with epsP=-1,epsQ=+1, and N+1=(P+1)^2. Removing this twin case does not exclude particular point kernels, as the report explicitly says.

Therefore W1=1 remains the sole unresolved preparation outcome of the displayed guarded controller. No claim that raw nonidentity, the original beta order, or the new palette guarantees separator survival is present. The all-input long-order supply and sixth-rate query remain open.

## Verdict

No correction required for these exact bytes. Positive constructions, guard branches, split collision logic, complete proper-witness screen, signed global decoder and raw palette are paid and correctly scoped. The surviving query retains the old soft m^1.5 bound; no all-input rate gain is claimed.
