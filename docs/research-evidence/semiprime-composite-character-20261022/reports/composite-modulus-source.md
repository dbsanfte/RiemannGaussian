# Composite odd row modulus: source and small-q-order audit

22 October 2026. Classical source audit; no repository changes or new Lean theorem. The intended supply is a public prime ell=3 modulo 4, m=(ell-1)/2 odd, m>=ceil(N^(1/6)), m=Theta(N^(1/6)). This removes the need to find ell=1 modulo a separately prescribed PRIME m. It does not solve long-H acquisition. Prime supply in the required constant interval is a separate analytic/algorithmic statement owned by root.

## Canonical source works on unit tags

For ANY odd m>=3 coprime to N, enumerate j in (Z/m)^*. Set a to the representative of N*j^-2 in [1,m), D0=(N-a*j²)/m, b=centered_m(-j^-1 D0), and c=(N+jmb-j²a)/m². All divisions are exact. Both a and j are units modulo m; their inverses and centered lifts cost soft O(m) total, even using independent Euclid calls. Factor m by trial division through sqrt(m) if a prime-power decomposition is needed. No hidden factor is an input.

Put ellrow=mb-2aj, Delta=b²-4ac, E=N+a+ellrow. The exact identities

    m²c-jmb+j²a=N,
    ellrow²-4aN=m²Delta

do not use primality of m. At the true hidden factor tag j=P modulo m, j is a unit because gcd(P,m)=1. Write P=j+mh. Then

    P*(aP+Q+ellrow)=m²*(a h²+b h+c),
    I=(aP+Q+ellrow)/m² is an integer,
    E-m² I=(P-1)(Q-a).

Thus the original Fermat collision and its scalar gamma source are retained. The true mask is exactly

    I modulo m in kappa+(4aj)^-1 Squares(Z/m),
    kappa=-Delta/(4aj) modulo m.

Completing the square proves both directions over Z/m because 2a and j are units. Singular/nonunit square values must remain in Squares(Z/m); a prime-modulus Legendre bit is not an adequate replacement. Root's composite palette catalog is needed for that part.

Centered bounds are unchanged: |b|<m/2, 1<=a,j<m, so |ellrow|<3m² and the inherited offset bounds -3m²<=a+ellrow<=m² hold by the same integer inequalities. NO BALANCE HYPOTHESIS is needed in the retained branch. Let P<=Q, P,Q>16m² and N<=m^6. Then P<=m³ and Q=N/P<m⁴/16. Therefore

    I>Q/m²-3>13,
    I<(mP+Q)/m²+3<(17/16)m²+3<4m² (m>=3).

Thus the standard nonnegative padded native interval L=4m² covers the true index for ALL retained semiprimes, not merely a balanced subfamily. All target exponents have O(log N) bits and are acquired in soft O(m).

On the retained N>256m⁴ branch and L<=4m², E-m²i>N-3m²-4m⁴>0 for every original native leaf. Hence saturated leaves yield nonzero O(log N)-bit annihilators. This is stronger than depending on a prime-modulus factor-sum theorem: the reviewed QRH decoder consumes the annihilator directly and has no row-primality input.

Antipodal j->m-j is fixed-point-free on the unit tags because m is odd. Exact integer a symmetry, bounded centered s in {0,1,2}, and all unit Gauss aggregate pairing identities survive. For character order m composite, exceptional NONPRIMITIVE characters must use their own projectors in the packed construction. However the inverse-character product for every nontrivial character remains ell here: chi(-1)=1 since m odd, so D=E0+(1-E0)ell remains valid. The already paid all-character packed primitive was designed for arbitrary k|ell-1, not just prime k.

## Actual source references: what uses primality and what does not

`RiemannGaussian/SemiprimeGlobalPhaseCancellation.lean` has low-level identities with hypotheses m>0 and j.Coprime m (for example lines 59 and 79). Its theorem at lines 178--192 explicitly uses m.Prime to turn arbitrary short positive DENOMINATORS t<m into units. That stronger all-denominator cancellation is not needed for the literal t=1 canonical rows above; for composite m it cannot be imported unchanged for nonunit t. Prime-field low-fiber/Legendre and distinct-center arguments likewise require replacement rather than automatic transfer.

`docs/research-evidence/semiprime-canonical-query-20261015/reports/canonical-coverage-and-recovery.md` states prime m, but its displayed t=1 quotient identity, integer bounds, proper-gcd localization and nonzero annihilator recovery use only the unit true tag and the stated order/size contracts. This is a classical extension audit, not a claim that existing prime-m Lean declarations have been generalized.

`RiemannGaussian/SemiprimeLocalOrderRouting.lean` formulates global order through the hidden-prime CRT and local orders, not primality of the auxiliary row modulus. `SemiprimeRoughProjection.lean` similarly uses its threshold B and hidden prime-order hypotheses; it does not infer that the row modulus is prime. These files do not by themselves certify a new end-to-end implementation for composite m: their actual preparation contract and thresholds still have to be instantiated.

The executable `scripts/probe_semiprime_sparse_residue_gauss.py` already accepts arbitrary public modulus H in `weighted_gauss` (line 87) and `factor_sparse_catalog` (line 350), requiring gcd(H,N)=1 and unit catalog residues, not prime H. The latter still INPUTS prepared alpha and explicitly marks `order_promises_checked=False`. It must not be cited as constructing the preparation.

## Loss of q-order is repairable by an actually paid screen

Raising gamma to m² can reduce its local orders when m is composite (also when prime). Do not claim unchanged q order without gcd(m,orders)=1. Instead run the existing `first_power_collision(N,q,B)` with B=16m² (or any required fixed constant multiple), q=gamma^(m²). Its source is lines 139--193 of the same script. It builds O(sqrt B) baby powers and a monic product tree, evaluates O(sqrt B) giant points, and localizes the FIRST nonunit leaf. Exact tail truncation ensures every tested exponent is in [1,B]. Cost is soft O(sqrt B)=soft O(m) with fast monic polynomial arithmetic.

A proper leaf gcd factors N. A saturated leaf q^e=1 gives the explicit nonzero gamma annihilator m²e (O(log N) bits), which the inherited reviewed decoder consumes within soft O(m) for the native scale. If there is no hit, both local orders of q exceed B, regardless of which factors of gamma's orders were lost. The script's `factor_sparse_catalog` lines 380 onward already applies this pattern with its required cap and calls `factor_annihilator` on H² times the returned exponent. The script's decoder is an inherited conditional interface, not a newly proved preparation algorithm here.

This q screen uses gamma's existing odd/coprime local-order decoder contract, not m primality; oddness and local-order coprimality are retained under powering. If a later theorem specifically needs q's orders coprime to m, it needs an additional argument; the large-order screen alone supplies only the lower bound. The current monic query/localization interfaces need the lower bound and known unit source, not that extra coprimality.

## Audit outcome

No essential primality requirement remains in the classical t=1 canonical coverage, exact mask, bounded exponents, original scalar recovery, antipodal weighted aggregate, or paid small-q-order screen. Prime-field mask compression, some denominator-rich/formal theorems and prior density arguments do NOT transfer automatically. The row/order/controller scripts and algebra cited above support a conditional composite-m source once the same prepared-gamma contract is supplied; they are not a new full paid-preparation proof. Root's ell-first supply construction can therefore remove the prescribed-prime-progression auxiliary gap at this source level, while palette acquisition and the unresolved long-H query remain separately charged.

## Final all-input public-gcd amendment

Before any divisions, factor the PUBLIC m (trial division through sqrt(m) is within budget) and compute gcd(N,p) separately for every distinct public prime p|m, and gcd(N,ell). Each tested number is prime. For composite semiprime N such a gcd is either 1 or a proper factor; it can never be N. Hence this screen supplies either a factor or gcd(N,ell*m)=1 without a saturated-product exception. It is preferable to testing only the combined product, whose gcd may be N even when each constituent prime would immediately factor. This amendment also supersedes the earlier balanced-only index discussion with the all-retained-input inequalities above. No new preparation or long-query theorem is asserted.
