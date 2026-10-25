# Independent arithmetic review: all-pairs lifted-norm consumer

Reviewed 22 October 2026: `/tmp/semiprime-common-product-20261022/lifted_relations/report.md`. Arithmetic verdict: PASS, under its explicit odd distinct-prime, coprime auxiliary and native-size promises. No implementation, tests, factor-success campaign, or repository changes were made. This review checks the arithmetic and the coprime-base interface; it does not reprove Bernstein's preprocessing algorithm or certify an implementation's runtime.

## 1. Lift, scale, and guards

From ell=mb-2aj and m²c-jmb+j²a=N,

    ell²-4aN=m²(b²-4ac)=m²Delta.

For v=ell-m²kappa,

    v²-4aN=m²(Delta-2ell*kappa+m²kappa²).

Since ell=-2aj modm and Delta+4aj*kappa=0 modm, its bracket is divisible by m. Hence z=(v²-4aN)/m³ is an exact integer and v²-m³z=4aN exactly. The native bounds a<m, |ell|<3m², 0<=kappa<m imply |v|<=m³+3m² and |z|=O(m⁴) when N=O(m⁶). Also v=-2aj modm is nonzero, so v is not the integer zero.

The proposed sufficient large-regime bound is valid. For m>=3, |v|<=2m³. If N>256m⁴ then |v|<N and

    |z| <=4m³+4N/m²
         <N*(1/(64m)+4/m²)<N.

Here the last parenthesis is at most 1/192+4/9<1. The prepared local-order promise P,Q>16m² implies N>256m⁴. Since N is squarefree, z=0 would imply N|v² and hence N|v, contradicting 0<|v|<N. Thus gcd(v,N), and likewise any nonunit gcd(z,N), is proper in this regime. More strongly, because m is a unit modulo N,

    gcd(v,N)=gcd(z,N)

for squarefree N. After v's unit screen, z is automatically a unit; the additional |z|<N bound is useful but not needed for that inference. Outside the proved range, use explicit proper/saturated/zero guards rather than silently accepting a saturated gcd as a factor.

## 2. Coprime-base signature equivalence is exact

Require base elements b>1, pairwise coprime, with exact nonnegative exponent representations |z_j|=product b^e_jb. Mark whether each b is an integer square, not whether it is squarefree. A nonsquare b has at least one odd prime valuation; pairwise coprimality makes that prime unique to this base element. Therefore product z_i z_j is a positive integer square if and only if signs agree and all nonsquare-base exponent parities agree. Square base elements never affect this condition. Units |z|=1 have an empty base signature and cause no exception.

For a class let D be the product of its odd-parity nonsquare base elements. Then D divides every |z_j| in the class, |z_j|/D is an exact integer square, and

    z_j=sigma*D*s_j², s_j>0.

D need not be squarefree; that does not change the argument. D divides each class member, so it and every s_j have O(log N) bits. On the no-factor unit branch D,s_j,m are all units modulo N, and gcd guards justify every inverse.

## 3. Normalized roots exactly detect all actionable pairs

Put M=m³, r_j=v_j/s_j modN. Every class member has

    r_j²=M*sigma*D modN,

with a UNIT right side. For any two members i,j, the two-row square relation has

    X=v_i*v_j, Y=M*D*s_i*s_j,
    X²=Y² modN.

The exact comparison is

    X∓Y=s_i*s_j*r_j*(r_i∓sigma*r_j) modN.

All displayed multiplicative weights are units. Thus the pair's gcd(X-Y,N), gcd(X+Y,N) are, up to swapping signs when sigma=-1, exactly the gcds from r_i-r_j and r_i+r_j. Normalization neither loses nor invents a proper factor for this pair mechanism.

Fix one representative r_0. Over each odd hidden field there are exactly two roots of the same nonzero square, so r_j/r_0 is +1 or -1 locally. If neither representative gcd is proper, their signs agree globally: r_j=r_0 modN or r_j=-r_0 modN. If this holds for every j, every pair is also globally equal up to sign and all its factor attempts are trivial. Conversely an actionable pair forces at least one actionable representative comparison. This proves the report's iff statement without assuming random sign patterns or testing m² pairs.

A saturated representative gcd is handled explicitly as global equality or global opposition, not as a factor. Both signs cannot simultaneously saturate since 2r_0 is a unit. Classes with one member simply have no pair to test. The result certifies absence of useful TWO-row square-product relations only, not higher dependencies or other norm consumers.

## 4. Cost and existence scope

Given the cited coprime-base algorithm's acquired base and exponent representations, total input bit size is O(m log N). Sparse signature construction, exact square tests/divisions/roots, deterministic sorting, one normalization per row and O(m) representative gcd pairs all fit soft O(m) native work. No prime factorization, quadratic all-pairs enumeration, or hidden local root label is an input. The report correctly distinguishes a cited preprocessing theorem from an unimplemented backend.

Finally, retaining both exact Hensel signs does not force an actionable pair. If representatives are v and -v, they have identical z and identical positive s, so their normalized roots are globally opposite. Both gcd attempts are trivial. Arbitrary shifted native representatives may differ and should be screened, but no existence conclusion follows from their number or from m-adic lifting alone. The missing universal-actionable-pair theorem remains missing.
