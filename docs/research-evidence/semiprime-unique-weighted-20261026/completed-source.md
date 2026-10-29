# Full nonaxis coefficient ellipse and a pair-marked finite source

26 October 2026. Native arithmetic completion and symbolic contraction, scratch only. No repository edits, code, tests, numerical campaign or Lean.

**Executed result:** the ENTIRE public weighted ellipse of nonaxis coefficient pairs, completed to all unit stationary colours, has fewer than 21K rows. Add only the four shortest-axis pairs that satisfy the same ellipse bound; the whole input has fewer than 23K rows and is acquired in soft K. Its canonical squared mark depends on (a,b) alone. The completed marked source contracts exactly into the paid quadratic-stratum GP bank, with all normalizers/endpoint units retained. This remains a K^(5/4) acquisition algorithm; primitive content g=1 retains the old scale. Completion itself and the earlier chirp identity keep prior credit.

## 1. Enumerate a genuine complete ellipse in soft K

For a public size-bin centre B0, define the actual weighted Gauss bound

    a² B0^4+b² N² <= (2/sqrt3)*K*B0²*N.        (1)

No hidden R or S is used to acquire this domain. Put its real semiaxes

    A=sqrt((2/sqrt3)*KN)/B0,
    B=sqrt((2/sqrt3)*K)*B0/sqrtN,
    A*B=(2/sqrt3)*K.

Enumerate ALL integer nonaxis pairs with 0<|a|<=floor A and 0<|b|<=floor B, then filter by (1). There are at most 4AB=O(K) candidates. If either floor is zero there are none; otherwise A+B<=2AB, so even generating the bounding ranges fits O(K). Exact integer-square comparisons implement (1); floating point and an enumerated convex hull are unnecessary.

Retain only pairs with gcd(a,K)=gcd(b,K)=g for which the divided unit conic has solutions modulo K/g, and acquire EVERY unit colour j modulo K satisfying a j²=bN modulo K. All inverses, root lifts and phases are public arithmetic at the completely factored pure K=2*3^e. The canonical phase is the actual stationary ell modulo H, as in the original source; numeric torus roots and physical clock normalization are rebuilt, not guessed.

The row count is explicitly linear. For content g, the number of pairs is at most 4 floor(A/g)floor(B/g)<=4AB/g². Each pair has at most 2g unit colour lifts. Therefore

    J_nonaxis <=8AB*sum_(g|K)1/g
       <8*(2/sqrt3)*K*(3/2)*(3/2)
       =12sqrt3*K <21K.                        (2)

No boundary error or generic divisor-function estimate is needed: both coefficients are nonzero, so the rectangular counting bound has no additive axis term. The 2-adic parity restrictions only REDUCE the colour count. From (1), |ab|<=K/sqrt3; hence every retained g has g²<=K/sqrt3 and is in the same tag-provenance range as the original nonaxis family.

Add each of (K,0),(-K,0),(0,K),(0,-K) ONLY if it satisfies (1), and complete it to its unit colours. This contributes at most 4phi(K)=4K/3 rows. Unfiltered axes at the wrong weighted scale would not inherit the correct-bin exponent margin. The filtered total is

    J_completed<23K.                           (3)

Every original chosen nonaxis vector is retained by (1); every original chosen shortest axis also passes that filter. Thus coverage is preserved without assuming a primitive or nonaxis witness. Every added row satisfies the same weighted bound, stationary phase and signed clock margin. In a correct bin every added hit is an exact integer hit and has the SAME factor tag modulo n=3^ceil(e/2), including the admitted axes. Its character is the original beta-coupled one, not a raw-torus alias.

This is a concrete complete coefficient ellipse, not a claim that a shortest-vector list equals its convex hull. It improves the regularity of the INPUT; it does not evaluate the marked query.

## 2. Canonical mark is acquired from the coefficient pair alone

For nonaxis a=gAcoef,b=gBcoef, put

    u_(a,b)=[N*Bcoef*Acoef^{-1}]_n, n=3^ceil(e/2). (4)

The divided integer coefficients Acoef,Bcoef are distinct notation from the public size-bin centre B0.

The inverse is legal public arithmetic modulo n: exact content makes Acoef a 3-unit, and g²<K implies n divides K/g. The stationary conic gives j²=N*Bcoef/Acoef modulo K/g, hence EVERY colour of the completed pair has the same CANONICAL integer u_(a,b) modulo n. It is also a unit square and lies in (0,n). The mark is invariant under both opposite phases and the lift multiplicities. Reduce modulo n FIRST; embedding the rational expression in B itself would set N to zero and is invalid.

Axes retain their public j² mark and their separate tag proof; formula (4) is not used with a zero coefficient. This axis bank has O(K) rows and stays separately charged.

## 3. Finite marked partition function and exact chirp contraction

For the completed rows v=(a,b,j), let T_v be the actual normalized root. The finite source is

    Z(delta,epsilon)=product_(v,t<h)
         (1+delta-T_v*rho^t+epsilon*u_v),
    M1_completed=Res_delta [partial_epsilon log Z]_(epsilon=0). (5)

This is a rational/logarithmic-derivative identity before specialization, interpreted componentwise at the selected pole. It uses constant clock weights. There is no q-binomial amplitude or hidden clock-cofactor normalization.

For each fixed (a,b), invoke the proved parity-adjusted quadratic lift formula from the frozen [quadratic-lifts §4](../semiprime-fused-readout-20261026/quadratic-lifts.md). Its hypotheses now apply to the COMPLETE colour fibre just acquired. With m=3^{v3(g)} and qhat=pi^{H/m}, complete the square and split into strata

    e=e0+Dv, D=3^{2r+1}, L=m/D, 0<=v<L,

of multiplicity mu=2*3^r, plus the zero-square singleton with its known multiplicity. There are at most two parity-adjusted branches. The effective odd modulus m, not an unjustified g-th root of unity, handles even g.

Recompute the FINAL canonical phase carry directly. Screen the four normalized endpoints -1,0,h-1,h on every completed row, with physical index t-M0. All nonunit endpoints have actual nontrivial short two-coordinate labels and terminate through the licensed mixed-relation decoder. On continuation their constants are genuine units. Removing carry shifts changes (5) only by finite endpoint factors that are formal units in delta,epsilon; their epsilon logarithmic derivative has no negative delta coefficient. This is residue equivalence, not unconditional equality of the original scalar products.

Crucially the mark (4) is CONSTANT on the full pair. Thus the marked source survives the finite concatenation unchanged. Put Aeps=1+delta+epsilon*u_(a,b), Z0=q^M0*y0. Then exactly BEFORE any deformation is specialized,

    product_(v=0)^(L-1) product_(t=0)^(h-1)
      [Aeps-Z0*qhat^{e0+Dv}*q^{-t}]
      =product_(s=-L(h-1))^(L-1)
      [Aeps-Z0*qhat^e0*(qhat^D)^s].             (6)

The bijection is s=v-Lt and qhat^m=q. Raise the right side to its known multiplicity mu. No coefficientwise phase selection, row-dependent epsilon rescaling or auxiliary root of unity is needed. Its contribution to M1 is mu*u_(a,b) times the unweighted simple residue of this ONE GP string.

All starts, multiplicities, marks and endpoint gates are acquired in soft K. The explicit native h bound and g²<=K/sqrt3 keep string lengths below the inherited 16H guard. Their bases are smooth powers of pi and have the same local order as q under roughness. Therefore each string has at most one local hit; multiplicity mu represents the original colour copies, not additional hidden clock roots.

## 4. Execute the completed scalar and count every startup

Batch the strata by content g and valuation r. A bank has common base, common length Lh and at most O(K/g²) starts, by the same ellipse count. Its initialized division-free shared GP query costs

    soft(J_(g,r)+sqrt(J_(g,r)*Lh)).

Acquire ALL string values, classify their norms/coordinates, and either factor or obtain their global 0/1 hit flags. Multiply flags by the KNOWN integer mu*u_(a,b) and sum. This computes the exact additive residue in (5), not merely a zero bit or a generic amplitude. No first clock derivative or Laurent inverse needs to be computed numerically after the flags are supplied.

Summing the geometric content/stratum bounds gives

    soft(K+sqrt(Kh))=soft K^(5/4).              (7)

The filtered original axis bank is separately completed by the inherited shared engine at the same bound; it is not assigned a free trace-alphabet evaluation. The g=1 nonaxis bank already has O(K) starts and horizon h. Formula (6) has L=1 there, so THIS contraction obtains no exponent improvement in that bank. This is the executed cost, not a lower bound for primitive-pair summation.

The correction factors screened above are binomial leaves with actual nonzero labels, never arbitrary additive zeros. Any terminating extractor remains once-only. Every source power or mark is an O(log N)-bit supplied integer; multiplicities are processed as weights, not expanded repeated starts.

## 5. One completed whole-bin M1 still has a paid consumer

No singleton or one-row-per-colour count is needed for the new completed source. At the correct field every hit has u=[R²]_n, and

    M1_completed=c=d*u, 1<=d<J_completed<23K.

Since n<=K/6 for e>=3,

    0<c<M=23K*n<4H,
    padded integer range <=4M<16H<P,Q.

The existing blocked modular-integer recovery therefore costs soft sqrt M<soft(2K). Factor the recovered public integer c<K² times a fixed constant, enumerate its divisor tags, and apply ONE shared restricted-HH palette at modulus n with the already verified parameter choice. The uniform divisor bound supplies S=O(K^{1/6}); fixed constants are absorbed by the same actual HH construction. Wrong-bin attempts may fail boundedly; verified factors alone are accepted. All recovery fits soft K.

This is an interface simplification, not the first license for the old pair completion: its previous (d,du) pair consumer already allowed it. The new point is that this explicit complete ellipse and pair-constant source can be sent to ONE canonical moment, with a direct finite marked contraction and no unknown amplitude normalization.

## 6. Primitive-fibre normalization: useful but not a scalar acquisition

For g=1, let m_j be the public number of admitted completed coefficient pairs in colour j. In a correct bin EVERY such row hits when j=R modulo K; conversely every primitive hit has that full tag. The physical window contains all own-colour rows by (1). Thus that fibre's residue is m_j*u_j or zero. A nonzero m_j is an integer <21K<R and is a certified scalar unit; the source u_j/m_j normalizes this primitive fibre to u_j without clock cofactors.

This is actual arithmetic count normalization. It does not guarantee a primitive witness and does not extend by counting all rows in a nonprimitive fibre: if a=gAcoef,b=gBcoef, n_g=K/g and j=R+n_g*t, then, writing z=(aR-bS)/K, its exact extra-hit condition is

    g divides t*(z+Acoef*t).

That finite condition depends on the hidden virtual difference z. A public fibre size is not its hit count. Therefore the all-content moment in §5 keeps actual multiplicities rather than silently normalizing them away.

The marked complete-ellipse source and GP-stratum contraction are fully initialized and finite, but the primitive bank still requires the long query in (7). No generic selected-residue obstruction, uncharged Brion sum, Schur coefficient or new sixth-rate factorer is claimed.

## 7. Compile every hypothetical-colour incidence in soft K

The hidden-difference condition of §6 has a stronger public form. For any admitted row define its ACTUAL polynomial f_j(X)=aX²+ell_j X+bN. Its supplied stationary phase gives integers f_j(j)=H*d_j and f'_j(j)=K*c_j. Put n_g=K/g. Every unit hypothetical hit colour has the form

    r=j+n_g*t mod K, t mod g,
    g divides t*((a/g)*t+c_j).                  (8)

Parity/unit r restrictions are tested explicitly. Formula (8) follows by substituting r in f_j and dividing its exact K²-scale expansion. Conversely it characterizes f_j(r)=0 modulo H. The valuation argument implies K/g divides r-j whenever f_j(r)=0; then f'_j(r)=f'_j(j)+2a(r-j) is divisible by K. Consequently

    f_j(r)=0 mod H iff f_j(r+K*z)=0 mod H

for every integer z. Thus the actual correct-bin hit condition depends ONLY on R modulo K, not on R modulo H. Once this congruence is true, the weighted bound places its integer physical index in the original interval. This is a complete hypothetical-colour compiler, not an assumption that the factor residue is known.

At the 3-part of g, a/g is a unit. Completing the square in (8) reduces it to a square-root congruence with discriminant c_j². It has at most 2*3^floor(v3(g)/2) roots there; the 2-part and odd-colour filter add only a constant. Thus O(sqrt g) roots per row can be acquired by explicit public ramified lifting. Since the completed number of rows of content g is O(K/g), the TOTAL incidence list costs

    O(K*sum_(g|K)g^{-1/2})=O(K)

up to logarithmic integer arithmetic. For pure 2*3^e the sum is uniformly bounded. Axes are handled directly: the four shortest-axis rows have f_j(r)=0 modulo H exactly at r=j modulo K, so their rootsets are singletons and add O(K) work. No generic tau(K)=polylog assertion occurs.

In particular one can acquire, for EVERY unit r modulo K,

    m_r=#admitted rows with r in their rootset,
    c_r=sum of their canonical squared marks
       =m_r*[r²]_n.

All m_r are positive: the original Gauss row for its own colour r is retained. At the true factor colour, these are exactly the completed hit count and M1. This public table does not evaluate its entry at the unknown R modulo K.

### Incidences are exact equal-phase classes within a fixed pair

Fix (a,b) and complete all its stationary colours. If r is in a row j's rootset, then f_j(r)=0 modulo H and K|f'_j(r). Eliminating a*r² from these two relations gives

    ell_j=-a*r-bN/r mod H,

which is exactly the unique canonical phase ell_r. Hence ell_r=ell_j as centered integers. Conversely equal phases give f_j(r)=f_r(r)=0 modulo H. Therefore the row's hypothetical rootset is precisely its PUBLIC equal-phase class inside that fixed pair. The class multiplicities can be acquired/deduplicated or divided out by their small integer sizes; marks are constant on each class.

That is a genuine finite normalization: repeated equal-phase copies can be replaced by one copy for a coverage/one-tag target, or by their known multiplicity for exact M1. It does not turn the unknown factor selector into a known functional. The public partition-of-unity identity sum_v 1_(r in rootset_v)/m_r=1 has coefficients depending on r. Substituting a row's own colour j for r is invalid unless m_r is proved constant on its entire rootset. No such across-pair constancy is assumed.

### Scoped native overlap geometry

There is also extra structure beyond an arbitrary incidence graph. Suppose two admitted vectors v,w lie in the same hypothetical lattice Lambda_r and share a conductor divisor d>1 in BOTH coordinatecontents. Divide both by d. They lie in the index-K/d lattice with the same stationary slope modulo K/d. Thus if independent, det(v,w) is a nonzero multiple of d*K. But the weighted norm bound (1) gives

    |det(v,w)|<= (2/sqrt3)*K <2K,

by the two-vector area inequality after the B0²,N coordinate scaling. This contradicts d*K>=2K. Therefore such overlapping vectors MUST be parallel. In particular all overlapping 3-divisible vectors are collinear, and likewise overlapping even vectors.

This does not prove every rootset across different primitive directions is nested: coprime-content cases and content one remain. Nor does parallelism by itself identify the hidden colour or acquire a long scalar. It is a concrete native structural input for a subsequent incidence/normalizer contraction. The completed marked GP-bank algorithm and its K^(5/4) cost remain unchanged.

### Final ambiguity isolation

If g has no 3-part, then g=1 or 2. Its root support is a SINGLE full colour modulo K. For g=1 this is immediate. For g=2, r-j is divisible by K/2=3^e; as r,j are odd, it is also even, hence divisible by K. The shortest-axis root supports are singletons too.

Therefore every genuinely ambiguous nonaxis rootset has 3 dividing BOTH coefficient coordinates. If two such rootsets share even one unit hypothetical colour, their vectors share the conductor divisor 3 and the preceding area argument makes them parallel. Consequently ambiguous rows from DIFFERENT rational coefficient directions have DISJOINT hypothetical-colour supports. All ambiguity affecting a given colour is confined to one rational direction; full-colour singleton rows can coexist there without contradicting this statement.

This is the completed native incidence/collinearity theorem for this turn. It does not say phase classes within one direction are all nested, normalize their hit count for free, identify which direction contains the actual factor colour, or solve the content-one query. The compiled incidence/source data and their paid GP execution are ready for further work; no additional representation or unproved contraction is introduced here.
