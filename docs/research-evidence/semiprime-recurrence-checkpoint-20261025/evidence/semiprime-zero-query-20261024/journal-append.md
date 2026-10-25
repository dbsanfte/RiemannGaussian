
## Matched-label recurrence query and canonical quadratic phases, 2026-10-24

The user asked for a better fast recurrence algorithm. This pass isolates
the exact implicit input such an algorithm must use, constructs a correct
matched-label selector, and gives the current quadratic-colour rows a
canonical phase description. It does not improve the complete acquisition
bound. In this route J=Theta(k), L=Theta(k^2), k=Theta(N^(1/6)); the retained
query costs soft(J+sqrt(JL)), while the intended new bound is
soft(J+sqrt L). The latter remains a research target.

### A selector that preserves the actual diagonal

Let P_b(Y)=prod_(i<b)(1-q^i Y), with actual unit-separated native arguments
y_j=V_j^(-1). Reshape its coefficients as C[rho,r]=c_(D*rho+r), and let
G(X,Y)=sum C[rho,r] X^rho Y^r, with both dimensions of order sqrt b.
The earlier acquired C and C^t actions cost soft sqrt b. The native value
is G(y_j^D,y_j); both vectors change with j.

Acquire F(T)=prod_j(T-y_j) and the rank-J algebra E=B[T]/F over the actual
quadratic base ring B. Target separation makes the derivative inverses
units, and interpolation acquires R_F=(F')^(-1) modF in soft J. The circuit

    Pi(T,S) = ((F(T)-F(S))/(T-S))*R_F(S) mod(F(T),F(S))

is a genuine diagonal idempotent: its values at (y_i,y_j) are delta_ij.
The divided difference is a polynomial computed by Horner operations;
T-S is never inverted. Its shared circuit is small, although the ambient
tensor algebra has rank J^2. The diagonal ideal itself has rank J.

Writing theta=T modF, a single bordered matrix over E,

    [[I, C v(theta)], [u(theta)^t, 0]],

has determinant -P_b(theta). Its E/B norm is (-1)^J prod_j P_b(y_j),
exactly the desired matched-label product. Orthogonal idempotents kill
cross-label terms, and the identity holds through zeros without inverting
any desired value. This differs from the earlier uniformly-unit ordinary
full determinant, which lost the diagonal test.

There is a complete implementation: acquire the powers in u(theta) and
v(theta), perform the fast C action over E, form the dot product, and
evaluate the resulting degree<J representative at the known y_j to take
its norm. Each expanded E operation costs soft J base work. The complete
bound is therefore soft(J sqrt b), not soft(J+sqrt b). With b=L it is
soft k^2 and is slower than the retained baby/giant query.

A constant-precision identity also selects the diagonal: multiply every
off-diagonal entry by epsilon with epsilon^2=0. Every nonidentity
permutation then vanishes. But constructing this perturbed matrix needs
its constant term diag(G(y_i^D,y_j)), precisely the unpaid native values.
The identity is correct; low auxiliary precision does not supply that
input. A squared-label constant-term mask has the same issue.

### The precise new recurrence operation

The useful algorithm-design target is now

    h(T)=G(T^D modF(T),T) modF(T)=P_b(T) modF(T),

or only its original zero-safe norm. F and its roots are actual acquired
data. G is supplied by its q-binomial generators and fast matrix actions,
not by a dense table of b coefficients. A conventional theorem requiring
that entire table has already exceeded the desired input clock.
Acquiring h suffices to recover all native values by soft-J multipoint
evaluation. A scalar-only alternative must additionally provide charged
restrictions or an original collision witness; a known nonunit scalar
without a localization procedure is not the full factoring interface.

For a coefficient functional ell_s on B[T]/F, the transposed target is

    [T^s]h = sum_(rho,r) C[rho,r]*ell_s(T^(D*rho+r) modF).

The second matrix comes from an acquired order-J recurrence. Its known-root
decomposition has J paired terms with both geometric vectors moving.
Fast action on one supplied vector does not yet contract those terms
simultaneously. This is a specific implicit modular-evaluation or middle-
product problem, not a lower bound against new recurrence algorithms.

The cheaper completed implementation remains actual baby/giant evaluation
with a degree-a block polynomial and J*b/a labelled arguments. Optimizing
a gives soft(J+sqrt(Jb)); row, block and tail labels remain attached for
the original norm-leaf consumer. An auxiliary selector or pivot is never
silently treated as a covered collision witness.

### Direct gcd arithmetic and bounded orbit normalization

The actual quadratic algebra also permits a simple guarded gcd interface.
For an acquired coefficient a=x+y*tau, first test gcd(Norm(a),N). A proper
gcd factors, while gcd one supplies its inverse. If the norm gcd is N,
a vanishes on the nonsplit field side, hence both x and y vanish there.
Consequently gcd(x,y,N) factors unless a is globally zero. Thus every
acquired coefficient is factor, unit or global zero. This supports guarded
Euclidean arithmetic on acquired polynomials; it does not acquire an
implicit long remainder.

Once a monic gcd of the native root polynomial and the long product has
been acquired, evaluate it at the native roots. A nonunit value factors
by the same primitive, or a global-zero value identifies an original row
with a nonsplit collision. Localize that row's original length-L product
in soft sqrt L and use the original leaf consumer. A globally zero gcd
value does not assert that both prime sides hit the same geometric index.

For the ORIGINAL rows, group delta_j by r=delta_j modH, H=k^2, and set
t_j=(delta_j-r)/H and A_j=V_j*q^(-t_j). All anchors in one group have the
same norm beta^(2(N+r)). There are at most five possible deltas and at
most sixteen tags per delta, so all within-group comparisons cost soft J.
The coefficient primitive identifies actual global equalities or factors.
After target deduplication an anchor has at most five original shifts.
Its collision support is exactly the union of intervals
[-t_j,L-1-t_j]. For L>4 this is one interval of length at most L+4;
short restrictions retain the actual interval union without filling holes.
A located index n maps back to a stored row and i=n+t_j. This is paid
normalization with a recovery map, but it retains at least J/5 anchors.
These constants describe the original family, not the amended family below.

The inspected primary q-difference theorem exposes the precise missing
oracle. [Abramov's 1999 paper](https://fpsac-archive.github.io/FPSAC99/ARTICLES/abramov.pdf)
assumes a characteristic-zero, non-root-of-unity q-suitable field: an
algorithm must already find all n>=0 with p(q^n)=0. Its dispersion step
therefore cannot provide our bounded finite-ring orbit query for free.
The additive stabilization theorem of Chen--Paule--Saad and Kaltofen's
straight-line polynomial gcd theorem also supply no stated deterministic
soft(J+sqrt L) bound for this input. Their exact premises and cached
primary-source fingerprints are retained in direct-gcd.md.

### Canonical quadratic phases of the actual row family

The earlier journal already proves the general Hensel discriminant identity
(2026-10-08) and a different balanced a=1 parity normalization (2026-10-23).
The present addition is an initialized parity repair for the CURRENT
quadratic-colour family, with its own coverage and recovery bounds.

For each unit tag j modulo the even public k, retain the original
a=[N*j^(-2)]_k and centered b. Put epsilon=b mod2 and acquire

    a'=a+epsilon*k,
    b'=center_k(b+epsilon*j), ell'=k*b'-2a'*j.

Then b' is even. More precisely, b'=b+epsilon*j-k*zeta with zeta in{0,1},
so ell'=ell-epsilon*k*j-H*zeta. Solve
a'*t=-b'/2 mod(k/2), choose 0<=t<k/2, and set
Jtilde=j+k*t and u=Jtilde^(-1) modH. These public modular inversions and
all actual row powers cost soft k for the full family. Expansion gives

    a'*Jtilde^2=N modH, ell'=-2a'*Jtilde modH,
    a'=[N*u^2]_H<2k,
    E'=N+a'+ell'=N*(u-1)^2 modH,
    T'=ell'-N-a'=-N*(u+1)^2 modH  (chi-minus).

The quadratic colour is chi_D(j)=chi_D(u). No injectivity of powering by
the possibly large u or Jtilde in hidden groups is assumed.

At the true smaller-prime tag j=P modk, the actual new index is

    I'=I+epsilon*(P-j)/k-zeta,
    H*I'=a'*P+Q+ell', 0<=I'<L'=3H+2.

The index identity proves integrality; a'<2k, P<=k^3, Q<H^2/16 and
-4.5H<ell'<H/2 prove the common horizon. The exact covering differences
remain E'-HI'=(P-1)(Q-a') and, for chi-minus,
T'-HI'=-(P+1)(Q+a'). Hence the same beta and norm-one W give an actual
own-row collision for every continuing input. The seed q=(beta W)^H has
not changed; L',2L'<16H retain its existing unit guards.

The canonical phases e=[N(u-1)^2]_H and t=[-N(u+1)^2]_H have exact bounded
carries. With c0=floor(N/H), eta_E in{-5,...,1}, and for chi-minus
eta_T in{-6,...,0},

    E'=H*(c0+eta_E)+e,
    T'=H*(-c0+eta_T)+t  (chi-minus),
    V'=q^(c0+eta_E)*(beta W)^e  (chi-plus),
    V'=(beta^H)^(c0+eta_E)*(W^H)^(-c0+eta_T)*beta^e*W^t
                                                (chi-minus).

These are canonical residues, not unbounded raw quadratic exponents.
Replacing e by N(u-1)^2 requires its actual row-dependent q-power; the
corresponding shift in the seed origin can be huge. It is not a bounded
carry merely because its binary length is O(log N).

The exact low-a filter contains two units u per original tag: the two
solutions have inverse residues differing by H/2. Choosing the inverse
below H/2 gives exactly phi(k) rows. Both representatives have the same
canonical phases, actual row, colour and carry labels. Retaining both
therefore squares the actual query product and preserves every prime zero
mask; the inverse-half selector is optional. The required low-a filter
[Nu^2]_H<2k remains.
A complete quadratic Gauss sum without that restriction is a different
query. Both colours must be retained; there is no guarantee that the
smaller-prime hit lies in the pure-(beta W) colour.

All preparation and recovery margins survive. The actual delta'=a'+ell'
span is less than5H; distinct norm labels stay separated below the beta
order guard. Its congruence modulo k is unchanged, retaining at most16 tags
per exact delta and J=Theta(k) after deduplication. For a saturated original
norm leaf, the scalar beta witness either factors or gives

    D_order divides (1+H*i-delta')-(P+Q),
    |(1+H*i-delta')-(P+Q)|<4H^2<D_order,

where D_order is the product of the coprime local beta orders, greater than
256H^2. Thus the same bounded factor-sum decoder works with the NEW labels.
The bounded quantity is the difference from P+Q, not E'-Hi, which includes N.

There is also a lawful common-content normalization. The canonical phases
give gcd(E',H)=gcd(j-1,k)^2 in the plus colour, and gcd(E',T',H)=4 in the
minus colour. Divide the actual integer exponents and H by their common
content. Its prime factors are at most k, so paid roughness preserves every
component zero mask; no hidden root extraction is used. The controlled k
has constantly many content types. Grouping the resulting seeds and
executing the original blocked query still costs soft k^(3/2); the minus
colour alone retains Theta(k) targets. This operation simplifies the
arithmetic but does not shorten the index interval or establish a new rate.

### Status and retained evidence

The whole-family soft-k acquisition theorem, and then the executable/Lean
bit-complexity composition, remain open. The present results specify usable
inputs and exact costs rather than a new factoring exponent. Reports,
independent exact-source reviews and the append validator are retained in
/tmp/semiprime-zero-query-20261024. All prior shared-document prefixes,
all 270 frozen evidence entries and concurrent RH work are preserved.
