# A factor-correlated Euclidean cover, with its exact remaining mass

26 October 2026. Research report, archived after review. No soft-k cover with total width soft(k²) is proved. This pass goes beyond the independent tag/real-scale domain: it constructs an O(k log k)-descriptor continued-fraction cover directly from the integer equation PQ=N, with no factor-size bins. Its complete menus still have total width Theta(k^(5/2)) up to logs at N=Theta(k^6). A positive result is that the literal constructor's first odd menus alone certify this mass; a useful improvement must make a coverage-safe selection or shrink those *correlated integer* menus, rather than merely deduplicate parametric events.

Read current native-contraction.md, primitive-coverage.md, its coverage review and event-count.md, the scalar catalogue and swap erratum. Their content restriction, tiling, half-center fold, HH tradeoff and full-domain descriptor bound are prior credit. The construction below is an adaptation of Lenstra's actual divisor-correlated Euclidean algorithm, not a claim that continued fractions supply a new factoring theorem.

## 1. Primary literature and precise operation

H. W. Lenstra Jr., *Divisors in Residue Classes*, Math. Comp. 42 (1984), author-hosted primary PDF https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1984b/art.pdf, Algorithm (1.2), Lemma (1.6), Proposition (1.7). It starts from (sx+r)(sy+r')=N, obtains a sequence of congruent linear forms by the Euclidean algorithm, and uses a sign-change lemma to guarantee a small form at some index. Polynomial-time divisor recovery in the source requires s>N^(1/3); that hypothesis is not available at s=k~N^(1/6). Here its parameterized sign-change lemma remains valid and supplies larger, explicitly charged menus.

For comparison, Harvey–Hittmeir https://arxiv.org/pdf/2105.11105, Proposition 3.3, supplies the narrow-bin stationary construction already audited. The present test uses the exact quotient-product correlation instead of requiring all independent residue/bin combinations.

## 2. Public Euclidean descriptors for one factor residue

For each unit j modulo k, acquire its inverse modulo k, let s=[N j^-1]_k in [1,k), and put C=(N-js)/k, an integer. If the actual P equals j mod k, write

    P=j+kx, Q=s+ky, x,y positive integers.

The hard branch P,Q>16k² ensures positivity. The exact public-correlated equation and its first congruence are

    (j+kx)(s+ky)=N,
    sx+jy=C mod k.                                     (1)

Let g=[s j^-1]_k, also a unit. Apply the alternating Euclidean chain from Lenstra's Algorithm (1.2) to (k,g), beginning

    (A0,B0,c0)=(k,0,0),
    (A1,B1,c1)=(g,1,[C j^-1]_k),

and apply the same quotient recurrence to all three coordinates, reducing c_i modulo k. Use Lenstra's parity convention explicitly: choose each quotient so that 0<=A_i<A_(i-1) at even i, and 0<A_i<=A_(i-1) at odd i. In a divisible odd step this chooses the positive equal remainder rather than terminating there; termination is at an even index. Ordinary Euclidean quotients without this convention do not directly justify the sign-change indexing below. There are O(log k) stages, with A_i>=0, B_i positive at odd stages and nonpositive at even stages. They obey

    A_i x+B_i y=c_i mod k,
    A_i j²=B_i N mod k.                               (2)

All coefficients have magnitude at most k. Nonaxis products satisfy |A_i B_i|<k: adjacent determinant identities and decreasing positive remainders give A_i|B_i|<k before termination. The endpoints are the stored axes. Thus these are actual native-sized coefficient labels, not a family with uncharged larger products.

Acquire one phase per stage:

    tau_i=k c_i+A_i j+B_i s mod H,
    lambda_i=[-tau_i]_H.                               (3)

The recurrence implies c_i=B_i C j^-1 mod k. Combining this with (2) directly gives tau_i²=4 A_i B_i N mod H. Thus lambda_i is a lawful native conic root, acquired without enumerating H lifts. For actual factors in the class, the physical value T_i=A_i P+B_i Q equals k(A_i x+B_i y)+A_i j+B_i s and is congruent to tau_i modulo H.

Every descriptor, modular inverse, Euclidean coefficient and phase in (2),(3) is acquired in soft(1) per stage, hence soft(k) total. This uses actual PQ=N through C and (1), rather than the full independent (j,t) product domain of event-count.md.

## 3. Uniform correlated coverage and explicit menus

Choose a public positive integer

    mu=ceil sqrt(N/k³).

Lenstra's Lemma (1.6), applied to the actual x,y and parameter mu, guarantees an index i for which

    |A_i x+B_i y|<mu*k                    if i even,

or

    2mu A_i B_i < A_i x+B_i y
                      < xy/mu+mu A_i B_i if i odd.       (4)

Since xy<N/k² and N/(mu*k²)<=mu*k, public covering menus are

    -mu*k < c < mu*k,                  c=c_i mod k, even;
    2mu A_i B_i < c < mu(k+A_i B_i),    c=c_i mod k, odd. (5)

No hidden factor value appears in these endpoints. Open endpoints can be converted exactly to integer floors/ceilings. Odd menus with lower endpoint at least upper endpoint are empty. Each even menu has at most 2mu+O(1) values; each odd menu has at most mu(1-A_i B_i/k)+O(1).

For each menu value c=c_i+kz, its original q-clock index is

    I=z+h_i,
    h_i=(k c_i+A_i j+B_i s+lambda_i)/H in Z.             (6)

Hence every stage gives a consecutive acquired integer q interval of length O(mu), with an explicit start. Equation (4) proves that the actual factor point is covered by at least one of these O(log k) stage intervals for its j. This is a uniform *factor-correlated* cover. It does not claim coverage for independent real scales and tags.

The scalar target for the P-local hit is beta^(A_i+B_i N+lambda_i). Add the swapped coefficient target beta^(B_i+A_i N+lambda_i) with the same phase and *same interval (6)*. At the witness stage and index I, the former hits q^I modulo P and the latter modulo Q. Their Fermat exponents are (P-1)(B_i Q-A_i) and (Q-1)(A_i P-B_i), both nonzero because |A_i|,|B_i|<=k<P,Q and the pair is nonzero. Public exact-zero deletion on the actual interval preserves both witness rows, as in the authoritative scalar argument.

For explicit deletion precision, (5) and |A_i B_i|<k give |c|<=2mu*k, while |A_i j+B_i s|<=2k². Thus |I|<=2mu+3. All actual row intervals lie in this public O(mu) envelope, whose diameter is below both local q orders: mu<=k^(3/2)+1 and the prepared bound is >16k². If a whole row were deleted by an integer match E=H*i0 in the declared envelope, its local witness equality would imply q^(I-i0)=1. The short-envelope diameter forces I=i0, contradicting its nonzero Fermat exponent. This short-interval step, not nonzero Fermat alone, justifies whole-row deletion. The old O(mu) envelope can also be retained after explicitly checking its constant against the same order bound.

Original labels and intervals therefore support the existing nonunit/annihilator consumer. They also preserve a full-zero endpoint if the aggregate includes every retained menu and both swaps. Reanchoring each target by its acquired interval start converts to nonnegative clocks; clipping prefixes must use the same paired starts. One may pad intervals to a common O(mu) horizon as a safe overcover, with public exact-zero deletion on the padded interval. This costs the same asymptotic support. No mixed-CRT zero predicate is replaced by an OR of per-menu zero predicates.

## 4. Exact paid cost and a literal-menu lower bound

There are R=O(k log k) acquired descriptors and each has O(mu) clock values. The old initialized variable-window evaluator gives

    soft(R+sqrt(S)),  S=sum_i menu_length_i
       <=soft(k+sqrt(k*mu)).                            (7)

At N=Theta(k^6), mu=Theta(k^(3/2)), so this is soft(k^(5/4)). The factor-correlated construction does not reach the requested S=soft(k²).

There is an exact reason its literal menu list cannot be charged only k² by a better *upper-bound estimate*. At the first odd stage, A1=g,B1=1. The menu c range in (5) has length mu(k-g), so contains mu(1-g/k)+O(1) candidate values in its residue class.

For k=2*3^e, the map j->g=N j^-2 modulo k runs over all odd units g satisfying g=N mod 3, each exactly twice. Indeed the unit squares modulo 3^e are precisely the units 1 mod 3, and the mod-2 unit condition adds no further choice. Therefore Theta(k) unit tags have g<=k/2. Their first odd menus each have at least mu/2-O(1) entries. Consequently

    S_literal=Omega(k*mu)=Omega(k^(5/2)).                (8)

The coefficient rows (g,1) for different such g are distinct. Integer exponent deduplication also loses only a constant here, but this needs an additional root-count argument. If E=N+R is fixed, a contributing g satisfies lambda=R-g and lambda²=4gN mod H, hence

    [g-(R+2N)]²=4N(R+N) mod H.

At H=4*3^(2e), the roots of any soluble square congruence partition into at most two global cosets with spacing at least 2*3^e=k: the mod-4 condition is one parity coset, and the mod-3^(2e) condition has at most two branches, each with spacing at least 3^e. Thus an interval of g values of width <k contains at most two contributing g. Each g has only two tag preimages. The argument uses only the fixed residue E mod H, not equality of full integer exponents. Consequently at most four first-odd descriptors have any one integer exponent class modulo H. Even known integer q-shift reanchoring, which groups E differing by H times an integer, can merge only this constant number; it cannot remove the power in (8). Arbitrary coincidences modulo the unknown local beta orders are not inferred from this integer statement. All these b=1 rows and their b=g swaps survive the original public zero-row deletion on the hard branch; deleting the complete diagonal subset affects only g=1.

Removing those first odd menus altogether would require a new coverage-safe selection proof: Lemma (1.6) is existential across stages and does not promise that a later stage always replaces them.

Equation (8) is scoped to this acquired Euclidean menu constructor, not to all factor-correlated covers. It is distinct from the previous full-domain descriptor lower bound: here R is already softly linear, and the remaining issue is the mass of the actual divisor-correlated candidate menus.

## 5. A concrete public filter and why the standard small-root theorem is insufficient

An actual PQ=N filter can be attached to any residue/bin before admitting its menu. Choose public p0=j mod k near B and q0=s mod k near N/p0. Write P=p0+ku,Q=q0+kv. The exact integer polynomial is

    f(u,v)=k uv+q0 u+p0 v+(p0q0-N)/k.                  (9)

It is integral, primitive and irreducible over Q: its bilinear determinant is -N, nonzero. A complete integer-root solver in the proposed u,v box can either recover a factor or certify that box empty, so this is genuinely factor-correlated filtering rather than independent tag/scale coverage.

Primary source: Don Coppersmith, *Small Solutions to Polynomial Equations, and Low Exponent RSA Vulnerabilities*, J. Cryptology 10 (1997), Theorem 2 and Corollary 2, DOI https://doi.org/10.1007/s001459900030; primary paper PDF https://citeseerx.ist.psu.edu/document?doi=e3e49df9da4ee17c8ee37e7104177331bb14af99&repid=rep1&type=pdf. For a polynomial of degree at most one in each variable, the theorem has explicit constant/epsilon slack around XY<W^(2/3), with W the largest scaled coefficient and time polynomial in log W and 1/epsilon. Corollary 2 handles the boundary by polynomial-time overhead. The scaling comparison below suppresses those constants and polylogarithmic accuracy factors; it asserts no exact unqualified cutoff at a chosen numerical constant. This is an integer theorem, not a generic multivariate modular-root heuristic.

For a balanced relative factor bin of width epsilon, the natural bounds are

    X=Theta(sqrt(N)*epsilon/k),
    Y=Theta(sqrt(N)*epsilon/k),
    XY=Theta(N epsilon²/k²),
    W=Theta(N epsilon/k)

in the range epsilon>=k/sqrt(N). Here p0 is a public residue-j point near B and q0 is a residue-s point within O(k) of N/p0, so |p0q0-N|/k=O(p0)=O(sqrt(N)); this constant coefficient is no larger than N*epsilon/k in the stated regime. The linear scaled coefficients also give that height as a lower bound. The height is therefore N*epsilon/k, **not N**: overlooking the scale of the shifted polynomial would falsely produce an N^(1/6) algorithm. With constant/epsilon slack understood, Coppersmith's scale condition gives epsilon=O(k/N^(1/4)); at N~k^6 this is O(k^-1/2). Covering all k tags and this balanced range literally costs soft(k^(3/2)) boxes. It is not a soft-k filter for the current menus.

At one constant-size balanced box per tag, X,Y~k² and W~k^5. A solver for the special semiprime-determinant polynomial (9) reaching XY~W^(4/5) would meet the needed native scale, whereas the cited theorem reaches W^(2/3). No such stronger theorem is asserted. This expresses a decisive, concrete arithmetic gap on a specific low-degree equation, rather than rephrasing the missing q-product oracle.

## 6. A narrower next lemma, with paid consequences

The useful remaining target is a **coverage-safe Euclidean-menu filter** for (1)–(6): acquire in soft(k) total work a subset or shortened union of these known stage intervals, with total width soft(k²), such that every actual semiprime factor point still has at least one retained stage and its swap. The filter may exploit (9), the exact quotient product (1), and relationships between adjacent Euclidean stages. It need not cover every independent unit tag/real scale, so event-count.md does not exclude it.

One particularly concrete sufficient result would show how to process the Theta(k) long first-odd menus in (8) collectively: either factor N or certify a replacement of total width soft(k²) by adjacent-stage intervals, retaining the same physical labels and common-index swap provenance. Neither their small descriptor count nor the fact that N has only two proper divisors proves that replacement is cheaply acquired. The complete root equation is already used in the menu congruences; it cannot be counted again as a free filter.

Once that filter is proved and acquired, (7) immediately gives soft(k), and the original saturated-leaf consumer closes the algorithm. Without it, the present exact construction and the standard small-root filter provide no new exponent. No tests or experiments are used as proof, and no repository files were edited.
