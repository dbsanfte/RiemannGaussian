# Count acquisition: public small-square data and the exact character input

23 October 2026. Read the frozen uniform-trace construction, inherited twist-character/count-deficit audit, normalized-discriminant sieve, and the new scratch arithmetic-detector report. No frozen files, repository source, or backend were changed. This continuation does not repeat the count-oracle reduction or large-index trace diagnostics.

**Outcome.** No soft-r per-window CRT collision count was acquired. The concrete positive computation here is a soft-r list of signed small modular squares attached to the exact Gauss rows, together with their gcd screening and batched small-smooth parts. This uses an actual public integer observable and a fully charged primary algorithm. It does not yet provide a count. A tempting way to convert these data into a character projector fails on one exact covered structured row; the missing arithmetic is identified precisely below. No operation lower bound is asserted.

## 1. Public Gauss discriminants are small, and their smooth parts are affordable

Write H=r^2, M=H^2. A Gauss row has

    d^2+X^2 b^2+X^4 a^2 <=(5/2)H^2 X^2,
    B=Hb-2as,
    CN=H^2d-Hbs+as^2 !=0.

Define the signed integer

    D0=b^2-4ad.

There is a sharper bound than multiplying the separate worst-case coefficient estimates:

    |D0| <= b^2+4|ad|
           <= b^2+2[(Xa)^2+(d/X)^2]
           <=5H^2=5r^4.                                      (1)

The exact root relation gives

    B^2-4aCN=H^2 D0,
    D0=(B H^(-1))^2 modulo N.                               (2)

Thus every row supplies an explicit small signed square modulo N and its known root. Both are acquired in soft-r work across the r rows of one window. Proper gcds of B or D0 with N immediately factor N. There is no saturated exceptional D0=0: for a!=0 it would imply N|B, but |B|<3H^2<N on the surviving P,Q>16H branch, forcing B=0 and then C=0. For a=0, D0=b^2!=0 since b is a unit modulo H.

For every public smoothness cutoff y<=r, the y-smooth parts of ALL |D0| can also be acquired in soft-r total bit work. Sieve the primes <=y, form their product, use a remainder tree modulo the |D0|, and use the bounded number of repeated squarings/gcds in Bernstein's algorithm. The total explicit input size is soft r: r integers of O(log N) bits and a prime list of O(r) total bits. Signs remain separate; a relation among signed D0 values needs its -1 parity retained.

Bernstein's primary algorithm computes smooth parts in b(lg b)^(2+o(1)) time for total input length b, with no randomness or input-distribution condition. See *How to find smooth parts of integers*, 2004-05-10, abstract and Section 2, pp.1-5: https://cr.yp.to/factorization/smoothparts-20040510.pdf . This pays the list/smooth-part observable, not the existence of enough smooth relations.

This route stops at a specific missing guarantee: these exact deterministic discriminants are not proved to supply enough independent square relations with a nontrivial sign split between P and Q. Linear rows illustrate the issue directly: D0=b^2 has the already supplied integer root b, so its individual square relation is trivial. Smaller modular squares alone do not count the original rho^K=1 events. No smoothness-density or root-orientation heuristic is used as a theorem.

## 2. Completing the actual exponent square identifies the relevant modulus

The normalized quadratic node is rho^K with

    K=a c^2+B c+CN-M sigma,
    rho^a=beta.

Let d_P be the local order of rho. Purification makes a and H units modulo d_P; all normalized bases have the same local order. Equations (1)-(2) give the exact identity

    4a K=(2ac+B)^2-H^2(D0+4a sigma).                       (3)

Consequently the local collision condition is equivalent to

    ((2ac+B) H^(-1))^2=D0+4a sigma modulo d_P.             (4)

For a controlled linear row, the corresponding condition is linear in c,sigma modulo the same d_P. Formula (4) is a useful source-specific quadratic congruence, but its modulus is the order d_P, rather than the known N or the field characteristic P. Taking a Jacobi symbol modulo N of its small right-hand side computes a different character.

The true INTEGER root identity is also exact, and explains the discrepancy. If g(h)=P sigma at the covered h, then

    (2ah+b)^2=D0+4aP sigma.                                (5)

Reducing P to 1 in (5) is legal modulo d_P. It is not legal modulo P or N. This is the precise arithmetic input needed by the proposed small-argument character observable; neither the lattice norm bound nor the short sigma cap supplies it.

One fixed covered row shows that replacing it by a modulo-N square filter can delete a true witness. The adjacent compact `check_integer_character_filter.py` verifies only this substitution, without a search or success campaign. In the root's structured catalog take

    r=43, P=59447, Q=59747, P0=59168,
    A=1, a=1, C=331, s=345, c=41,
    B=1082824, b=586, d=343984, sigma=48.

All catalog double-root and window identities hold; C is within its catalog cap. Here

    D0=-1032540,
    D0+4aP sigma=10381284=3222^2,
    Jacobi(D0+4a sigma,N)=-1.

So a nonnegative-Jacobi square filter at that substituted argument would discard the true leaf. This does not disprove a different weighted character identity; it rules out this precise candidate. The script uses the factors only to verify the claimed covered integer relation, not to construct a detector.

## 3. The correct public integer-root filter retains both indices

The public normalized discriminant that actually preserves the true witness is

    D(c,sigma)=D0*c^2-2B*c*sigma+M*sigma^2.                 (6)

Indeed

    (Bc-Msigma)^2-4a*c^2*CN=H^2 D(c,sigma),

and at the true factor this equals (a c^2P-CQ)^2. Thus (6) is an INTEGER square. Its two-index organization is essential; D0+4a sigma is not a substitute.

This agrees with the inherited normalized-discriminant sieve and the sibling arithmetic detector's conic. For a fixed row and c, (6) is a public quadratic in sigma, so correct local-square masks can be generated. Acquiring all their character weights by explicit evaluation still pays r rows times r multipliers times O(r) seeds. A proof contracting those correlated weights is absent; no implicit mask table is counted as supplied.

I checked Bernstein's primary doubly focused enumeration algorithm against this concrete input rather than treating CRT descriptions as a free count. Its stated analysis is H/M^(2+o(1)) with M=H^(1/log_2 log H), averaged over the offset for a fixed nonconstant squarefree polynomial. On length-r sigma windows this is r^(1-o(1)) per supplied row/c quadratic even if an appropriate uniform extension were available. It does not give a total soft-r bound over the r^2 changing quadratics here, nor a count of the group collisions. See Section 3, pp.4-5: https://cr.yp.to/focus/focus-20030928.pdf . This is a check of that algorithm's actual charge, not a lower bound for a new shared sieve.

## 4. Structured catalog and the remaining computation

The parent's newer catalog makes a positive: 1<=a<=A, 0<|C|<=T, CN=a modulo r, with O(r) rows and a common rho_a for each a. The per-a C progression and actual centered B are genuine supplied structure. For it the same small-discriminant scale follows from

    |aC|<H, |B|<=M/2,
    D0=(B^2-4aCN)/M,
    |D0|<M/4+4N/H<=17H^2/4.

It therefore admits the same soft-r small-square and smooth-part computations; (3)-(6) remain exact. No linear-row exception is needed for that catalog. The preceding character-substitution test was deliberately taken from this structured nonzero-a source.

A fully explicit factor-or-count baseline remains soft r^2 per window: for each row form its r multiplier targets and O(r) seed polynomial, then use polynomial gcd/squarefree decomposition with factor-on-nonunit arithmetic and preserve target multiplicities. All degrees are below the hidden characteristics. This is ordinary charged polynomial arithmetic, not a new backend or a soft-r implicit acquisition. Grouping shared rho_a bases does not remove the r^2 target-root construction.

The precise productive next operation is to acquire the weighted intersection multiplicities for the implicit chirp target polynomials and their short geometric seed sets, exploiting fixed-a C progressions and the carried B values. Alternatively, a new positive integer-square/character identity may use (6) while paying the correlated two-index weights. The public data (1)-(2) and their smooth parts are available; the existence/independence or projector step converting them to an all-input count is not proved. No improved factoring exponent follows from this report.

## Sources and replay

Only scratch files were written. The two primary PDFs were downloaded and read locally:

* `sources/bernstein-smoothparts-20040510.pdf`, SHA256 `2ef7aa60f8133ec1125bac4a39498285b626c0f553571fb00385822377facda7`.
* `sources/bernstein-focus-20030928.pdf`, SHA256 `8f0b40557c7d0095bb2c277c8a35bf9fd06a2451d53c2bb23b71fa118724cdae`.

The one-row replay is `python3 -B check_integer_character_filter.py`. It verifies the wrong-modulus substitution failure and the correct public normalized discriminant square; it is not a coverage campaign or runtime certificate.
