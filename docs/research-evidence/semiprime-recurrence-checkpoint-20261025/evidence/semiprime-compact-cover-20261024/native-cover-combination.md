# Fused inverse-row arithmetic cover: exact cancellation returns weighted Fermat rays

2026-10-24. Scratch only; no repository edits, examples or backend work. This tests ONE concrete two-row combination using the actual native inverse phase. It derives a covered transformed family with acquired O(m) metadata, but then simplifies that family EXACTLY to ordinary weighted candidate-factor/Fermat rays. Its seed coordinate still ranges over m^2 and its base varies with the row. No pair of soft-m acquired exponent GAPs with proved all-input cover is constructed; no new sixth-rate claim is made.

## Duplicate guards and actual source

Read the older supplied-GAP consumer and its arithmetic cover gap:

- group-gap-criterion.md, SHA256 6fb196a7d87a81a53e1169810044fa5a946f85f683f79b25f2498e648929a5c9;
- coindex-constructor-verdict.md, b7e5929bd1eb415914575cffca654d754d7bec262eecb51b609fed9a6f4dbd12;
- paid-cover-transfer.md, 782c39a8e1eaa5a32b03cfcf2f6f61561aa3595d20c2dbd9cc7deb0ee856f644.

Those consumers need an ACTUALLY constructed cover and its nonzero-difference/witness ledger. A group annihilator removes prefactoring of a selected difference; it does not construct the cover. The older long-annihilator/QRH contract is not silently imported into a short-exponent route.

Also read the native multiplier recursion/closure, parameter-N Charlier report, and native-arithmetic-query.md (SHA256 8fa62736713cf6af639649502ce4ca9a0fb7b9cf48df18538fd712dc544f0e31). The already-paid Euclidean short-weight controller has an extra prefix costing m^1.25 at the sixth-root modulus; it cannot be counted as a free soft-m shorter family. Charlier central coefficient cancellation has no established short-menu cover. The exact inverse phase below is inherited from native-pivot-contraction.md, SHA256 9e363fee81473624d32088c4cba883d60fb3f9194d93f5ba30368c8881318c9a, not claimed as a new identity.

Retain the original prepared beta, prime m, H=m^2, N=P Q<=m^6, P<Q, P,Q>16H, and actual native a_j,ell_j,delta_j=a_j+ell_j. Both local beta/q orders exceed16H, are odd and the beta orders are coprime; the global beta order exceeds256H^2. Here q=beta^H. All row data are acquired in soft m bits. The own tag is j=P modm and

    H I=a_j P+Q+ell_j, 0<=I<2H+2.

The question is whether combining the inverse-tag equations eliminates the long unknown I into a two-list cover, rather than merely relabeling it.

## 1. What the known beta^N actually encodes

Put S=P+Q. Since beta is a unit and phi(N)=N+1-S,

    beta^N=beta^(S-1) modulo N.

The encoded exponent S-1 has a public bound below the prepared global order, so there is no small-range ambiguity in this identity. Its discrete logarithm is NOT acquired by the identity. Factoring this shared scalar gamma=beta^N out of all target polynomials is already paid; it leaves the native delta offsets, not the integer S.

The proposed fusion tries to use the reciprocal tag to remove gamma while retaining a short arithmetic witness. All subsequent identities keep the full common-scale phase until its cancellation is explicitly performed.

## 2. Cheap exception queries and the regular inverse data

For j*=[N/j]_m define

    A=a_j, B=a_(j*), AB=1+m*rho,
    B*(delta_j+1)-(delta_j*+1)=m*kappa,
    kappa=rho*(1-j) modulo m.

All are ACTUAL public integers computed from the centered native rows; rho>=0 and |m*kappa|<4mH. The all-row cost is soft m. The full target ratio is

    Y_j^B/Y_j*=beta^[(N-1)(B-1)+m*kappa],

so applying a variable power B does not leave gamma unchanged.

If A=1 then B=1, rho=0, j*=j and kappa=0 exactly. A fused zero difference there would be an integer-zero tautology, not an annihilator. Handle these at most two tags by their ORIGINAL one-row length-(2H+2) queries, each paid in soft m with its original localization/decoder. Query original j=1 too if distinct; this is one more soft-m call. If any such row is nonunit the existing original controller finishes. If they all return units, the unknown own tag is not among them.

After routing rho=0 (equivalently A=B=1) as above, compute gcd(rho,N) before treating the powered base: a proper gcd is a factor and is returned. On the inherited hard branch 1<=rho<=m-2<P,Q certifies the unit branch; a saturated gcd is excluded for these positive rho. All such guards cost soft m. The continuing own tag satisfies A!=1,j!=1, so kappa is nonzero modulo m. This is paid exception routing, not deleting possible own witnesses.

## 3. Exact inverse-row combination, including the larger complementary index

For proof only, the other factor Q has tag j*. Its native integrality gives an integer

    H I*=B Q+P+ell_j*.

Unlike I, this I* is NOT licensed the original short horizon: Q can be as large as m^4/16, so I* may have order m^3. No value or modular power at this private index is supplied to the algorithm.

Combining the two integer identities eliminates Q:

    H*(B I-I*)=m*rho*P+B*ell_j-ell_j*.

Since delta_j=A+ell_j and delta_j*=B+ell_j*, the known phase identity implies

    B*ell_j-ell_j*=m*(kappa-rho).

Hence the EXACT arithmetic relation is

    m*(B I-I*)=rho*(P-1)+kappa.                   (1)

Modulo the local order at P, this gives the fused group relation

    beta^(m*kappa)=q^(B I-I*) modulo P.           (2)

Both (1) and (2) are genuine consequences of the actual N=PQ and native carries. Neither contains a newly acquired small seed index: its exponent B I-I* can still have order m^3.

Now set the public integer

    csharp=(kappa+rho*(j-1))/m,

which is integral by the nonzero-residue formula above. Writing P=j+m*h, with h=(P-j)/m, equation (1) becomes

    B I-I*=rho*h+csharp.

Thus a seemingly useful transformed target is

    Z_j=beta^(m*kappa)*q^(-csharp),
    base_j=q^rho,
    Z_j=base_j^h modulo P at the own tag.          (3)

Every target/base/offset in (3) is acquired in soft m total signed-power work. The algebra has really eliminated I and the large common gamma; no target table or hidden factor is an input.

## 4. The decisive simplification: it is exactly a weighted ordinary Fermat ray

Substitute the acquired csharp definition into the target exponent:

    m*kappa-H*csharp=-m*rho*(j-1).

Therefore (3) simplifies IDENTICALLY, for every public regular tag, to

    Z_j=beta^[-m*rho*(j-1)],
    Z_j-(q^rho)^h is nonunit at P
       iff beta^[m*rho*(j+m*h-1)]=1 at P.          (4)

The native inverse phase has canceled out. Its remaining rho_j is still N-dependent metadata, but the matched exponent is exactly m*rho_j*(x-1), with the ordinary candidate-factor coordinate x=j+m*h. At x=P, Fermat proves the hit. This is a valid covered family, not a smaller arithmetic selector derived from S.

For x in the public factor interval 16H<x<=floor(sqrt N), the own h is in a public interval of length at most m^2 per tag. It has NOT shrunk to O(m), and the bases q^rho_j vary. The candidate two-list interpretation would have to acquire all these varying-base horizon values or a new implicit aggregate. Decomposing h=u+m*v simply inserts the row-dependent factors q^(rho_j*u) and q^(m*rho_j*v); the O(m) original metadata does not acquire their m-by-m arrays or a common seed list.

In particular the shortcut does not give O(m) target powers versus O(m) common seed powers. It gives O(m) targets versus O(m) DIFFERENT long seed streams. The exact identity (4), rather than a generic rank argument, is the stopping point of this chosen fusion.

## 5. Actual costs and all leaf branches of the transformed family

Use the complete public h interval for each tag defined by 16H<j+mh<=W, W=floor sqrt N. There are no x=1 leaves, and rho>0 on all retained regular tags, so every integer exponent

    K=m*rho*(j+mh-1)

is positive and nonzero, with K<m^5 and O(log N) bits. Thus there is no hidden integer-zero exception. A proper gcd of beta^K-1 factors. A saturated such leaf supplies a valid SHORT original-beta annihilator; if that experimental branch is used, its licensed consumer is the pinned unbalanced short-annihilator theorem from the uniform setup (report hash a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be), costing soft N^(31/192), within soft m. The original bounded-sum decoder does not directly apply to these changed exponents. No long-K decoder or prefactorization is assumed.

For each distinct acquired rho, group its targets and the at-most-two actual h lengths, using a common base q^rho. Monic product/MPE blocking is lawful even with repeated targets. Its charge is

    soft sum_rho (J_rho+sqrt(J_rho*L_rho)),
    L_rho<=m^2, sum J_rho=O(m).

This is a real initialized upper bound, at worst soft m^2 when many different bases are processed. Even the favorable common-base ledger retains the old sqrt(m*m^2)=m^1.5 scale; these are charges of this grouping implementation, not lower bounds on distinct rho counts or a future implicit method. No m^2 output enumeration is called an advance.

A practical complete fallback should instead use the simpler original order interval cover below. The fusion was tested to find a smaller cover, not to replace the known faster routine with this larger one.

## 6. Fully acquired two-GAP fallback, with its honest volume

The smaller prime's prepared local beta order d_P divides P-1, hence d_P<=W-1. Let Dcap=W-1 and b=ceil sqrt Dcap. The public exponent GAPs

    S={0,1,...,b-1},
    T={b,2b,...,b*ceil(Dcap/b)}

have separated hulls, and their positive cross-differences cover EVERY integer from 1 through b*ceil(Dcap/b), in particular d_P. All modular powers are acquired by simple recurrences; monic MPE/product trees and localization cost soft b. Their ACTUAL total box volume is Theta(sqrt W), at most soft m^1.5, not soft m.

Every selected cross exponent is <=W+b. On the hard native branch this is less than256m^4, below the prepared GLOBAL beta order, so a saturated GLOBAL leaf is impossible. Saturated products can still occur from different local leaves and are descended normally; a nonunit leaf therefore gives a proper gcd. Alternatively a known nonzero short global annihilator would have the valid consumer discussed above, but it is not needed for this fallback.

The bit cost includes O(b) residues of O(log N) bits, all input powers, selected labels and monic arithmetic: soft sqrt W=soft N^1/4=soft m^1.5 at the balanced worst scale. This is the already-known ordinary order/factor interval cover. Its whole-family coverage and recovery are fully proved, but its volume does not meet the mandatory sixth-root budget.

## Outcome

The chosen actual-native inverse fusion DOES produce an exact acquired relation and a covered transformed target family. Carrying all phases then proves that it is just the ordinary weighted Fermat coordinate x-1, with a row-dependent multiplier rho and the old m^2 seed range. The cheap exception rows are retained, and all selected annihilator/leaf branches have valid bounded-bit recovery. The beta^N encoding of S is not acquired as an integer, and the fused cancellation does not provide a new two-list cover of its hidden local orders.

No soft-m cover or new arithmetic lower bound is claimed. This is a precise failure of this specific combination, with a fully charged fallback rather than an unconstructed cover promise. A positive continuation would need a different acquired relation that genuinely shortens or merges the remaining candidate-factor rays, or a new soft-m norm on them; merely dividing or renaming the carried inverse phase does not do so.
