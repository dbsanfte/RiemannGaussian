# Boundary coverage on the actual Gauss Cartesian family

26 October 2026. Paper-only follow-up to the archived rectangle-query
packet, especially `sparse-projection.md` and `corner-query.md`.

Two completely initialized boundary modifications do cover: lengthen
the generator clock to the old Gauss horizon, or include every
interior difference as a boundary start. Their costs are respectively
the old soft k^(5/4) bound and soft k^2. Neither gives the requested
soft-k query. The first is existing Gauss coverage, newly compared
with the corner screen here; it is not a new factoring algorithm.
The specific attempt to push a hit to a corner by homothetic scaling
requires an extra arithmetic alignment and a longer clock. No claim
that all bounded-translate constructions fail is made.

## Input and accounting

Use the actual retained cells of `sparse-projection.md`: a Gauss basis
u,w of the colour lattice, lengths ell1<=ell2, generator phases
lambda_u,lambda_w in [0,H), X=beta^E_u, Y=beta^E_w, H=k^2,
and A=ceil(R/ell1), B=ceil(R/ell2), R=2k sqrt(N).
There are soft k cells; AB=O(k), A,B<2k. At the true cell,

    H I_u=a_u P+b_u Q+lambda_u,
    H I_w=a_w P+b_w Q+lambda_w,
    X=q^I_u, Y=q^I_w modulo P.

The public a-span filter is retained. Its guarantee applies to all
original difference coordinates |r|<A, |s|<B, not both zero, and
clock 0<=h<=4k. It proves their integer beta labels nonzero. We do
not transpose the cells, or assume their products vanish globally:
the promised outcome is a nonunit at P. Any proposed aggregate must
support nonunit localization, rather than only an exact-global-zero
bit. A proper gcd finishes; a saturated nonzero short beta label
uses the licensed extractor, charged at most once as
T_ext=soft O(N^(31/192)), which is within soft O(k). Shorter general
factor-or-value calls must still include this terminating cost.

All geometric-string evaluations below use the inherited monic,
division-free joint backend. No inverses of rejected factors, no
root-of-unity clock assumption, and no numerical division by the
omitted origin line are introduced.

## 1. A uniform generator boundary cover, at the old horizon

The Gauss inequalities give

    ell1^2 <= 2kN/sqrt(3),
    |I_u| <= 2sqrt(2) ell1/H+1
            < 4 sqrt(kN)/H+1.

Put D=ceil(sqrt(kN)) and

    M_gen=ceil(4D/H)+2.

Add the two strings

    product_(h=0..M_gen)(1-X q^(-h)),
    product_(h=0..M_gen)(1-X^(-1) q^(-h))

to every cell. These are a bounded number of acquired generator
starts per cell. At the true cell choose X if I_u>=0, otherwise
X^(-1). The hit occurs at |I_u|. It has integer label, up to sign,

    K_u=E_u-H I_u=(P-1)(b_u Q-a_u) != 0.

Indeed |a_u|<=a_span<=H<Q; if b_u is nonzero its Q term dominates,
and if b_u=0 then a_u is nonzero because u is a basis vector.
This also handles I_u=0: a central local hit need not be a literal
integer-zero label.

For every auxiliary string first identify any index with literal
label L-Hh=0, and omit it by an explicit interval split. This cannot
remove the guaranteed true hit because K_u is nonzero. Every other
nonunit is likewise decodable by its own short nonzero label; it
need not be mapped back to an old |ab|<k row. All indices, generator
coefficients, and resulting labels have O(log N) bits. Negative
orientation uses X^(-1) directly, without pretending it is a
canonically rephased opposite row.

Since N<=k^6, M_gen=O(k^(3/2)). There are soft k starts and at most
a constant number of split intervals per start. Common-clock
interval grouping and the inherited engine cost

    soft O(k + sqrt(k M_gen) + T_ext) = soft O(k^(5/4)).

Thus a paid boundary cover exists, but this is precisely the old
Gauss short-vector horizon and old query rate. It does not justify
replacing M_gen by 4k.

## 2. A uniform short-clock boundary cover, with too many starts

Include the strings

    product_(h=0..4k)(1-X^r Y^s q^(-h))

for every original nonzero difference coordinate |r|<A, |s|<B.
Equivalently each such coordinate can be exposed as the corner of
an appropriate translated finite rectangle. Omit the entire
(r,s)=(0,0) line before evaluating, not by division after evaluation.
The original span filter makes all included labels nonliteral,
and the original pigeonhole theorem guarantees one nonunit.

This is an actual finite covering construction: O(k) starts per
cell, hence soft O(k^2) starts globally. Their acquisition and the
joint length-O(k) engine cost soft O(k^2), including localization
and at most one terminating T_ext. It supplies no target gain.
No lower bound on other, implicitly initialized boundary schemes
is inferred from this explicit construction.

## 3. The exact arithmetic obligation for the eight cheap corners

Here is a native-specific test of the missing coverage step. A useful
corner hit here always refers to a factor retained AFTER the known
literal-zero indices were omitted. In particular the origin-hole
factor (r,s,h)=(0,0,0) is absent; its tautology is not useful coverage.
At the
true cell each of the original corner strings has coordinates
|r|<=A, |s|<=B. The generator index estimates imply, for 0<=h<=4k,

    |r I_u+s I_w-h| < 16H.

For clarity the constants can be paid explicitly. Reduced-basis
bounds imply

    ell1+ell2 <= (sqrt(2)+sqrt(2/3) k) sqrt(N).

To see this, write C=2kN/sqrt(3), use ell2<=C/ell1 and
sqrt(2N)<=ell1<=sqrt(C), and maximize x+C/x on that interval
at its left endpoint. Since A ell1<R+ell1 and similarly for B,

    |r I_u+s I_w-h|
      < (8sqrt(2)+4/sqrt(3)) k sqrt(N)/H
         +4sqrt(N)/H+8k
      <= (8sqrt(2)+4/sqrt(3)) H+12k <16H

for k>16. The large local q order therefore makes a true-cell
corner hit equivalent to the INTEGER equation

    r I_u+s I_w=h,                 0<=h<=4k.             (1)

It cannot be supplied merely by an untracked local-order alias.
For v=r u+s w=(a,b) and the unwrapped phase
L=r lambda_u+s lambda_w, equation (1) is exactly

    aP+bQ+L=Hh,
    aP^2+(L-Hh)P+bN=0.                                (2)

This is an actual additional arithmetic condition on P,Q and the
chosen corners. The established pigeonhole argument supplies a
nonzero INTERIOR difference satisfying (1); it does not select one
of the eight displayed corner vectors. Equation (2) states the
remaining obligation precisely. This report does not claim to
prove that every actual semiprime violates that obligation.

## 4. Tested modification: push the useful zero outward by scaling

Suppose the guaranteed difference is (r0,s0,h0). In the unwrapped
actual family, integer multiplication gives an exact propagated
hit (d r0,d s0,d h0). For this propagated hit to land at a prescribed
corner (c1,c2) requires

    c1=d r0, c2=d s0,
    c1 s0-c2 r0=0,

as well as divisibility and d h0<=4k if the short clock is kept.
Homothetic enlargement leaves corner rays unchanged; the Gauss
coverage theorem supplies neither ray alignment nor the required
clock inequality. For h0=0 the alignment issue still remains.
A local-order alias might independently create another corner
hit, but is not a consequence of this propagation rule.

Translating a corner onto a KNOWN (r0,s0) is straightforward. Doing
so before knowing the witness requires a covering family of
translates; the fully paid exhaustive version is Section 2. This
is a failure of the particular homothetic push rule as a coverage
proof, not an impossibility theorem for all small translate sets.
Moreover new scaled corners outside the original span filter
cannot silently inherit its nonliteral-label certificate. Their
literal labels must be screened directly, or a fresh span bound
must be proved before the decoder is invoked.

## Outcome

The finite corner identity remains a valid possible recursion, but
no initialized recursion reducing the required bulk values to
soft-k useful short-clock boundary starts was obtained. The two
explicit coverage completions above are fully chargeable and
preserve the origin omission and decoder. Their costs expose the
precise tradeoff: old long clock with soft-k starts, or short clock
with soft-k^2 starts. A target improvement still needs an arithmetic
selection of the interior witness, or a genuinely initialized joint
contraction; the cleared identity alone supplies neither.
