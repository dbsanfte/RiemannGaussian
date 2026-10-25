# Independent review of the quadratic acquisition candidate

2026-10-24. Reviewer: root. Result: **PASS within the stated restricted scope**.

Reviewed `cover-literature.md`, SHA256
`28b9b5e14ac5e94a101213d17f4ca387ad959efb708160f90af66b2eb21970d1`.
The report explicitly does not establish universal coverage. A separate exact
counterexample investigation is pending and is not assumed here.

## Arithmetic and acquisition

For supplied beta with nontrivial coprime odd local orders, the factored
smooth exponent M has soft-m bit length. Its full N-sized prime-power cap
kills every small primary component of either local order. The one-path
kernel descent is valid: at x^K=1, writing K=AB and testing x^A either
separates the primes, retains x with annihilator A, or retains x^A with
annihilator B and both local orders nontrivial. Coprimality persists.
A prime-power leaf cannot annihilate both surviving orders. Balanced tree
height times the total input bit length bounds all powers on the path,
so no unproved short-decoder claim for long M is needed.

The ordered universal separator has the precise interface asserted by
the pinned unbalanced extractor. Its minimum-exponent localization is
essential; an arbitrary global collision would certify only a common
multiple. Here its exact-common-order outcome is excluded by coprimality
and nontriviality. NoHit supplies both orders greater than 16m^2.

For f(x)=x(N-x), direct subtraction gives

    f(h(b+1))-f(hb) = hN-h^2(2b+1).

The second difference is -2h^2. The two actual group streams for h=1,m
therefore require O(m) multiplications and a constant number of modular
powers with O(log N)-bit exponents. All inversions are of the known unit
gamma'. Initial powers, labels and the group values are included.

For x=mb, y=a the positive integer difference is

    Delta=(mb-a)(N-mb-a).

The assumption N>2m^2 and 1<=b<=m, 0<=a<m guarantees Delta>0;
the small-N trial-division branch is paid. Delta<=m^2 N has logarithmic
bit length. This positivity is sufficient to exclude tautological zero
annihilators even if list residues repeat.

## Exact coverage and recovery

The map (b,a) -> mb-a enumerates [1,m^2], while (b,a) -> mb+a enumerates
[m,m^2+m-1]. A local collision is equivalent to the entire local order
dividing the product of these two corresponding factors. If the order
is prime and exceeds m^2, the first factor is nonzero below it, so the
second interval condition is necessary and sufficient. For a composite
order, splitting factors within this ONE difference is legitimate;
combining divisibility from unrelated pairs is not used.

The old interval guarantee is already subsumed by the preceding 16m^2
screen. The report correctly does not count it as new coverage in the
surviving branch. Coprime rough orders alone do not establish the required
short residue of the complementary factor.

Monic product and evaluation trees work over Z/N without division by
differences between points. At a saturated row, descending its product
tree gives either a proper gcd or a saturated single pair. The latter
provides gamma'^Delta=1. The base gamma', rather than the original beta,
has the guarded odd local orders required by the short-annihilator
extractor, and Delta is short. I read the extractor in full:

`docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md`,
SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.

Its asymptotic Burgess-based cost soft N^(31/192) applies to this input
and is below soft N^(1/6). The report does not hide the longer M*Delta
inside that theorem's input contract. Only one selected global leaf
requires that decoder.

## Primary literature and limits

Checked the primary Umans-Wang arXiv HTML and Zimmermann author PDF via
the web tool, alongside the report's cached-source references. The former
presents a structured divisor-cover conjecture; the latter describes
polynomial stage-two extensions. The report treats neither as a theorem
of universal coverage for these two particular lists.

Accepted conclusion: the construction and the covered-branch consumer
cost soft m, with an exact individual coverage predicate. This is a
correctly acquired candidate. It is not a fast evaluator for the original
guaranteed long query and is not a sixth-rate factorization theorem.
