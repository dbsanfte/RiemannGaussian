# Independent review: restricted-residue HH consumer

26 October 2026. Read primary Harvey–Hittmeir 2105.11105 Proposition 3.3, Algorithms 4.1/4.3, Proposition 4.4 and their proofs, and the updated parameterized-controller.md including the n|k palette extension. Paper review only; no tests or repository edits.

**PASS. This is a valid conditional consumer, not a supplied factor-residue palette or a new complete factoring rate.**

Primary source: [HH HTML](https://arxiv.org/html/2105.11105), with downloaded PDF/text inspected in `/tmp/semiprime-axis-supplier-20261026/` and hashes retained in the companion report. Source orientation is aQ+bP, and its modular centre is aN/sigma+b*sigma modulo n². Keeping only a supplied residue menu preserves its true-bin proof if at least one menu entry is P modulo n. The integer centre loop covers every smaller-factor value; wrong menus return only checked factors or bounded FAIL, never primality. These are the precise source interfaces used.

## Native constants and initialization

After deduplication let S>=1 count the supplied unit residues. Require n|k and n>=S*k^(1/3), and put r=ceil(16k/S). Then

    S*r<=16k+S,
    n*r>=16*k^(4/3),
    lambda=ceil(4sqrt(N)/(nr)^(3/2))<=ceil(k/16),
    kappa=2lambda+1<=k/8+3<k (native k>16).

Moreover q=(beta^(n²))^(H/n²). Hence the local order of delta=beta^(n²) is at least that of q, exceeding 16H. This is a divisibility argument, stronger than dividing the beta-order bound by n²; it works for n through k with no new order preparation or roughness assumption.

Each of the S residue searches has soft r actual centre starts; total giant count is soft(Sr)=soft k. All lattice coefficients and integer exponents have O(log N) bits by the primary polynomial-height bound. The common baby alphabet has kappa<k entries. Products, geometric evaluation and sort/match processing therefore fit soft k. Palette acquisition is additional unless already supplied. Nonunit candidates cannot be true factor residues since gcd(n,N)=1; filtering/deduplication costs soft S. Complementing a palette for either factor has only constant overhead, with constants in r adjusted if necessary.

## Exact matches, literal exponents and zero coefficients

Process ALL global matches with their source labels before deleting matched giants. Baby entries are locally distinct throughout the index window. Therefore, if the true giant is globally matched, its matching index is necessarily the true local index, and u=n²i+j equals aQ+bP. An extraneous global match cannot remove that true giant without the corresponding exact recovery succeeding. Duplicate giants may yield as many matches as giant entries; this still fits soft k and does not require the source's stronger informal count.

For a,b both nonzero, exact quadratic recovery uses bX²-uX+aN, tests both rational/integer roots and verifies a nontrivial divisor. If a=0,b!=0, test u/b; if b=0,a!=0, test u/a as Q. Both zero is excluded by the lattice construction. These explicit cases avoid relying on the primary recovery lemma's overly broad literal wording for a=b=0.

A global match with integer exponent label aN+b-j-n²i=0 is not sent to the generic annihilator consumer. It is handled by the same exact u test and removed if extraneous. Thus literal-zero labels do not invalidate the collision routine. After match removal no remaining giant is globally equal to a baby. A saturated evaluation then contains a nonunit individual difference that is NOT zero modulo N, so scanning that one evaluation yields a proper gcd. The promised consumer needs no T_ext fallback; if a separate fallback is used, its nonzero label and once-only charge remain necessary.

## Optimization and scope

The restricted giant/baby accounting is

    soft O(S*r+sqrt(N)/(nr)^(3/2)+S+1).

Integer r>=1 gives optimized upper cost

    soft O(S+1+N^(1/5)*(S/n)^(3/5)).

The report now includes the essential additive S ceiling term; S>=1 absorbs the displayed +1. A lone correct residue at n of order k^(1/3), or a genuinely covering S=O(k^(2/3)) palette at n=k, thus has a soft-k consumer. These are promises on actual FACTOR residues. An arbitrary odd-axis alias only supplies its own legal exponent/kernel clock residue and cannot be substituted as a P tag.

No correct palette, residue supplier, earlier controller termination or all-semiprime improvement follows from this review. The improved consumer threshold is valid and useful as a sharper acquisition target.
