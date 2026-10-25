# Exact integration review: selected-scalar acquisition packet

24 October 2026. **PASS.** Both frozen draft summaries faithfully integrate the two independently reviewed source reports. No draft correction is requested.

Exact draft pins:

- journal-append.md: `95d669d1252a7cdd2c70fa006e96454cf7d9ce1871cac126e693d683b1a84dbf`
- agents-append.md: `c6e61348516de2e882358c53bf32dd208922c13cd000e9fcb8e98a00e840c388`

All paths are under /tmp/semiprime-selected-scalar-acquisition-20261024/.

Exact source/review pairs read and verified:

- lattice-batching.md: `e7e9582f310c0d1dad8b59bf15d52b485a4cc92926e234b206bd1d6899f0a293`
- lattice-batching-review.md: `f09dd41a4df360d2f98369b408b197b491d028861d1cc71639e7221334441c70`
- literature.md: `6cd4ab03933c048f1490f5af2f8cb590a9740188e94188d518f00a0fe5516d68`
- literature-review.md: `0e61d23ad31eb800aec6a05812fb4653a6bf2b3194d6d897f36d8c3945556f6b`

## Structured-solver integration

The nilpotent Stein operator in the drafts is the actual operator supported by Khichane–Neiger's stated theorem. The effective-field/supplied-generators/RHS contract, alpha-dependent complexity and absence of generic-rank/random-preconditioner hypotheses match the source and independent primary review. No arbitrary cyclic Sylvester operator is imported.

The exact formula for D=(Bez(F,h)+e0e0^t)R, with h=G mod F, has the correct sign and reversal orientation. Its displayed generator has three columns; J>=3 satisfies the theorem's input constraint, and J<=2 is explicitly treated by direct fixed-size methods. For J>1 the first displaced column is h. Thus an arbitrary explicit generator for this PARTICULAR matrix already yields h in O(alpha J), correctly exposing its missing native input rather than proving a general representation lower bound. Once h is supplied, guarded polynomial gcd already supplies the old root consumer; the new solver is not counted as an additional query advance.

The coefficient classifier in the composite quadratic algebra is accurately summarized as unit/global-zero/proper-factor classification. It does not supply h or an unknown local field. The primary ECCC revision notice and its 28January2026 gap scope agree with the reviewed source; the border-composition/GCD results are not imported.

## Lattice integration

The polynomial group batching is genuinely initialized from public residues, offsets and m^-1, with monic degree delta<=g. The interval/bin/root-radius summary matches the complete source: epsilon=1/n, exact integer-root rounding, X_g=1 direct enumeration, every integer-root candidate validated, and no unknown factor or selected root supplied as input.

The grouped call count and balanced-bin expression are the source's SCHEDULED complete-search budget. Both drafts now explicitly distinguish it from actual runtime with early exit and make no Omega assertion on semiprimes. Polylogarithmic g is the range where the lattice degree/dimension work can be hidden in logarithms; the draft does not award polynomial grouping a free LLL call. The local square has no acquired c_local, and no bounded integer translation certificate follows merely from modular coefficient equality or q carries.

## Scope and preservation

Both drafts lead with no whole-query acquisition gain. The soft sqrt(JL), hence soft k^(3/2) bound at the stated native dimensions, is preserved. The all-semiprime sixth-rate goal, unconditional orientation and executable Lean bit-cost proof remain open. No new backend, numerical coverage evidence, strong output oracle or generic impossibility theorem is claimed.

The draft preservation instructions retain earlier prefixes, 270 frozen entries, HEAD and concurrent work, including the gated-DeltaNet proposal. This review checked mathematical integration and exact bytes only. It did not append shared documents, run the repository preservation validator, or certify the later validation result; those are root's separate final actions. No draft/source/shared file was changed by this review.
