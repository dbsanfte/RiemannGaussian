# Independent supplement and integration review

2026-10-16. Verdict: PASS. The immutable main proof-review-A.md is unchanged.

## Exact targets

- rational-approximation-barrier.md: 3450 bytes, SHA256 `40da69ad305c1446c032132ef38643e43681eb8180fad569ab1d3f36a2324741`.
- README.md: 2922 bytes, SHA256 `475c344ca69736d5cdc3cd42a20ea031893b44b1d7e81e997432779c5b05e384`.
- journal-entry.md: 3424 bytes, SHA256 `5013ea817285da1e3e8c2e41ac9a677f8ba84b1b4b21cae5c8e088a4e1227551`.

Main prerequisite remains pade-constant-recurrence.md7291/SHA256 `d749385717bca05f1cdb1bbe3e432b3571200b07e79902b64491a796739d6937`. Metadata remains source-pins.json1313/SHA256 `e94471eab58bd43ad292e3bcbe41d62181966d9ddb4cef2cb49f316226fd86a5`; all five dependencies were independently byte/hash checked in review A.

## Supplement proof

The four shifted denominator product has nonzero constant term. For numerator degree u and denominator degree v its cleared residual numerator has degree at most u+3v+1. Therefore assuming u+3v+1<=L makes the residual exactly zero from its order>=L+1 vanishing. The finite coefficient recursion then determines the rational series through L+v under ord(q)>L+v. Its coefficients beyond L through L+v vanish. P-QC has degree<=L+v because u<L and vanishes to higher order, giving the contradiction. This remains valid for v=0: agreement through L alone then already forces P=QC. Integer negation of the contradiction gives u+3v>=L exactly, with no off-by-one error.

The proof uses only finite precision and does not assert infinite uniqueness past the unknown finite q-order. Arbitrary characteristic and inseparability cause no issue. The canonical bound16m²>L+v holds under the stated explicit bound on v; eventual u,v=O(m polylog m) satisfies it and violates u+3v>=L. The constant-recurrence specialization u<=r-1,v<=r gives the main4r<=L exclusion. None of these degree conclusions prices succinct high-degree circuits.

## Integration claims and provenance

The README and entry faithfully state the complete finite-stream recurrence obstruction, effective-order convention, arbitrary advised field coefficients and both-field applications. The original qualified source and the latest all-semiprime setup supply the exact local q-order premise, the latter only on its certified no-factor branch. No coverage transfer or factor acquisition is inferred from this obstruction. The earlier coefficient identity, chirp, small-order obstruction and standard Pade/denominator-clearing methods are credited. The sharper four-shift finite-stream application is distinguished without an absolute priority claim.

Both documents explicitly retain the unchanged soft m^(3/2) query bound and the missing soft-m whole-family query/Lean objective. The weighted degree corollary concerns the full Taylor stream, not a rational interpolant through the selected query values. General q-dependent recurrences, multivariate/vector state, another stream, nonlinear representation and direct scalar norms remain outside. No upper complexity bound is converted into an operation lower bound.

## Planned links

Under docs/research-evidence/semiprime-pade-obstruction-20261016/, README links reports/pade-constant-recurrence.md and reports/rational-approximation-barrier.md point to the two exact reviewed reports. Its reviews/ directory reference matches the planned placement of the three review artifacts. The journal link research-evidence/semiprime-pade-obstruction-20261016/README.md is correct relative to docs/. This is planned-layout verification, not an assembled inventory audit.

No correction requested. No repository files were edited, no prior review was mutated and no builds were run.
