# Discover reusable components in the QRH Catalogue

The [QRH Catalogue](https://github.com/HaileyStorm/QRH-Catalogue) is a public
cross-project index of mathematical and Lean components. Its
[linked directory](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/DIRECTORY.md)
covers the full public inventory. Search by mathematical topic, module,
declaration name or repository; some historical Lean declarations use their
original record kinds rather than `formal-component`.

For reusable formal-component records, the standard-library Python CLI supports:

```sh
python catalogue.py query --kind formal-component --json --limit 100
python catalogue.py query Gaussian --kind formal-component
python catalogue.py query Montgomery --kind formal-component
python catalogue.py show --id LEAN-RG-f5fd3ddb-RiemannGaussian.ZetaSquarefreeEulerQuadratic
```

These commands run from a local copy of the catalogue. Increase the result
limit or narrow the search terms to explore more records. The public catalogue
contains metadata and source pointers; it is not a single importable Lean
library and does not add a dependency to this project.

Selected RiemannGaussian entries retain the source revision
`f5fd3ddb407972f9ca65298fbe9be3225fe06635`, including these stable module IDs:

- [LEAN-RG-f5fd3ddb-RiemannGaussian.GaussianXiLogDerivativeGrowth](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-gaussianxilogderivativegrowth-b430d3c9a3)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.Hybrid.EtaSupportGapPhaseGram](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-hybrid-etasupportgapphasegram-73061ba605)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.Hybrid.EtaSupportGapPhaseCoercivity](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-hybrid-etasupportgapphasecoerciv-6a82f043f5)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.ZetaSquarefreeEulerQuadratic](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-zetasquarefreeeulerquadratic-ac2b3b2b70)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.DirichletHigherDerivativeBound](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-dirichlethigherderivativebound-02a6c13bec)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.UniformDirichletPowerBound](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-uniformdirichletpowerbound-237dcf5b54)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.MontgomeryVaughan.Final](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-montgomeryvaughan-final-40519663c7)
- [LEAN-RG-f5fd3ddb-RiemannGaussian.ZetaQuasiRHOpenAI](https://github.com/HaileyStorm/QRH-Catalogue/blob/44824138c975e34552d35e314cda60b32ad346b5/generated/records/0129.md#lean-rg-f5fd3ddb-riemanngaussian-zetaquasirhopenai-36b90e471d)

Follow each exact pinned declaration and expand its definitions and hypotheses
before reuse. In particular, the squarefree Euler diagonalization retains
complex products rather than squared norms, phase-Gram coercivity retains its
width and dimension conditions, and Montgomery–Vaughan here has explicit
diagonal constant `13` and bilinear constant `26`.

Mathematical status, independent review and formal verification are separate
fields. The catalogue distinguishes source-reported checks from independent
typechecking, axiom audits and kernel checks tied to an exact revision.
A catalogue entry or a successful metadata validation is not proof acceptance.
Source attribution and licensing remain attached to each component, including
the Anthropic notices on the adapted Montgomery–Vaughan development. Cite the
original source alongside a catalogue ID and a commit-pinned catalogue link.

The catalogue's contribution guide explains how to add or correct records.
This resource link makes no claim that RH is complete or that another
project's theorem applies without its original hypotheses.
