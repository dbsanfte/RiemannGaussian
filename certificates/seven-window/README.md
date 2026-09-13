# Proposed seven-window cover

`cover-proposal.json.gz` records an untrusted integer proposal for the
six-dimensional compact floor used by the candidate 6731/10000 zeta
simple-critical-zero certificate. It contains subdivision nodes, anchor
indices, signed curvature bounds and proposed integer Gram factors.

The data alone prove nothing. The generated Lean modules check every leaf
and every parent connection using the existing continuous soundness theorems.
The exact scalar and matrix checks use integers; floating-point numerical
search was used only to propose this data.

Generate the proposed proof sources with:

```bash
python3 scripts/generate_montgomery_taylor_cover.py \
  certificates/seven-window/cover-proposal.json.gz
```

The generated manifest under
`RiemannGaussian/CertificateData/MontgomeryTaylorCover/manifest.json` records
the proposal's SHA-256, exact domain, subdivision sizes and build groups.
See [status and verification](../../docs/numerical-certificate.md) for the
optional build, current proof status and mathematical provenance.
