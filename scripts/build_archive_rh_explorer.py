"""Render the shorter RH proof and its local Lean imports for Pages."""

from html import escape
import re

from verify_alpoge_archive_rh import ENDPOINT, IMPORT, ROOT, module_path


REPOSITORY = "https://github.com/dbsanfte/RiemannGaussian"
WORKFLOW = REPOSITORY + "/actions/workflows/alpoge_archive_ci.yml"


def local_imports():
    """Collect direct imports between the endpoint's repository modules."""
    modules = {}

    def visit(module):
        source = ROOT / "scripts" / module_path(module, ".lean")
        if module in modules or not source.is_file():
            return
        imports = [
            dep for line in IMPORT.findall(source.read_text())
            for dep in line.partition("--")[0].split()
            if (ROOT / "scripts" / module_path(dep, ".lean")).is_file()
        ]
        modules[module] = imports
        for dep in imports:
            visit(dep)

    visit(ENDPOINT)
    return modules


def source_link(module, label, line=None):
    path = (module_path(module, ".lean").as_posix())
    anchor = f"#L{line}" if line else ""
    ref = escape(f"scripts/{path}{anchor}", quote=True)
    return f'<a data-proof-source="{ref}" href="{REPOSITORY}/blob/main/{ref}">{escape(label)}</a>'


def declaration_link(module, name, label):
    lines = (ROOT / "scripts" / module_path(module, ".lean")).read_text().splitlines()
    declaration = re.compile(r"^theorem " + re.escape(name) + r"\b")
    locations = [line for line, text in enumerate(lines, 1) if declaration.match(text)]
    assert len(locations) == 1, f"Expected one declaration of {module}.{name}"
    return source_link(module, label, locations[0])


def render():
    modules = local_imports()
    archive_notes = "docs/research-evidence/alpoge-archive-rh/README.md"
    rank_module = "CheckAlpogePrincipalArchivedBundleRank"
    row_module = "CheckAlpogePrincipalArchivedBundleRows"
    rank = declaration_link(rank_module, "principal_lift_rank_of_archived_bundles", "Lift-rank bound")
    comparisons = declaration_link(row_module, "rh_of_principal_archived_bundle_rows", "Comparisons on the selected family")
    covolume = declaration_link(ENDPOINT, "principal_archived_covolume", "Hodge covolume bound")
    grid = declaration_link(ENDPOINT, "rh_of_principal_archived_grid", "Common period grid")
    window = declaration_link(ENDPOINT, "principal_archived_window", "Principal height-401 window")
    theorem = declaration_link(ENDPOINT, "rh_of_principal_archived_geometry", "Final Lean declaration")
    module_sections = []
    for module, imports in modules.items():
        edges = "".join(f"<li>{source_link(dep, dep)}</li>" for dep in imports)
        contents = f"<ul>{edges}</ul>" if edges else "<p>This module imports archive or library code.</p>"
        module_sections.append(
            f'<li data-module="{escape(module, quote=True)}"><details>'
            f"<summary>{escape(module)}</summary><p>{source_link(module, 'Open module source')}</p>"
            f"{contents}</details></li>"
        )
    return f'''<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="description" content="Explore the shorter Lean proof of RH and its local imports.">
  <title>A Shorter Lean Proof of the Riemann Hypothesis · RiemannGaussian</title>
  <script>
    function openNativeEndpoint() {{
      const fragment = new URLSearchParams(window.location.hash.slice(1));
      if (fragment.has("endpoint")) {{
        window.location.replace("native.html" + window.location.search + window.location.hash);
      }}
    }}
    openNativeEndpoint();
    window.addEventListener("hashchange", openNativeEndpoint);
  </script>
  <script src="release.js" defer></script>
  <style>
    :root {{ color-scheme: light dark; font: 1rem/1.55 system-ui, sans-serif; }}
    body {{ margin: 0; }}
    main {{ width: min(70rem, calc(100% - 2rem)); margin: 2.5rem auto; }}
    header {{ max-width: 54rem; }}
    h1 {{ font-family: Georgia, serif; font-size: clamp(2rem, 6vw, 3.75rem); line-height: 1.12; }}
    h2 {{ margin-block: 0 .45rem; }}
    h3 {{ margin: 0; }}
    p {{ margin: .55rem 0; }}
    a {{ text-underline-offset: .2em; }}
    .steps {{ margin: 2.5rem 0; }}
    .step {{ border: 1px solid GrayText; border-radius: .65rem; padding: 1rem 1.15rem; }}
    .result {{ border-width: 2px; }}
    .branches {{ display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 1rem; }}
    .arrow {{ text-align: center; margin-block: .35rem; font-size: 1.45rem; }}
    summary {{ cursor: pointer; font-weight: 600; overflow-wrap: anywhere; }}
    ul {{ padding-left: 1.35rem; }}
    li {{ margin-block: .35rem; overflow-wrap: anywhere; }}
    footer {{ margin-top: 2rem; }}
    @media (max-width: 42rem) {{ .branches {{ grid-template-columns: 1fr; }} }}
  </style>
</head>
<body>
<main>
  <header>
    <a href="{REPOSITORY}">RiemannGaussian</a>
    <h1>A Shorter Lean Proof of the Riemann Hypothesis</h1>
    <p>The principal-character optimisation uses <strong>165,070 archive modules</strong>.
      It saves <strong>10,104 modules (5.8%)</strong> from our earlier route.</p>
    <p>Underlying proof and Lean archive by <a href="https://alpo.ge/remark.pdf">Levent Alpöge, working with Claude</a>.</p>
  </header>
  <section class="steps" aria-label="Proof assembly">
    <article class="step">
      <h2>Pinned archive inputs</h2>
      <p>Alpöge’s archive supplies the representation theory, theta identities,
        Hodge estimates and Galois results. The archive imports are grouped here.</p>
      <p><a href="https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/9036e64326acf4acfae159b96664e9708445c1d1">Pinned public objects</a></p>
    </article>
    <div class="branches">
      <div>
        <div class="arrow" aria-hidden="true">↓</div>
        <article class="step">
          <h2>Principal geometric family</h2>
          <p>One selected family supports the lift-rank bound and the weighted,
            irreducibility, divisibility and spectral comparisons. A common
            theta period grid supplies the period estimates.</p>
          <ul><li>{rank}</li><li>{comparisons}</li><li>{covolume}</li><li>{grid}</li></ul>
        </article>
      </div>
      <div>
        <div class="arrow" aria-hidden="true">↓</div>
        <article class="step">
          <h2>Principal arithmetic window</h2>
          <p>The representation, cohomology and CM inputs give the
            height-401 window for the principal character. The window
            supplies the host used by the geometric family.</p>
          <p>{window}</p>
        </article>
      </div>
    </div>
    <div class="arrow" aria-hidden="true">↓</div>
    <article class="step result">
      <h2><code>RiemannHypothesis</code></h2>
      <p>The final theorem uses the principal window to supply the host
        required by the geometric construction. Lean 4.33.1 checked the closed
        statement and standalone kernel replay passed locally.</p>
      <p>{theorem} · <a href="{WORKFLOW}">Archive CI</a></p>
    </article>
  </section>
  <details id="local-imports">
    <summary>Direct imports among the {len(modules)} local Lean modules</summary>
    <p>Each module lists its direct repository imports. Archive and Mathlib
      imports are grouped outside this local graph.</p>
    <ul>{''.join(module_sections)}</ul>
  </details>
  <footer>
    <a data-proof-source="{archive_notes}" href="{REPOSITORY}/blob/main/{archive_notes}">Verification and source pins</a>
    · <a href="native.html">Native Gaussian–Suzuki theory</a>
  </footer>
</main>
<script>
document.addEventListener("DOMContentLoaded", () => {{
  const revision = window.PROOF_RELEASE?.revision;
  if (!revision) return;
  for (const link of document.querySelectorAll("[data-proof-source]")) {{
    link.href = "{REPOSITORY}/blob/" + revision + "/" + link.dataset.proofSource;
  }}
}});
</script>
</body>
</html>
'''.encode()
