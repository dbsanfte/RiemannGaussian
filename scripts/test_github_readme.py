#!/usr/bin/env python3
"""Check README math with GitHub's actual Markdown and browser renderers.

The default previews the working file in a local browser DOM on GitHub;
it does not write to GitHub. --published checks the exact HEAD README page.
Requires authenticated gh and the project's pinned Playwright installation.
"""
import argparse
import base64
import json
from pathlib import Path
import re
import subprocess

from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "dbsanfte/RiemannGaussian"
PROOF_SITE = "https://dbsanfte.github.io/RiemannGaussian/rh-proof/"
ORIGINAL_PROOF = "https://alpo.ge/remark.pdf"
LEAN_PROOF = "scripts/CheckAlpogePrincipalArchivedGeometryRH.lean#L710"
ARCHIVE_WORKFLOW = f"https://github.com/{REPOSITORY}/actions/workflows/alpoge_archive_ci.yml"


def gh(*args, payload=None):
    return subprocess.run(
        ["gh", "api", *args], cwd=ROOT, input=payload, text=True,
        check=True, capture_output=True,
    ).stdout


def run(output, published):
    output.mkdir(parents=True, exist_ok=True)
    readme = (ROOT / "README.md").read_text()
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
    ).strip()
    if published:
        remote = json.loads(gh(
            "--method", "GET", f"repos/{REPOSITORY}/readme",
            "-f", f"ref={revision}",
        ))
        assert base64.b64decode(remote["content"]).decode() == readme, (
            "The working README differs from the published commit"
        )
        url = f"https://github.com/{REPOSITORY}/tree/{revision}"
        rendered = None
    else:
        url = f"https://github.com/{REPOSITORY}"
        rendered = gh("--method", "POST", "markdown", "--input", "-", payload=json.dumps({
            "text": readme, "mode": "gfm", "context": REPOSITORY,
        }))
        (output / "markdown.html").write_text(rendered)

    checks = []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        try:
            for width in (1280, 390):
                page = browser.new_page(viewport={"width": width, "height": 1000})
                # GitHub can keep background requests open after the README is
                # ready. Wait for the actual DOM and math below, not network idle.
                response = page.goto(url, wait_until="domcontentloaded", timeout=60000)
                assert response.status == 200, f"GitHub returned HTTP {response.status}"
                article = page.locator("article.markdown-body").first
                article.wait_for()
                page.wait_for_function("Boolean(customElements.get('math-renderer'))")
                selector = "article.markdown-body"
                # Keep the working preview outside GitHub's React-managed root,
                # so hydration cannot replace it with the published README.
                # The real custom element and GitHub styles still render it.
                if rendered is not None:
                    # Select and measure a visible source atomically: mobile
                    # hydration can otherwise leave the detached preview
                    # permanently fixed at a transient zero-pixel width.
                    page.wait_for_function("""html => {
                        const e = [...document.querySelectorAll('article.markdown-body')]
                            .find(node => node.clientWidth > 0 && node.getClientRects().length);
                        if (!e) return false;
                        const preview = document.createElement('article');
                        preview.id = 'github-readme-working-preview';
                        preview.className = e.className;
                        preview.style.width = `${e.clientWidth}px`;
                        preview.style.maxWidth = '100%';
                        preview.style.margin = '24px auto';
                        preview.innerHTML = html;
                        document.body.prepend(preview);
                        return true;
                    }""", arg=rendered)
                    selector = "#github-readme-working-preview"
                    article = page.locator(selector)
                headings = [text.strip() for text in article.locator("h2").all_inner_texts()]
                assert headings == [
                    "A Shorter Lean Proof of the Riemann Hypothesis",
                    "Verify the Shorter Proof", "Current Proof Shortening Direction",
                    "Related Research", "Native Library", "License",
                ], headings
                assert "Current RH Proof Direction" not in article.inner_text()
                assert "RH remains open" not in article.inner_text()
                attribution = article.get_by_role("link", name="Alpöge’s original announcement", exact=True)
                assert attribution.get_attribute("href") == ORIGINAL_PROOF
                theorem = article.get_by_role("link", name="Checked Lean theorem", exact=True)
                assert theorem.get_attribute("href").endswith(LEAN_PROOF)
                archive_badge = article.get_by_role("img", name="Archive RH CI", exact=True)
                assert archive_badge.locator("..").get_attribute("href") == ARCHIVE_WORKFLOW
                archive_link = article.get_by_role("link", name="Archive verification workflow", exact=True)
                assert archive_link.get_attribute("href").endswith(".github/workflows/alpoge_archive_ci.yml")
                explorer = article.get_by_role("link", name="Explore the shorter proof", exact=True)
                assert explorer.get_attribute("href") == PROOF_SITE
                content = ' '.join(article.inner_text().split())
                assert "Levent Alpöge, working with Claude" in content
                assert all(term in content for term in ("165,070", "10,104 modules (5.8%)", "175,174-module"))
                forward = article.get_by_role("link", name="Forward implication", exact=True)
                assert forward.get_attribute("href").endswith("scripts/CheckAlpogeFixedPrimeBandCorner.lean")
                tail = article.get_by_role("link", name="Direct tail implication", exact=True)
                assert tail.get_attribute("href").endswith("scripts/CheckAlpogeFixedPrimeBandCentered.lean")
                rational = article.get_by_role("link", name="Rational window test", exact=True)
                assert rational.get_attribute("href").endswith("scripts/CheckAlpogeFixedPrimeBandMoments.lean")
                criterion = article.get_by_role("link", name="Exact window criterion", exact=True)
                assert criterion.get_attribute("href").endswith("scripts/CheckAlpogeFixedPrimeBandCenteredBounds.lean")
                assert "arbitrarily late square windows" in content
                assert "5,337 modules in total, including 27 selected Alpöge modules" in content
                assert "Standalone kernel replay" in content
                assert "propext" in content and "Classical.choice" in content and "Quot.sound" in content

                expected = len(re.findall(r"^```math$", readme, re.M))
                math = article.locator("math-renderer")
                assert expected > 0 and math.count() >= expected, "README math blocks were lost"
                page.wait_for_function("""selector => {
                    const nodes = document.querySelector(selector)?.querySelectorAll('math-renderer');
                    return nodes?.length && [...nodes].every(e =>
                        e.clientWidth > 0 && e.querySelector('math, mjx-container, .flash-error'));
                }""", arg=selector)
                errors = math.locator(".flash-error, merror, [data-mml-node='merror']").all_text_contents()
                assert not errors, f"GitHub math renderer errors: {errors}"
                sizes = math.evaluate_all("""els => els.map(e => ({
                    width: e.clientWidth, scroll: e.scrollWidth
                }))""")
                assert all(0 < s["width"] and s["scroll"] <= s["width"] + 1 for s in sizes), sizes
                first_formula = math.first
                assert first_formula.evaluate("""e => {
                    const headings = e.closest('article').querySelectorAll('h2');
                    return Boolean(headings[0].compareDocumentPosition(e) & Node.DOCUMENT_POSITION_FOLLOWING)
                        && Boolean(e.compareDocumentPosition(headings[1]) & Node.DOCUMENT_POSITION_FOLLOWING);
                }"""), "The RH formula must appear in the headline section"
                article.get_by_role("heading", name=headings[0], exact=True).scroll_into_view_if_needed()
                page.screenshot(path=str(output / f"rh-proof-{width}.png"))
                checks.append({"width": width, "mathBlocks": math.count(), "errors": errors,
                               "sizes": sizes, "headline": headings[0], "sourceAttribution": ORIGINAL_PROOF,
                               "leanProof": theorem.get_attribute("href"), "archiveCI": ARCHIVE_WORKFLOW,
                               "relatedResearchFollowsProof": True})
                page.close()
        finally:
            browser.close()
    report = {"mode": "published" if published else "working preview",
              "revision": revision, "url": url, "checks": checks}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--published", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/github-readme")
    args = parser.parse_args()
    run(args.output, args.published)
