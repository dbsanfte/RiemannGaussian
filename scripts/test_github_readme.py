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
SITE = "https://dbsanfte.github.io/RiemannGaussian/"


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
                # The working graph need not have been published yet. Serve
                # precisely this local image in the otherwise live GitHub DOM.
                # Published mode loads the image from the actual commit.
                if not published:
                    page.route("**/docs/zero-free-regions/comparison.svg*", lambda route:
                               route.fulfill(path=str(ROOT / "docs/zero-free-regions/comparison.svg"),
                                             content_type="image/svg+xml"))
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
                    article.evaluate("""(e, html) => {
                        const preview = document.createElement('article');
                        preview.id = 'github-readme-working-preview';
                        preview.className = e.className;
                        preview.style.width = `${e.clientWidth}px`;
                        preview.style.maxWidth = '100%';
                        preview.style.margin = '24px auto';
                        preview.innerHTML = html;
                        document.body.prepend(preview);
                    }""", rendered)
                    selector = "#github-readme-working-preview"
                    article = page.locator(selector)
                assert article.locator("h2").first.inner_text().strip() == "Proved Zero-Free Region"
                plot = article.locator("img[alt^='Zero-free region comparison:']")
                assert plot.count() == 1
                assert "docs/zero-free-regions/comparison.svg" in plot.locator("..").get_attribute("href")
                plot.evaluate("e => e.scrollIntoView({block: 'center'})")
                # Hydration can briefly replace the article with an image
                # whose intrinsic size is known before layout is visible.
                # Capture loaded-image and positive-layout evidence together.
                placement = page.wait_for_function("""selector => {
                    const e = document.querySelector(selector)?.querySelector(
                        "img[alt^='Zero-free region comparison:']");
                    if (!e || !e.complete || e.naturalWidth <= 0) return false;
                    const article = e.closest('article');
                    if (e.clientWidth <= 0 || article.clientWidth <= 0) return false;
                    const headings = article.querySelectorAll('h2');
                    const after = n => Boolean(e.compareDocumentPosition(n) & Node.DOCUMENT_POSITION_FOLLOWING);
                    return {width: e.clientWidth, available: article.clientWidth,
                        naturalWidth: e.naturalWidth, afterHeading: !after(headings[0]),
                        beforeNextHeading: after(headings[1]),
                        beforeFormula: after(article.querySelector('math-renderer'))};
                }""", arg=selector).json_value()
                assert 0 < placement["width"] <= placement["available"] + 1, placement
                assert placement["afterHeading"] and placement["beforeNextHeading"] and placement["beforeFormula"], placement
                page.screenshot(path=str(output / f"zero-free-graph-{width}.png"))
                math = article.locator("math-renderer")
                expected = len(re.findall(r"^```math$", readme, re.M))
                assert expected > 0
                assert math.count() >= expected, "README math blocks were lost"
                page.wait_for_function("""selector => {
                    const nodes = document.querySelector(selector).querySelectorAll('math-renderer');
                    return nodes.length && [...nodes].every(e =>
                        e.querySelector('math, mjx-container, .flash-error'));
                }""", arg=selector)
                errors = math.locator(".flash-error, merror, [data-mml-node='merror']").all_text_contents()
                for i in range(math.count()):
                    frame = math.nth(i).locator("xpath=ancestor::table[1]")
                    (frame if frame.count() else math.nth(i)).evaluate(
                        "e => e.scrollIntoView({block: 'center'})",
                    )
                    # A viewport capture survives GitHub replacing a rendered
                    # element while its page hydrates; assertions use locators.
                    page.screenshot(path=str(output / f"math-{width}-{i + 1}.png"))
                assert not errors, f"GitHub math renderer errors: {errors}"
                boxes = math.locator("menclose[notation='box'], [data-mml-node='menclose']").count()
                assert boxes == readme.count(r"\boxed{"), "A mathematical box was lost"
                frames = math.evaluate_all("""els => els.filter(e =>
                    e.querySelector("menclose[notation='box'], [data-mml-node='menclose']")
                ).map(e => {
                    const td = e.closest('td');
                    return td ? parseFloat(getComputedStyle(td).borderTopWidth) : 0;
                })""")
                assert all(border > 0 for border in frames), "A visible formula frame was lost"
                tables = math.evaluate_all("""els => els.map(e => e.closest('table'))
                    .filter(Boolean).map(e => ({width: e.clientWidth, scroll: e.scrollWidth}))""")
                assert all(s["scroll"] <= s["width"] + 1 for s in tables), tables
                sizes = math.evaluate_all("""els => els.map(e => ({
                    width: e.clientWidth, scroll: e.scrollWidth
                }))""")
                assert all(s["scroll"] <= s["width"] + 1 for s in sizes), sizes
                # Published headings also have an accessible permalink link.
                cta = article.locator(f"h3 a[href='{SITE}']")
                assert cta.count() == 1
                assert "Open the interactive theorem explorer" in cta.inner_text()
                preview = article.locator("a img[alt^='Click to explore']")
                assert preview.count() == 1
                assert preview.locator("..").get_attribute("href") == SITE
                checks.append({"width": width, "mathBlocks": math.count(), "boxes": boxes,
                               "errors": errors, "sizes": sizes, "frameBorders": frames,
                               "frameSizes": tables,
                               "zeroFreeGraph": placement,
                               "explorerLinks": "valid"})
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
