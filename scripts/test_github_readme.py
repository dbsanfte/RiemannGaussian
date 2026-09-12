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
                response = page.goto(url, wait_until="networkidle", timeout=60000)
                assert response.status == 200, f"GitHub returned HTTP {response.status}"
                article = page.locator("article.markdown-body").first
                article.wait_for()
                page.wait_for_function("Boolean(customElements.get('math-renderer'))")
                # Replace only this browser's DOM with GitHub's rendering of
                # the working file. The live custom element performs its real
                # HTML decode, TeX conversion, sanitization and error handling.
                if rendered is not None:
                    article.evaluate("(e, html) => { e.innerHTML = html; }", rendered)
                math = article.locator("math-renderer")
                expected = len(re.findall(r"^```math$", readme, re.M))
                assert expected > 0
                assert math.count() >= expected, "README math blocks were lost"
                page.wait_for_function("""() => {
                    const nodes = document.querySelectorAll('article.markdown-body math-renderer');
                    return nodes.length && [...nodes].every(e =>
                        e.querySelector('math, mjx-container, .flash-error'));
                }""")
                errors = math.locator(".flash-error, merror, [data-mml-node='merror']").all_text_contents()
                for i in range(math.count()):
                    frame = math.nth(i).locator("xpath=ancestor::table[1]")
                    (frame if frame.count() else math.nth(i)).screenshot(
                        path=str(output / f"math-{width}-{i + 1}.png"),
                    )
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
                cta = article.get_by_role("link", name=re.compile("Open the interactive theorem explorer"))
                assert cta.count() == 1 and cta.get_attribute("href") == SITE
                preview = article.locator("a img[alt^='Click to explore']")
                assert preview.count() == 1
                assert preview.locator("..").get_attribute("href") == SITE
                checks.append({"width": width, "mathBlocks": math.count(), "boxes": boxes,
                               "errors": errors, "sizes": sizes, "frameBorders": frames,
                               "frameSizes": tables,
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
