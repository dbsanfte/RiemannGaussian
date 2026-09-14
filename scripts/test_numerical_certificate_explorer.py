#!/usr/bin/env python3
"""Exercise the certificate's real UI and provenance, locally or after publication."""
import argparse
from functools import partial
from http.server import ThreadingHTTPServer
import json
from pathlib import Path
import subprocess
import threading

from playwright.sync_api import sync_playwright
from test_theorem_explorer import QuietHandler

ROOT = Path(__file__).resolve().parents[1]


def run(output, url=None):
    output.mkdir(parents=True, exist_ok=True)
    server = None
    if not url:
        server = ThreadingHTTPServer(("127.0.0.1", 0), partial(QuietHandler, directory=str(ROOT)))
        threading.Thread(target=server.serve_forever, daemon=True).start()
        url = f"http://127.0.0.1:{server.server_port}/docs/numerical-certificate-explorer/"
    published = server is None
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    checks, errors = [], []
    expected_verification = json.loads((ROOT / "docs/numerical-certificate/verification.json").read_bytes())
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch()
            for width in (1600, 390):
                page = browser.new_page(viewport={"width": width, "height": 1000})
                page.on("pageerror", lambda error: errors.append(str(error)))
                response = page.goto(url, wait_until="domcontentloaded")
                assert response.status == 200
                page.wait_for_function("window.PROOF_VIEW && PROOF_VIEW.visible.size > 5")
                assert "67.31%" in page.locator("h1").inner_text()
                assert page.evaluate("PROOF_VIEW.endpoint.id") == "cumulative"
                if published:
                    assert page.evaluate("PROOF_RELEASE.revision") == revision
                    assert "Presentation commit" in page.locator("#revision-link").inner_text()
                assert page.locator(".zone-label").count() > 0
                assert "unevaluated" in page.locator("#scope-text").inner_text()
                page.screenshot(path=str(output / f"overview-{width}.png"))
                root = page.evaluate("PROOF_VIEW.endpoint.roots[0]")
                data = page.evaluate("PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]]")
                node = page.locator(f'[data-node="{root}"]')
                node.hover()
                assert page.locator("#tooltip").is_visible()
                assert data["name"] in page.locator("#tooltip").inner_text()
                node.click()
                assert page.locator("#details pre").inner_text().strip() == data["statement"].strip()
                assert "Quot.sound" in page.locator("#details").inner_text()
                source_url = page.locator("#details .source-button").get_attribute("href")
                assert source_url.endswith(f"#L{data['source']['line']}")
                if published:
                    assert f"/blob/{revision}/{data['source']['path']}" in source_url
                else:
                    with page.expect_popup() as opened:
                        page.locator("#details .source-button").click()
                    source = opened.value
                    source.wait_for_selector(".source-line:target")
                    assert "theorem " + data["id"].split(".")[-1] in source.locator(".source-line:target").inner_text()
                    source.close()
                assert page.locator("#details a", has_text="Successful exhaustive certificate run").get_attribute("href") == expected_verification["runUrl"]
                page.screenshot(path=str(output / f"terminal-{width}.png"))
                page.locator("#close-details").click()
                before = page.locator("#zoom-value").inner_text()
                page.locator("#zoom-in").click()
                assert page.locator("#zoom-value").inner_text() != before
                page.locator("#fit").click()
                page.locator("#search").fill("CertificateData.Cover.checked")
                page.locator(".search-result").first.click()
                assert "Generated-data proof boundary" in page.locator("#details").inner_text()
                assert "separately linked optional certificate workflow" in page.locator("#details").inner_text()
                page.locator("#close-details").click()
                page.locator("#endpoint").select_option("dyadic")
                assert page.evaluate("PROOF_VIEW.endpoint.id") == "dyadic"
                page.locator("#endpoint").select_option("exact")
                assert page.evaluate("PROOF_VIEW.endpoint.id") == "exact"
                page.locator("#scope-more").click()
                assert "Successful exhaustive certificate run" in page.locator("#details").inner_text()
                assert "explicit boundary leaves" in page.locator("#details").inner_text()
                for asset in ("audit.json", "certificate-audit.json", "hosted-audit.json", "snapshot.json", "verification.json", "families.json", "preview.svg"):
                    fetched = page.request.get(url + asset)
                    assert fetched.status == 200, asset
                hosted = page.request.get(url + "hosted-audit.json").json()
                verification = page.request.get(url + "verification.json").json()
                assert hosted["inputSha256"] == verification["inputSha256"]
                assert verification["conclusion"] == "success"
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth + 1")
                checks.append({"width": width, "source": source_url,
                               "hoverAndStatement": True, "dataBoundary": True,
                               "endpointsAndZoom": True, "fullAuditLinks": True,
                               "exhaustiveRun": verification["runUrl"]})
                page.close()
            browser.close()
    finally:
        if server:
            server.shutdown()
            server.server_close()
    assert not errors, errors
    report = {"url": url, "revision": revision, "published": published, "checks": checks, "errors": errors}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--url", help="Check the deployed site against the exact current HEAD")
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/numerical-certificate-explorer/browser")
    args = parser.parse_args()
    run(args.output, args.url)
