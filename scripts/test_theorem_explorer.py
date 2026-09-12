#!/usr/bin/env python3
"""Exercise the real browser, including source lines and mobile interactions."""
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import argparse
import json
import threading
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, *_args):
        pass


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    server = ThreadingHTTPServer(("127.0.0.1", 0), partial(QuietHandler, directory=str(ROOT)))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    origin = f"http://127.0.0.1:{server.server_port}"
    url = origin + "/docs/theorem-explorer/"
    errors, checks = [], []
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch()
            page = browser.new_page(viewport={"width": 1600, "height": 1000}, device_scale_factor=1)
            page.on("pageerror", lambda error: errors.append(str(error)))
            page.goto(url)
            page.wait_for_function("window.PROOF_VIEW && window.PROOF_VIEW.visible.size > 5")
            assert page.locator(".zone-label", has_text="Gaussian heat").count()
            assert page.locator(".zone-label", has_text="Suzuki machinery").count()
            root = page.evaluate("PROOF_VIEW.endpoint.roots[0]")
            node = page.locator(f'[data-node="{root}"]')
            initial = page.evaluate("PROOF_VIEW.visible.size")
            page.screenshot(path=str(output / "desktop-overview.png"))
            node.hover()
            assert page.locator("#tooltip").is_visible()
            assert "ZetaGaussianBandExclusion.exact_strip" in page.locator("#tooltip").inner_text()
            node.click()
            assert page.locator("#details").is_visible()
            assert "450000" in page.locator("#details pre").inner_text()
            assert "Quot.sound" in page.locator("#details").inner_text()
            with page.expect_popup() as opened:
                page.locator("#details .source-button").click()
            source = opened.value
            source.wait_for_selector(".source-line:target")
            assert "theorem exact_strip" in source.locator(".source-line:target").inner_text()
            source_line = page.evaluate("PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]].source.line")
            assert source.url.endswith(f"#L{source_line}")
            source.close()
            checks.append("hover, statement, axiom metadata and exact source line")
            page.locator("#expand-deps").click()
            assert page.evaluate("PROOF_VIEW.visible.size") > initial
            page.screenshot(path=str(output / "theorem-details.png"))
            page.locator("#close-details").click()
            page.locator("#overview").click()
            before = page.locator("#zoom-value").inner_text()
            page.locator("#zoom-in").click()
            assert page.locator("#zoom-value").inner_text() != before
            graph = page.locator("#graph").bounding_box()
            before = page.locator("#world").get_attribute("transform")
            page.mouse.move(graph["x"] + 9, graph["y"] + 100)
            page.mouse.down(); page.mouse.move(graph["x"] + 99, graph["y"] + 140, steps=5); page.mouse.up()
            assert page.locator("#world").get_attribute("transform") != before
            before = page.locator("#zoom-value").inner_text()
            page.mouse.wheel(0, -180)
            page.wait_for_timeout(100)
            assert page.locator("#zoom-value").inner_text() != before
            page.locator("#fit").click()
            checks.append("button zoom, wheel zoom and pointer pan")
            # Click a real hit-tested point on a collapsed dependency curve.
            point = page.evaluate("""() => {
              for (const el of document.querySelectorAll('[data-edge]')) {
                const path = el.querySelector('.edge-hit');
                for (const ratio of [.3,.5,.7]) {
                  const p = path.getPointAtLength(path.getTotalLength()*ratio).matrixTransform(path.getScreenCTM());
                  if (document.elementFromPoint(p.x,p.y)?.closest('[data-edge]') === el) return {x:p.x,y:p.y};
                }
              }
            }""")
            assert point
            page.mouse.click(**point)
            assert "reference step" in page.locator("#details h2").inner_text()
            page.locator("#expand-path").click()
            page.locator("#overview").click()
            page.locator('[data-family="suzuki"]').click()
            assert page.evaluate("PROOF_VIEW.visible.size") > initial
            assert page.locator('[data-family="suzuki"]').get_attribute("aria-pressed") == "true"
            checks.append("witnessed edge inspection, path expansion and coloured family expansion")
            page.locator("#search").fill("GaussianStripProfile.source_lower")
            page.locator(".search-result").first.click()
            assert "GaussianStripProfile.source_lower" in page.locator("#details .decl-name").inner_text()
            saved = page.url
            page.reload()
            page.wait_for_selector("#details:not([hidden])")
            assert page.url == saved
            page.locator("#endpoint").select_option("union")
            assert "maximum" in page.locator("#scope-text").inner_text()
            page.locator("#all-steps").click()
            assert page.evaluate("PROOF_VIEW.visible.size") > 1000
            checks.append("search, permalink restoration, endpoint switch and full theorem view")
            page.locator("#overview").click()
            page.locator("#help-button").click()
            assert page.locator("#help").is_visible()
            page.keyboard.press("Escape")
            assert not page.locator("#help").is_visible()
            page.keyboard.press("/")
            assert page.locator("#search").evaluate("el => el === document.activeElement")
            checks.append("keyboard navigation and accessible help dialog")
            # File URLs must work too: unpublished theorem files are not on GitHub yet.
            offline = browser.new_page()
            offline.goto((ROOT / "docs/theorem-explorer/index.html").as_uri())
            offline.wait_for_function("window.PROOF_VIEW")
            assert offline.locator(".node").count() > 5
            offline.close()
            checks.append("offline file preview without a web server or CDN")
            published = browser.new_page()
            fake_sha = "0123456789abcdef0123456789abcdef01234567"
            published.route("**/release.js", lambda route: route.fulfill(content_type="application/javascript", body="window.PROOF_RELEASE=" + json.dumps({"revision": fake_sha, "runUrl":"https://github.com/dbsanfte/RiemannGaussian/actions/runs/123"}) + ";"))
            published.goto(url)
            published.wait_for_function("window.PROOF_VIEW")
            published.locator("#terminal").click()
            expected_source = f"https://github.com/dbsanfte/RiemannGaussian/blob/{fake_sha}/RiemannGaussian/ZetaGaussianBandExclusion.lean#L{source_line}"
            assert published.locator("#details .source-button").get_attribute("href") == expected_source
            assert published.locator("#revision-link").get_attribute("href").endswith("/runs/123")
            published.close()
            checks.append("published source links pinned to the verified commit and CI run")
            mobile = browser.new_context(viewport={"width": 390, "height": 844}, is_mobile=True, has_touch=True, device_scale_factor=1)
            phone = mobile.new_page()
            phone.on("pageerror", lambda error: errors.append(str(error)))
            phone.goto(url)
            phone.wait_for_function("window.PROOF_VIEW")
            assert phone.evaluate("document.documentElement.scrollWidth <= innerWidth")
            phone.locator("#search").fill("ZetaGaussianBandExclusion.exact_strip")
            phone.locator(".search-result").first.tap()
            assert phone.locator("#details").is_visible()
            phone.screenshot(path=str(output / "mobile-details.png"))
            phone.locator("#close-details").tap()
            node = phone.locator(f'[data-node="{root}"]')
            node.tap()
            assert phone.locator("#details").is_visible(), "Touching a theorem must open its inspector"
            phone.locator("#close-details").tap()
            phone.locator("#overview").tap()
            phone.screenshot(path=str(output / "mobile-overview.png"))
            checks.append("mobile layout, search and direct touch selection")
            # Exercise a true two-touch pinch via Chromium's input protocol.
            session = mobile.new_cdp_session(phone)
            rect = phone.locator("#graph").bounding_box()
            cy = rect["y"] + rect["height"] / 2
            before = phone.locator("#zoom-value").inner_text()
            session.send("Input.dispatchTouchEvent", {"type": "touchStart", "touchPoints": [{"x":150,"y":cy,"id":0},{"x":230,"y":cy,"id":1}]})
            session.send("Input.dispatchTouchEvent", {"type": "touchMove", "touchPoints": [{"x":110,"y":cy,"id":0},{"x":270,"y":cy,"id":1}]})
            session.send("Input.dispatchTouchEvent", {"type": "touchEnd", "touchPoints": []})
            phone.wait_for_function("before => document.getElementById('zoom-value').textContent !== before", arg=before)
            checks.append("two-finger pinch zoom")
            mobile.close()
            browser.close()
        assert not errors, errors
        result = {"checks": checks, "browserErrors": errors, "screenshots": str(output)}
        (output / "browser-checks.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result, indent=2))
    finally:
        server.shutdown(); server.server_close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/theorem-explorer/browser-tests")
    run(parser.parse_args().output)
