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
            root_data = page.evaluate("PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]]")
            node = page.locator(f'[data-node="{root}"]')
            initial = page.evaluate("PROOF_VIEW.visible.size")
            page.screenshot(path=str(output / "desktop-overview.png"))
            node.hover()
            assert page.locator("#tooltip").is_visible()
            assert root_data["name"] in page.locator("#tooltip").inner_text()
            node.click()
            assert page.locator("#details").is_visible()
            assert root_data["statement"].strip() == page.locator("#details pre").inner_text().strip()
            assert "Quot.sound" in page.locator("#details").inner_text()
            with page.expect_popup() as opened:
                page.locator("#details .source-button").click()
            source = opened.value
            source.wait_for_selector(".source-line:target")
            declaration = root_data["source"]["declaration"].split(".")[-1]
            assert f"theorem {declaration}" in source.locator(".source-line:target").inner_text()
            source_line = root_data["source"]["line"]
            assert source.url.endswith(f"#L{source_line}")
            source.close()
            checks.append("hover, statement, axiom metadata and exact source line")
            # A terminal theorem can already have every direct ingredient
            # visible. Exercise expansion on a node with an actual hidden step.
            expandable = page.evaluate("""() => {
                const named = i => {
                    const n = PROOF_DATA.nodes[i];
                    return n.project && n.kind === 'theorem' && !n.generated;
                };
                return [...PROOF_VIEW.visible].find(i =>
                    PROOF_VIEW.model.nearest(i, named).some(d => !PROOF_VIEW.visible.has(d)));
            }""")
            assert expandable is not None
            page.locator("#close-details").click()
            page.locator(f'[data-node="{expandable}"]').click()
            page.locator("#expand-deps").click()
            assert page.evaluate("PROOF_VIEW.visible.size") > initial
            page.screenshot(path=str(output / "theorem-details.png"))
            page.locator("#close-details").click()
            page.locator("#overview").click()
            page.locator("#endpoint").select_option("retained-cost")
            page.wait_for_function("PROOF_VIEW.endpoint.id === 'retained-cost'")
            retained_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(retained_roots) == 6
            assert "320000" in page.locator("#scope-text").inner_text()
            for theorem in retained_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("improved curve retains the full cost, strict containment and original squarefree arithmetic radius")
            page.locator("#endpoint").select_option("explicit-band")
            page.wait_for_function("PROOF_VIEW.endpoint.id === 'explicit-band'")
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
            page.locator("#endpoint").select_option("multiplicity")
            assert "restricts multiple zeros" in page.locator("#scope-text").inner_text()
            multiplicity_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(multiplicity_roots) == 3
            for theorem in multiplicity_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("multiplicity endpoint exposes its location, comparison and eta-current roots with scope")
            page.locator("#endpoint").select_option("separation")
            assert "restricts clusters" in page.locator("#scope-text").inner_text()
            separation_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(separation_roots) == 3
            for theorem in separation_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("separation endpoint exposes both rectangle counts and the inverse-distance bound with scope")
            page.locator("#endpoint").select_option("filter-cost")
            assert "no independent signed bulk floor" in page.locator("#scope-text").inner_text()
            filter_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(filter_roots) == 3
            for theorem in filter_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("filter-cost endpoint separates the coefficient bound, reduction error and negative source")
            # Lean emits this helper locally, but the enclosing abbrev is
            # in Mathlib. Keep its audited dependency and its true source.
            helper = page.evaluate("PROOF_DATA.nodes.find(n => n.id === 'LSeries.logMul.eq_1')")
            assert helper["project"] and helper["generated"] and not helper["source"]["project"]
            page.locator("#search").fill("LSeries.logMul.eq_1")
            page.locator(".search-result").first.click()
            assert page.locator("#details .source-button").get_attribute("href") == helper["source"]["url"]
            assert "enclosing declaration" in page.locator("#details").inner_text()
            checks.append("locally emitted library helper links to its pinned external enclosing source")
            page.locator("#endpoint").select_option("prime-work")
            assert "not an upper bound on actual prime work" in page.locator("#scope-text").inner_text()
            prime_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(prime_roots) == 3
            for theorem in prime_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("prime-work endpoint distinguishes the actual arithmetic floor from the minorant ceiling")
            page.locator("#endpoint").select_option("prime-correlation")
            assert "finite-set floor criterion retains an explicit energy-gap hypothesis" in page.locator("#scope-text").inner_text()
            correlation_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(correlation_roots) == 5
            for theorem in correlation_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("prime-correlation endpoint retains the exact phase projection and distinguishes its conditional finite-set floor")
            page.locator("#endpoint").select_option("prime-reduction")
            assert "not an upper bound on the ordinary-prime energy" in page.locator("#scope-text").inner_text()
            reduction_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(reduction_roots) == 3
            for theorem in reduction_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("prime-reduction endpoint separates its proved remainder decay from the ordinary-prime energy target")
            page.locator("#endpoint").select_option("signed-budget")
            assert "signed clipped left mean remains the obstruction" in page.locator("#scope-text").inner_text()
            assert "no unclipped integral limit" in page.locator("#scope-text").inner_text()
            budget_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(budget_roots) == 3
            for theorem in budget_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("signed-budget endpoint preserves the exact left mean and labels its open source-beating estimate")
            page.locator("#endpoint").select_option("source-support")
            assert "visibility cutoffs, not zero-free boundaries" in page.locator("#scope-text").inner_text()
            assert "fixed finite zero window eventually contributes exactly zero" in page.locator("#scope-text").inner_text()
            assert "strictly positive source in adaptive geometry" in page.locator("#scope-text").inner_text()
            support_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(support_roots) == 6
            for theorem in support_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("source-support endpoint distinguishes cutoffs from zero exclusion and retains the full adaptive fixed-zero source inequality")
            page.locator("#endpoint").select_option("prime-discrepancy")
            assert "quadratic correlation tool" in page.locator("#scope-text").inner_text()
            assert "original linear carrier floor" in page.locator("#scope-text").inner_text()
            discrepancy_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(discrepancy_roots) == 5
            for theorem in discrepancy_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("prime-discrepancy endpoint retains all arithmetic roots and distinguishes diagonal decay from the open linear carrier floor")
            page.locator("#endpoint").select_option("lattice-carrier")
            assert "original normalized linear source remains minus its analytic multiplicity" in page.locator("#scope-text").inner_text()
            assert "independent cofinal signed lower bound" in page.locator("#scope-text").inner_text()
            lattice_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(lattice_roots) == 5
            for theorem in lattice_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("lattice-carrier endpoint retains signed sampling, full error bounds and the conditional original linear source")
            page.locator("#endpoint").select_option("vaughan-factors")
            assert "independent cofinal signed lower bound and RH remain open" in page.locator("#scope-text").inner_text()
            assert "No arbitrary-coefficient Type II estimate" in page.locator("#scope-text").inner_text()
            assert "Chebyshev prime-power density" in page.locator("#scope-text").inner_text()
            assert "floor(u^(-N)/(N+1))" in page.locator("#scope-text").inner_text()
            assert "entire nonsquarefree contribution" in page.locator("#scope-text").inner_text()
            assert "signed lower bound remains open" in page.locator("#scope-text").inner_text()
            vaughan_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(vaughan_roots) == 25
            assert "physical and divisor logarithms cancel" in page.locator("#scope-text").inner_text()
            assert "every moving finite probability mixture" in page.locator("#scope-text").inner_text()
            assert "complete measurable finite cell partition" in page.locator("#scope-text").inner_text()
            assert "explicit ordinary-prime endpoint" in page.locator("#scope-text").inner_text()
            assert "This reflection depends on n" in page.locator("#scope-text").inner_text()
            for theorem in vaughan_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("Vaughan endpoint retains the full budget, exact floor average, prime correction, Möbius reflection and conditional Riesz source")
            page.locator("#endpoint").select_option("prime-energy")
            assert "normalized energy decay at the current dilation is proved" in page.locator("#scope-text").inner_text()
            assert "source-beating bound on the signed boundary budget remains open" in page.locator("#scope-text").inner_text()
            energy_roots = page.evaluate("PROOF_VIEW.endpoint.roots")
            assert len(energy_roots) == 4
            for theorem in energy_roots:
                assert page.locator(f'[data-node="{theorem}"]').count()
            checks.append("prime-energy endpoint exposes current-dilation decay, its actual source limit and the retained signed budget")
            page.locator("#endpoint").select_option("riesz-vk")
            page.wait_for_function("PROOF_VIEW.endpoint.id === 'riesz-vk'")
            assert "No independent saving" in page.locator("#scope-text").inner_text()
            riesz_name = "RiemannGaussian.ZetaRieszConditionedEnergy.actual_band_le_mixed_moments"
            riesz_roots = page.evaluate("PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i].name)")
            assert riesz_name in riesz_roots
            assert "RiemannGaussian.ZetaRieszConditionedEnergy.tendsto_actual_residue_source" in riesz_roots
            page.locator("#search").fill(riesz_name)
            page.locator(".search-result").first.click()
            assert "rieszMomentMaximum" in page.locator("#details pre").inner_text()
            with page.expect_popup() as riesz_opened:
                page.locator("#details .source-button").click()
            riesz_source = riesz_opened.value
            riesz_source.wait_for_selector(".source-line:target")
            assert "theorem actual_band_le_mixed_moments" in riesz_source.locator(".source-line:target").inner_text()
            riesz_source.close()
            page.locator("#close-details").click()
            checks.append("Riesz bridge exposes the literal mixed-moment bound, retained source, open scope and exact Lean source line")
            page.locator("#endpoint").select_option("union")
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
            expected_source = f"https://github.com/dbsanfte/RiemannGaussian/blob/{fake_sha}/{root_data['source']['path']}#L{source_line}"
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
            phone.locator("#search").fill(root_data["name"])
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
