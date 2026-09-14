#!/usr/bin/env python3
"""Exercise the real RH campaign explorer and capture its evergreen README screenshot."""
import argparse
from functools import partial
from http.server import ThreadingHTTPServer
import importlib.metadata
import json
from pathlib import Path
import subprocess
import threading

from playwright.sync_api import sync_playwright
import build_rh_proof_explorer as campaign
from test_theorem_explorer import QuietHandler

ROOT = Path(__file__).resolve().parents[1]


def run(output, url=None, refresh_preview=False):
    assert not (url and refresh_preview), 'Refresh the preview from checked local files, not a remote page'
    output.mkdir(parents=True, exist_ok=True)
    server = None
    if not url:
        server = ThreadingHTTPServer(('127.0.0.1', 0), partial(QuietHandler, directory=str(ROOT)))
        threading.Thread(target=server.serve_forever, daemon=True).start()
        url = f'http://127.0.0.1:{server.server_port}/docs/rh-proof-explorer/'
    published = server is None
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    meta = campaign.metadata()
    status = json.loads((ROOT / 'docs/proof-status.json').read_bytes())
    expected = campaign.explorer.at_path(status, meta['campaign']['frontierStatusPath'])
    checks, errors = [], []
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch()
            for width in (1440, 390):
                page = browser.new_page(viewport={'width': width, 'height': 850}, device_scale_factor=1, reduced_motion='reduce')
                page.on('pageerror', lambda error: errors.append(str(error)))
                response = page.goto(url, wait_until='domcontentloaded')
                assert response.status == 200
                page.wait_for_function('window.PROOF_VIEW && PROOF_VIEW.visible.size >= 4')
                page.evaluate('document.fonts.ready')
                assert page.locator('h1').inner_text() == 'Current RH Proof Direction'
                assert page.evaluate('PROOF_VIEW.endpoint.id') == meta['defaultEndpoint']
                assert 'remains open' in page.locator('#scope-text').inner_text()
                assert page.locator('.zone-label').count() >= 2
                roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i].id)')
                assert roots == [expected]
                if published:
                    assert page.evaluate('PROOF_RELEASE.revision') == revision
                page.mouse.move(0, 0)
                preview = page.screenshot(path=str(output / f'overview-{width}.png'), animations='disabled')
                if width == 1440 and refresh_preview:
                    (campaign.SITE / 'preview.png').write_bytes(preview)
                    capture = {'schemaVersion': 1,
                        'capture': 'Playwright Chromium screenshot of the actual default explorer overview',
                        'endpoint': meta['defaultEndpoint'], 'terminalTheorems': roots,
                        'viewport': {'width': width, 'height': 850},
                        'browserVersion': browser.version,
                        'playwrightVersion': importlib.metadata.version('playwright'),
                        'visibleTheorems': page.evaluate('[...PROOF_VIEW.visible].map(i => PROOF_DATA.nodes[i].id).sort()'),
                        'inputSha256': campaign.screenshot_inputs(),
                        'imageSha256': campaign.explorer.digest(preview)}
                    (campaign.SITE / 'preview.json').write_bytes(campaign.explorer.json_bytes(capture))
                root = page.evaluate('PROOF_VIEW.endpoint.roots[0]')
                data = page.evaluate('PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]]')
                assert data['id'].endswith('.exists_original_band_critical_profile')
                assert 'correlatedSamplingCost' in data['statement']
                assert 'beta < 0' in data['statement'] and 'p ^ S' in data['statement']
                assert 'conditioningAllowance' not in data['statement']
                assert '0 < eps' in data['statement'] and '∃' in data['statement']
                node = page.locator(f'[data-node="{root}"]')
                node.hover()
                assert page.locator('#tooltip').is_visible()
                assert data['name'] in page.locator('#tooltip').inner_text()
                node.click()
                assert page.locator('#details pre').inner_text().strip() == data['statement'].strip()
                assert 'Quot.sound' in page.locator('#details').inner_text()
                source_url = page.locator('#details .source-button').get_attribute('href')
                assert source_url.endswith(f"#L{data['source']['line']}")
                if published:
                    assert f"/blob/{revision}/{data['source']['path']}" in source_url
                else:
                    with page.expect_popup() as opened:
                        page.locator('#details .source-button').click()
                    source = opened.value
                    source.wait_for_selector('.source-line:target')
                    assert 'theorem ' + data['id'].split('.')[-1] in source.locator('.source-line:target').inner_text()
                    source.close()
                page.screenshot(path=str(output / f'terminal-{width}.png'))
                page.locator('#close-details').click()
                zoom = page.locator('#zoom-value').inner_text()
                page.locator('#zoom-in').click()
                assert page.locator('#zoom-value').inner_text() != zoom
                page.locator('#fit').click()
                page.locator('#scope-more').click()
                assert 'what remains to prove' in page.locator('#details').inner_text().lower()
                assert 'combined correlation, sampling and normalization cost' in page.locator('#details').inner_text()
                assert 'still needs a source-scale saving' in page.locator('#details').inner_text()
                page.locator('#close-details').click()
                page.locator('#endpoint').select_option('source-limit')
                assert page.evaluate('PROOF_VIEW.endpoint.id') == 'source-limit'
                assert 'hypothetical' in page.locator('#scope-text').inner_text()
                source_root = page.evaluate('PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]].id')
                assert source_root == campaign.explorer.at_path(status, meta['campaign']['sourceStatusPath'])
                page.locator('#all-steps').click()
                assert page.evaluate('PROOF_VIEW.visible.size > 5')
                page.locator('#overview').click()
                for asset in ('audit.json', 'families.json', 'metadata.json', 'preview.png', 'preview.json', 'lean-graph.json.gz'):
                    fetched = page.request.get(url + asset)
                    # The first preview is created above before these requests.
                    assert fetched.status == 200, asset
                audit = page.request.get(url + 'audit.json').json()
                assert audit['standardAxiomsOnly'] and not audit['rhImplied']
                endpoint_roots = {
                    campaign.explorer.at_path(status, path)
                    for endpoint in meta['endpoints'] for path in endpoint['statusPaths']
                }
                assert set(audit['endpointAxioms']) == endpoint_roots
                for endpoint in meta['endpoints']:
                    page.locator('#endpoint').select_option(endpoint['id'])
                    actual = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i].id)')
                    assert set(actual) == {
                        campaign.explorer.at_path(status, path) for path in endpoint['statusPaths']
                    }
                    if endpoint['id'] == 'initial-conditioning':
                        assert 'unweighted' in page.locator('#scope-text').inner_text()
                        assert 'remain open' in page.locator('#scope-text').inner_text()
                        statement = page.evaluate('PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]].statement')
                        assert 'meanValue' in statement and '∃' in statement
                        assert '0 < eps' in statement and 'eps' in statement
                        saving = page.evaluate("PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i]).find(n => n.id.endsWith('.exists_dirichlet_block_saving'))")
                        assert saving is not None
                        assert 'dirichletTerm' in saving['statement'] and '12 ≤ k' in saving['statement']
                        assert '1 /' in saving['statement'] and 'M₀ ≤ M' in saving['statement']
                        assert saving['source']['path'].endswith('VinogradovDirichletSaving.lean')
                        assert 'block' in saving['statement'] and '2 * k - 2' in saving['statement']
                        assert 'z ≤ 2 *' in saving['statement'] and '128' in saving['statement']
                        damped = page.evaluate("PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i]).find(n => n.id.endsWith('.exists_feature_block_saving'))")
                        assert damped is not None
                        assert 'zetaPrimeFeature' in damped['statement'] and 'zetaPrimeExpWeight' in damped['statement']
                        assert '0 ≤ s.re' in damped['statement'] and '12 ≤ k' in damped['statement']
                        assert damped['source']['path'].endswith('VinogradovDampedSaving.lean')
                        cost = page.evaluate("PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i]).find(n => n.id.endsWith('.gaussian_moment_root_le_two'))")
                        assert cost is not None
                        cost_statement = ' '.join(cost['statement'].split())
                        assert cost_statement.endswith('≤ 2') and '12 ≤ k' in cost_statement
                        assert '1 / ↑(2 * r * r)' in cost_statement
                        finite = page.evaluate("PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i]).find(n => n.id.endsWith('.exists_finite_critical_iteration'))")
                        assert finite is not None
                        assert all(term in finite['statement'] for term in ('meanValue', 'A ^ n', 'factorial', '1 ≤ X', 'defect'))
                        assert finite['source']['path'].endswith('VinogradovFiniteCritical.lean')
                        profile = page.evaluate("PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i]).find(n => n.id.endsWith('.uniform_profile_degree_cost_iteration'))")
                        assert profile is not None
                        assert all(term in profile['statement'] for term in ('conditionedMoment', '7 * k', 'C * B', 'iterationConstant'))
                    if endpoint['id'] == 'full-recurrence':
                        statement = page.evaluate('PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]].statement')
                        assert 'conditioningAllowance' in statement and 'a ≤ b' in statement
                    if endpoint['id'] == 'exponent-audit':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'only the deep remainder' in scope
                        assert 'intermediate conditioned energy is identical' in scope
                        statement = page.evaluate('PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]].statement')
                        assert 'conditioningAllowance' in statement and 'eps' in statement
                    if endpoint['id'] == 'signed-fourier-tail':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'first-order prime-phase exponential' in scope and 'remain open' in scope
                        assert 'ordinary-prime correction' in scope and 'signed first moment' in scope
                        root_data = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        carrier = next(n for n in root_data if n['id'].endswith('.actual_physical_band_eq_fourierResponse'))
                        assert all(term in carrier['statement'] for term in (
                            'zetaArithmeticBand', 'zetaPrimeFilterKernel P N', 'zetaPrimeLogBand N', 'physicalCutoff u N'))
                        remainder = next(n for n in root_data if n['id'].endswith('.integral_norm_actual_logRemainder_div_le'))
                        assert all(term in remainder['statement'] for term in ('16 ≤ p', '1 / 2 < s.re', '∫', 'logRemainder', '∑\''))
                        criterion = next(n for n in root_data if n['id'].endswith('.false_of_cofinal_original_riesz_floor'))
                        assert all(term in criterion['statement'] for term in ('c < 1 →', '∃ᶠ', 'zetaRightHalfPoleJetFilter', '→\n      False'))
                        source = next(n for n in root_data if n['id'].endswith('.tendsto_actual_fourierResponse'))
                        assert 'NontrivialZetaZero' in source['statement'] and 'analyticZetaZeroMultiplicity' in source['statement']
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', carrier['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == carrier['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{carrier['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{carrier['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem actual_physical_band_eq_fourierResponse' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'prime-factor-tail':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'decreasing integrated allowance tending to zero' in scope
                        assert 'independent fixed cofinal floor remain open' in scope
                        assert 'explicit signed boundary' in scope
                        root_data = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        prime_carrier = next(n for n in root_data if n['id'].endswith('.actual_band_eq_primePair_integral'))
                        assert all(term in prime_carrier['statement'] for term in (
                            'zetaArithmeticBand', 'zetaPrimeFilterKernel P N', 'zetaPrimeLogBand N', 'bandPrimePair', 'L'))
                        tail = next(n for n in root_data if n['id'].endswith('.exists_uniform_nonlinearFactor_tail_lt'))
                        tail_statement = ' '.join(tail['statement'].split())
                        assert all(term in tail_statement for term in (
                            '1 / 2 < sigma', '0 < eps', '16 ≤ K', 's.re = sigma', 'K ≤ p', '∫', 'Complex.exp', '< eps'))
                        assert tail['source']['path'].endswith('ZetaPrimeNonlinearTail.lean')
                        boundary = next(n for n in root_data if n['id'].endswith('.actual_band_symbol_eq_completed_sub_boundary'))
                        assert all(term in boundary['statement'] for term in (
                            'primorial', '2 ^ (32 * N)', 'n ∉ RiemannGaussian.zetaPrimeLogBand N', 'compositeResponse', 'primeProduct'))
                        compensated = next(n for n in root_data if n['id'].endswith('.sum_composites_eq_compensated_exp'))
                        assert all(term in ' '.join(compensated['statement'].split())
                                   for term in ('16 ≤ p', 'firstOrder', 'logRemainder', '- 1 -'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', tail['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == tail['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{tail['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{tail['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem exists_uniform_nonlinearFactor_tail_lt' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'fixed-cofactor-decay':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'vanishing full prime-insertion band' in scope
                        assert 'joint signed semiprime and multiple-large-prime estimate remains open' in scope
                        assert 'assembly of the finite cofactor deletion' in scope
                        root_data = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        decay = next(n for n in root_data if n['id'].endswith('.tendsto_actual_composite_cofactor_band'))
                        statement = ' '.join(decay['statement'].split())
                        assert all(term in statement for term in (
                            'Squarefree a', 'a ≠ 1', '¬Nat.Prime a', '0 < u', 'u < 1',
                            'primeCofactorBand a N', 'coefficient', 'length u N', 'zetaPrimeFilterKernel P N', 'Tendsto'))
                        assert decay['source']['path'].endswith('ZetaRieszFixedCofactor.lean')
                        semiprime = next(n for n in root_data if n['id'].endswith('.coefficient_prime_pair_above_cutoff'))
                        assert all(term in ' '.join(semiprime['statement'].split()) for term in (
                            'Nat.Prime a', 'Nat.Prime p', 'Real.log', 'L', 'coefficient'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', decay['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == decay['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{decay['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{decay['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_composite_cofactor_band' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    page.locator('#all-steps').click()
                    assert page.evaluate('PROOF_VIEW.visible.size > 5')
                    page.locator('#overview').click()
                    page.locator('#fit').click()
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                checks.append({'width': width, 'terminal': expected, 'source': source_url,
                               'conditionalSource': source_root, 'hoverStatementAndAxioms': True,
                               'endpointSwitchAndZoom': True, 'openObstructionVisible': True,
                               'signedFourierCarrierAndOpenFloor': True,
                               'vanishingNonlinearTailAndRetainedBoundary': True,
                               'fixedCofactorDecayAndExplicitUnpaidClasses': True})
                page.close()
            browser.close()
    finally:
        if server:
            server.shutdown()
            server.server_close()
    assert not errors, errors
    if not published:
        campaign.check_screenshot()
    report = {'url': url, 'revision': revision, 'published': published, 'checks': checks, 'errors': errors}
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', help='Check the deployed site against the exact current HEAD')
    parser.add_argument('--refresh-preview', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT / '.lake/rh-proof-explorer/browser')
    args = parser.parse_args()
    run(args.output, args.url, args.refresh_preview)
