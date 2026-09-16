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
                        assert 'finite cofactor deletion is now assembled' in scope
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
                    if endpoint['id'] == 'growing-cofactor-decay':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'tends to infinity' in scope
                        assert 'retains the original negative-multiplicity source' in scope
                        assert 'Semiprimes and composite cofactors larger than A_N remain unpaid jointly' in scope
                        assert 'explicitly assumes the unproved cofinal arithmetic floor' in scope
                        root_data = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        decay = next(n for n in root_data if n['id'].endswith('.tendsto_growing_composite_band'))
                        statement = ' '.join(decay['statement'].split())
                        assert all(term in statement for term in (
                            '0 < u', 'u < 1', 'growingCompositeBand N', 'coefficient',
                            'length u N', 'zetaPrimeFilterKernel P N', 'Tendsto'))
                        assert decay['source']['path'].endswith('ZetaRieszGrowingCofactor.lean')
                        source = next(n for n in root_data if n['id'].endswith('.tendsto_growing_reduced_source'))
                        assert all(term in ' '.join(source['statement'].split()) for term in (
                            'NontrivialZetaZero', 'growingReducedBand N', 'analyticZetaZeroMultiplicity',
                            'zetaRightHalfPoleJetFilter'))
                        closure = next(n for n in root_data if n['id'].endswith('.rh_of_reduced_cofinal_floors'))
                        assert all(term in closure['statement'] for term in (
                            '∃ c < 1', '∃ᶠ', '→', 'RiemannHypothesis', 'reducedHeadBand'))
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
                            assert 'theorem tendsto_growing_composite_band' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'exponential-cofactor-decay':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'eventually exceeds N^k for every fixed k' in scope
                        assert 'for every hypothetical right-half zero' in scope
                        assert 'Semiprimes and larger composite cofactors remain unpaid jointly' in scope
                        assert 'general spatial estimate is now proved' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.norm_exponential_composite_band_le'))
                        assert all(t in ' '.join(bound['statement'].split()) for t in (
                            '2 / 3 < u', 'u ≤ 1', 'exponentialCompositeBand u N',
                            'zetaPrimeFilterKernel P N', '√'))
                        assert bound['source']['path'].endswith('ZetaRieszExponentialCofactor.lean')
                        source = next(n for n in roots if n['id'].endswith('.tendsto_adaptive_reduced_source'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'adaptiveReducedBand', 'analyticZetaZeroMultiplicity'))
                        assert '5 / 6' not in source['statement']
                        optimizer = next(n for n in roots if n['id'].endswith('.minimumRate_eq_tiltRate_iff'))
                        assert all(t in optimizer['statement'] for t in ('tiltRate', 'optimalTilt', '↔'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', bound['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == bound['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{bound['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{bound['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem norm_exponential_composite_band_le' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'general-tilt-decay':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'Every q>1/2 with r(u,q)<1' in scope
                        assert 'except u=exp(-1/2)' in scope
                        assert 'for every hypothetical right-half zero' in scope
                        assert 'Semiprimes and larger composite cofactors remain unpaid jointly' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        general = next(n for n in roots if n['id'].endswith('.norm_tilted_composite_band_le'))
                        assert all(t in ' '.join(general['statement'].split()) for t in (
                            '1 / 2 < q', 'tiltRate u q < 1', 'tiltedCompositeBand u q N',
                            'zetaPrimeFilterKernel P N', '√'))
                        bound = next(n for n in roots if n['id'].endswith('.norm_optimal_composite_band_le'))
                        assert all(t in ' '.join(bound['statement'].split()) for t in (
                            '1 / 2 < u', 'u < 1', 'u ≠', 'Real.exp',
                            'optimalTilt u', 'minimumRate u', 'zetaPrimeFilterKernel P N'))
                        assert bound['source']['path'].endswith('ZetaRieszGeneralCofactorTilt.lean')
                        source = next(n for n in roots if n['id'].endswith('.tendsto_optimized_reduced_source'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'optimizedReducedBand', 'analyticZetaZeroMultiplicity'))
                        assert 'Real.exp' not in source['statement']
                        growth = next(n for n in roots if n['id'].endswith('.eventually_pow_le_optimalSchedule'))
                        assert all(t in growth['statement'] for t in ('∀ᶠ', 'N ^ k', 'tiltedSchedule'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', bound['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == bound['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{bound['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{bound['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem norm_optimal_composite_band_le' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'euler-correction-decay':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'Every prime interaction order is retained' in scope
                        assert 'odd correction has integrable energy' in scope
                        assert 'all Re(s)>=sigma at each fixed sigma>1/2' in scope
                        assert 'original factorial filter and signed completion boundary remain unpaid' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        even = next(n for n in roots if n['id'].endswith('.integral_norm_actual_paired_correctionProduct_le_tail'))
                        assert all(t in ' '.join(even['statement'].split()) for t in (
                            '1 / 2 < sigma', 'sigma ≤ s.re', 'correctionProduct Q', 'squareLogTail sigma K'))
                        odd = next(n for n in roots if n['id'].endswith('.integral_actual_odd_correctionProduct_energy_le_tail'))
                        assert all(t in ' '.join(odd['statement'].split()) for t in (
                            '1 / 2 < sigma', 'sigma ≤ s.re', 'correctionProduct Q', '^ 2 / xi ^ 2'))
                        for suffix in ('.exists_uniform_actual_paired_correctionProduct_lt',
                                       '.exists_uniform_actual_odd_correctionProduct_energy_lt'):
                            decay = next(n for n in roots if n['id'].endswith(suffix))
                            assert all(t in ' '.join(decay['statement'].split()) for t in (
                                '0 < eps', '∃ K', '16 ≤ K', 'sigma ≤ s.re', '< eps'))
                        weighted = next(n for n in roots if n['id'].endswith('.weighted_correction_pair_split'))
                        assert all(t in weighted['statement'] for t in ('Vp', 'Vm', 'Hp', 'Hm', '/ 2'))
                        assert even['source']['path'].endswith('ZetaRieszEulerCorrectionEnergy.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', even['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == even['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{even['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{even['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem integral_norm_actual_paired_correctionProduct_le_tail' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'euler-correction-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'literal original normalized arithmetic band' in scope
                        assert 'actual growing Riesz length' in scope
                        assert 'no hypothetical-zero premise' in scope
                        assert 'mixed leading-correction term' in scope
                        assert 'entire signed off-band completion boundary' in scope
                        assert 'joint independent cofinal real floor above minus one and RH remain open' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_residual'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '0 < u', 'u < 1', 'zetaArithmeticBand',
                            'SquarefreeVaughanLogSource.length u N', 'residualResponse P N y', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        bound = next(n for n in roots if n['id'].endswith('.norm_scaled_filteredResponse_le'))
                        assert all(t in ' '.join(bound['statement'].split()) for t in (
                            '0 < R', '0 < a', 'a ≤ L', 'filterRadiusCost P R', '(u / R) ^ (N + 1)'))
                        integrable = next(n for n in roots if n['id'].endswith('.integrable_residualKernel'))
                        assert all(t in ' '.join(integrable['statement'].split()) for t in (
                            '1 / 2 < s.re', 'IntegrableOn', 'residualKernel P N s L'))
                        identity = next(n for n in roots if n['id'].endswith('.actual_band_eq_residual_response'))
                        assert all(t in identity['statement'] for t in (
                            'zetaArithmeticBand', 'residualResponse', 'filteredResponse', 'originalCorrectionPrimes'))
                        assert deletion['source']['path'].endswith('ZetaRieszEulerCorrectionDeletion.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_band_sub_residual' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'euler-growing-head-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'literal original normalized arithmetic band' in scope
                        assert 'positive integer stride d' in scope
                        assert 'head primes at most n+16' in scope
                        assert 'growing leading quotient is not independently bounded' in scope
                        assert 'joint cofinal real floor above minus one and RH remain open' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.exists_stride_actual_band_sub_windowResidual'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '0 < u', 'u < 1', '∃ d', '0 < d', 'zetaArithmeticBand',
                            'd * n', 'n + 16', 'windowResidualResponse', 'SquarefreeVaughanLogSource.length', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        bound = next(n for n in roots if n['id'].endswith('.norm_scaled_headFilteredResponse_le_product'))
                        assert all(t in ' '.join(bound['statement'].split()) for t in (
                            '0 < R', '0 < a', 'a ≤ L', 'Real.exp', 'headFilteredResponse',
                            'filterRadiusCost P R', '(u / R) ^ (N + 1)'))
                        source = next(n for n in roots if n['id'].endswith('.exists_stride_normalizedWindowResidual_source'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'normalizedWindowResidual', 'analyticZetaZeroMultiplicity'))
                        integrable = next(n for n in roots if n['id'].endswith('.integrable_windowResidualKernel'))
                        assert all(t in ' '.join(integrable['statement'].split()) for t in (
                            '16 ≤ b + 1', '1 / 2 < s.re', 'IntegrableOn', 'windowResidualKernel P N b'))
                        identity = next(n for n in roots if n['id'].endswith('.actual_band_eq_windowResidual_response'))
                        assert all(t in identity['statement'] for t in (
                            'zetaArithmeticBand', 'windowResidualResponse', 'headFilteredResponse',
                            'actualWindowHead', 'actualWindowTail'))
                        assert deletion['source']['path'].endswith('ZetaRieszEulerWindowDeletion.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem exists_stride_actual_band_sub_windowResidual' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'euler-quadratic-head-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'through N^2, at every original factorial order' in scope
                        assert 'uniformly for sigma>=1/2' in scope
                        assert 'Small primes still occur in S' in scope
                        assert 'independent joint cofinal real floor above minus one and RH remain open' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_quadraticResidual'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '0 < u', 'u < 1', 'zetaArithmeticBand', 'n ^ 2',
                            'windowResidualResponse', 'SquarefreeVaughanLogSource.length', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        assert '∃ d' not in statement
                        bound = next(n for n in roots if n['id'].endswith('.eventually_quadratic_head_product_le'))
                        assert all(t in ' '.join(bound['statement'].split()) for t in (
                            '0 < eps', 'Nat.Prime p', 'p ≤ n ^ 2', '1 / 2 ≤ sigma', 'Real.exp'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_normalizedQuadraticResidual'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'normalizedQuadraticResidual', 'analyticZetaZeroMultiplicity'))
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_quadraticResidual_cofinal_floors'))
                        assert all(t in closure['statement'] for t in (
                            '∀ (rho', '∃ c < 1', '∃ᶠ', 'normalizedQuadraticResidual', '→', 'RiemannHypothesis'))
                        assert deletion['source']['path'].endswith('ZetaRieszEulerQuadraticHead.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_band_sub_quadraticResidual' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'smooth-prime-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert '32*log(2)*u*sum(norm(P_k))*N*(sqrt(u))^N' in scope
                        assert 'actual prime above N^2' in scope
                        assert 'scalar contact with its polynomial fallback' in scope
                        assert 'Semiprimes and larger surviving composite cofactors remain coupled' in scope
                        assert 'RH remains open' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_optimizedRoughResponse'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '1 / 2 < u', 'u < 1', 'zetaArithmeticBand', 'optimizedRoughResponse',
                            'SquarefreeVaughanLogSource.length', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        rate = next(n for n in roots if n['id'].endswith('.eventually_norm_quadratic_head_sum_le_sqrt'))
                        assert all(t in ' '.join(rate['statement'].split()) for t in (
                            '0 < u', 'u < 1', '∀ᶠ', 'Nat.Prime p', 'p ≤ N ^ 2',
                            '0 < L', '32', '√u ^ N', 'coefficient L'))
                        support = next(n for n in roots if n['id'].endswith('.optimizedRoughBand_support'))
                        assert all(t in support['statement'] for t in (
                            'optimizedReducedBand', 'Squarefree n', 'Nat.Prime p', 'p ∣ n', 'N ^ 2 < p'))
                        cofactor = next(n for n in roots if n['id'].endswith('.optimizedRoughBand_cofactor_gt'))
                        assert all(t in cofactor['statement'] for t in (
                            'optimizedRoughBand', 'optimizedCofactorThreshold', 'n = p * a'))
                        bridge = next(n for n in roots if n['id'].endswith('.tendsto_quadraticResidual_sub_optimizedRoughResponse'))
                        assert all(t in bridge['statement'] for t in (
                            'windowResidualResponse', 'optimizedRoughResponse', 'N ^ 2', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in bridge['statement']
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_optimizedRoughResponse_cofinal_floors'))
                        assert all(t in closure['statement'] for t in (
                            '∀ (rho', '∃ c < 1', '∃ᶠ', 'normalizedOptimizedRoughResponse', '→', 'RiemannHypothesis'))
                        assert deletion['source']['path'].endswith('ZetaRieszSmoothCofactor.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_band_sub_optimizedRoughResponse' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'physical-prime-prefix-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '1/2<u<exp(-1/2)', 'Every order-dependent subband mask',
                            'no separate cofactor size cap', 'p>(D_N+2)^2',
                            'previous remainder is retained as a fallback', 'RH remains open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_prefixResidual'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '1 / 2 < u', 'u < Real.exp (-(1 / 2))', 'zetaArithmeticBand',
                            'prefixResidualResponse', 'SquarefreeVaughanLogSource.length', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        masks = next(n for n in roots if n['id'].endswith('.tendsto_actualProductBand_of_small_source'))
                        assert all(t in masks['statement'] for t in (
                            '(keep : ℕ → ℕ → Prop)', 'actualProductBand (keep N)',
                            'u < Real.exp (-(1 / 2))', 'coefficient'))
                        support = next(n for n in roots if n['id'].endswith('.surviving_single_prime_above_physical_cutoff'))
                        assert all(t in ' '.join(support['statement'].split()) for t in (
                            'prefixResidualBand', 'Squarefree a', 'Nat.Prime p',
                            'r ≤ N ^ 2', 'n = p * a', 'linearDampedCutoff u N + 2) ^ 2 < p'))
                        adaptive = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_adaptivePrefix'))
                        assert all(t in ' '.join(adaptive['statement'].split()) for t in (
                            '1 / 2 < u', 'u < 1', 'adaptivePrefixResponse', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in adaptive['statement']
                        source = next(n for n in roots if n['id'].endswith('.tendsto_normalizedAdaptivePrefix'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'normalizedAdaptivePrefix', 'analyticZetaZeroMultiplicity'))
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_adaptivePrefix_cofinal_floors'))
                        assert all(t in closure['statement'] for t in (
                            '∀ (rho', '∃ c < 1', '∃ᶠ', 'normalizedAdaptivePrefix', '→', 'RiemannHypothesis'))
                        assert deletion['source']['path'].endswith('ZetaRieszPhysicalPrefixDeletion.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_band_sub_prefixResidual' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'composite-smooth-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '1/2<u<exp(-1/2)', 'no separate cofactor size cap or physical-prime cutoff',
                            '2^omega(a)/a', '2*u^2<1', 'at least two distinct primes above N^2',
                            'previous remainder is retained as a fallback', 'RH remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_compositeResidual'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '1 / 2 < u', 'u < Real.exp (-(1 / 2))', 'zetaArithmeticBand',
                            'compositeResidualResponse', 'SquarefreeVaughanLogSource.length', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        actual = next(n for n in roots if n['id'].endswith('.tendsto_actual_compositeSmoothBand'))
                        assert all(t in actual['statement'] for t in (
                            '(keep : ℕ → ℕ → Prop)', 'compositeSmoothBand (keep N)',
                            'u < Real.exp (-(1 / 2))', 'coefficient'))
                        large = next(n for n in roots if n['id'].endswith('.tendsto_actual_largeCofactorBand'))
                        assert all(t in ' '.join(large['statement'].split()) for t in (
                            '0 < u', '2 * u ^ 2 < 1', 'largeCofactorBand (keep N)', 'Tendsto'))
                        support = next(n for n in roots if n['id'].endswith('.surviving_support_dichotomy'))
                        assert all(t in ' '.join(support['statement'].split()) for t in (
                            'coefficient L n ≠ 0', 'Nat.Prime a', 'a ≤ N ^ 2',
                            'linearDampedCutoff u N + 2) ^ 2 < p', '∨', 'p ≠ r', 'p ∣ n',
                            'r ∣ n', 'N ^ 2 < p', 'N ^ 2 < r'))
                        adaptive = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_adaptiveComposite'))
                        assert all(t in ' '.join(adaptive['statement'].split()) for t in (
                            '1 / 2 < u', 'u < 1', 'adaptiveCompositeResponse', 'Tendsto'))
                        bridge = next(n for n in roots if n['id'].endswith('.tendsto_quadraticResidual_sub_adaptiveComposite'))
                        assert all(t in bridge['statement'] for t in (
                            'windowResidualResponse', 'adaptiveCompositeResponse', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in bridge['statement']
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_adaptiveComposite_cofinal_floors'))
                        assert all(t in closure['statement'] for t in (
                            '∀ (rho', '∃ c < 1', '∃ᶠ', 'normalizedAdaptiveComposite', '→', 'RiemannHypothesis'))
                        assert deletion['source']['path'].endswith('ZetaRieszCompositeDeletion.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_band_sub_compositeResidual' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'large-smooth-factor-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '2*u^2<1', 'any number of rough primes',
                            'every order-dependent subband mask', '2^omega(a)/a',
                            'factorization existence is proved',
                            'fallback preserves the previous remainder', 'RH remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_largeSmoothResidual'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in (
                            '1 / 2 < u', '2 * u ^ 2 < 1', 'zetaArithmeticBand',
                            'largeSmoothResidualResponse', 'SquarefreeVaughanLogSource.length', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        actual = next(n for n in roots if n['id'].endswith('.tendsto_actual_largeSmoothFactorBand'))
                        assert all(t in ' '.join(actual['statement'].split()) for t in (
                            '(keep : ℕ → ℕ → Prop)', '0 < u', '2 * u ^ 2 < 1',
                            'largeSmoothFactorBand (keep N)', 'coefficient', 'Tendsto'))
                        support = next(n for n in roots if n['id'].endswith('.surviving_support_with_small_smooth_factor'))
                        assert all(t in ' '.join(support['statement'].split()) for t in (
                            'coefficient L n ≠ 0', '∃ a b', 'Squarefree a', 'Squarefree b',
                            'a.primeFactors', 'b.primeFactors', 'p ≤ N ^ 2', 'N ^ 2 < p',
                            'n = b * a', 'a <', 'linearDampedCutoff u N + 2) ^ 2'))
                        adaptive = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_adaptiveSmooth'))
                        assert all(t in ' '.join(adaptive['statement'].split()) for t in (
                            '1 / 2 < u', 'u < 1', 'adaptiveSmoothResponse', 'Tendsto'))
                        bridge = next(n for n in roots if n['id'].endswith('.tendsto_quadraticResidual_sub_adaptiveSmooth'))
                        assert all(t in bridge['statement'] for t in (
                            'windowResidualResponse', 'adaptiveSmoothResponse', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in bridge['statement']
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_adaptiveSmooth_cofinal_floors'))
                        assert all(t in closure['statement'] for t in (
                            '∀ (rho', '∃ c < 1', '∃ᶠ', 'normalizedAdaptiveSmooth', '→', 'RiemannHypothesis'))
                        assert deletion['source']['path'].endswith('ZetaRieszLargeSmoothDeletion.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_band_sub_largeSmoothResidual' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'extreme-prime-window':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            'Factorization existence is proved', 'disappear only from the Riesz profile',
                            'norm at most log(n)', 'independently of the number of extreme primes',
                            'X_N<d*a and d<X_N', 'Both equality boundaries vanish',
                            'Every Moebius sign', '1/2<u and 2*u^2<1', 'RH remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.norm_coefficient_physical_extreme_le_log'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            'Squarefree (b * a)', 'a ≤', 'b.primeFactors',
                            'linearDampedCutoff u N + 2) ^ 2 ≤ p', 'coefficient', 'Real.log'))
                        assert 'NontrivialZetaZero' not in statement
                        window = next(n for n in roots if n['id'].endswith('.coefficient_extreme_composite_eq_physical_window'))
                        assert all(t in ' '.join(window['statement'].split()) for t in (
                            'Squarefree (b * (q * a))', 'a ≠ 1', '¬Nat.Prime a',
                            'q.divisors with', '< d * a', 'd <', 'moebius', 'VaughanLogAverage.riesz'))
                        assert 'NontrivialZetaZero' not in window['statement']
                        support = next(n for n in roots if n['id'].endswith('.surviving_layers_with_boundary_witness'))
                        assert all(t in ' '.join(support['statement'].split()) for t in (
                            'largeSmoothResidualBand', 'coefficient', '≠ 0', '∃ a q b',
                            'a.primeFactors', 'q.primeFactors', 'b.primeFactors',
                            'n = b * (q * a)', '∃ d ∈ q.divisors', 'VaughanLogAverage.riesz'))
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_band_sub_largeSmoothResidual'))
                        assert all(t in ' '.join(deletion['statement'].split()) for t in (
                            '1 / 2 < u', '2 * u ^ 2 < 1', 'Tendsto'))
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_adaptiveSmooth_cofinal_floors'))
                        assert all(t in closure['statement'] for t in (
                            '∀ (rho', '∃ c < 1', '∃ᶠ', 'normalizedAdaptiveSmooth', '→', 'RiemannHypothesis'))
                        assert support['source']['path'].endswith('ZetaRieszSurvivingPrimeLayers.lean')
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', support['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == support['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{support['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{support['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem surviving_layers_with_boundary_witness' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'unfiltered-narrow-carrier':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'independent cofinal floor' in scope and 'open' in scope
                        assert 'Composite-cofactor fallback' in scope and '2*u^2<1' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        deletion = next(n for n in roots if n['id'].endswith('.tendsto_actual_residual_sub_narrow'))
                        statement = ' '.join(deletion['statement'].split())
                        assert all(t in statement for t in ('0 < u', 'u < 1', 'Tendsto', 'residualResponse'))
                        assert 'NontrivialZetaZero' not in statement
                        source = next(n for n in roots if n['id'].endswith('ZetaRieszNarrowCarrier.tendsto_normalizedResidual'))
                        assert all(t in source['statement'] for t in ('NontrivialZetaZero', 'analyticZetaZeroMultiplicity', 'normalizedResidual'))
                        cosine = next(n for n in roots if n['id'].endswith('.re_normalizedResidual_eq_cosine_sum'))
                        assert all(t in cosine['statement'] for t in ('Real.cos', 'factorial', 'coefficient'))
                        rate = next(n for n in roots if n['id'].endswith('.upperRate_cube'))
                        assert all(t in rate['statement'] for t in ('upperRate', '125', '128'))
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_exposed_narrow_floors'))
                        assert all(t in closure['statement'] for t in ('∃ c < 1', '∃ᶠ', 'RiemannHypothesis'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', deletion['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == deletion['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{deletion['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{deletion['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_actual_residual_sub_narrow' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'extreme-degree-deletion':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'floor for the whole residual remains open' in scope
                        assert 'intermediate primes' in scope and 'N^2<p<X_N' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.eventually_norm_four_extreme_sum_le'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in ('0 < u', 'Real.exp', '4 ≤', 'fourRate', 'tiltConstant'))
                        assert 'NontrivialZetaZero' not in statement
                        source = next(n for n in roots if n['id'].endswith('.tendsto_normalizedFourResidual'))
                        assert all(t in source['statement'] for t in ('NontrivialZetaZero', 'analyticZetaZeroMultiplicity'))
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_exposed_fourResidual_floors'))
                        assert all(t in closure['statement'] for t in ('∃ c < 1', '∃ᶠ', 'RiemannHypothesis'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', bound['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == bound['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{bound['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{bound['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem eventually_norm_four_extreme_sum_le' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'physical-annulus':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'JOINT sum of the two classes remains open' in scope
                        assert 'X_N<n<X_N^2' in scope and 'fallback' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        upper = next(n for n in roots if n['id'].endswith('.tendsto_above_physical_square'))
                        statement = ' '.join(upper['statement'].split())
                        assert all(t in statement for t in ('0 < u', 'Real.exp', 'linearDampedCutoff', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in statement
                        lower = next(n for n in roots if n['id'].endswith('.coefficient_eq_zero_below_physical'))
                        lower_statement = ' '.join(lower['statement'].split())
                        assert all(t in lower_statement for t in ('coefficient', '≤', '= 0'))
                        cases = next(n for n in roots if n['id'].endswith('.annulus_support_dichotomy'))
                        assert all(t in cases['statement'] for t in ('primeFactors', '∨', 'coefficient', 'Real.log'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_normalizedAnnulus'))
                        assert all(t in source['statement'] for t in ('NontrivialZetaZero', 'analyticZetaZeroMultiplicity'))
                        closure = next(n for n in roots if n['id'].endswith('.rh_of_exposed_annulus_floors'))
                        assert all(t in closure['statement'] for t in ('∃ c < 1', '∃ᶠ', 'RiemannHypothesis'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', upper['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == upper['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{upper['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{upper['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem tendsto_above_physical_square' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'annulus-prime-completion':
                        scope = page.locator('#scope-text').inner_text()
                        assert 'independent JOINT signed floor remains open' in scope
                        assert 'MINUS its exact finite physical prefix' in scope
                        assert 'Diagonal and repeated prefix incidences' in scope
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.eventually_norm_joint_sub_annulus_le'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in ('1 / 2 ≤ u', 'Real.exp', 'jointResponse', 'annulusResponse', 'degreeRate', 'tiltConstant'))
                        assert 'NontrivialZetaZero' not in statement
                        complete = next(n for n in roots if n['id'].endswith('.hasSum_crossCoefficient'))
                        assert all(t in complete['statement'] for t in ('HasSum', 'completedCofactorHead', 'prefixCoefficient'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_jointResponse_exposed'))
                        assert all(t in source['statement'] for t in ('NontrivialZetaZero', 'Real.exp', 'analyticZetaZeroMultiplicity'))
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', bound['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        assert page.locator('#details pre').inner_text().strip() == bound['statement'].strip()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{bound['source']['line']}")
                        if published:
                            assert f"/blob/{revision}/{bound['source']['path']}" in link
                        else:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem eventually_norm_joint_sub_annulus_le' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'prefix-central-window':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            'intermediate-prime logarithmic mark', 'unique integer labels',
                            '3N/2<log(n)<=8N/3', 'central signed floor is open',
                            'Do not apply the central cut to the completed head'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.norm_sub_centralBand_le'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            '0 < u', 'u < Real.exp (-(2 / 3))', 'centralBand S N',
                            'centralLowerRate', 'centralUpperRate', 'zetaMoebiusLogMajorant'))
                        assert 'NontrivialZetaZero' not in statement
                        mixed = next(n for n in roots if n['id'].endswith('.tendsto_mixedResponse'))
                        assert all(t in ' '.join(mixed['statement'].split()) for t in (
                            '1 / 2 < u', 'u < Real.exp (-(1 / 2))', 'N ^ 2 < a',
                            'mixedResponse (A N)', 'Tendsto'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_centralAnnulus_exposed'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'centralAnnulusResponse', 'analyticZetaZeroMultiplicity'))
                        for theorem in (bound, mixed):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'central-prime-layers':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            'whole completed prime head retained', 'Twenty is only the clip threshold',
                            'log(n)/2', 'four-or-more-prime response',
                            'unevaluated phase cost is not a subunit source-scale floor',
                            'whole joint floor remains open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.actual_three_prime_coefficient_bounds'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            'n.primeFactors.card = 3', '0 < L', '2 * L',
                            'SquarefreeVaughanLogSource.coefficient', 'Real.log'))
                        assert 'NontrivialZetaZero' not in statement
                        clip = next(n for n in roots if n['id'].endswith('.centralPairResponse_eq_log_sum'))
                        assert all(t in ' '.join(clip['statement'].split()) for t in (
                            '1 / 2 ≤ u', '20 ≤ N', 'centralPairResponse', 'centralBand'))
                        layers = next(n for n in roots if n['id'].endswith('.eventually_centralJoint_eq_prime_layers'))
                        assert all(t in layers['statement'] for t in (
                            'completedCofactorHead', 'centralPairResponse',
                            'centralThreePrimeResponse', 'centralHigherPrimeResponse'))
                        phase = next(n for n in roots if n['id'].endswith('.re_normalized_three_ge_negative_phase'))
                        assert all(t in ' '.join(phase['statement'].split()) for t in (
                            '0 ≤ u', 'u < Real.exp (-(2 / 3))', 'max 0',
                            'zetaPrimeFilterKernel', 'centralThreePrimeResponse'))
                        assert 'NontrivialZetaZero' not in phase['statement']
                        for theorem in (bound, phase):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'head-orders':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '16k>=15(N+j+1)', 'exp(-7N/3200)',
                            'No zero, exposure or cancellation premise',
                            'Neither prime variable is truncated',
                            'whole signed floor remains open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.norm_highHead_le'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            '1 / 2 ≤ u', 'u < Real.exp (-(2 / 3))', '2 ≤ N',
                            'highHead', 'highHeadCost', 'highRate'))
                        assert 'NontrivialZetaZero' not in statement
                        assert 'hexposed' not in statement
                        transport = next(n for n in roots if n['id'].endswith('.norm_centralJoint_sub_orderReduced_le'))
                        assert all(t in transport['statement'] for t in (
                            'centralJoint', 'orderReducedJoint', 'highHeadCost'))
                        assert 'NontrivialZetaZero' not in transport['statement']
                        source = next(n for n in roots if n['id'].endswith('.tendsto_orderReducedJoint_exposed'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'orderReducedJoint', 'analyticZetaZeroMultiplicity'))
                        for theorem in (bound, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'pair-orders':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '8k>=7(N+j+1)', '8k<=M or 8k>=7M',
                            'exp(-7N/9216)', 'No zero, exposure or cancellation premise',
                            '1/2<=u<exp(-2/3)', 'not fractions of arithmetic mass',
                            'joint cofinal real floor above -1 remains open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.norm_outerPairResponse_le'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            '0 < u', 'u < Real.exp (-(2 / 3))', '3 ≤ N',
                            'outerPairResponse', 'outerPairCost', 'adaptiveRate'))
                        assert 'NontrivialZetaZero' not in statement
                        assert 'hexposed' not in statement
                        diagonal = next(n for n in roots if n['id'].endswith('.tendsto_pairDiagonal'))
                        assert all(t in diagonal['statement'] for t in ('0 < u', 'u < 1', 'pairDiagonal'))
                        assert 'NontrivialZetaZero' not in diagonal['statement']
                        transport = next(n for n in roots if n['id'].endswith('.tendsto_centralJoint_sub_middleJoint'))
                        assert all(t in transport['statement'] for t in (
                            'centralJoint', 'middleJoint', '1 / 2 ≤ u'))
                        assert 'NontrivialZetaZero' not in transport['statement']
                        form = next(n for n in roots if n['id'].endswith('.middleJoint_eq_unpaired_add_form'))
                        assert all(t in form['statement'] for t in (
                            'centralUnpairedResponse', 'jointPrimeForm'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_middleJoint_exposed'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'middleJoint', 'analyticZetaZeroMultiplicity'))
                        for theorem in (bound, form, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'matched-middle':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '-m_rho^2/8', 'explicit zero and exposure premises',
                            'multiplicity is not assumed one', 'NO zero premise',
                            'ONLY the structural threshold',
                            'remaining JOINT floor and other global source ranges remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        completion = next(n for n in roots if n['id'].endswith('.eventually_norm_finite_sub_complete_le'))
                        statement = ' '.join(completion['statement'].split())
                        assert all(t in statement for t in (
                            '0 < u', 'u < Real.exp (-(2 / 3))',
                            '128 * k ≤ 65 * N', 'finiteMoment', 'ordinaryPrimeMoment'))
                        assert 'NontrivialZetaZero' not in statement
                        assert 'hexposed' not in statement
                        bound = next(n for n in roots if n['id'].endswith('.eventually_matchedBlock_re_bounds'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            'NontrivialZetaZero', 'tau ≠ rho →',
                            '‖3 / 2 + Complex.I * ↑(↑rho).im - ↑tau‖',
                            '3 / 2 - (↑rho).re < Real.exp (-(2 / 3))',
                            'analyticZetaZeroMultiplicity', '^ 2 / 8', 'matchedBlock'))
                        assert statement.endswith('< 0')
                        complement = next(n for n in roots if n['id'].endswith('.middleJoint_one_eq_unmatched_add_matched'))
                        assert all(t in complement['statement'] for t in (
                            'middleJoint 1', 'unmatchedJoint', 'matchedBlock'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_unmatched_add_matched_exposed'))
                        assert all(t in source['statement'] for t in (
                            'NontrivialZetaZero', 'unmatchedJoint', 'matchedBlock', 'analyticZetaZeroMultiplicity'))
                        for theorem in (completion, bound, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'wider-matched':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '-m_rho^2/1536', 'explicit zero and exposure premises',
                            'unrestricted multiplicity', 'ONLY the structural threshold',
                            'remaining JOINT floor and other global source ranges remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        bound = next(n for n in roots if n['id'].endswith('.eventually_matchedBlock_persistent_bounds'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            'NontrivialZetaZero', 'tau ≠ rho →',
                            '‖3 / 2 + Complex.I * ↑(↑rho).im - ↑tau‖',
                            'Real.exp (-(2 / 3))', '^ 2 / 8', '^ 2 / 1536', 'matchedBlock'))
                        completion = next(n for n in roots if n['id'].endswith('.eventually_norm_wider_completion'))
                        statement = ' '.join(completion['statement'].split())
                        assert all(t in statement for t in ('1 / 2 ≤ u', '32 * k ≤ 17 * N', 'finiteMoment', 'ordinaryPrimeMoment'))
                        assert 'NontrivialZetaZero' not in statement
                        identity = next(n for n in roots if n['id'].endswith('.reflected_sharedAtom_eq'))
                        assert all(t in identity['statement'] for t in ('sharedAtom', 'taperedMoment', 'finiteMoment', 'ordinaryPrimeMoment'))
                        taper = next(n for n in roots if n['id'].endswith('.norm_actual_taperedMoment_le'))
                        statement = ' '.join(taper['statement'].split())
                        assert all(t in statement for t in ('0 < q', '1 < sigma', '0 < q + sigma - 3 / 2', 'taperedMoment'))
                        assert 'NontrivialZetaZero' not in statement
                        source = next(n for n in roots if n['id'].endswith('.tendsto_unmatched_add_matched_exposed'))
                        assert all(t in source['statement'] for t in ('unmatchedJoint', 'matchedBlock', 'analyticZetaZeroMultiplicity'))
                        assert any(n['id'].endswith('.wider_order_not_old') for n in roots)
                        assert any(n['id'].endswith('.not_tendsto_unmatched_full_source') for n in roots)
                        for theorem in (bound, completion, taper):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'complete-head-harmonic':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '1/2<=u<exp(-2/3)', 'unrestricted multiplicity',
                            'structural threshold only', 'The head itself does not vanish',
                            'joint signed lower bound for T3+T>=4+taperedWing',
                            'other global source ranges remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        wing = next(n for n in roots if n['id'].endswith('.tendsto_wingError'))
                        assert all(t in wing['statement'] for t in ('ℕ → ℝ', '0 < u', 'wingError', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in wing['statement']
                        prefix = next(n for n in roots if n['id'].endswith('.sum_norm_weighted_smallPrimeMoment'))
                        assert all(t in prefix['statement'] for t in ('Finset ℕ', '600', 'smallPrimeMoment', '√'))
                        assert 'NontrivialZetaZero' not in prefix['statement']
                        continuity = next(n for n in roots if n['id'].endswith('.tendsto_harmonic_product_error'))
                        assert all(t in continuity['statement'] for t in ('ℕ → ℂ', 'ℕ → Finset ℕ', 'b ^ 2', '2 * k ≤ N + 1'))
                        assert 'NontrivialZetaZero' not in continuity['statement']
                        bound = next(n for n in roots if n['id'].endswith('.eventually_completeHead_re_bounds'))
                        statement = ' '.join(bound['statement'].split())
                        assert all(t in statement for t in (
                            'NontrivialZetaZero', 'tau ≠ rho →', 'Real.exp (-(2 / 3))',
                            'analyticZetaZeroMultiplicity', 'headHarmonicWeight', '0 < ε', '∧'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_three_higher_taper_budget'))
                        assert all(t in source['statement'] for t in (
                            'centralThreePrimeResponse', 'centralHigherPrimeResponse',
                            'centralBlock', 'taperedWing', 'headHarmonicWeight', 'analyticZetaZeroMultiplicity'))
                        for theorem in (continuity, bound, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'exact-harmonic-costs':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '1/2<=u<exp(-2/3)', 'unrestricted multiplicity',
                            'structural threshold only', 'source range is unchanged',
                            'source is linear in m', 'simplicity is not assumed',
                            'Exactly three unpaid components remain',
                            'other global source ranges remain open'))
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        continuity = next(n for n in roots if n['id'].endswith('.tendsto_nonneg_weighted_sum'))
                        assert all(t in continuity['statement'] for t in ('Finset α', 'ℕ → α → ℝ', 'ℕ → α → ℂ', '0 ≤ w N k', 'Tendsto'))
                        assert 'NontrivialZetaZero' not in continuity['statement']
                        scalar = next(n for n in roots if n['id'].endswith('.paidHarmonicCost_lt_one'))
                        assert 'NontrivialZetaZero' not in scalar['statement']
                        assert 'paidHarmonicCost u < 1' in scalar['statement']
                        head = next(n for n in roots if n['id'].endswith('.tendsto_completeHead_exact_cost'))
                        assert all(t in head['statement'] for t in ('tau ≠ rho →', '≤ 3 / 5', 'Real.log', 'analyticZetaZeroMultiplicity'))
                        bound = next(n for n in roots if n['id'].endswith('.eventually_head_central_gt_neg_multiplicity_square'))
                        assert all(t in bound['statement'] for t in ('tau ≠ rho →', 'Real.exp (-(2 / 3))', '^ 2 <', 'completeHead', 'centralBlock'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_three_unpaid_exact_source'))
                        assert all(t in source['statement'] for t in (
                            'centralThreePrimeResponse', 'centralHigherPrimeResponse', 'taperedWing',
                            'analyticZetaZeroMultiplicity', 'paidHarmonicCost', '^ 2'))
                        assert 'centralBlock' not in source['statement'] and 'completeHead' not in source['statement']
                        for theorem in (continuity, bound, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] in ('prime-cells', 'small-composite-cells'):
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        scope = page.locator('#scope-text').inner_text()
                        assert 'remain open' in scope or 'remains open' in scope
                        if endpoint['id'] == 'prime-cells':
                            assert len(roots) == 10
                            assert 'independent of height and filter' in scope
                            assert 'No internal phase-dependent prime selection' in scope
                            bound = next(n for n in roots if n['id'].endswith('.norm_actual_band_le_cell_saving'))
                            assert all(t in bound['statement'] for t in ('validCellCycle', 'arithmeticCellResponse', 'totalSaving'))
                            source = next(n for n in roots if n['id'].endswith('.tendsto_retained_cell_source'))
                            assert all(t in source['statement'] for t in ('cellRetention', 'zetaRightHalfPoleJetFilter', 'analyticZetaZeroMultiplicity'))
                        else:
                            assert len(roots) == 4
                            assert 'log a <= N/10' in scope and 'component decay theorem' in scope
                            assert 'no numerical starting order' in scope
                            bound = next(n for n in roots if n['id'].endswith('.eventually_smallOwner_mass_le'))
                            assert all(t in bound['statement'] for t in ('smallOwnerBand', 'centralLowerRate', 'bandWeight', '1 / 2 ≤ u', 'Real.exp (-(2 / 3))'))
                            assert 'NontrivialZetaZero' not in bound['statement']
                            source = next(n for n in roots if n['id'].endswith('.tendsto_remaining_cell_source'))
                            assert all(t in source['statement'] for t in ('remainingCells', 'Real.exp (-(2 / 3))', 'analyticZetaZeroMultiplicity'))
                        for theorem in (bound, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
                                source_page.close()
                            page.locator('#close-details').click()
                    if endpoint['id'] == 'owner-windows':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exp(N/5)', 'exp(-16/25)', 'moving heights',
                                                        'except u=exp(-1/2)', 'starting order is unevaluated',
                                                        'joint signed bound remains open'))
                        bound = next(n for n in roots if n['id'].endswith('.eventually_fifth_owner_mass_le'))
                        assert all(t in bound['statement'] for t in ('ownerBand (1 / 5)', 'fifthOwnerRate',
                                                                     'Real.exp (-(2 / 3))', 'bandWeight'))
                        wider = next(n for n in roots if n['id'].endswith('.eventually_tenth_owner_mass_le'))
                        assert all(t in wider['statement'] for t in ('ownerBand (1 / 10)', 'tenthOwnerRate',
                                                                     'Real.exp (-(16 / 25))'))
                        assert 'NontrivialZetaZero' not in bound['statement'] + wider['statement']
                        general = next(n for n in roots if n['id'].endswith('.exists_growing_owner_mass_decay'))
                        assert all(t in general['statement'] for t in ('1 / 2 < u', 'u < 1',
                                                                       'u ≠ Real.exp (-(1 / 2))', '∃ δ'))
                        source = next(n for n in roots if n['id'].endswith('.tendsto_fifth_remaining_source'))
                        assert all(t in source['statement'] for t in ('remainingCells (1 / 5)',
                                                                      'Real.exp (-(2 / 3))',
                                                                      'zetaRightHalfPoleJetFilter',
                                                                      'analyticZetaZeroMultiplicity'))
                        for theorem in (bound, source):
                            selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', theorem['id'])
                            node = page.locator(f'[data-node="{selected}"]')
                            node.hover()
                            assert page.locator('#tooltip').is_visible()
                            node.click()
                            assert page.locator('#details pre').inner_text().strip() == theorem['statement'].strip()
                            link = page.locator('#details .source-button').get_attribute('href')
                            assert link.endswith(f"#L{theorem['source']['line']}")
                            if published:
                                assert f"/blob/{revision}/{theorem['source']['path']}" in link
                            else:
                                with page.expect_popup() as opened:
                                    page.locator('#details .source-button').click()
                                source_page = opened.value
                                source_page.wait_for_selector('.source-line:target')
                                assert 'theorem ' + theorem['id'].rsplit('.', 1)[-1] in source_page.locator('.source-line:target').inner_text()
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
                               'fixedCofactorDecayAndExplicitUnpaidClasses': True,
                               'growingCofactorDecayAndRetainedSource': True,
                               'conditionalRHClosurePremiseVisible': True,
                               'exponentialCofactorBoundAndAdaptiveSource': True,
                               'generalTiltArithmeticBoundAndWholeSource': True,
                               'fullEulerCorrectionEvenAndOddBounds': True,
                               'originalBandCorrectionDeletionAndExplicitResidual': True,
                               'growingPrimeHeadDeletionAndCofinalSource': True,
                               'quadraticPrimeDensityDeletionAtEveryOrder': True,
                               'actualSmoothRateAndJointPrimeCofactorDeletion': True,
                               'scalarTiltAuditDistinguishedFromArithmeticBound': True,
                               'arbitraryRoughPrimeCountAndCompleteSmoothFactorDeletion': True,
                               'exactThreePrimeLayersAndSignedBoundaryWindow': True,
                               'independentNarrowedTailAndConditionalCosineSource': True,
                               'fourExtremePrimeBoundAndOpenWholeResidualFloor': True,
                               'physicalAnnulusBoundAndJointTwoClassObstruction': True,
                               'completePrimeRangeBoundAndRetainedSignedPrefix': True,
                               'boundedPrefixComponentsAndActualCentralWindow': True,
                               'centralThreePrimeSignBoundsAndNegativePhaseCost': True})
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
