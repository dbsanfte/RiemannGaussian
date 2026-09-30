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
                assert data['id'] == 'RiemannGaussian.ZetaRieszDominantAllocation.tendsto_nondominant_exact_source'
                assert all(term in data['statement'] for term in (
                    'nondominantRemainder', 'retainedCost', 'analyticZetaZeroMultiplicity',
                    'tau ≠ rho →', 'Real.exp (-(11 / 16))', 'Tendsto'))
                assert '-eta ≤' not in data['statement']
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
                assert 'every original mask' in page.locator('#details').inner_text()
                assert '13/20' in page.locator('#details').inner_text()
                assert 'independent cofinal real floor remains open' in page.locator('#details').inner_text()
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
                    if endpoint['id'] == 'full-positive-five-payment':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 14
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        transfer = next(n for n in roots if n['id'].endswith('.eventually_checked_tree_mass_upper'))
                        assert all(t in transfer['statement'] for t in ('Cover.check', 'population', '1003 / 1000'))
                        coverage = next(n for n in roots if n['id'].endswith('.remaining_positive_five_coefficient_eq_zero'))
                        assert all(t in coverage['statement'] for t in ('coreBand', 'residualCoefficient', '= 5', '= 0'))
                        six = next(n for n in roots if n['id'].endswith('.coefficient_six_two_outer_sharp'))
                        assert all(t in six['statement'] for t in ('Squarefree', '= 6', 'outerPrimes', 'minFac'))
                        centered = next(n for n in roots if n['id'].endswith('.coefficient_six_one_outer_centered'))
                        assert all(t in centered['statement'] for t in ('min', 'activePart', 'minFac', '= 1'))
                        savings = next(n for n in roots if n['id'].endswith('.centeredSixCost_le_reflected'))
                        assert all(t in savings['statement'] for t in ('centeredSixCost', 'reflectedSixCost', '≤'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('original moving masks', 'favorable interior atoms',
                            'exact signed rest', 'both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'triple-period-cancellation':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 11
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        whole = next(n for n in roots if n['id'].endswith('.eventually_whole_saddle_bound'))
                        assert all(t in whole['statement'] for t in ('lowerThresholdPacket',
                            'shortOverflowPacket', 'coreBand', 'residualCoefficient', 'Nonempty',
                            '25000', 'factorial', 'Tendsto'))
                        period = next(n for n in roots if n['id'].endswith('.eventually_weighted_prime_period'))
                        assert all(t in period['statement'] for t in ('1 / 500', 'logPrimes', 'Real.cos'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed complement',
                            'not source-o(1)', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'combined-triple-payment':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        payment = next(n for n in roots if n['id'].endswith('.eventually_signed_population_bound'))
                        assert all(t in payment['statement'] for t in ('6250', 'allocationBound',
                            'residualCoefficient', 'coreBand', 'population'))
                        floor = next(n for n in roots if n['id'].endswith('.scaled_floor_after_signed_payment'))
                        ceiling = next(n for n in roots if n['id'].endswith('.scaled_ceiling_after_signed_payment'))
                        assert 'max' in floor['statement'] and 'min' in ceiling['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', '1051 chunks',
                            '(2/25*sqrt(N+1)-1/8)', 'not source-o(1)',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'centered-prime-energy':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 10
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        saving = next(n for n in roots if n['id'].endswith('.centeredEnergy_eq'))
                        assert all(t in saving['statement'] for t in ('centeredEnergy', 'rawEnergy',
                            'logCross', 'logEnergy'))
                        optimal = next(n for n in roots if n['id'].endswith('.centeredEnergy_le_shifted'))
                        assert 'shiftedEnergy' in optimal['statement']
                        comparison = next(n for n in roots if n['id'].endswith('.retainedCenteredCost_le'))
                        assert all(t in comparison['statement'] for t in ('retainedCenteredCost',
                            'retainedMovingCost', '≤'))
                        owned = next(n for n in roots if n['id'].endswith('.exists_literal_centered_owned_bounds'))
                        assert all(t in owned['statement'] for t in ('residualCoefficient',
                            'zetaPrimeLogKernel', 'biUnion', 'boundedShare'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('OPTIMALLY CENTERED', 'COFACTOR-DEPENDENT',
                            'ZERO AND ONE', 'UNEVALUATED', 'PROVED NO LARGER', 'SAME E',
                            'WHOLE-CORE COVER', 'TOTAL source-normalized cost remain OPEN',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'moving-prime-interval-bound':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        moving = next(n for n in roots if n['id'].endswith('.exists_moving_mean'))
                        assert all(t in moving['statement'] for t in ('Finset.Ico', 'movingEnergy', 'Squarefree'))
                        owned = next(n for n in roots if n['id'].endswith('.exists_literal_owned_bounds'))
                        assert all(t in owned['statement'] for t in ('residualCoefficient', 'zetaPrimeLogKernel',
                            'retainedMovingCost', 'biUnion', 'boundedShare'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('COFACTOR-DEPENDENT', 'ZERO AND ONE', 'INSIDE',
                            'UNEVALUATED', 'unique largest-prime ownership', 'WHOLE-CORE COVER',
                            'TOTAL source-normalized cost remain OPEN',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'joined-smooth-prime-bound':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        smooth = next(n for n in roots if n['id'].endswith('.factorial_smooth_interval_bound'))
                        assert all(t in smooth['statement'] for t in ('factorialAmplitude', 'Real.cos', '∫', '|y|'))
                        mean = next(n for n in roots if n['id'].endswith('.exists_joined_prime_mean'))
                        assert all(t in mean['statement'] for t in ('primeResponse', 'joinedCost', 'Squarefree'))
                        family = next(n for n in roots if n['id'].endswith('.exists_literal_joined_family_bounds'))
                        assert all(t in family['statement'] for t in ('residualCoefficient', 'zetaPrimeLogKernel',
                            'retainedJoinedCost', '∃', '∧'))
                        assert 'smoothResponse' not in family['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('ORIGINAL', 'COMMON', 'PAID', 'ZERO AND ONE',
                            'UNEVALUATED', 'unique ownership', 'TOTAL source-scaled cost remain OPEN',
                            'NOT uniformly better', 'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'retained-prime-discrepancy':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 6
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        phase = next(n for n in roots if n['id'].endswith('.exists_cosine_error_mean'))
                        assert all(t in phase['statement'] for t in ('cosineError', 'intervalError', 'Squarefree'))
                        family = next(n for n in roots if n['id'].endswith('.exists_literal_family_error'))
                        assert all(t in family['statement'] for t in ('residualCoefficient', 'zetaPrimeLogKernel',
                            'boundedShare', 'smoothResponse', 'retainedErrorCost', 'choose', '∃', '∧'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('ORIGINAL', 'BOTH Riesz cutoffs', 'ZERO AND ONE',
                            'COMMON', 'UNEVALUATED', 'JOINT SIGNED SMOOTH CARRIER IS NOT PAID',
                            'unique ownership', 'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'coupled-prime-discrepancy':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 4
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        energy = next(n for n in roots if n['id'].endswith('.eventually_profile_error_energy'))
                        assert all(t in energy['statement'] for t in ('profile', 'smoothDifference',
                            'intervalError', '^ 2', '5000'))
                        bounds = next(n for n in roots if n['id'].endswith('.exists_joint_response_error_bounds'))
                        assert all(t in bounds['statement'] for t in ('primeResponse', 'smoothResponse',
                            'Squarefree', 'intervalError', '√', '∧'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('BOTH Riesz cutoffs', 'COMMON',
                            'UNEVALUATED', 'NOT paid', 'Low factorial orders are not deleted',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'joint-prime-error':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        theta = next(n for n in roots if n['id'].endswith('.eventually_theta_error'))
                        assert all(t in theta['statement'] for t in ('Chebyshev.theta', '5000', '^ 2', '∃'))
                        literal = next(n for n in roots if n['id'].endswith('.eventually_retained_interval_error'))
                        assert all(t in literal['statement'] for t in ('boundedShare',
                            'factorialAmplitude', 'factorialError', 'choose', 'Squarefree', '∫'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('UNEVALUATED', 'ZERO AND ONE',
                            'COMMON', 'PRIME-MOMENT', 'NOT a bound for the full Riesz carrier',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'joint-period-energy':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 7
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        profile = next(n for n in roots if n['id'].endswith('.joint_profile_energy'))
                        assert all(t in profile['statement'] for t in ('profile', 'Ioc', '∑', '^ 2'))
                        literal = next(n for n in roots if n['id'].endswith('.exists_literal_joint_period_bounds'))
                        assert all(t in literal['statement'] for t in ('residualCoefficient',
                            'zetaPrimeLogKernel', 'factorialJointEnergy', 'choose', 'Squarefree', '5000', '54'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('UNEVALUATED', 'COMMON',
                            'Cofactor-dependent prime holes', 'remain OPEN',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'retained-factorial-periods':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 10
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        allocation = next(n for n in roots if n['id'].endswith('.unassigned_multinomial'))
                        assert all(t in allocation['statement'] for t in (
                            'boundedShare', 'piAntidiag', 'unpaidOrders', 'allocationWeight'))
                        order = next(n for n in roots if n['id'].endswith('.factorial_order_budget'))
                        assert all(t in order['statement'] for t in ('amplitudeEnergy', 'factorialScore', 'choose', '√'))
                        literal = next(n for n in roots if n['id'].endswith('.exists_literal_family_bounds'))
                        assert all(t in literal['statement'] for t in ('residualCoefficient',
                            'zetaPrimeLogKernel', 'summedPeriodCost', 'Squarefree', '5000', '54', '∧'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('UNEVALUATED', 'ALL factorial orders',
                            'Cofactor-dependent prime holes', 'NOT a whole-carrier smallness theorem',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'signed-cutoff-energy':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 7
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        mean = next(n for n in roots if n['id'].endswith('.exists_signed_profile_mean'))
                        assert all(t in mean['statement'] for t in ('Squarefree', 'Ioc', 'b i ^ 2'))
                        literal = next(n for n in roots if n['id'].endswith('.exists_literal_joint_bounds'))
                        assert all(t in literal['statement'] for t in ('primeProfile',
                            'residualCoefficient', 'zetaPrimeLogKernel', 'Real.exp', 'primeFactors', 'Squarefree'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('UNEVALUATED', 'NO separate absolute crossing price',
                            'not a source-small energy estimate',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'linear-cutoff-mean':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        mean = next(n for n in roots if n['id'].endswith('.exists_min_riesz_difference_mean_bound'))
                        assert all(t in mean['statement'] for t in ('Squarefree', 'Ioc',
                            'VaughanLogAverage.riesz', 'min', 'B - A'))
                        joint = next(n for n in roots if n['id'].endswith('.exists_joint_difference_bounds'))
                        assert all(t in joint['statement'] for t in ('w n', 'min', '√', '∧'))
                        literal = next(n for n in roots if n['id'].endswith('.exists_literal_prime_fibre_bounds'))
                        assert all(t in literal['statement'] for t in ('signedPrimeWeight',
                            'residualCoefficient', 'zetaPrimeLogKernel', 'Real.log',
                            'primeFactors', 'Squarefree', 'min'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('UNEVALUATED', 'remain UNPAID',
                            'unit is excluded explicitly', 'not a source-normalized o(1)',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'quantitative-prime-periods':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        period = next(n for n in roots if n['id'].endswith('.cosine_period_bound'))
                        assert all(t in period['statement'] for t in ('5000', '54', 'Nat.Prime', 'Real.cos', '4 / a ^ 2'))
                        first = next(n for n in roots if n['id'].endswith('.cosine_first_period_bound'))
                        assert all(t in first['statement'] for t in ('Real.sin', 'Real.cos', '1 / a ^ 2'))
                        profile = next(n for n in roots if n['id'].endswith('.signed_profile_bound'))
                        assert all(t in profile['statement'] for t in ('HasDerivAt', 'Continuous', '41 / 100', '∫'))
                        joint = next(n for n in roots if n['id'].endswith('.all_count_period_bound'))
                        assert all(t in joint['statement'] for t in ('Squarefree', 'primeFactors', 'primeHarmonic', 'Real.cos'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('constant within each prime period',
                            'endpoint sine difference', 'NOT automatically covered',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'owner-count-energy':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        count = next(n for n in roots if n['id'].endswith('.prime_count_second_moment'))
                        assert all(t in count['statement'] for t in ('primeFactors.card', 'Nat.Prime', '^ 2'))
                        energy = next(n for n in roots if n['id'].endswith('.shell_energy_le'))
                        assert all(t in energy['statement'] for t in ('Ioc', 'W ^ 2', 'primeHarmonic', 'Real.log'))
                        phase = next(n for n in roots if n['id'].endswith('.exists_complex_owner_shell_bounds'))
                        assert all(t in phase['statement'] for t in ('ℂ', 'ownerWeight', 'cutoffSlope', '144', 'Real.exp', '‖a i‖'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('unevaluated', 'fixed across labels',
                            'cofactor energy sum and exponential prime-count price are paid',
                            'Remaining coefficient energy',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'uniform-period-budget':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 13
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        mean = next(n for n in roots if n['id'].endswith('.exists_separated_mean_bound'))
                        assert all(t in mean['statement'] for t in ('Squarefree', 'Ioc', 'Real.log', 'a i ^ 2'))
                        owner = next(n for n in roots if n['id'].endswith('.exists_owner_interval_mean_bound'))
                        assert all(t in owner['statement'] for t in ('ownerWeight', '36', 'Squarefree', 'Ico'))
                        slope = next(n for n in roots if n['id'].endswith('.exists_owner_slope_bounds'))
                        assert all(t in slope['statement'] for t in ('cutoffSlope', 'ownerWeight', 'T n i', '√'))
                        assert 'blockFloorCost' not in slope['statement']
                        density = next(n for n in roots if n['id'].endswith('.exists_density_mean_bound'))
                        assert all(t in density['statement'] for t in ('v n i', 'D ^ 2', 'ownerWeight'))
                        reciprocal = next(n for n in roots if n['id'].endswith('.exists_reciprocal_slope_bounds'))
                        assert all(t in reciprocal['statement'] for t in ('δ n', 'w n / δ n', 'T n i - Real.log', 'cutoffSlope'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('unevaluated', 'fixed across labels',
                            'No separate counting-error term remains', 'explicit unpaid weight energy',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'squarefree-dual-mean':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        reflection = next(n for n in roots if n['id'].endswith('.sharp_reflection'))
                        assert all(t in reflection['statement'] for t in ('Squarefree', 'n - 1', '/ R'))
                        mean = next(n for n in roots if n['id'].endswith('.exists_uniform_linear_mean_bound'))
                        assert all(t in mean['statement'] for t in ('Ioc', 'Squarefree', 'E *'))
                        joint = next(n for n in roots if n['id'].endswith('.exists_joint_riesz_bounds'))
                        assert all(t in joint['statement'] for t in ('riesz', '√', 'E *', '∧'))
                        literal = next(n for n in roots if n['id'].endswith('.exists_literal_prime_fibre_bounds'))
                        assert all(t in literal['statement'] for t in ('signedPrimeWeight',
                            'residualCoefficient', 'zetaPrimeLogKernel', 'Real.log', 'primeFactors'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('unevaluated', 'fixed across labels',
                            'explicit weight energy', 'no raw-prime-bound premise',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'owner-maximal':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 10
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        variation = next(n for n in roots if n['id'].endswith('.ownerWeight_variation_le_two'))
                        assert all(t in variation['statement'] for t in ('ownerWeight', '2', '32'))
                        mean = next(n for n in roots if n['id'].endswith('.exists_owner_interval_mean_bound'))
                        assert all(t in mean['statement'] for t in ('36', 'dyadicCost', 'blockFloorCost', 'Ico'))
                        slope = next(n for n in roots if n['id'].endswith('.exists_owner_slope_bounds'))
                        assert all(t in slope['statement'] for t in ('cutoffSlope', 'ownerWeight', 'Real.log', 'T n i', '√'))
                        literal = next(n for n in roots if n['id'].endswith('.literal_owner_prime_partial_bound'))
                        literal_statement = ' '.join(literal['statement'].split())
                        assert all(t in literal_statement for t in (
                            '∀ k ≤ m', 'coefficient L', 'B) →',
                            'residualCoefficient', 'zetaPrimeLogKernel', '3 * B'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('unevaluated', 'fixed across labels',
                            'raw partial-sum bound is an explicit premise', 'not source decay',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'joint-cross-cutoff':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 10
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        decay = next(n for n in roots if n['id'].endswith('.exists_symmetric_cross_bound'))
                        assert all(t in decay['statement'] for t in ('Real.log', 'lcm', '∃'))
                        mean = next(n for n in roots if n['id'].endswith('.exists_separated_mean_bound'))
                        assert all(t in mean['statement'] for t in ('Ioc', 'Real.log', '∃'))
                        slope = next(n for n in roots if n['id'].endswith('.exists_joint_slope_bounds'))
                        assert all(t in slope['statement'] for t in ('cutoffSlope', '√', 'Real.exp', '∧'))
                        sharper = next(n for n in roots if n['id'].endswith('.exists_joint_cancellation_slope_bounds'))
                        assert all(t in sharper['statement'] for t in ('cutoffSlope', 'I.sup', 'if', '√'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('unevaluated', 'no period-count factor',
                            'before the absolute value', 'fixed across labels',
                            'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'uniform-cutoff-change':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 6
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        sharp = next(n for n in roots if n['id'].endswith('.exists_sharp_quadratic_bound'))
                        assert all(t in sharp['statement'] for t in ('∃', 'lcm'))
                        assert 'μ' in sharp['statement'] or 'moebius' in sharp['statement']
                        mean = next(n for n in roots if n['id'].endswith('.exists_riesz_difference_interval_bound'))
                        assert all(t in mean['statement'] for t in ('Ioc', 'riesz', 'Real.exp'))
                        signed = next(n for n in roots if n['id'].endswith('.exists_masked_difference_bounds'))
                        assert all(t in signed['statement'] for t in ('√', 'Ioc', 'riesz', '∧'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('unevaluated', 'weight energy',
                            'moving cutoffs', 'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'all-count-riesz-mean-square':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 6
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        mean = next(n for n in roots if n['id'].endswith('.riesz_mean_square_le'))
                        assert all(t in mean['statement'] for t in ('riesz', '196', '16', 'Real.log'))
                        literal = next(n for n in roots if n['id'].endswith('.literal_residual_bounds'))
                        assert all(t in literal['statement'] for t in (
                            'residualCoefficient', 'literalWeight', '√', 'Squarefree'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('all-count', 'weight energy',
                            'moving cutoffs', 'Both whole -79/1000 floor and 3/2 ceiling remain open'))
                    if endpoint['id'] == 'signed-cutoff-crossings':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 7
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        signed = next(n for n in roots if n['id'].endswith('.literal_signed_affine_bounds'))
                        assert all(t in signed['statement'] for t in ('residualCoefficient',
                            'signedPrimeWeight', 'cutoffSlope', 'min', 'max'))
                        growth = next(n for n in roots if n['id'].endswith('.eventually_period_crossing_growth'))
                        assert all(t in growth['statement'] for t in ('absolutePeriodCrossing',
                            'dyadicMomentOrder', 'radiusCeiling'))
                        assert any(n['id'].endswith('.not_eventually_period_cost_bounded') for n in roots)
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('all cofactor counts', 'prime-count lower bounds',
                            'not only a loose majorant', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'global-owner-allocation':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 7
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        paid = next(n for n in roots if n['id'].endswith('.nonowner_sum_bound'))
                        assert all(t in paid['statement'] for t in ('literalWindow', 'assignedCoefficient',
                            'largestPrime', 'erase', 'nonownerRate'))
                        joint = next(n for n in roots if n['id'].endswith('.tendsto_joint_sub_owner'))
                        assert all(t in joint['statement'] for t in ('lowerThresholdPacket',
                            'shortOverflowPacket', 'ZetaRieszLeastBoundary.rest', 'residualCoefficient'))
                        variation = next(n for n in roots if n['id'].endswith('.owner_fibre_variation'))
                        assert all(t in variation['statement'] for t in ('boundedShare', 'largestPrime',
                            '12', '√'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('independently source-o(1)', '124/125',
                            'no fixed prime-count ceiling', 'two signed prime moments',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'global-cutoff-crossings':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 6
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        owned = next(n for n in roots if n['id'].endswith('.owned_population_affine_bounds'))
                        assert all(t in owned['statement'] for t in ('residualCoefficient', 'signedPrimeWeight', 'biUnion', 'cutoffSlope'))
                        radial = next(n for n in roots if n['id'].endswith('.radial_affine_error_le'))
                        assert 'Real.exp' in radial['statement'] and 'cutoffSlope' in radial['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('no upper prime-count ceiling', 'component bound',
                            'two actual signed moments', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'owner-geometry-prime-periods':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 7
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        coverage = next(n for n in roots if n['id'].endswith('.mem_cofactors_iff_of_count_le'))
                        assert all(t in coverage['statement'] for t in ('54', 'cofactors', 'Squarefree', '1 / 16'))
                        assert '197 / 200' not in coverage['statement']
                        actual = next(n for n in roots if n['id'].endswith('.eventually_near_balanced_extra'))
                        assert all(t in actual['statement'] for t in ('logPrimes', 'extra', '21 / 25', '2109 / 2500'))
                        thin = next(n for n in roots if n['id'].endswith('.eventually_thin_gap_extra'))
                        assert all(t in thin['statement'] for t in ('199 / 200', '534 / 625', '21369 / 25000'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', '70-percent',
                            '(N/16)*sourceCredit', 'not source-o(1)',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'unsaturated-prime-periods':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 6
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        exact = next(n for n in roots if n['id'].endswith('.coefficient_eq_response'))
                        assert 'response' in exact['statement'] and 'coefficient' in exact['statement']
                        actual = next(n for n in roots if n['id'].endswith('.eventually_unsaturated_extra'))
                        assert all(t in actual['statement'] for t in ('logPrimes', 'extra', 'VaughanLogAverage.riesz', '1733 / 2500'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('second cutoff is constant', 'exact signed rest',
                            '(N/16)*sourceCredit', 'not source-o(1)',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'fixed-count-prime-periods':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 9
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        core = next(n for n in roots if n['id'] == 'RiemannGaussian.ZetaRieszFixedCountPeriod.eventually_population_bound')
                        assert all(t in core['statement'] for t in ('coreBand', 'residualCoefficient', 'Real.cos', 'factorial'))
                        joint = next(n for n in roots if n['id'] == 'RiemannGaussian.ZetaRieszFixedCountBand.eventually_population_bound')
                        assert '90000' in joint['statement'] and 'residualCoefficient' in joint['statement']
                        strict = next(n for n in roots if n['id'].endswith('.eventually_extra_nonempty'))
                        assert 'Nonempty' in strict['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('7 through 55', 'exact signed rest',
                            '(N/16)*sourceCredit', 'not source-o(1)',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'six-small-prime-cancellation':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 7
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        riesz = next(n for n in roots if n['id'].endswith('.riesz_le_minFac'))
                        assert all(t in riesz['statement'] for t in ('Squarefree', '= 6', '3 *', 'minFac'))
                        whole = next(n for n in roots if n['id'].endswith('.eventually_core_subset_bounds'))
                        assert all(t in whole['statement'] for t in ('coreBand', 'residualCoefficient',
                            'max', 'min', 'floorCost', 'ceilingCost'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('[-3,4] to [-1,4]', 'exact signed rest',
                            '(N/16)*sourceCredit', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'saddle-band-joint-credit':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 9
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        payment = next(n for n in roots if n['id'].endswith('.eventually_six_population_bound'))
                        assert all(t in payment['statement'] for t in ('residualCoefficient', 'coreBand', '√'))
                        margin = next(n for n in roots if n['id'].endswith('.margin_lower'))
                        assert '16' in margin['statement'] and 'periodCount' in margin['statement']
                        assert any(n['id'].endswith('.floor_union') for n in roots)
                        assert any(n['id'].endswith('.ceiling_union') for n in roots)
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', '(N/16)*sourceCredit',
                            'paid once', 'not paid twice', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'multiple-six-prime-periods':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 9
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        cost = next(n for n in roots if n['id'].endswith('.eventually_period_cost_small'))
                        assert all(t in cost['statement'] for t in ('residualCoefficient', 'periodCount', 'factorial'))
                        floor = next(n for n in roots if n['id'].endswith('.scaled_floor_after_signed_payment'))
                        ceiling = next(n for n in roots if n['id'].endswith('.scaled_ceiling_after_signed_payment'))
                        assert 'max' in floor['statement'] and 'min' in ceiling['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', 'not source-o(1)', 'not paid twice',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'allocation-transition-payment':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        variation = next(n for n in roots if n['id'].endswith('.boundedShare_fibre_variation'))
                        assert all(t in variation['statement'] for t in ('boundedShare', '√', '24'))
                        residual = next(n for n in roots if n['id'].endswith('.eventually_residual_population_small'))
                        assert all(t in residual['statement'] for t in ('residualCoefficient', 'Real.cos', 'factorial'))
                        cross = next(n for n in roots if n['id'].endswith('.eventually_added_population_crosses_transition'))
                        assert '19 / 32' in cross['statement'] and 'primeFactors' in cross['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', 'not source-o(1)', 'not paid twice',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'six-prime-cofactor-period':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        residual = next(n for n in roots if n['id'].endswith('.eventually_residual_population_small'))
                        assert all(t in residual['statement'] for t in ('residualCoefficient', 'Real.cos', 'factorial', 'population'))
                        signed = next(n for n in roots if n['id'].endswith('.eventually_signed_population_bound'))
                        assert 'coreBand' in signed['statement'] and 'allocationBound' not in signed['statement']
                        strict = next(n for n in roots if n['id'].endswith('.eventually_added_population_nonempty'))
                        assert 'Nonempty' in strict['statement'] and 'ZetaRieszWideSixPeriod.population' in strict['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', 'not source-o(1)', 'not paid twice',
                            'strict enlargement', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'wide-six-prime-period':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 9
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        residual = next(n for n in roots if n['id'].endswith('.eventually_residual_population_small'))
                        assert all(t in residual['statement'] for t in ('residualCoefficient', 'Real.cos', 'factorial', 'population'))
                        signed = next(n for n in roots if n['id'].endswith('.eventually_signed_population_bound'))
                        assert 'coreBand' in signed['statement'] and 'allocationBound' not in signed['statement']
                        inclusion = next(n for n in roots if n['id'].endswith('.broad_population_subset'))
                        assert 'ZetaRieszBroadSixPeriod.population' in inclusion['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', 'not source-o(1)', 'not paid twice',
                            'Only Q retains', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'broad-six-prime-period':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 10
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        raw = next(n for n in roots if n['id'].endswith('.eventually_raw_population_small'))
                        assert all(t in raw['statement'] for t in ('Real.cos', 'factorial', 'coefficient', 'population'))
                        whole = next(n for n in roots if n['id'].endswith('.eventually_whole_joint_bound'))
                        assert all(t in whole['statement'] for t in ('lowerThresholdPacket', 'shortOverflowPacket', 'Tendsto'))
                        inclusion = next(n for n in roots if n['id'].endswith('.old_population_subset'))
                        assert 'ZetaRieszSixPrimePeriod.population' in inclusion['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', 'not source-o(1)', 'not paid twice',
                            'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'six-prime-period-payment':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 10
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        payment = next(n for n in roots if n['id'].endswith('.eventually_signed_population_bound'))
                        assert all(t in payment['statement'] for t in ('100000', 'allocationBound',
                            'residualCoefficient', 'coreBand', 'population'))
                        whole = next(n for n in roots if n['id'].endswith('.eventually_whole_joint_bound'))
                        assert all(t in whole['statement'] for t in ('lowerThresholdPacket',
                            'shortOverflowPacket', 'Tendsto', '100000'))
                        nonempty = next(n for n in roots if n['id'].endswith('.eventually_population_nonempty'))
                        assert 'Nonempty' in nonempty['statement']
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('exact signed rest', '(1/16*sqrt(N+1)-1/8)',
                            'not source-o(1)', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'six-prime-second-reflection':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 8
                        assert all('NontrivialZetaZero' not in n['statement'] for n in roots)
                        three = next(n for n in roots if n['id'].endswith('.coefficient_three_inner'))
                        assert all(t in three['statement'] for t in ('Squarefree', 'secondCount', '= 3', 'minFac'))
                        savings = next(n for n in roots if n['id'].endswith('.costs_le_centered'))
                        assert all(t in savings['statement'] for t in ('floorCost', 'ceilingCost', 'centeredSixCost'))
                        core = next(n for n in roots if n['id'].endswith('.core_subset_bounds'))
                        assert all(t in core['statement'] for t in ('coreBand', 'residualCoefficient', 'max', 'min'))
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('[-2,1]', '[-1,1]', '[0,1]',
                            'exact unpaid rest', 'Both numerical whole endgame bounds remain open'))
                    if endpoint['id'] == 'harmonic-rectangle-reserve':
                        nodes = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        reserve = next(n for n in nodes if n['id'].endswith('.eventually_rectangleReserve_ge'))
                        assert all(t in reserve['statement'] for t in (
                            'rectangleReserve', '1 / 160', 'analyticZetaZeroMultiplicity rho = 1',
                            'tau ≠ rho →', 'radiusCeiling', 'dyadicMomentOrder'))
                        for suffix in ('tendsto_rectangleMaskError', 'tendsto_separate_sub_rectangle'):
                            error = next(n for n in nodes if n['id'].endswith('.' + suffix))
                            assert 'Tendsto' in error['statement'] and 'ℕ → ℝ' in error['statement']
                            assert 'NontrivialZetaZero' not in error['statement']
                        overlap = next(n for n in nodes if n['id'].endswith('.completion_rest_rectangle_ledger'))
                        overlap_statement = ' '.join(overlap['statement'].split()).replace(
                            'RiemannGaussian.ZetaRieszSkewAllocation.', '')
                        assert all(t in overlap_statement for t in (
                            'rectangleCorrectionRest', 'ownerRectangleComplement', '2 * rectangleReserve'))
                        scope = page.locator('#scope-text').inner_text()
                        assert 'whole-carrier pass criterion is unmet' in scope
                        assert 'simple exposed-zero hypotheses' in scope
                        assert 'not a -3/40 whole-carrier floor' in scope
                    if endpoint['id'] == 'carrier-bound':
                        old_bound = page.evaluate('PROOF_DATA.nodes[PROOF_VIEW.endpoint.roots[0]]')
                        assert old_bound['id'].endswith('.exists_original_band_critical_profile')
                        assert all(term in old_bound['statement'] for term in (
                            'correlatedSamplingCost', 'beta < 0', 'p ^ S', '0 < eps', '∃'))
                        assert 'conditioningAllowance' not in old_bound['statement']
                    if endpoint['id'] in ('allowance-obstruction', 'one-sided-arithmetic'):
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 4
                        scope = page.locator('#scope-text').inner_text()
                        assert 'fixed' in scope and 'cofinal' in scope
                        assert all('NontrivialZetaZero' not in theorem['statement'] for theorem in roots)
                        if endpoint['id'] == 'allowance-obstruction':
                            assert all(t in scope for t in ('positive infinity', 'exactly three',
                                'every fixed real height', '1/2<u<=exp(-11/16)',
                                'cofinal 3/40 ceiling is impossible', 'starting index are unevaluated'))
                            growth = next(n for n in roots if n['id'].endswith('.eventually_complement_growth'))
                            assert all(t in growth['statement'] for t in ('∃ c', '0 < c', 'dyadicMomentOrder', 'fourCharge'))
                            divergence = next(n for n in roots if n['id'].endswith('.improved_allowance_tendsto_atTop'))
                            assert 'Tendsto' in divergence['statement'] and divergence['statement'].count('atTop') == 2
                            ceiling = next(n for n in roots if n['id'].endswith('.not_frequently_improved_allowance_le_three_fortieths'))
                            assert '¬' in ceiling['statement'] and '3 / 40' in ceiling['statement']
                        else:
                            assert '75-percent' in scope and 'not a saving on the whole carrier' in scope
                            bound = next(n for n in roots if n['id'].endswith('.nondominantRemainder_lower_with_four_credit'))
                            assert all(t in bound['statement'] for t in ('antichainBudget', 'fourCharge', 'nondominantRemainder'))
                        for theorem in roots:
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
                    if endpoint['id'] in ('harmonic-remainder', 'dominant-prime-sector'):
                        scope = page.locator('#scope-text').inner_text()
                        assert all(term in scope for term in (
                            '13/20', '12001/12000', 'N>=320', 'every real height',
                            '1/2<=u<=exp(-11/16)', '1/2<u<exp(-11/16)',
                            'arbitrary moving heights', 'simple exposed zeros',
                            'independent cofinal real floor at -3/40 remains open',
                            'Balanced products remain unpaid'))
                        if endpoint['id'] == 'dominant-prime-sector':
                            dominant_roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                            bound = next(n for n in dominant_roots if n['id'].endswith('.dominantSector_bound'))
                            assert all(t in bound['statement'] for t in (
                                'dominantSector', 'residualCoefficient', 'upperRate', 'lowerRate',
                                'zetaMoebiusLogMajorantMass', '320 ≤ N', '11 / 16'))
                            assert 'NontrivialZetaZero' not in bound['statement']
                            support = next(n for n in dominant_roots if n['id'].endswith('.nondominant_prime_log_lt'))
                            support_statement = ' '.join(support['statement'].split())
                            assert all(t in support_statement for t in (
                                'nondominantBand', '≠ 0', 'primeFactors', '13 / 20'))
                            deficit = next(n for n in dominant_roots if n['id'].endswith('.eventually_nondominant_re_lt_neg_three_fortieths'))
                            assert all(t in deficit['statement'] for t in (
                                'analyticZetaZeroMultiplicity rho = 1', 'tau ≠ rho →',
                                'nondominantRemainder', '3 / 40', '∀ᶠ'))
                    if endpoint['id'] == 'exact-wing-reserve':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            'log(19/17)', 'log(15/13)', 'c_ret(u)<37/40',
                            'source-forced negativity', 'independent cofinal real floor remains open'))
                        reserve_roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        reserve = next(n for n in reserve_roots if n['id'].endswith('.tendsto_reserve_exact'))
                        assert all(t in reserve['statement'] for t in ('reserve', 'Tendsto', 'tau ≠ rho →'))
                    if endpoint['id'] == 'joint-allocation':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in (
                            '1_S-theta', 'every off-mask correction is paid',
                            'arbitrary moving heights', 'independent signed floor remains open'))
                    if endpoint['id'] == 'joint-wing-cancellation':
                        scope = page.locator('#scope-text').inner_text()
                        assert all(term in scope for term in (
                            'C_gamma(N+1)^2 exp(-N/64)', '1/2<=u<exp(-2/3)',
                            '1/2<u<exp(-11/16)', '15/544', '7N/4<log n<=9N/4',
                            'joint arithmetic floor remains open', 'simple exposed zeros',
                            'not uniform in height', 'MINUS the complete composite companion'))
                        if endpoint['id'] == 'joint-wing-cancellation':
                            joint_roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                            joint_bound = next(n for n in joint_roots if n['id'].endswith('.exists_unpaidWing_add_compositeWing_bound'))
                            assert all(t in joint_bound['statement'] for t in (
                                'unpaidWing', 'compositeWing', '∃ C', '∀ (u', '∀ᶠ',
                                'Real.exp', '/ 64', '1 < |y|'))
                            assert 'NontrivialZetaZero' not in joint_bound['statement']
                            assert 'arithmeticRemainder' not in joint_bound['statement']
                    if endpoint['id'] in ('harmonic-paid-components', 'harmonic-floor-criterion'):
                        scope = page.locator('#scope-text').inner_text()
                        assert all(term in scope for term in (
                            '1/2<u<exp(-2/3)', '1/2<u<exp(-11/16)', '15/544',
                            '25N/16<log n<=5N/2', '7N/4<log n<=9N/4',
                            'joint arithmetic floor remains open', 'simple exposed zeros'))
                        harmonic_roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        if endpoint['id'] == 'harmonic-paid-components':
                            reserve = next(n for n in harmonic_roots if n['id'].endswith('.eventually_re_reserve_ge'))
                            assert all(t in reserve['statement'] for t in (
                                '15 / 544', 'analyticZetaZeroMultiplicity', 'tau ≠ rho →', 'Real.exp (-(11 / 16))'))
                            decay = next(n for n in harmonic_roots if n['id'].endswith('.eventually_norm_highWing'))
                            assert all(t in decay['statement'] for t in ('highWing', '^ 2', 'Real.exp', '1 / 1024'))
                            for suffix, ceiling in (('exists_annular_window_error', '2 / 3'), ('exists_reserve_window_error', '11 / 16')):
                                window = next(n for n in harmonic_roots if n['id'].endswith('.' + suffix))
                                assert all(t in window['statement'] for t in ('r < 1', 'r ^ N * C', 'fewResponse', 'windowResponse', ceiling))
                                assert 'NontrivialZetaZero' not in window['statement']
                        if endpoint['id'] == 'harmonic-floor-criterion':
                            criterion = harmonic_roots[0]
                            assert all(t in criterion['statement'] for t in (
                                'analyticZetaZeroMultiplicity rho = 1', 'eta <', '15 / 544', '∃ᶠ', 'False'))
                            assert '-eta ≤' in criterion['statement']
                            assert ' '.join(criterion['statement'].split()).endswith(').re) → False')
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
                    if endpoint['id'] == 'signed-main-density-bound':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 13
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('|c_D|<=2', '|eta(t)|<=7',
                                                        'STILL GROWS', 'remain unpaid', 'remain OPEN'))
                        core = next(n for n in roots if n['id'].endswith('.core_signed_main_bound'))
                        assert all(t in core['statement'] for t in ('coreBand', 'Squarefree',
                            'compositeModel', 'maskedWeight', '28', 'Real.exp 2', '(2 * u) ^ (N + 1)'))
                        assert 'NontrivialZetaZero' not in core['statement']
                        assert set(core['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
                        mask = next(n for n in roots if n['id'].endswith('.literal_short_allowance_lower'))
                        assert all(t in mask['statement'] for t in ('maskedWeight', 'ownerRows', '15', '32'))
                        assert 'NontrivialZetaZero' not in mask['statement']
                        assert set(mask['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
                        assert 'MAJORANT' in scope and 'actual signed error' in scope
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', core['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{core['source']['line']}")
                        if not published:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem core_signed_main_bound' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'exposed-cofactor-coupling':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 63
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('501/1000', '|xi|<=1/2000',
                            '(9999/10000)^N', 'Re(tau)<=999/1000', 'selected',
                            'remain OPEN', 'no double counting', 'GLOBAL horizontal zero sector'))
                        bound = next(n for n in roots if n['id'].endswith('.logMain_reduced_bound'))
                        assert all(t in bound['statement'] for t in ('paidConstant', 'reducedMain',
                            'radiusCeiling', '9999', '10000'))
                        horizontal = next(n for n in roots if n['id'].endswith('.horizontalResponse_bound'))
                        assert all(t in horizontal['statement'] for t in ('z.re', '501', '1000',
                            'horizontalResponse', 'couplingMassConstant'))
                        transfer = next(n for n in roots if n['id'].endswith('.tendsto_reduced_sub_current'))
                        assert all(t in transfer['statement'] for t in ('lowerThresholdPacket',
                            'shortOverflowPacket', 'dyadicPrimeCount', 'reducedMain'))
                        completion = next(n for n in roots if n['id'].endswith('.completionResponse_bound'))
                        assert all(t in completion['statement'] for t in ('completionResponse',
                            'couplingMassConstant', '9999', '10000', 'radiusCeiling'))
                        gamma_transfer = next(n for n in roots if n['id'].endswith('.tendsto_completionReduced_sub_current'))
                        assert all(t in gamma_transfer['statement'] for t in ('completionReducedMain',
                            'lowerThresholdPacket', 'shortOverflowPacket', 'dyadicPrimeCount'))
                        assert 'Gamma completion' in scope and 'pole-minus-xi' in scope
                        unshifted = next(n for n in roots if n['id'].endswith('.quotientResponse_single_rate'))
                        assert all(t in unshifted['statement'] for t in ('quotientResponse', 'paymentConstant', '300', 'radiusCeiling'))
                        unshifted_transfer = next(n for n in roots if n['id'].endswith('.tendsto_selectedReduced_sub_current'))
                        assert all(t in unshifted_transfer['statement'] for t in ('selectedReducedMain', 'lowerThresholdPacket', 'shortOverflowPacket', 'dyadicPrimeCount'))
                        assert 'shifted resonance' in scope and 'exp(-N/300)' in scope
                        full_unshifted = next(n for n in roots if n['id'].endswith('.exists_exposed_unshifted_bound'))
                        assert all(t in full_unshifted['statement'] for t in ('tau ≠ rho', 'NontrivialZetaZero',
                            'unshiftedResponse', 'roughPrimes', 'length', '300', 'radiusCeiling'))
                        shifted_transfer = next(n for n in roots if n['id'].endswith('.tendsto_shifted_sub_current'))
                        assert all(t in shifted_transfer['statement'] for t in ('tau ≠ rho', 'shiftedMain',
                            'lowerThresholdPacket', 'shortOverflowPacket', 'dyadicPrimeCount'))
                        assert 'complete unshifted logarithmic' in scope and 'no simplicity' in scope
                        global_bound = next(n for n in roots if n['id'].endswith('.globalResponse_bound'))
                        assert all(t in global_bound['statement'] for t in ('globalResponse', 'zeroMass y',
                            'responseConstant', 'radiusCeiling', '9999', '10000'))
                        global_split = next(n for n in roots if n['id'].endswith('.hasSum_xiDifference'))
                        assert all(t in global_split['statement'] for t in ('HasSum', 'analyticZetaZeroMultiplicity',
                            'modeDifference', 'signedTaylorMoment', 'riemannXi'))
                        global_transfer = next(n for n in roots if n['id'].endswith('.tendsto_poleEdge_sub_current'))
                        assert all(t in global_transfer['statement'] for t in ('poleEdgeMain',
                            'lowerThresholdPacket', 'shortOverflowPacket', 'dyadicPrimeCount'))
                        assert 'tau ≠ rho' not in global_transfer['statement']
                        assert 'not an infinite-product inverse' in scope
                        exterior_bound = next(n for n in roots if n['id'].endswith('.logMain_resonant_bound'))
                        assert all(t in exterior_bound['statement'] for t in ('logMain', 'resonantMain',
                            'paymentConstant y', 'zeroMass y', '9999', '10000'))
                        exterior_support = next(n for n in roots if n['id'].endswith('.retained_shift_support'))
                        assert all(t in exterior_support['statement'] for t in ('2000', '40', 'z.im', '∨'))
                        exterior_transfer = next(n for n in roots if n['id'].endswith('.tendsto_resonant_sub_current'))
                        assert all(t in exterior_transfer['statement'] for t in ('resonantMain',
                            'lowerThresholdPacket', 'shortOverflowPacket', 'dyadicPrimeCount'))
                        assert 'SHIFTED EXTERIOR' in scope and 'unshifted pole/right-edge terms still appear' in scope
                        for theorem in (bound, horizontal, transfer, completion, gamma_transfer, unshifted, unshifted_transfer,
                                        full_unshifted, shifted_transfer, global_bound, global_split, global_transfer,
                                        exterior_bound, exterior_support, exterior_transfer):
                            assert set(theorem['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', bound['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{bound['source']['line']}")
                        if not published:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem logMain_reduced_bound' in source_page.locator('.source-line:target').inner_text()
                            source_page.close()
                        page.locator('#close-details').click()
                    if endpoint['id'] == 'exposed-moving-complement':
                        roots = page.evaluate('PROOF_VIEW.endpoint.roots.map(i => PROOF_DATA.nodes[i])')
                        assert len(roots) == 12
                        scope = page.locator('#scope-text').inner_text()
                        assert all(t in scope for t in ('(u/R)^(N+1)', 'polynomial budget',
                            'selected term', 'remain unpaid', 'remain OPEN', 'ONE marked prime'))
                        bound = next(n for n in roots if n['id'].endswith('.complement_bound'))
                        assert all(t in bound['statement'] for t in ('S.erase z0', 'u / R',
                            'N + 1', 'a N z', 'R ≤'))
                        split = next(n for n in roots if n['id'].endswith('.primeFilter_resonance_bound'))
                        assert all(t in split['statement'] for t in ('analyticZetaZeroMultiplicity',
                            'Polynomial.eval', 'adaptiveZetaResidualFilter', 'adaptiveZetaReflectedFilter'))
                        bridge = next(n for n in roots if n['id'].endswith('.literal_profile_error_exponential'))
                        assert all(t in bridge['statement'] for t in ('maskedWeight', 'R ^ 2 ≤ k',
                            'densityPrefix', 'countingConstant', '32'))
                        assert 'NontrivialZetaZero' not in bridge['statement']
                        for theorem in (bound, split, bridge):
                            assert set(theorem['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
                        selected = page.evaluate('id => PROOF_DATA.nodes.findIndex(n => n.id === id)', split['id'])
                        page.locator(f'[data-node="{selected}"]').click()
                        link = page.locator('#details .source-button').get_attribute('href')
                        assert link.endswith(f"#L{split['source']['line']}")
                        if not published:
                            with page.expect_popup() as opened:
                                page.locator('#details .source-button').click()
                            source_page = opened.value
                            source_page.wait_for_selector('.source-line:target')
                            assert 'theorem primeFilter_resonance_bound' in source_page.locator('.source-line:target').inner_text()
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
                    expected_steps = page.evaluate('''() => {
                        const roots = PROOF_VIEW.endpoint.roots;
                        return [...new Set([
                            ...[...PROOF_VIEW.model.closure(roots)].filter(i => {
                                const node = PROOF_DATA.nodes[i];
                                return node.project && node.kind === 'theorem' && !node.generated;
                            }), ...roots
                        ])].sort((a, b) => a - b);
                    }''')
                    actual_steps = page.evaluate('[...PROOF_VIEW.visible].sort((a, b) => a - b)')
                    assert actual_steps == expected_steps, endpoint['id']
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
