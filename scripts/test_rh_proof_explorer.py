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
                assert 'not yet bounded strongly enough' in page.locator('#details').inner_text()
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
                        assert '1 / (3 *' in statement
                    page.locator('#all-steps').click()
                    assert page.evaluate('PROOF_VIEW.visible.size > 5')
                    page.locator('#overview').click()
                    page.locator('#fit').click()
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                checks.append({'width': width, 'terminal': expected, 'source': source_url,
                               'conditionalSource': source_root, 'hoverStatementAndAxioms': True,
                               'endpointSwitchAndZoom': True, 'openObstructionVisible': True})
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
