#!/usr/bin/env python3
"""Focused generator checks and optional real file/HTTP desktop/mobile browser checks."""
from __future__ import annotations

import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
import threading
import unittest

import build_semiprime_proof_explorer as builder


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.site = self.root / 'docs/semiprime-proof-explorer'
        self.site.mkdir(parents=True)
        self.packet = self.root / 'docs/research-evidence/test-publication'
        self.packet.mkdir(parents=True)
        for name in builder.STATIC:
            path = self.site / name; path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((builder.SITE / name).read_bytes())
        meta = json.loads((self.site / 'metadata.json').read_bytes())
        meta['publication_packet'] = self.packet.relative_to(self.root).as_posix()
        (self.site / 'metadata.json').write_bytes(builder.json_bytes(meta))
        source = self.root / 'RiemannGaussian/SemiprimeExample.lean'
        source.parent.mkdir()
        source.write_text('namespace RiemannGaussian.SemiprimeExample\n/-- A real source anchor. -/\ntheorem complete : True := by trivial\nend RiemannGaussian.SemiprimeExample\n')
        evidence = self.packet / 'component.json'
        evidence.write_text('{"status":"FINAL_ALL_WRITERS_STOPPED"}\n')
        record = {'path': evidence.relative_to(self.root).as_posix(), 'sha256': builder.digest(evidence.read_bytes())}
        self.inventory = {'schema_version': 1, 'modules': [{'module': 'RiemannGaussian.SemiprimeExample', 'path': source.relative_to(self.root).as_posix(), 'sha256': builder.digest(source.read_bytes()), 'status': 'finalized-machine', 'groups': ['example'], 'evidence': [record], 'validation': {'fresh_lean_build': False, 'validation_scope': 'Browser UI only; separate publication Lean checks are not asserted here.'}, 'scope_note': 'A prepared component only.'}], 'groups': [{'id': 'example', **record}], 'evidence': [record]}
        self.progress = {'schema_version': 1, 'research_goal': {'status': 'paused'}, 'full_goal_complete': False, 'curated_stage_order_not_lean_dependencies': True, 'stages': [{'id': 'example', 'title': 'Example stage', 'summary': 'The whole bound remains open.', 'status': 'partial', 'remaining': ['Literal caller'], 'groups': ['example'], 'proof_anchors': [{'module': 'RiemannGaussian.SemiprimeExample', 'declaration': 'RiemannGaussian.SemiprimeExample.complete'}]}]}
        self.save()

    def save(self):
        (self.packet / 'inventory.json').write_bytes(builder.json_bytes(self.inventory))
        (self.packet / 'progress.json').write_bytes(builder.json_bytes(self.progress))

    def test_deterministic_snapshots_and_exact_anchor(self):
        first = builder.build(self.root, self.site)
        self.assertEqual(first, builder.build(self.root, self.site))
        data = json.loads(first[self.site / 'data/explorer.js'].decode().split('=', 1)[1].rstrip(';\n'))
        self.assertEqual(data['stages'][0]['proof_anchors'][0]['line'], 3)
        module = data['modules'][0]
        source = first[self.site / f"data/sources/{module['bucket']}.js"].decode()
        self.assertIn('theorem complete', source)
        self.assertFalse(data['full_goal_complete'])

    def test_comments_strings_and_namespaces_do_not_invent_declarations(self):
        source = '''namespace RiemannGaussian.Test
/- theorem imaginary : True := by trivial /- nested -/ -/
def text := "theorem stringOnly : True"
section
@[simp] theorem actual : True := by trivial
end
end RiemannGaussian.Test
'''
        names = builder.declarations(source)
        self.assertEqual([d['name'] for d in names], ['RiemannGaussian.Test.text', 'RiemannGaussian.Test.actual'])
        self.assertEqual(names[1]['line'], 5)

    def test_rejects_changed_source_or_evidence(self):
        source = self.root / self.inventory['modules'][0]['path']
        old = source.read_bytes(); source.write_bytes(old + b'\n')
        with self.assertRaisesRegex(ValueError, 'hash mismatch'): builder.build(self.root, self.site)
        source.write_bytes(old)
        (self.packet / 'component.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'hash mismatch'): builder.build(self.root, self.site)

    def test_rejects_missing_anchor_and_incomplete_inventory(self):
        self.progress['stages'][0]['proof_anchors'][0]['declaration'] = 'nonexistent'
        self.save()
        with self.assertRaisesRegex(ValueError, 'declaration'): builder.build(self.root, self.site)
        self.progress['stages'][0]['proof_anchors'][0]['declaration'] = 'complete'
        self.save(); (self.root / 'RiemannGaussian/SemiprimeUnindexed.lean').write_text('def omitted := 1\n')
        with self.assertRaisesRegex(ValueError, 'cover all'): builder.build(self.root, self.site)

    def test_rejects_status_promotion_and_false_dependency_claim(self):
        self.inventory['modules'][0]['evidence'] = []; self.save()
        with self.assertRaisesRegex(ValueError, 'lacks recorded evidence'): builder.build(self.root, self.site)
        self.inventory['modules'][0]['status'] = 'draft'; self.save()
        self.progress['full_goal_complete'] = True; self.save()
        with self.assertRaisesRegex(ValueError, 'OPEN full theorem'): builder.build(self.root, self.site)
        self.progress['full_goal_complete'] = False
        self.progress['curated_stage_order_not_lean_dependencies'] = False; self.save()
        with self.assertRaisesRegex(ValueError, 'curated'): builder.build(self.root, self.site)

    def test_rejects_nonfinal_manifest_even_with_matching_hashes(self):
        evidence = self.packet / 'component.json'
        evidence.write_text('{"status":"DRAFT"}\n')
        new_hash = builder.digest(evidence.read_bytes())
        for record in builder.evidence_records(self.inventory):
            if record['path'].endswith('component.json'): record['sha256'] = new_hash
        self.save()
        with self.assertRaisesRegex(ValueError, 'not a recorded FINAL'): builder.build(self.root, self.site)

    def test_rejects_inconsistent_historical_membership(self):
        row = self.inventory['modules'][0]
        self.inventory['groups'][0]['modules'] = [{'module': row['module'], 'sha256': '0' * 64}]
        self.save()
        with self.assertRaisesRegex(ValueError, 'membership/source hash mismatch'): builder.build(self.root, self.site)

    def test_path_escape_and_unknown_status_are_rejected(self):
        with self.assertRaises(ValueError): builder.safe_path(self.root, '../outside')
        with self.assertRaises(ValueError): builder.safe_path(self.root, '/tmp/outside')
        self.inventory['modules'][0]['status'] = 'all-proved'; self.save()
        with self.assertRaisesRegex(ValueError, 'Unknown module status'): builder.build(self.root, self.site)


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, *_args): pass


def browser_checks(output: Path, refresh_preview=False, url=None, expected_revision=None):
    from playwright.sync_api import sync_playwright
    output.mkdir(parents=True, exist_ok=True)
    server = None
    if url:
        if refresh_preview: raise ValueError('Refresh previews from local checked files only')
        urls = {'published': url.rstrip('/') + '/'}
    else:
        server = ThreadingHTTPServer(('127.0.0.1', 0), partial(QuietHandler, directory=str(builder.ROOT)))
        threading.Thread(target=server.serve_forever, daemon=True).start()
        urls = {'file': (builder.SITE / 'index.html').as_uri(), 'http': f'http://127.0.0.1:{server.server_port}/docs/semiprime-proof-explorer/'}
    checks, errors = [], []
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch()
            for mode, url in urls.items():
                for width in (1440, 390):
                    page = browser.new_page(viewport={'width': width, 'height': 1000}, reduced_motion='reduce')
                    page.on('pageerror', lambda error: errors.append(str(error)))
                    page.goto(url, wait_until='load')
                    page.wait_for_function('window.SEMIPRIME_VIEW && window.SEMIPRIME_DATA.modules.length > 0')
                    if expected_revision:
                        assert page.evaluate('window.PROOF_RELEASE && PROOF_RELEASE.revision') == expected_revision
                        assert page.locator('#publication-verification').is_visible()
                    assert 'OPEN' in page.locator('.target-top').inner_text()
                    assert 'not a Lean-extracted dependency graph' in page.locator('#pipeline-note').inner_text()
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                    stage_count = page.locator('.stage-button').count()
                    assert stage_count >= 4
                    first = page.locator('.stage-button').first
                    first.focus(); first.press('ArrowDown')
                    assert page.locator('.stage-button').nth(1).get_attribute('aria-pressed') == 'true'
                    assert page.evaluate('SEMIPRIME_VIEW.stage') == page.locator('.stage-button').nth(1).get_attribute('data-stage')
                    assert page.locator('#stage-detail h3').inner_text() == page.locator('.stage-button').nth(1).locator('.stage-name').inner_text()
                    if width == 1440: page.evaluate('scrollTo(0,document.querySelector(".snapshot").offsetTop-30)')
                    shot = page.screenshot(path=str(output / f'pipeline-{mode}-{width}.png'), full_page=False)
                    if refresh_preview and mode == 'http' and width == 1440:
                        (builder.SITE / 'assets/preview.png').write_bytes(shot)
                        capture = {'schema_version': 1, 'capture': 'Actual local Playwright Chromium screenshot',
                                   'viewport': {'width': width, 'height': 1000}, 'scroll_y': page.evaluate('scrollY'),
                                   'selected_stage': page.locator('.stage-button[aria-pressed=true]').get_attribute('data-stage'), 'browser_version': browser.version,
                                   'input_sha256': builder.preview_inputs(), 'image_sha256': builder.digest(shot),
                                   'fresh_lean_build': False, 'validation_scope': 'Browser UI only; separate publication Lean checks are not asserted here.'}
                        (builder.SITE / 'assets/preview.json').write_bytes(builder.json_bytes(capture))
                    page.keyboard.press('/')
                    assert page.locator('#search').evaluate('(n)=>n===document.activeElement')
                    page.locator('#search').fill('factorBits_complete')
                    assert page.locator('.module-row').count() >= 1
                    assert 'factorBits_complete' in page.locator('#module-list').inner_text()
                    source_link = page.locator('.module-declarations a').filter(has_text='factorBits_complete').first
                    href = source_link.get_attribute('href'); assert '#L' in href
                    page.goto(url.rsplit('/', 1)[0] + '/' + href if mode == 'file' else url + href, wait_until='load')
                    page.wait_for_function('document.querySelectorAll(".source-line").length > 2')
                    target = page.locator('.source-line.requested-line')
                    assert 'factorBits_complete' in target.inner_text()
                    assert 'SHA-256' in page.locator('#source-provenance').inner_text()
                    if expected_revision:
                        assert f'/blob/{expected_revision}/RiemannGaussian/' in page.locator('#repository-source').get_attribute('href')
                    page.goto(url, wait_until='load'); page.wait_for_function('window.SEMIPRIME_VIEW')
                    page.locator('#search').fill('no-module-matches-this-string')
                    assert page.locator('.empty-state').is_visible()
                    page.locator('#reset').click()
                    page.locator('#status-filter').select_option('draft')
                    assert page.locator('#module-list .status').all_text_contents() == ['Draft / not finalized'] * page.locator('.module-row').count()
                    page.locator('#reset').click()
                    if not page.locator('#next').is_disabled():
                        page.locator('#next').click(); assert 'Page 2' in page.locator('#page-status').inner_text()
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                    checks.append({'mode': mode, 'width': width, 'source_snapshot': True, 'keyboard': True, 'filters': True, 'horizontal_overflow': False})
                    page.close()
            browser.close()
    finally:
        if server: server.shutdown()
    assert not errors, errors
    report = {'status': 'PASS', 'checks': checks, 'page_errors': errors, 'fresh_lean_build': False, 'validation_scope': 'Browser UI only; separate publication Lean checks are not asserted here.'}
    (output / 'browser-checks.json').write_bytes(builder.json_bytes(report))
    print('Semiprime browser PASS: desktop + mobile, keyboard/source/search/filter/pagination, modes=' + ','.join(urls))


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--browser', action='store_true'); parser.add_argument('--refresh-preview', action='store_true'); parser.add_argument('--url'); parser.add_argument('--expected-revision'); parser.add_argument('--output', type=Path, default=builder.ROOT / '.lake/semiprime-explorer-browser')
    args = parser.parse_args()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(GeneratorTests))
    if not result.wasSuccessful(): raise SystemExit(1)
    if args.refresh_preview and not args.browser: parser.error("--refresh-preview requires --browser")
    if args.url and not args.browser: parser.error("--url requires --browser")
    if args.expected_revision and not args.url: parser.error("--expected-revision requires --url")
    if args.browser: browser_checks(args.output, args.refresh_preview, args.url, args.expected_revision)


if __name__ == '__main__': main()
