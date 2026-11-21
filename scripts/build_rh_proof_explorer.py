#!/usr/bin/env python3
"""Build the shorter RH proof overview and the independent native explorer."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

import build_archive_rh_explorer as archive
import build_theorem_explorer as explorer

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'docs/rh-proof-explorer'
SHARED = ROOT / 'docs/theorem-explorer'
RAW = ROOT / '.lake/rh-proof-explorer/lean-graph.json'
METADATA = 'docs/rh-proof-explorer/metadata.json'
PREVIEW_INPUTS = ('metadata.json', 'native.html', 'data.js', 'app.js', 'graph-core.js', 'style.css', 'release.js')


def metadata():
    return json.loads((ROOT / METADATA).read_bytes())


def screenshot_inputs():
    paths = [SITE / name for name in PREVIEW_INPUTS]
    paths += [ROOT / 'scripts/test_rh_proof_explorer.py', ROOT / 'scripts/requirements-browser.txt']
    return {p.relative_to(ROOT).as_posix(): explorer.digest(p.read_bytes()) for p in paths}


def check_screenshot():
    report = json.loads((SITE / 'preview.json').read_bytes())
    assert report['inputSha256'] == screenshot_inputs(), 'Stale RH explorer screenshot; run the browser check with --refresh-preview'
    assert report['imageSha256'] == explorer.digest((SITE / 'preview.png').read_bytes()), 'RH screenshot changed without its capture audit'
    assert report['endpoint'] == metadata()['defaultEndpoint']
    data = json.loads((SITE / 'data.js').read_text().split('window.PROOF_DATA=', 1)[1].rstrip(';\n'))
    endpoint = next(e for e in data['endpoints'] if e['id'] == report['endpoint'])
    assert report['terminalTheorems'] == [data['nodes'][i]['id'] for i in endpoint['roots']]
    assert report['capture'] == 'Playwright Chromium screenshot of the native theorem explorer overview'
    assert report['viewport'] == {'width': 1440, 'height': 850}


def check_commit_update(base, staged=False):
    subprocess.run(['git', 'rev-parse', '--verify', base], cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    ref = ':' if staged else 'HEAD:'
    current = json.loads(subprocess.check_output(['git', 'show', ref + METADATA], cwd=ROOT))
    assert current == metadata(), 'Stage the current metadata together with its generated explorer'
    old = subprocess.run(['git', 'show', f'{base}:{METADATA}'], cwd=ROOT, capture_output=True)
    if old.returncode:
        # The first commit introducing the dedicated view has no predecessor.
        assert subprocess.run(['git', 'cat-file', '-e', f'{base}:{METADATA}'], cwd=ROOT, capture_output=True).returncode
        return
    previous = json.loads(old.stdout)['campaign']
    current = current['campaign']
    update, before = current['latestUpdate'], previous['latestUpdate']
    assert update['kind'] in ('theorem', 'presentation', 'maintenance')
    assert re.fullmatch(r'[a-z0-9-]+', update['id'])
    assert all(update[key].strip() and '\n' not in update[key] for key in ('title', 'body', 'next'))
    assert (ROOT / update['documentation'].split('#')[0]).is_file()
    assert update['sequence'] > before['sequence'], 'Every commit must advance Latest Update.sequence'
    assert update['id'] != before['id'], 'Give this commit its own Latest Update.id'
    assert (update['title'], update['body']) != (before['title'], before['body']), 'Latest Update must describe this commit, not repeat the last one'
    direction, prior = current['direction'], previous['direction']
    if (direction['branch'], direction['statement']) != (prior['branch'], prior['statement']):
        assert direction['changeReason'].strip() and direction['changeReason'] != prior['changeReason'], 'Record why the active branch or material direction changed'


def build():
    meta = metadata()
    taxonomy = json.loads((SHARED / 'metadata.json').read_bytes())
    status_text = (ROOT / 'docs/proof-status.json').read_text()
    status = json.loads(status_text.replace(
        'RH remains open', 'the independent native signed-signal estimate remains open'
    ))
    meta['families'] = taxonomy['families']
    meta['moduleFamilies'] = taxonomy['moduleFamilies']
    status['rhCampaign'] = meta['scopes']
    default = next(e for e in meta['endpoints'] if e['id'] == meta['defaultEndpoint'])
    assert default['statusPaths'] == [meta['campaign']['frontierStatusPath']], 'Default view must end at the current checked frontier'
    assert status['rhImplied'] is False, 'Revisit this explorer if the native root proves RH'
    outputs = {SITE / name: content for name, content in explorer.build(raw_path=RAW, metadata=meta, status_data=status).items()}
    outputs[SITE / 'families.json'] = explorer.json_bytes({'source': 'docs/theorem-explorer/metadata.json', 'families': taxonomy['families'], 'moduleFamilies': taxonomy['moduleFamilies']})
    for name in ('app.js', 'graph-core.js', 'style.css', 'source.html', 'document.html', 'snapshot.js', 'snapshot.css'):
        outputs[SITE / name] = (SHARED / name).read_bytes()
    html = (SHARED / 'index.html').read_text()
    html = html.replace('The zero-free region · RiemannGaussian proof explorer', meta['title'] + ' · RiemannGaussian')
    html = html.replace('The mathematics behind the zero-free region', meta['title'])
    html = html.replace("RiemannGaussian's zero-free region", "RiemannGaussian's native Gaussian–Suzuki theory")
    html = html.replace('href="metadata.json" target="_blank" rel="noopener">Family metadata', 'href="families.json" target="_blank" rel="noopener">Family metadata')
    html = html.replace('href="preview.svg"', 'href="preview.png"')
    outputs[SITE / 'native.html'] = html.encode()
    outputs[SITE / 'index.html'] = archive.render()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--node', default='node')
    parser.add_argument('--check-commit-update', metavar='BASE', help='Require a new update relative to this revision')
    parser.add_argument('--staged', action='store_true', help='Check the staged update rather than HEAD')
    args = parser.parse_args()
    if args.check_commit_update:
        check_commit_update(args.check_commit_update, args.staged)
    for path, content in build().items():
        if args.check:
            assert path.is_file() and path.read_bytes() == content, f'Stale RH campaign asset: {path.relative_to(ROOT)}'
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
    if args.check:
        check_screenshot()
    subprocess.run([args.node, str(ROOT / 'scripts/check_theorem_graph.cjs'), str(SITE)], cwd=ROOT, check=True)
    print('Shorter RH proof overview and native theorem dependencies are consistent.')


if __name__ == '__main__':
    main()
