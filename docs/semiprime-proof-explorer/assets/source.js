(() => {
  'use strict';
  const params = new URLSearchParams(location.search), name = params.get('module');
  const data = window.SEMIPRIME_DATA, row = data && data.modules.find(m => m.module === name);
  const error = message => {document.getElementById('source-title').textContent = 'Source unavailable'; const node = document.getElementById('source-error'); node.hidden = false; node.textContent = message;};
  if (!row) {error('Choose a module from the proof index. This name is not in the pinned publication inventory.'); return;}
  document.title = `${row.module} · Source snapshot`;
  document.getElementById('source-title').textContent = row.module.replace(/^RiemannGaussian\./, '');
  document.getElementById('source-provenance').textContent = `${row.path} · SHA-256 ${row.sha256} · ${data.metadata.status_labels[row.status]}. Exact indexed source bytes; declaration locations are source-parsed, not a Lean dependency export.`;
  const script = document.createElement('script'); script.src = `data/sources/${row.bucket}.js`;
  script.onerror = () => error('The local source bundle could not be loaded. Keep the complete generated explorer folder together.');
  script.onload = () => {
    const source = window.SEMIPRIME_SOURCES && window.SEMIPRIME_SOURCES[row.module];
    if (typeof source !== 'string') {error('The source bundle does not contain the indexed module.'); return;}
    const pre = document.getElementById('source-code');
    source.split('\n').forEach((text, index) => {const n = index + 1, line = document.createElement('span'); line.className = 'source-line'; line.id = `L${n}`; const anchor = document.createElement('a'); anchor.className = 'line-number'; anchor.href = `#L${n}`; anchor.textContent = String(n); anchor.setAttribute('aria-label', `Line ${n}`); line.append(anchor, document.createTextNode(text)); pre.append(line);});
    const selectLine = () => {
      pre.querySelectorAll('.requested-line').forEach(n => {n.classList.remove('requested-line'); n.removeAttribute('aria-current');});
      const highlight = document.getElementById(location.hash.slice(1));
      if (highlight && highlight.classList.contains('source-line')) {highlight.classList.add('requested-line'); highlight.setAttribute('aria-current', 'location'); highlight.tabIndex = -1; highlight.scrollIntoView({block: 'center'}); highlight.focus({preventScroll: true});}
      const release = window.PROOF_RELEASE;
      if (release && /^[a-f0-9]{40}$/.test(release.revision || '')) {const a = document.getElementById('repository-source'); a.href = `${data.metadata.repository_url}/blob/${release.revision}/${row.path}${/^#L\d+$/.test(location.hash) ? location.hash : ''}`; a.hidden = false;}
    };
    selectLine(); addEventListener('hashchange', selectLine);
  };
  document.head.append(script);
})();
