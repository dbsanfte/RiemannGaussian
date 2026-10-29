/* Curated algorithm navigation. These links are not elaborated Lean dependencies. */
(() => {
  'use strict';
  const data = window.SEMIPRIME_DATA;
  if (!data) return;
  const $ = id => document.getElementById(id);
  const labels = data.metadata.status_labels;
  const stageLabels = {...labels, partial: 'Partial machine pipeline', mixed: 'Components finalized · join open', open: 'Open obligation', proved: 'Mathematical result proved', finalized: 'Components finalized'};
  const el = (tag, cls, text) => {const n = document.createElement(tag); if (cls) n.className = cls; if (text !== undefined) n.textContent = text; return n;};
  const badge = (status, stage = false) => el('span', `status ${status}`, (stage ? stageLabels : labels)[status] || status);
  const link = (text, href, cls) => {const n = el('a', cls, text); n.href = href; return n;};
  const sourceURL = (module, line = 1) => `source.html?module=${encodeURIComponent(module)}#L${line}`;
  const moduleMap = new Map(data.modules.map(m => [m.module, m]));
  const stageMap = new Map(data.stages.map(s => [s.id, s]));
  let chosen = null, page = 0;
  const pageSize = 35;
  $('intro').textContent = data.metadata.intro;
  $('target-scope').textContent = data.metadata.target_scope;
  $('pipeline-note').textContent = data.metadata.pipeline_disclaimer;
  $('evidence-note').textContent = data.metadata.evidence_disclaimer;
  $('module-count').textContent = data.modules.length.toLocaleString();
  $('group-count').textContent = data.groups.length.toLocaleString();
  $('index-scope').textContent = `${data.modules.length.toLocaleString()} source files; declaration locations are parsed from authored source, not exported from Lean. Unclassified legacy files carry no new validation claim. No completion percentage is inferred.`;
  if (window.PROOF_RELEASE && /^[a-f0-9]{40}$/.test(window.PROOF_RELEASE.revision || '')) $('release-status').textContent = `Published revision ${window.PROOF_RELEASE.revision.slice(0, 12)}`;
  if (window.PROOF_RELEASE && /^https:\/\/github\.com\/[^/]+\/[^/]+\/actions\/runs\/\d+(?:\/.*)?$/.test(window.PROOF_RELEASE.runUrl || '')) {const a = $('publication-verification'); a.hidden = false; a.href = window.PROOF_RELEASE.runUrl;}

  function chooseStage(id, updateHash = true) {
    const stage = stageMap.get(id); if (!stage) return;
    chosen = id;
    if (window.SEMIPRIME_VIEW) window.SEMIPRIME_VIEW.stage = id;
    for (const b of $('stage-list').querySelectorAll('button')) b.setAttribute('aria-pressed', String(b.dataset.stage === id));
    const panel = $('stage-detail'); panel.replaceChildren();
    panel.append(badge(stage.status, true), el('h3', '', stage.title), el('p', 'summary', stage.summary));
    if (stage.scope_note) panel.append(el('p', 'note', stage.scope_note));
    for (const [field, title] of [['inputs', 'Physical inputs / assumptions'], ['outputs', 'What is established']]) {
      if (!stage[field] || !stage[field].length) continue;
      panel.append(el('h4', '', title)); const ul = el('ul');
      for (const item of stage[field]) ul.append(el('li', '', item)); panel.append(ul);
    }
    if (stage.remaining.length) {
      const box = el('div', 'remaining'); box.append(el('h4', '', 'Still required'));
      const ul = el('ul'); for (const item of stage.remaining) ul.append(el('li', '', item)); box.append(ul); panel.append(box);
    }
    if (stage.proof_anchors.length) {
      panel.append(el('h4', '', 'Read the proof sources'));
      const links = el('div', 'proof-links');
      for (const a of stage.proof_anchors) {
        const m = moduleMap.get(a.module); const n = link(a.label || a.declaration || a.module.replace(/^RiemannGaussian\./, ''), sourceURL(a.module, a.line), 'proof-link');
        n.append(el('code', '', `${m.path}:${a.line} · ${labels[m.status]}`)); links.append(n);
      }
      panel.append(links);
    }
    const groups = stage.groups.map(g => data.groups.find(row => row.id === g)).filter(Boolean);
    if (groups.length) {
      panel.append(el('h4', '', 'Recorded component evidence')); const links = el('div', 'group-links');
      for (const group of groups) links.append(link(group.title || group.id, group.local_evidence || 'data/audit.json'));
      panel.append(links);
    }
    const browse = el('button', 'stage-search', 'Show this stage in the module index →'); browse.type = 'button';
    browse.addEventListener('click', () => {$('stage-filter').value = id; $('search').value = ''; page = 0; renderModules(); $('modules').scrollIntoView(); $('search').focus({preventScroll: true});}); panel.append(browse);
    if (updateHash) history.replaceState(null, '', `#stage=${encodeURIComponent(id)}`);
  }
  data.stages.forEach((s, i) => {
    const li = el('li'); const b = el('button', 'stage-button'); b.type = 'button'; b.dataset.stage = s.id; b.setAttribute('aria-controls', 'stage-detail'); b.setAttribute('aria-pressed', 'false');
    b.append(el('span', 'step-number', String(i + 1).padStart(2, '0'))); const body = el('span'); body.append(el('span', 'stage-name', s.title), badge(s.status, true)); b.append(body);
    b.addEventListener('click', () => chooseStage(s.id));
    b.addEventListener('keydown', e => {if (!['ArrowDown', 'ArrowUp', 'Home', 'End'].includes(e.key)) return; e.preventDefault(); const buttons = [...$('stage-list').querySelectorAll('button')]; let next = e.key === 'Home' ? 0 : e.key === 'End' ? buttons.length - 1 : (i + (e.key === 'ArrowDown' ? 1 : -1) + buttons.length) % buttons.length; buttons[next].focus(); chooseStage(buttons[next].dataset.stage);});
    li.append(b); $('stage-list').append(li);
    const option = el('option', '', s.title); option.value = s.id; $('stage-filter').append(option);
  });
  const fromHash = new URLSearchParams(location.hash.slice(1)).get('stage');
  chooseStage(stageMap.has(fromHash) ? fromHash : data.stages[0].id, false);
  addEventListener('hashchange', () => {const id = new URLSearchParams(location.hash.slice(1)).get('stage'); if (id && id !== chosen) chooseStage(id, false);});
  for (const [value, title] of Object.entries(labels)) {const o = el('option', '', title); o.value = value; $('status-filter').append(o);}

  function renderModules() {
    const q = $('search').value.trim().toLowerCase(); const status = $('status-filter').value; const stage = $('stage-filter').value;
    const rows = data.modules.filter(m => (status === 'all' || m.status === status) && (stage === 'all' || m.stages.includes(stage)) && (!q || m.search.includes(q)));
    const pages = Math.max(1, Math.ceil(rows.length / pageSize)); page = Math.min(page, pages - 1);
    $('results-status').textContent = `${rows.length.toLocaleString()} module${rows.length === 1 ? '' : 's'}${q ? ` matching “${$('search').value.trim()}”` : ''}. ${rows.length ? `Showing ${page * pageSize + 1}–${Math.min((page + 1) * pageSize, rows.length)}.` : 'Try a broader query or reset the filters.'}`;
    const list = $('module-list'); list.replaceChildren();
    if (!rows.length) list.append(el('p', 'empty-state', 'No modules match these filters.'));
    for (const m of rows.slice(page * pageSize, (page + 1) * pageSize)) {
      const row = el('article', 'module-row'); row.dataset.module = m.module; const body = el('div'); body.append(link(m.module.replace(/^RiemannGaussian\./, ''), sourceURL(m.module), 'module-name'));
      body.append(el('p', 'module-summary', m.scope_note || 'See the source and the recorded evidence boundary for this module.'));
      const matches = q ? m.declarations.filter(d => d.name.toLowerCase().includes(q)) : m.declarations.filter(d => d.kind === 'theorem').slice(0, 2);
      if (matches.length) {const names = el('div', 'module-declarations'); for (const d of matches.slice(0, 3)) names.append(link(d.name.split('.').pop(), sourceURL(m.module, d.line))); if (matches.length > 3) names.append(el('span', '', `+${matches.length - 3} declarations`)); body.append(names);}
      row.append(body, badge(m.status)); list.append(row);
    }
    $('previous').disabled = page === 0; $('next').disabled = page + 1 >= pages; $('page-status').textContent = `Page ${page + 1} of ${pages}`;
    window.SEMIPRIME_VIEW = {stage: chosen, filteredModules: rows.length, page, pages};
  }
  for (const id of ['search', 'status-filter', 'stage-filter']) $(id).addEventListener(id === 'search' ? 'input' : 'change', () => {page = 0; renderModules();});
  $('reset').addEventListener('click', () => {$('search').value = ''; $('status-filter').value = 'all'; $('stage-filter').value = 'all'; page = 0; renderModules(); $('search').focus();});
  $('previous').addEventListener('click', () => {page--; renderModules(); $('results-status').scrollIntoView({block: 'nearest'});});
  $('next').addEventListener('click', () => {page++; renderModules(); $('results-status').scrollIntoView({block: 'nearest'});});
  document.addEventListener('keydown', e => {if (e.key === '/' && !['INPUT', 'TEXTAREA', 'SELECT'].includes(document.activeElement.tagName)) {e.preventDefault(); $('search').focus();} if (e.key === 'Escape' && document.activeElement === $('search')) {$('search').value = ''; page = 0; renderModules();}});
  for (const item of data.metadata.glossary) {const card = el('article'); card.append(el('h3', '', item.term), el('p', '', item.meaning)); $('glossary').append(card);}
  if (data.archived_sources && data.archived_sources.length) {
    const node = $('archive-note'); node.hidden = false;
    node.append(el('p', '', `${data.archived_sources.length} historical external-bridge files are archived outside the current algorithm and ordinary library build. They are retained as historical source, not labelled freshly built.`));
    for (const row of data.archived_sources) node.append(link(row.module || row.path.split('/').pop(), row.local_snapshot), document.createTextNode(' · '));
  }
  renderModules();
})();
