(function () {
  "use strict";
  const data = window.PROOF_DATA, release = window.PROOF_RELEASE;
  const core = window.ProofGraph, model = core.create(data), esc = core.escape;
  const $ = id => document.getElementById(id), svg = $("graph"), world = $("world");
  const families = new Map(data.families.map(f => [f.id, f]));
  let endpoint, scope, visible, edgeList = [], layout, selected = null, activeFamily = null;
  let camera = {x: 0, y: 0, scale: 1}, mapCamera, lastFocusedNode = null;
  const sourceURL = n => {
    if (!n.source) return null;
    if (!n.source.project) return n.source.url;
    if (release) return `${data.repository}/blob/${release.revision}/${n.source.path}#L${n.source.line}`;
    return `source.html?path=${encodeURIComponent(n.source.path)}#L${n.source.line}`;
  };
  const repoURL = path => `${data.repository}/blob/${release ? release.revision : "main"}/${path}`;
  const namedStep = i => data.nodes[i].project && data.nodes[i].kind === "theorem" && !data.nodes[i].generated;
  const buttonNode = (i, suffix = "") => `<button class="dependency" data-reveal="${i}">${esc(data.nodes[i].label)}<small>${esc(data.nodes[i].name)}${suffix ? " · " + esc(suffix) : ""}</small></button>`;
  const notify = text => { $("announcement").textContent = text; };

  function updateHash() {
    const params = new URLSearchParams({endpoint: endpoint.id});
    if (selected !== null) params.set("node", data.nodes[selected].id);
    history.replaceState(null, "", "#" + params);
  }
  function resetEndpoint(id, reset = true) {
    endpoint = data.endpoints.find(e => e.id === id) || data.endpoints.find(e => e.id === data.defaultEndpoint);
    scope = model.closure(endpoint.roots); visible = model.overview(endpoint.roots);
    selected = null; activeFamily = null;
    $("endpoint").value = endpoint.id;
    $("scope-text").textContent = endpoint.scope;
    $("details").hidden = true; $("search").value = ""; closeSearch();
    renderFamilies(); render(true);
    if (reset) updateHash();
  }
  function renderFamilies() {
    const counts = new Map();
    for (const i of scope) if (data.nodes[i].project) counts.set(data.nodes[i].family, (counts.get(data.nodes[i].family) || 0) + 1);
    $("families").innerHTML = data.families.filter(f => counts.has(f.id)).map(f =>
      `<button class="family-chip" data-family="${f.id}" style="--family:${f.color}" aria-pressed="${activeFamily === f.id}" title="${esc(f.description)}"><span class="dot"></span>${esc(f.label)}<span class="family-count">${counts.get(f.id)}</span></button>`).join("");
  }
  function render(fit = false) {
    hideTooltip();
    edgeList = model.edges(visible); layout = model.layout(visible, edgeList);
    let html = layout.zones.map(z => {
      const f = families.get(z.family);
      return `<g class="zone"><rect x="${z.x}" y="${z.y}" width="${z.width}" height="${z.height}" rx="12" fill="${f.color}" fill-opacity=".055" stroke="${f.color}" stroke-opacity=".33"/><text class="zone-label" x="${z.x + 12}" y="${z.y + 20}" fill="${f.color}">${esc(f.label)}</text></g>`;
    }).join("");
    html += edgeList.map((e, i) => {
      const curve = core.curve(layout.positions.get(e.source), layout.positions.get(e.target));
      const type = e.kinds.includes("type") ? " type" : "";
      return `<g data-edge="${i}"><path class="edge-hit" d="${curve}"/><path class="edge${e.collapsed ? " collapsed" : ""}${type}" d="${curve}"/><title>${esc(data.nodes[e.source].name)} → ${esc(data.nodes[e.target].name)}; ${e.path.length - 1} reference step(s). Select to inspect.</title></g>`;
    }).join("");
    for (const i of visible) {
      const n = data.nodes[i], p = layout.positions.get(i), f = families.get(n.family), url = sourceURL(n);
      const terminal = endpoint.roots.includes(i);
      const count = model.direct[i].filter(d => data.nodes[d.id].project).length;
      html += `<g class="node${terminal ? " terminal" : ""}${i === selected ? " selected" : ""}" data-node="${i}" style="--family:${f.color}" tabindex="0" role="button" aria-label="${esc(n.name)}. ${esc(f.label)}. Inspect theorem details."><rect class="node-box" x="${p.x}" y="${p.y}" width="${p.width}" height="${p.height}" rx="8"/><text class="node-label">`;
      core.wrap(n.label, 27, 2).forEach((line, j) => { html += `<tspan x="${p.x + 13}" y="${p.y + 25 + j * 18}">${esc(line)}</tspan>`; });
      html += `</text><text class="node-meta" x="${p.x + 13}" y="${p.y + p.height - 10}">${terminal ? "TERMINAL THEOREM" : n.generated ? "GENERATED HELPER" : esc(n.kind.toUpperCase())}${count ? ` · ${count} project refs` : ""}</text>`;
      if (url) html += `<a href="${esc(url)}" target="_blank" rel="noopener" aria-label="Open Lean source for ${esc(n.name)}" class="source-shortcut"><title>Open exact Lean source${n.source.exact ? "" : " (enclosing declaration)"}</title><text class="node-source" x="${p.x + p.width - 24}" y="${p.y + p.height - 10}">↗</text></a>`;
      html += "</g>";
    }
    world.innerHTML = html;
    const projectCount = [...scope].filter(i => data.nodes[i].project).length;
    $("counts").textContent = `${visible.size.toLocaleString()} visible / ${projectCount.toLocaleString()} project declarations in this proof · ${edgeList.length.toLocaleString()} displayed paths`;
    if (fit) fitAll(); else transform();
    paintSelection();
  }
  function paintSelection() {
    world.querySelectorAll(".node").forEach(el => el.classList.toggle("selected", Number(el.dataset.node) === selected));
    world.querySelectorAll("[data-edge]").forEach(el => {
      const e = edgeList[Number(el.dataset.edge)];
      el.querySelector(".edge").classList.toggle("related", selected !== null && (e.target === selected || e.source === selected));
    });
  }
  function transform() {
    world.setAttribute("transform", `translate(${camera.x} ${camera.y}) scale(${camera.scale})`);
    $("zoom-value").value = Math.round(camera.scale * 100) + "%";
    drawMinimap();
  }
  function dimensions() { const r = svg.getBoundingClientRect(); return {width: r.width, height: r.height}; }
  function fitAll() {
    if (!layout) return;
    const {width, height} = dimensions();
    const availableHeight = Math.max(180, height - 115);
    camera.scale = Math.min(1.1, (width - 70) / layout.width, availableHeight / layout.height);
    camera.x = (width - layout.width * camera.scale) / 2;
    camera.y = 42 + (availableHeight - layout.height * camera.scale) / 2;
    transform();
  }
  function zoom(factor, x, y) {
    const dim = dimensions(); x ??= dim.width / 2; y ??= dim.height / 2;
    const next = Math.max(.025, Math.min(3.5, camera.scale * factor));
    const ratio = next / camera.scale;
    camera.x = x - (x - camera.x) * ratio; camera.y = y - (y - camera.y) * ratio;
    camera.scale = next; transform(); hideTooltip();
  }
  function centerNode(i) {
    const p = layout.positions.get(i); if (!p) return;
    const {width, height} = dimensions();
    camera.scale = Math.min(1.15, Math.max(.7, width / 800));
    const rightPanel = $("details").hidden || width < 800 ? 0 : 420;
    camera.x = (width - rightPanel) / 2 - (p.x + p.width / 2) * camera.scale;
    camera.y = height / 2 - (p.y + p.height / 2) * camera.scale;
    transform();
  }
  function drawMinimap() {
    if (!layout) return;
    const s = Math.min(244 / layout.width, 96 / layout.height), x = (260 - layout.width * s) / 2, y = (112 - layout.height * s) / 2;
    mapCamera = {s, x, y};
    let html = '<rect width="260" height="112" fill="transparent"/>';
    for (const [i, p] of layout.positions) html += `<rect x="${x + p.x * s}" y="${y + p.y * s}" width="${Math.max(2, p.width * s)}" height="${Math.max(2, p.height * s)}" rx="1" fill="${families.get(data.nodes[i].family).color}" opacity=".6"/>`;
    const dim = dimensions();
    html += `<rect x="${x - camera.x / camera.scale * s}" y="${y - camera.y / camera.scale * s}" width="${dim.width / camera.scale * s}" height="${dim.height / camera.scale * s}" fill="#adffdc" fill-opacity=".035" stroke="#c4e1d7" stroke-width="1"/>`;
    $("minimap").innerHTML = html;
  }
  function showNode(i, center = false) {
    if (!scope.has(i)) return;
    if (!visible.has(i)) { visible.add(i); render(); }
    selected = i; lastFocusedNode = i;
    const n = data.nodes[i], f = families.get(n.family), src = n.source, url = sourceURL(n);
    const projectRefs = model.direct[i].filter(d => data.nodes[d.id].project);
    const externalRefs = model.direct[i].filter(d => !data.nodes[d.id].project);
    const location = src ? `${src.path}${src.line ? ":" + src.line : ""}` : "Library declaration with no exported source range";
    let html = `<span class="proof-kind" style="--family:${f.color}">${esc(f.label)} · ${esc(n.kind)}${n.generated ? " · generated helper" : ""}</span><h2>${esc(n.label)}</h2><p class="decl-name">${esc(n.id)}</p>`;
    if (n.summary) html += `<p>${esc(n.summary)}</p>`;
    html += '<div class="button-row">';
    if (url) html += `<a class="source-button" href="${esc(url)}" target="_blank" rel="noopener">Lean source ↗</a>`;
    if (n.project) html += `<button id="expand-deps">Expand dependencies</button>`;
    html += `</div><p class="audit-field">${esc(location)}${src && !src.exact ? " · enclosing declaration" : ""}${src && src.project && !release ? " · exact local snapshot" : ""}</p><h3>Lean statement</h3><pre>${esc(n.statement)}</pre><h3>Proof audit</h3><p class="audit-ok">✓ Transitive axioms checked by Lean</p><p class="audit-field">${n.axioms.length ? esc(n.axioms.join(", ")) : "No axiom dependencies"}</p><a class="small-link" href="audit.json" target="_blank" rel="noopener">Graph audit, endpoint checks &amp; source hashes ↗</a><a class="small-link" href="lean-graph.json.gz" download>Exact Lean dependency export (.json.gz)</a>`;
    if (release) html += `<a class="small-link" href="${esc(release.runUrl)}" target="_blank" rel="noopener">CI verification of ${release.revision.slice(0, 12)} ↗</a>`;
    else html += '<p class="audit-field">Local export; no published commit or new remote CI run is claimed.</p>';
    for (const path of n.documentation) html += `<a class="small-link" href="${esc(docURL(path))}" target="_blank" rel="noopener">${esc(path.replace("docs/", ""))} ↗</a>`;
    if (n.toolkits.length) {
      html += '<details><summary>Linked project audit metadata</summary>';
      for (const t of n.toolkits) html += `<button class="dependency" data-toolkit="${esc(t.key)}">${esc(t.key)}</button>`;
      html += '</details>';
    }
    html += `<h3>Direct references</h3><p>${projectRefs.length} project · ${externalRefs.length} external library. Body and statement references remain distinguishable.</p>`;
    html += projectRefs.map(d => buttonNode(d.id, d.kind === "body" ? "body reference" : "statement / structure reference")).join("");
    if (externalRefs.length) html += `<details><summary>${externalRefs.length} external library references</summary>${externalRefs.map(d => buttonNode(d.id, d.kind + " reference")).join("")}</details>`;
    html += `<div class="button-row"><button id="copy-link">Copy theorem link</button><button id="focus-node">Center on canvas</button></div>`;
    $("detail-content").innerHTML = html; $("details").hidden = false; $("details").scrollTop = 0;
    $("expand-deps")?.addEventListener("click", () => expandNode(i));
    $("focus-node").addEventListener("click", () => centerNode(i));
    $("copy-link").addEventListener("click", async () => {
      updateHash();
      try { await navigator.clipboard.writeText(locationURL()); $("copy-link").textContent = "Copied"; }
      catch { $("copy-link").textContent = "Link is in the address bar"; }
    });
    paintSelection(); hideTooltip(); updateHash(); if (center) centerNode(i);
    notify(`Selected ${n.name}`);
  }
  function locationURL() { return window.location.href; }
  function docURL(path) { return release ? repoURL(path) : `document.html?path=${encodeURIComponent(path)}`; }
  function expandNode(i) {
    const deps = model.nearest(i, namedStep);
    deps.forEach(d => visible.add(d));
    visible.add(i); render(true); showNode(i);
    notify(`Expanded ${deps.length} named proof dependencies.`);
  }
  function showEdge(i) {
    const e = edgeList[i]; selected = null; paintSelection(); hideTooltip();
    $("detail-content").innerHTML = `<span class="proof-kind">EXPORTED DEPENDENCY PATH</span><h2>${e.path.length - 1} reference step${e.path.length === 2 ? "" : "s"}</h2><p>This path follows constants in Lean's elaborated declarations, from an earlier ingredient to the theorem using it. It is one witnessed route; other routes and hypotheses may also contribute.</p>${e.path.map((n, k) => buttonNode(n, k < e.kinds.length ? e.kinds[k] + " reference in next step" : "used by the next visible theorem")).join("")}<div class="button-row"><button id="expand-path">Expand this path</button></div>`;
    $("details").hidden = false; $("details").scrollTop = 0;
    $("expand-path").addEventListener("click", () => { e.path.forEach(n => visible.add(n)); render(true); $("details").hidden = true; });
    updateHash();
  }
  function showScope() {
    selected = null; paintSelection(); hideTooltip(); updateHash();
    $("detail-content").innerHTML = `<span class="proof-kind">SCOPE &amp; PROVENANCE</span><h2>${esc(endpoint.label)}</h2><p>${esc(endpoint.scope)}</p>${endpoint.roots.map(i => buttonNode(i)).join("")}<h3>What has been compared</h3><p>${esc(data.benchmarkScope)}</p><p>${esc(data.limitNote)}</p><h3>Verification</h3><p class="audit-ok">Every displayed declaration has only permitted transitive axioms.</p><p>${esc(data.audit.externalBoundary)}</p><a class="small-link" href="audit.json" target="_blank" rel="noopener">Complete graph and axiom audit ↗</a><a class="small-link" href="${esc(docURL(endpoint.documentation))}" target="_blank" rel="noopener">Mathematical proof notes ↗</a><a class="small-link" href="${esc(release ? "proof-status.json" : "../../docs/proof-status.json")}" target="_blank" rel="noopener">Whole-project proof-status JSON ↗</a>${release ? `<a class="small-link" href="${esc(release.runUrl)}" target="_blank" rel="noopener">Exact-commit CI run ↗</a>` : '<p class="audit-field">This is an unpublished local proof snapshot.</p>'}`;
    $("details").hidden = false; $("details").scrollTop = 0;
  }
  function showToolkit(key) {
    const value = data.toolkits[key]; if (!value) return;
    $("detail-content").innerHTML = `<span class="proof-kind">EXISTING PROJECT AUDIT METADATA</span><h2>${esc(key)}</h2><p>Read from the generated proof-status JSON. These descriptions do not create graph edges.</p>` + Object.entries(value).map(([k, v]) => `<h3>${esc(k)}</h3><div class="status-value">${esc(typeof v === "string" ? v : JSON.stringify(v, null, 2))}</div>`).join("");
    $("details").scrollTop = 0;
  }
  function closeDetails() {
    $("details").hidden = true; selected = null; paintSelection(); updateHash();
    if (lastFocusedNode !== null) world.querySelector(`[data-node="${lastFocusedNode}"]`)?.focus({preventScroll: true});
  }
  function showTooltip(i, x, y) {
    const n = data.nodes[i], f = families.get(n.family);
    $("tooltip").innerHTML = `<span class="hover-family" style="--family:${f.color}">${esc(f.label)} · ${esc(n.kind)}</span><strong>${esc(n.label)}</strong><span class="hover-name">${esc(n.name)}</span>${n.summary ? `<p>${esc(n.summary.slice(0, 290))}${n.summary.length > 290 ? "…" : ""}</p>` : ""}<p>${n.source ? esc(n.source.path + (n.source.line ? ":" + n.source.line : "")) : "External library boundary"}${n.source && !n.source.exact ? " · enclosing declaration" : ""}<br>✓ ${esc(n.axioms.join(", ") || "No axioms")}<br>Select for statement, source and audits.</p>`;
    const tip = $("tooltip"); tip.hidden = false;
    const rect = tip.getBoundingClientRect();
    tip.style.left = Math.max(10, Math.min(x + 15, window.innerWidth - rect.width - 12)) + "px";
    tip.style.top = Math.max(10, Math.min(y + 15, window.innerHeight - rect.height - 12)) + "px";
  }
  function hideTooltip() { $("tooltip").hidden = true; }
  function closeSearch() { $("search-results").hidden = true; $("search").setAttribute("aria-expanded", "false"); }
  function search() {
    const q = $("search").value.trim().toLocaleLowerCase();
    if (!q) { closeSearch(); return; }
    const terms = q.split(/\s+/);
    const found = [...scope].filter(i => {
      const n = data.nodes[i], text = [n.id, n.label, n.summary, families.get(n.family).label].join(" ").toLocaleLowerCase();
      return terms.every(t => text.includes(t));
    }).sort((a, b) => Number(data.nodes[b].project) - Number(data.nodes[a].project) || Number(data.nodes[a].generated) - Number(data.nodes[b].generated) || data.nodes[a].id.localeCompare(data.nodes[b].id));
    $("search-results").innerHTML = `<div class="search-heading">${found.length} matching declaration${found.length === 1 ? "" : "s"} in this proof${found.length > 40 ? " · first 40 shown; refine your search" : ""}</div>` + found.slice(0, 40).map(i => {
      const n = data.nodes[i]; return `<button class="search-result" data-search-node="${i}">${esc(n.label)}<small>${esc(families.get(n.family).label)} · ${esc(n.id)}</small></button>`;
    }).join("");
    $("search-results").hidden = false; $("search").setAttribute("aria-expanded", "true");
  }

  // Event delegation keeps large expanded views responsive.
  world.addEventListener("click", event => {
    if (event.target.closest("a")) return;
    const node = event.target.closest("[data-node]");
    if (node) { showNode(Number(node.dataset.node)); return; }
    const edge = event.target.closest("[data-edge]"); if (edge) showEdge(Number(edge.dataset.edge));
  });
  world.addEventListener("dblclick", event => { const n = event.target.closest("[data-node]"); if (n && !event.target.closest("a")) { event.preventDefault(); expandNode(Number(n.dataset.node)); } });
  world.addEventListener("pointerover", event => { const n = event.target.closest("[data-node]"); if (n && !n.contains(event.relatedTarget)) showTooltip(Number(n.dataset.node), event.clientX, event.clientY); });
  world.addEventListener("pointerout", event => { const n = event.target.closest("[data-node]"); if (n && !n.contains(event.relatedTarget)) hideTooltip(); });
  world.addEventListener("focusin", event => { const n = event.target.closest("[data-node]"); if (n) { const r = n.getBoundingClientRect(); showTooltip(Number(n.dataset.node), r.left, r.bottom); } });
  world.addEventListener("focusout", hideTooltip);
  world.addEventListener("keydown", event => {
    const n = event.target.closest("[data-node]"); if (!n || event.target.closest("a")) return;
    if (event.key === "Enter" || event.key === " ") { event.preventDefault(); showNode(Number(n.dataset.node)); }
  });
  $("detail-content").addEventListener("click", event => {
    const n = event.target.closest("[data-reveal]"); if (n) showNode(Number(n.dataset.reveal), true);
    const t = event.target.closest("[data-toolkit]"); if (t) showToolkit(t.dataset.toolkit);
  });
  $("search-results").addEventListener("click", event => { const n = event.target.closest("[data-search-node]"); if (n) { closeSearch(); showNode(Number(n.dataset.searchNode), true); } });
  $("search-results").addEventListener("keydown", event => {
    const buttons = [...$("search-results").querySelectorAll("button")], i = buttons.indexOf(document.activeElement);
    if (event.key === "ArrowDown" || event.key === "ArrowUp") { event.preventDefault(); buttons[(i + (event.key === "ArrowDown" ? 1 : buttons.length - 1)) % buttons.length]?.focus(); }
  });
  $("search").addEventListener("input", search);
  $("search").addEventListener("keydown", event => { if (event.key === "ArrowDown") { event.preventDefault(); $("search-results").querySelector("button")?.focus(); } });
  document.addEventListener("click", event => { if (!event.target.closest(".search-box")) closeSearch(); });
  $("families").addEventListener("click", event => {
    const b = event.target.closest("[data-family]"); if (!b) return;
    activeFamily = activeFamily === b.dataset.family ? null : b.dataset.family;
    visible = model.overview(endpoint.roots);
    if (activeFamily) for (const i of scope) if (namedStep(i) && data.nodes[i].family === activeFamily) visible.add(i);
    selected = null; $("details").hidden = true; renderFamilies(); render(true); updateHash();
  });
  $("endpoint").addEventListener("change", () => resetEndpoint($("endpoint").value));
  $("overview").addEventListener("click", () => resetEndpoint(endpoint.id));
  $("all-steps").addEventListener("click", () => { visible = new Set([...scope].filter(namedStep)); endpoint.roots.forEach(i => visible.add(i)); selected = null; activeFamily = null; $("details").hidden = true; renderFamilies(); render(true); updateHash(); notify("All authored theorem steps are now visible. Zoom or search to inspect them."); });
  $("terminal").addEventListener("click", () => showNode(endpoint.roots[0], true));
  $("fit").addEventListener("click", fitAll);
  $("zoom-in").addEventListener("click", () => zoom(1.25));
  $("zoom-out").addEventListener("click", () => zoom(.8));
  $("close-details").addEventListener("click", closeDetails);
  $("scope-more").addEventListener("click", showScope);
  $("help-button").addEventListener("click", () => $("help").showModal());
  $("close-help").addEventListener("click", () => $("help").close());
  svg.addEventListener("wheel", event => { event.preventDefault(); const r = svg.getBoundingClientRect(); zoom(Math.exp(-event.deltaY * .0015), event.clientX - r.left, event.clientY - r.top); }, {passive: false});
  const pointers = new Map();
  let touchGesture = false;
  svg.addEventListener("click", event => {
    if (touchGesture) { event.preventDefault(); event.stopPropagation(); }
  }, {capture: true});
  svg.addEventListener("pointerdown", event => {
    const touch = event.pointerType === "touch";
    if (event.button !== 0 || (!touch && event.target.closest("a, [data-node], [data-edge]"))) return;
    if (!pointers.size) touchGesture = false;
    pointers.set(event.pointerId, {x: event.clientX, y: event.clientY, startX: event.clientX, startY: event.clientY});
    if (pointers.size > 1) touchGesture = true;
    // Keep taps on boxes and source links native; their pointer events still
    // bubble to the canvas, so a pinch can begin over either kind of element.
    (touch ? event.target : svg).setPointerCapture(event.pointerId);
    svg.classList.add("dragging"); hideTooltip();
  });
  svg.addEventListener("pointermove", event => {
    if (!pointers.has(event.pointerId)) return;
    const old = [...pointers.values()], previous = pointers.get(event.pointerId);
    pointers.set(event.pointerId, {...previous, x: event.clientX, y: event.clientY});
    if (event.pointerType === "touch" && Math.hypot(event.clientX - previous.startX, event.clientY - previous.startY) > 8) touchGesture = true;
    if (pointers.size === 2) {
      const now = [...pointers.values()], dist = pts => Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
      const r = svg.getBoundingClientRect(), ox = (old[0].x + old[1].x) / 2, oy = (old[0].y + old[1].y) / 2;
      if (dist(old) > 0) zoom(dist(now) / dist(old), ox - r.left, oy - r.top);
      camera.x += (now[0].x + now[1].x) / 2 - ox; camera.y += (now[0].y + now[1].y) / 2 - oy;
    } else { camera.x += event.clientX - previous.x; camera.y += event.clientY - previous.y; }
    transform();
  });
  for (const event of ["pointerup", "pointercancel", "lostpointercapture"]) svg.addEventListener(event, e => { pointers.delete(e.pointerId); if (!pointers.size) svg.classList.remove("dragging"); });
  $("minimap").addEventListener("click", event => {
    const r = $("minimap").getBoundingClientRect(), x = (event.clientX - r.left) * 260 / r.width, y = (event.clientY - r.top) * 112 / r.height;
    const dim = dimensions(); camera.x = dim.width / 2 - (x - mapCamera.x) / mapCamera.s * camera.scale;
    camera.y = dim.height / 2 - (y - mapCamera.y) / mapCamera.s * camera.scale; transform();
  });
  document.addEventListener("keydown", event => {
    if (event.key === "Escape") { closeSearch(); hideTooltip(); if (!$("details").hidden) closeDetails(); return; }
    if (event.target.closest("input,select,textarea") || $("help").open) return;
    if (event.key === "/") { event.preventDefault(); $("search").focus(); }
    if (event.key.toLowerCase() === "f") fitAll();
    if (event.key === "+" || event.key === "=") zoom(1.25);
    if (event.key === "-") zoom(.8);
    if (event.target === svg && event.key.startsWith("Arrow")) {
      event.preventDefault(); camera.x += event.key === "ArrowLeft" ? 80 : event.key === "ArrowRight" ? -80 : 0;
      camera.y += event.key === "ArrowUp" ? 80 : event.key === "ArrowDown" ? -80 : 0; transform();
    }
  });
  window.addEventListener("resize", () => { hideTooltip(); transform(); });
  function loadHash() {
    const p = new URLSearchParams(window.location.hash.slice(1)); resetEndpoint(p.get("endpoint"), false);
    const i = model.byName.get(p.get("node")); if (i !== undefined && scope.has(i)) showNode(i, true);
  }
  window.addEventListener("hashchange", loadHash);
  $("endpoint").innerHTML = data.endpoints.map(e => `<option value="${e.id}">${esc(e.label)}</option>`).join("");
  $("lean-badge").textContent = `✓ Lean ${data.leanVersion} · axioms audited`;
  $("scope-note").textContent = data.limitNote;
  $("metadata-guide").href = docURL("docs/theorem-explorer.md");
  if (release) { $("revision-link").textContent = `Verified commit ${release.revision.slice(0, 10)} ↗`; $("revision-link").href = release.runUrl; }
  loadHash();
  // Read-only diagnostics used by integrity and interaction tests.
  window.PROOF_VIEW = {model, get visible() {return new Set(visible);}, get edges() {return edgeList;}, get layout() {return layout;}, get endpoint() {return endpoint;}};
})();
