// No hand-drawn implication edges: use the same witnessed paths as the explorer.
const path = require("node:path");
const vm = require("node:vm");
const fs = require("node:fs");
const core = require("../docs/theorem-explorer/graph-core.js");
const context = {window: {}};
vm.runInNewContext(fs.readFileSync(path.join(__dirname, "../docs/theorem-explorer/data.js"), "utf8"), context);
const data = context.window.PROOF_DATA, graph = core.create(data), esc = core.escape;
const root = data.endpoints.find(e => e.id === data.defaultEndpoint);
const scope = graph.closure(root.roots);
const highlights = [
  "RiemannGaussian.pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one",
  "RiemannGaussian.ZetaEulerLineBound.bound",
  "RiemannGaussian.ZetaGaussianStripPhaseFamily.source_add_mixedWork_le_exactBudget",
  "RiemannGaussian.phaseContactExactFamily_kernel_nonneg",
  "RiemannGaussian.ZetaGaussianBandBudget.budget_le",
  "RiemannGaussian.ZetaGaussianBandExclusion.selected_source_lower",
  "RiemannGaussian.ZetaGaussianBandExclusion.exact_strip"
];
const visible = new Set(highlights.map(n => graph.byName.get(n)).filter(i => scope.has(i)));
root.roots.forEach(i => visible.add(i));
const edges = graph.edges(visible), layout = graph.layout(visible, edges, {width: 204, columnGap: 58, height: 67});
const families = new Map(data.families.map(f => [f.id, f]));
const canvasWidth = 1280, canvasHeight = 430;
const scale = Math.min(1210 / layout.width, 305 / layout.height);
const x = (canvasWidth - layout.width * scale) / 2, y = 91;
let svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${canvasWidth} ${canvasHeight}" role="img" aria-labelledby="title desc">
<title id="title">Explore the Lean proof of the explicit zero-free band</title>
<desc id="desc">A compact selection of actual proof dependencies, grouped by mathematical family. Open the interactive explorer to zoom, expand every branch, inspect theorem statements and follow source and audit links. RH remains open.</desc>
<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="5" markerHeight="5" orient="auto"><path d="M0 0L10 5L0 10" fill="#8395ad"/></marker></defs>
<rect width="1280" height="430" rx="16" fill="#101923"/>
<text x="30" y="32" fill="#9caec3" font-family="system-ui,sans-serif" font-size="11" letter-spacing="2">RIEMANNGAUSSIAN / PROOF EXPLORER</text>
<text x="30" y="64" fill="#f2f4f5" font-family="system-ui,sans-serif" font-size="23" font-weight="600">Follow the mathematics to the zero-free region</text>
<rect x="1004" y="29" width="246" height="39" rx="20" fill="#25443f" stroke="#77dac3"/>
<text x="1127" y="54" text-anchor="middle" fill="#bdf2e4" font-family="system-ui,sans-serif" font-size="14">Open interactive explorer ↗</text>
<g transform="translate(${x} ${y}) scale(${scale})" font-family="system-ui,sans-serif">`;
for (const z of layout.zones) {
  const f = families.get(z.family);
  svg += `<rect x="${z.x}" y="${z.y}" width="${z.width}" height="${z.height}" rx="12" fill="${f.color}" fill-opacity=".08" stroke="${f.color}" stroke-opacity=".38"/><text x="${z.x + 12}" y="${z.y + 20}" fill="${f.color}" font-size="12">${esc(f.label)}</text>`;
}
for (const e of edges) svg += `<path d="${core.curve(layout.positions.get(e.source), layout.positions.get(e.target))}" fill="none" stroke="#8395ad" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>`;
for (const i of visible) {
  const n = data.nodes[i], p = layout.positions.get(i), f = families.get(n.family);
  svg += `<g><title>${esc(n.id)}</title><rect x="${p.x}" y="${p.y}" width="${p.width}" height="${p.height}" rx="8" fill="#182534" stroke="${f.color}"/><text fill="#f0f3f6" font-size="14" font-weight="500">`;
  core.wrap(n.label, 26, 2).forEach((line, j) => { svg += `<tspan x="${p.x + 12}" y="${p.y + 28 + j * 19}">${esc(line)}</tspan>`; });
  svg += "</text></g>";
}
svg += `</g><path d="M30 383H1250" stroke="#2a3949"/>
<text x="30" y="410" fill="#b8c5d3" font-family="system-ui,sans-serif" font-size="12">Zoom · expand proof paths · inspect Lean statements · open source lines &amp; axiom audits</text>
<text x="1250" y="410" text-anchor="end" fill="#91a5b9" font-family="system-ui,sans-serif" font-size="11">Arrows follow collapsed proof references · RH remains open</text></svg>\n`;
process.stdout.write(svg);
