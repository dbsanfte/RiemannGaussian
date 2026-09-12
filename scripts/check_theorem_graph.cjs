// Validate displayed paths against the raw Lean export, not hand-authored edges.
const fs = require("node:fs"), vm = require("node:vm"), zlib = require("node:zlib");
const assert = require("node:assert/strict");
const crypto = require("node:crypto");
const core = require("../docs/theorem-explorer/graph-core.js");
const base = "docs/theorem-explorer/", context = {window: {}};
vm.runInNewContext(fs.readFileSync(base + "data.js", "utf8"), context);
const data = JSON.parse(JSON.stringify(context.window.PROOF_DATA));
const rawBytes = zlib.gunzipSync(fs.readFileSync(base + "lean-graph.json.gz"));
const raw = JSON.parse(rawBytes), rawById = new Map(raw.nodes.map(n => [n.id, n]));
const audit = JSON.parse(fs.readFileSync(base + "audit.json"));
assert.equal(crypto.createHash("sha256").update(rawBytes).digest("hex"), audit.rawGraphSha256);
const model = core.create(data);
assert.equal(data.nodes.length, raw.nodes.length);
for (const n of data.nodes) {
  const original = rawById.get(n.id); assert(original);
  assert.deepEqual(n.axioms, original.axioms);
  for (const [field, rawField] of [["body", "bodyDependencies"], ["typeRefs", "typeDependencies"], ["constructors", "constructorDependencies"]]) {
    assert.deepEqual(n[field].map(i => data.nodes[i].id), original[rawField]);
  }
  assert(data.families.some(f => f.id === n.family));
  if (n.project) assert(n.source?.path && n.source.line > 0, n.id);
}
function checkView(visible, scope) {
  visible.forEach(i => assert(scope.has(i), "View contains an unrelated theorem"));
  const edges = model.edges(visible), layout = model.layout(visible, edges);
  for (const e of edges) {
    assert.equal(e.path[0], e.source); assert.equal(e.path.at(-1), e.target);
    assert.equal(e.collapsed, e.path.length > 2);
    for (let i = 0; i < e.path.length - 1; i++) {
      const dependency = data.nodes[e.path[i]].id, parent = rawById.get(data.nodes[e.path[i + 1]].id);
      const key = {body: "bodyDependencies", type: "typeDependencies", constructor: "constructorDependencies"}[e.kinds[i]];
      assert(parent[key].includes(dependency), "Invented proof edge");
    }
    for (const middle of e.path.slice(1, -1)) assert(!visible.has(middle), "Collapsed path bypasses a visible step");
    assert(layout.ranks.get(e.source) < layout.ranks.get(e.target));
  }
  for (const [i, p] of layout.positions) {
    assert(layout.zones.some(z => z.family === data.nodes[i].family && z.x <= p.x && z.y <= p.y && z.x + z.width >= p.x + p.width && z.y + z.height >= p.y + p.height), "Theorem lies outside its family zone");
  }
  return edges.length;
}
let checked = 0;
for (const endpoint of data.endpoints) {
  const scope = model.closure(endpoint.roots), overview = model.overview(endpoint.roots);
  endpoint.roots.forEach(i => assert(overview.has(i)));
  checked += checkView(overview, scope);
  const all = new Set([...scope].filter(i => data.nodes[i].project && data.nodes[i].kind === "theorem" && !data.nodes[i].generated));
  endpoint.roots.forEach(i => all.add(i));
  checked += checkView(all, scope);
}
for (const [path, hash] of Object.entries(audit.sourceSha256)) assert.equal(crypto.createHash("sha256").update(fs.readFileSync(path)).digest("hex"), hash, "Source snapshot changed");
console.log(`Checked ${data.endpoints.length} endpoints, ${data.nodes.length} declarations and ${checked} displayed paths against the Lean export.`);
