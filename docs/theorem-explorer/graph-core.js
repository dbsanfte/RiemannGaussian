/* Dependency traversal and layout shared by the browser and README preview. */
(function (root, factory) {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.ProofGraph = api;
})(typeof globalThis !== "undefined" ? globalThis : this, function () {
  "use strict";
  function create(data) {
    const nodes = data.nodes;
    const byName = new Map(nodes.map((n, i) => [n.id, i]));
    const direct = nodes.map(n => {
      const refs = new Map();
      for (const i of n.typeRefs) refs.set(i, "type");
      for (const i of n.constructors) refs.set(i, "constructor");
      for (const i of n.body) refs.set(i, "body");
      return Array.from(refs, ([id, kind]) => ({id, kind}));
    });
    function closure(roots) {
      const seen = new Set(), pending = [...roots];
      while (pending.length) {
        const i = pending.pop();
        if (seen.has(i)) continue;
        seen.add(i);
        for (const d of direct[i]) pending.push(d.id);
      }
      return seen;
    }
    function overview(roots) {
      const scope = closure(roots);
      return new Set([...scope].filter(i => nodes[i].overview || roots.includes(i)));
    }
    function nearest(start, accept) {
      const seen = new Set([start]), result = [], queue = direct[start].map(d => d.id);
      for (let q = 0; q < queue.length; q++) {
        const i = queue[q];
        if (seen.has(i)) continue;
        seen.add(i);
        if (accept(i)) result.push(i);
        else for (const d of direct[i]) queue.push(d.id);
      }
      return result;
    }
    // Every compressed edge includes a literal path in the exported graph.
    // Finding one path is not claiming it is the unique or necessary proof.
    function edges(visible) {
      const result = [];
      for (const target of visible) {
        const seen = new Set([target]);
        const queue = direct[target].map(d => ({id: d.id, path: [target, d.id], kinds: [d.kind]}));
        for (let q = 0; q < queue.length; q++) {
          const current = queue[q];
          if (seen.has(current.id)) continue;
          seen.add(current.id);
          if (visible.has(current.id)) {
            result.push({source: current.id, target, path: current.path.slice().reverse(),
              kinds: current.kinds.slice().reverse(), collapsed: current.path.length > 2});
          } else {
            for (const d of direct[current.id]) {
              if (!seen.has(d.id)) queue.push({id: d.id, path: [...current.path, d.id],
                kinds: [...current.kinds, d.kind]});
            }
          }
        }
      }
      return result;
    }
    function layout(visible, edgeList, options = {}) {
      const width = options.width || 220, height = options.height || 70;
      const columnGap = options.columnGap || 58, rowGap = options.rowGap || 20;
      const familyOrder = new Map(data.families.map((f, i) => [f.id, i]));
      const successors = new Map([...visible].map(i => [i, []]));
      edgeList.forEach(e => successors.get(e.source).push(e.target));
      const depths = new Map(), active = new Set();
      function depth(i) {
        if (depths.has(i)) return depths.get(i);
        if (active.has(i)) throw new Error("Cyclic declaration view; inspect the raw dependency graph.");
        active.add(i);
        const d = Math.max(-1, ...successors.get(i).map(depth)) + 1;
        active.delete(i); depths.set(i, d); return d;
      }
      visible.forEach(depth);
      const maxDepth = Math.max(0, ...depths.values());
      const ranks = new Map([...depths].map(([i, d]) => [i, maxDepth - d]));
      const columns = new Map();
      ranks.forEach((r, i) => { if (!columns.has(r)) columns.set(r, []); columns.get(r).push(i); });
      const positions = new Map(), zones = [], columnHeights = new Map();
      let totalHeight = 0;
      for (const [r, ids] of [...columns].sort((a, b) => a[0] - b[0])) {
        ids.sort((a, b) => familyOrder.get(nodes[a].family) - familyOrder.get(nodes[b].family)
          || (nodes[a].id < nodes[b].id ? -1 : nodes[a].id > nodes[b].id ? 1 : 0));
        let y = 48;
        for (let k = 0; k < ids.length;) {
          const family = nodes[ids[k]].family;
          const begin = y;
          y += 30;
          do {
            positions.set(ids[k], {x: 36 + r * (width + columnGap), y, width, height});
            y += height + rowGap;
            k++;
          } while (k < ids.length && nodes[ids[k]].family === family);
          zones.push({family, column: r, x: 24 + r * (width + columnGap), y: begin,
            width: width + 24, height: y - begin - rowGap + 12});
          y += 22;
        }
        totalHeight = Math.max(totalHeight, y + 24);
        columnHeights.set(r, y + 24);
      }
      // Place short chains near the middle instead of piling every leaf into
      // the first column. Each proof dependency still points strictly right.
      for (const [i, p] of positions) p.y += (totalHeight - columnHeights.get(ranks.get(i))) / 2;
      for (const z of zones) z.y += (totalHeight - columnHeights.get(z.column)) / 2;
      return {positions, zones, width: 72 + (Math.max(0, ...ranks.values()) + 1) *
        (width + columnGap) - columnGap, height: totalHeight, ranks};
    }
    return {nodes, byName, direct, closure, overview, nearest, edges, layout};
  }
  function wrap(text, limit = 27, lines = 2) {
    const words = text.replaceAll("_", " ").split(/\s+/), result = [];
    let line = "";
    for (const word of words) {
      if (line && line.length + word.length + 1 > limit) { result.push(line); line = ""; }
      line += (line ? " " : "") + word;
    }
    if (line) result.push(line);
    if (result.length > lines) return [...result.slice(0, lines - 1), result.slice(lines - 1).join(" ").slice(0, limit - 1) + "…"];
    return result;
  }
  function escape(text) {
    return String(text).replace(/[&<>"']/g, c => ({"&":"&amp;", "<":"&lt;", ">":"&gt;", '"':"&quot;", "'":"&#39;"})[c]);
  }
  function curve(a, b) {
    const x1 = a.x + a.width, y1 = a.y + a.height / 2, x2 = b.x, y2 = b.y + b.height / 2;
    const bend = Math.max(24, (x2 - x1) / 2);
    return `M${x1},${y1} C${x1 + bend},${y1} ${x2 - bend},${y2} ${x2},${y2}`;
  }
  return {create, wrap, escape, curve};
});
