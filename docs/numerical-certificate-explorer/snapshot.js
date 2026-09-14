(function () {
  "use strict";
  const path = new URLSearchParams(location.search).get("path");
  const content = (window.PROOF_SOURCES || window.PROOF_DOCUMENTS || {})[path];
  const container = document.getElementById("source");
  if (content === undefined) { container.textContent = "This path is not in the checked source snapshot. Return to the explorer and use a theorem's source link."; return; }
  document.getElementById("path").textContent = path;
  document.title = path + " · RiemannGaussian";
  if (window.PROOF_DOCUMENTS) container.classList.add("document");
  if (window.PROOF_RELEASE) {
    const a = document.createElement("a"); a.textContent = "View this exact commit on GitHub ↗";
    a.href = `https://github.com/dbsanfte/RiemannGaussian/blob/${window.PROOF_RELEASE.revision}/${path}${location.hash}`;
    document.getElementById("provenance").replaceChildren(a);
  }
  const fragment = document.createDocumentFragment();
  content.split("\n").forEach((line, index) => {
    const div = document.createElement("div"); div.className = "source-line"; div.id = "L" + (index + 1);
    const a = document.createElement("a"); a.className = "line-number"; a.href = "#" + div.id; a.textContent = index + 1; a.setAttribute("aria-label", "Line " + (index + 1));
    const code = document.createElement("code"); code.textContent = line;
    div.append(a, code); fragment.append(div);
  });
  container.append(fragment);
  const target = document.getElementById(location.hash.slice(1)); if (target) target.scrollIntoView({block: "center"});
})();
