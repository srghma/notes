import { writeFileSync } from "node:fs";
import { EDGES, LANES, NODES, TIMELINE_COLS } from "./data";
import type { NodeGroupRef } from "./groups";
import type { CommitMeta, NodeDef } from "./types";

function esc(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

export function renderHtml(
  outPath: string,
  metaByNode: Map<string, CommitMeta>,
  nodeGroups: Map<string, NodeGroupRef[]>
): void {
  const colCount = TIMELINE_COLS.length;
  const nodeByCell = new Map<string, NodeDef>();
  for (const n of NODES) {
    nodeByCell.set(`${n.col}:${n.lane}`, n);
  }

  const inspectorData = NODES.map((n) => {
    const meta = metaByNode.get(n.id);
    const refs = nodeGroups.get(n.id) ?? [];
    return {
      id: n.id,
      commit: n.commit,
      title: n.title,
      desc: n.desc,
      kind: n.kind,
      authorDate: meta?.authorDate ?? "?",
      committerDate: meta?.committerDate ?? "?",
      subject: meta?.subject ?? "",
      groups: refs,
    };
  });

  const renderNodeCard = (n: NodeDef): string => {
    const meta = metaByNode.get(n.id);
    const refs = nodeGroups.get(n.id) ?? [];
    const dateStr = meta?.committerDate ?? "????-??-??";
    const badges = refs
      .map((r) => `<span class="g-pill" title="${esc(r.fname)}">${esc(r.gname)} · ${esc(r.shortPath)}</span>`)
      .join("");

    return `
      <button type="button"
        class="node-card kind-${n.kind}"
        data-node-id="${esc(n.id)}"
        style="grid-column:${n.col + 2};grid-row:${n.lane + 1};">
        <div class="node-head">
          <span class="node-hash">${esc(n.commit)}</span>
          <span class="node-date">${esc(dateStr)}</span>
        </div>
        <div class="node-title">${esc(n.title)}</div>
        <div class="node-desc">${esc(n.desc)}</div>
        <div class="node-badges">${badges || '<span class="g-pill missing">MISSING</span>'}</div>
      </button>`;
  };

  const guideCols = TIMELINE_COLS.map(
    (t) => `<div class="col-guide${t.isTarget ? " is-target" : ""}" style="grid-column:${t.col + 2};grid-row:1 / span ${LANES.length};"></div>`
  ).join("");

  const laneLabels = LANES.map(
    (l) => `<div class="lane-label band-${l.band}" style="grid-column:1;grid-row:${l.lane + 1};">
      <span class="band-tag">${l.band === "upstream" ? "AeneasVerif/kraken" : "sgraf812/kraken"}</span>
      <span class="lane-name">${esc(l.label)}</span>
    </div>`
  ).join("");

  const bandDivider = `<div class="band-divider" style="grid-column:1 / span ${colCount + 1};grid-row:3;"></div>`;

  const nodeCards = NODES.map(renderNodeCard).join("\n");

  const timelineCells = TIMELINE_COLS.map(
    (t) => `<div class="tl-cell${t.isTarget ? " is-target" : ""}" style="grid-column:${t.col + 2};grid-row:${LANES.length + 1};">
      <div class="tl-dot"></div>
      <div class="tl-date">${esc(t.dateLabel)}</div>
      <div class="tl-sub">${esc(t.subLabel)}</div>
    </div>`
  ).join("\n");

  const html = `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width,initial-scale=1" />
<title>Kraken P3 / VCGen Branch Tree &amp; Timeline</title>
<style>
  :root {
    --bg: #f8fafc;
    --border: #cbd5e1;
    --text: #0f172a;
    --muted: #475569;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: Inter, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
    background: var(--bg);
    color: var(--text);
  }
  .topbar {
    position: sticky;
    top: 0;
    z-index: 40;
    background: #ffffff;
    border-bottom: 1px solid var(--border);
    padding: 10px 16px;
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    justify-content: space-between;
    gap: 12px;
  }
  .topbar h1 {
    font-size: 15px;
    margin: 0;
    font-weight: 700;
  }
  .legend {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    align-items: center;
    font-size: 11.5px;
  }
  .leg-item {
    display: inline-flex;
    align-items: center;
    gap: 5px;
    padding: 2px 8px;
    border-radius: 999px;
    border: 1.5px solid #94a3b8;
    background: #fff;
    font-weight: 500;
  }
  .leg-upstream { background: #dbeafe; border-color: #2563eb; }
  .leg-baseBranch { background: #f1f5f9; border-color: #64748b; }
  .leg-mergeNode { background: #ede9fe; border-color: #7c3aed; }
  .leg-activePR { background: #fce7f3; border-color: #be123c; border-width: 2.5px; }
  .leg-targetCommit { background: #fef08a; border-color: #b45309; border-width: 2.5px; }
  .leg-trackA { background: #ccfbf1; border-color: #0d9488; }
  .leg-trackB { background: #dcfce7; border-color: #15803d; }

  .controls {
    display: flex;
    gap: 6px;
    align-items: center;
  }
  .controls button {
    border: 1px solid var(--border);
    background: #fff;
    color: var(--text);
    border-radius: 6px;
    padding: 4px 10px;
    font-size: 12px;
    cursor: pointer;
  }
  .controls button:hover { background: #f1f5f9; }
  .controls button.active { background: #0f172a; color: #fff; border-color: #0f172a; }

  .viewport {
    overflow: auto;
    padding: 16px;
    padding-bottom: 180px;
  }
  .board-scale {
    transform-origin: top left;
    display: inline-block;
  }
  .board {
    position: relative;
    display: grid;
    grid-template-columns: 190px repeat(${colCount}, 218px);
    grid-template-rows: repeat(${LANES.length}, minmax(112px, auto)) 78px;
    column-gap: 34px;
    row-gap: 18px;
    background: #ffffff;
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 16px;
  }
  .edges-svg {
    position: absolute;
    inset: 0;
    pointer-events: none;
    z-index: 5;
    overflow: visible;
  }
  .col-guide {
    border-left: 1px dashed #e2e8f0;
    margin-left: -17px;
    pointer-events: none;
    z-index: 1;
  }
  .col-guide.is-target {
    border-left: 2px dashed #d97706;
    background: rgba(254, 240, 138, 0.14);
  }
  .band-divider {
    border-top: 2px solid #cbd5e1;
    margin-top: -10px;
    pointer-events: none;
    z-index: 2;
  }
  .lane-label {
    position: sticky;
    left: 0;
    z-index: 20;
    background: rgba(255, 255, 255, 0.96);
    border-right: 2px solid #e2e8f0;
    padding: 8px 12px 8px 4px;
    display: flex;
    flex-direction: column;
    justify-content: center;
    gap: 3px;
  }
  .band-tag {
    font-size: 10px;
    text-transform: uppercase;
    letter-spacing: 0.04em;
    color: var(--muted);
    font-weight: 700;
  }
  .lane-name {
    font-size: 12.5px;
    font-weight: 700;
    color: var(--text);
  }

  .node-card {
    position: relative;
    z-index: 10;
    text-align: left;
    border-radius: 10px;
    border: 2px solid #94a3b8;
    padding: 8px 10px;
    background: #fff;
    cursor: pointer;
    display: flex;
    flex-direction: column;
    gap: 4px;
    box-shadow: 0 1px 3px rgba(15, 23, 42, 0.08);
    transition: transform 0.12s ease, opacity 0.15s ease, box-shadow 0.15s ease;
    align-self: center;
    font: inherit;
  }
  .node-card:hover {
    transform: translateY(-1px);
    box-shadow: 0 6px 14px rgba(15, 23, 42, 0.14);
  }
  .node-card.dimmed { opacity: 0.25; }
  .node-card.selected { outline: 3px solid #0f172a; outline-offset: 2px; }

  .kind-upstream { background: #dbeafe; border-color: #2563eb; }
  .kind-baseBranch { background: #f1f5f9; border-color: #64748b; }
  .kind-mergeNode { background: #ede9fe; border-color: #7c3aed; }
  .kind-activePR { background: #fce7f3; border-color: #be123c; border-width: 3px; }
  .kind-targetCommit { background: #fef08a; border-color: #b45309; border-width: 3px; border-radius: 18px; }
  .kind-trackA { background: #ccfbf1; border-color: #0d9488; }
  .kind-trackB { background: #dcfce7; border-color: #15803d; }

  .node-head {
    display: flex;
    justify-content: space-between;
    align-items: center;
    gap: 6px;
    font-size: 11px;
  }
  .node-hash {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-weight: 700;
    background: rgba(255, 255, 255, 0.72);
    padding: 1px 5px;
    border-radius: 4px;
  }
  .node-date {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    color: #334155;
    font-size: 10.5px;
    font-weight: 600;
  }
  .node-title {
    font-size: 12.5px;
    font-weight: 700;
    line-height: 1.25;
  }
  .node-desc {
    font-size: 11px;
    line-height: 1.3;
    color: #1e293b;
  }
  .node-badges {
    display: flex;
    flex-wrap: wrap;
    gap: 4px;
    margin-top: 2px;
  }
  .g-pill {
    font-size: 10px;
    font-weight: 700;
    padding: 1px 5px;
    border-radius: 4px;
    background: rgba(15, 23, 42, 0.1);
    color: #0f172a;
  }
  .g-pill.missing { background: #fee2e2; color: #991b1b; }

  /* Row 2: Timeline axis */
  .tl-corner {
    position: sticky;
    left: 0;
    z-index: 25;
    background: #f1f5f9;
    border-top: 2px solid #64748b;
    border-right: 2px solid #cbd5e1;
    display: flex;
    flex-direction: column;
    justify-content: center;
    padding: 8px 12px 8px 8px;
    border-bottom-left-radius: 8px;
  }
  .tl-corner strong { font-size: 12px; }
  .tl-corner span { font-size: 10.5px; color: var(--muted); }

  .tl-cell {
    position: relative;
    z-index: 10;
    border-top: 2px solid #64748b;
    background: #f8fafc;
    padding: 12px 8px 6px;
    text-align: center;
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: flex-start;
    gap: 2px;
    border-radius: 0 0 8px 8px;
  }
  .tl-cell.is-target {
    background: #fef9c3;
    border-top-color: #b45309;
    border-top-width: 3px;
  }
  .tl-dot {
    width: 11px;
    height: 11px;
    border-radius: 50%;
    background: #334155;
    border: 2px solid #fff;
    position: absolute;
    top: -6.5px;
  }
  .tl-cell.is-target .tl-dot {
    background: #b45309;
    width: 13px;
    height: 13px;
    top: -8px;
  }
  .tl-date {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 11.5px;
    font-weight: 700;
    color: #0f172a;
  }
  .tl-sub {
    font-size: 10.5px;
    color: #475569;
    line-height: 1.2;
  }

  /* Inspector drawer */
  .inspector {
    position: fixed;
    left: 16px;
    right: 16px;
    bottom: 14px;
    z-index: 50;
    background: #0f172a;
    color: #f8fafc;
    border-radius: 10px;
    padding: 12px 16px;
    box-shadow: 0 12px 30px rgba(15, 23, 42, 0.35);
    display: none;
    gap: 16px;
    align-items: flex-start;
    justify-content: space-between;
  }
  .inspector.open { display: flex; }
  .inspector h2 { margin: 0 0 4px; font-size: 14px; }
  .inspector p { margin: 2px 0; font-size: 12px; color: #cbd5e1; }
  .inspector code {
    background: rgba(255, 255, 255, 0.12);
    padding: 1px 6px;
    border-radius: 4px;
    font-size: 11.5px;
  }
  .inspector-files {
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
    margin-top: 6px;
  }
  .inspector-files a {
    color: #93c5fd;
    background: rgba(59, 130, 246, 0.16);
    padding: 3px 8px;
    border-radius: 5px;
    font-size: 11.5px;
    text-decoration: none;
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  }
  .inspector-files a:hover { background: rgba(59, 130, 246, 0.3); }
  .inspector-close {
    background: rgba(255, 255, 255, 0.12);
    border: none;
    color: #fff;
    border-radius: 6px;
    padding: 4px 10px;
    cursor: pointer;
    font-size: 12px;
  }
</style>
</head>
<body>
  <header class="topbar">
    <h1>Kraken P3 / VCGen Branch Tree &amp; Timeline</h1>
    <div class="legend">
      <span class="leg-item leg-upstream">Upstream main</span>
      <span class="leg-item leg-baseBranch">Frozen / base</span>
      <span class="leg-item leg-mergeNode">Merge</span>
      <span class="leg-item leg-activePR">Active PR (no 829c9468)</span>
      <span class="leg-item leg-targetCommit">Target 829c9468</span>
      <span class="leg-item leg-trackA">Track A: FMA3 &amp; speedups</span>
      <span class="leg-item leg-trackB">Track B: Active VCGen</span>
    </div>
    <div class="controls">
      <button type="button" data-zoom="1" class="active">100%</button>
      <button type="button" data-zoom="0.75">75%</button>
      <button type="button" data-zoom="0.55">55%</button>
      <button type="button" id="btnFit">Fit Width</button>
    </div>
  </header>

  <main class="viewport" id="viewport">
    <div class="board-scale" id="boardScale">
      <div class="board" id="board">
        <svg class="edges-svg" id="edgesSvg"></svg>
        ${guideCols}
        ${bandDivider}
        ${laneLabels}
        ${nodeCards}
        <div class="tl-corner" style="grid-column:1;grid-row:${LANES.length + 1};">
          <strong>Timeline (2026)</strong>
          <span>Committer dates (L → R)</span>
        </div>
        ${timelineCells}
      </div>
    </div>
  </main>

  <section class="inspector" id="inspector">
    <div>
      <h2 id="insTitle"></h2>
      <p id="insMeta"></p>
      <p id="insDesc"></p>
      <div class="inspector-files" id="insFiles"></div>
    </div>
    <button type="button" class="inspector-close" id="insClose">Close</button>
  </section>

<script>
const EDGES = ${JSON.stringify(EDGES).replace(/</g, "\\u003c")};
const NODES_META = ${JSON.stringify(inspectorData).replace(/</g, "\\u003c")};
const metaMap = new Map(NODES_META.map(n => [n.id, n]));

const board = document.getElementById("board");
const svg = document.getElementById("edgesSvg");
const boardScale = document.getElementById("boardScale");
const viewport = document.getElementById("viewport");

let currentZoom = 1;
let activeId = null;

function applyZoom(z) {
  currentZoom = z;
  boardScale.style.transform = \`scale(\${z})\`;
  boardScale.style.width = \`\${board.offsetWidth * z}px\`;
  boardScale.style.height = \`\${board.offsetHeight * z}px\`;
  document.querySelectorAll(".controls button[data-zoom]").forEach(btn => {
    btn.classList.toggle("active", Number(btn.dataset.zoom) === z);
  });
}

document.querySelectorAll(".controls button[data-zoom]").forEach(btn => {
  btn.addEventListener("click", () => applyZoom(Number(btn.dataset.zoom)));
});
document.getElementById("btnFit").addEventListener("click", () => {
  const avail = viewport.clientWidth - 36;
  const fit = Math.min(1, Math.max(0.3, avail / board.offsetWidth));
  applyZoom(Number(fit.toFixed(2)));
});

function boxRel(el) {
  const bRect = board.getBoundingClientRect();
  const r = el.getBoundingClientRect();
  return {
    left: (r.left - bRect.left) / currentZoom,
    right: (r.right - bRect.left) / currentZoom,
    top: (r.top - bRect.top) / currentZoom,
    bottom: (r.bottom - bRect.top) / currentZoom,
    cx: ((r.left + r.right) / 2 - bRect.left) / currentZoom,
    cy: ((r.top + r.bottom) / 2 - bRect.top) / currentZoom,
  };
}

function drawEdges() {
  const w = board.scrollWidth;
  const h = board.scrollHeight;
  svg.setAttribute("width", String(w));
  svg.setAttribute("height", String(h));
  svg.setAttribute("viewBox", \`0 0 \${w} \${h}\`);

  const NS = "http://www.w3.org/2000/svg";
  svg.innerHTML = \`
    <defs>
      <marker id="arrowSolid" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto">
        <path d="M 0 1 L 9 5 L 0 9 z" fill="#334155" />
      </marker>
      <marker id="arrowDashed" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto">
        <path d="M 0 1 L 9 5 L 0 9 z" fill="#64748b" />
      </marker>
      <marker id="arrowActive" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto">
        <path d="M 0 1 L 9 5 L 0 9 z" fill="#b45309" />
      </marker>
    </defs>\`;

  for (const e of EDGES) {
    const fromEl = board.querySelector(\`[data-node-id="\${e.from}"]\`);
    const toEl = board.querySelector(\`[data-node-id="\${e.to}"]\`);
    if (!fromEl || !toEl) continue;

    const a = boxRel(fromEl);
    const b = boxRel(toEl);
    const isNeighbor = activeId && (e.from === activeId || e.to === activeId);
    const isDimmed = activeId && !isNeighbor;

    let d, lx, ly;
    if (Math.abs(a.cx - b.cx) < 12) {
      // Same-column vertical edge
      const goingDown = b.cy > a.cy;
      const x1 = a.cx, y1 = goingDown ? a.bottom : a.top;
      const x2 = b.cx, y2 = goingDown ? b.top : b.bottom;
      d = \`M \${x1} \${y1} L \${x2} \${y2}\`;
      lx = x1 + 6;
      ly = (y1 + y2) / 2;
    } else {
      const x1 = a.right, y1 = a.cy;
      const x2 = b.left, y2 = b.cy;
      const dx = Math.max(24, (x2 - x1) * 0.45);
      d = \`M \${x1} \${y1} C \${x1 + dx} \${y1}, \${x2 - dx} \${y2}, \${x2} \${y2}\`;
      lx = (x1 + x2) / 2;
      ly = (y1 + y2) / 2 - 6;
    }

    const g = document.createElementNS(NS, "g");
    g.style.opacity = isDimmed ? "0.18" : "1";

    const path = document.createElementNS(NS, "path");
    path.setAttribute("d", d);
    path.setAttribute("fill", "none");
    path.setAttribute("stroke", isNeighbor ? "#b45309" : (e.dashed ? "#64748b" : "#334155"));
    path.setAttribute("stroke-width", isNeighbor ? "2.6" : "1.8");
    if (e.dashed) path.setAttribute("stroke-dasharray", "5,4");
    path.setAttribute("marker-end", isNeighbor ? "url(#arrowActive)" : (e.dashed ? "url(#arrowDashed)" : "url(#arrowSolid)"));
    g.appendChild(path);

    if (e.label) {
      const text = document.createElementNS(NS, "text");
      text.setAttribute("x", String(lx));
      text.setAttribute("y", String(ly));
      text.setAttribute("text-anchor", "middle");
      text.setAttribute("font-size", "10.5");
      text.setAttribute("font-weight", "600");
      text.setAttribute("fill", isNeighbor ? "#92400e" : "#475569");
      text.setAttribute("paint-order", "stroke");
      text.setAttribute("stroke", "#ffffff");
      text.setAttribute("stroke-width", "4");
      text.textContent = e.label;
      g.appendChild(text);
    }

    svg.appendChild(g);
  }
}

function selectNode(id) {
  activeId = activeId === id ? null : id;
  const connected = new Set();
  if (activeId) {
    connected.add(activeId);
    for (const e of EDGES) {
      if (e.from === activeId) connected.add(e.to);
      if (e.to === activeId) connected.add(e.from);
    }
  }

  board.querySelectorAll(".node-card").forEach(el => {
    const nid = el.dataset.nodeId;
    el.classList.toggle("selected", nid === activeId);
    el.classList.toggle("dimmed", Boolean(activeId && !connected.has(nid)));
  });

  const ins = document.getElementById("inspector");
  if (!activeId) {
    ins.classList.remove("open");
  } else {
    const m = metaMap.get(activeId);
    document.getElementById("insTitle").textContent = \`\${m.title} (\${m.commit})\`;
    document.getElementById("insMeta").innerHTML =
      \`Author: <code>\${m.authorDate}</code> · Committer: <code>\${m.committerDate}</code> · Subject: <code>\${m.subject}</code>\`;
    document.getElementById("insDesc").textContent = m.desc;
    const filesEl = document.getElementById("insFiles");
    filesEl.innerHTML = m.groups.length
      ? m.groups.map(g => \`<a href="./\${encodeURIComponent(g.fname)}" target="_blank">\${g.gname} (\${g.shortPath}, \${g.lines} lines) → \${g.fname}</a>\`).join("")
      : "<span>No matching P3/Examples file in this commit</span>";
    ins.classList.add("open");
  }
  drawEdges();
}

board.querySelectorAll(".node-card").forEach(el => {
  el.addEventListener("click", () => selectNode(el.dataset.nodeId));
});
document.getElementById("insClose").addEventListener("click", () => {
  if (activeId) selectNode(activeId);
});

window.addEventListener("load", () => {
  drawEdges();
  applyZoom(1);
});
new ResizeObserver(drawEdges).observe(board);
</script>
</body>
</html>
`;

  writeFileSync(outPath, html, "utf8");
}
