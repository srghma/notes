"use client";

import { FileCode2, GitBranch, Maximize2, Search, X } from "lucide-react";
import { useCallback, useLayoutEffect, useMemo, useRef, useState } from "react";
import type { GraphData, NodeDef, NodeKind } from "@/lib/types";
import { cn } from "@/utils/cn";

interface EdgePath {
  key: string;
  d: string;
  lx: number;
  ly: number;
  label?: string;
  dashed?: boolean;
  isNeighbor: boolean;
  isDimmed: boolean;
}

const KIND_CARD_STYLES: Record<NodeKind, string> = {
  upstream: "bg-blue-950/75 border-blue-500/80 text-blue-50",
  baseBranch: "bg-slate-900/90 border-slate-500/80 text-slate-100",
  mergeNode: "bg-violet-950/75 border-violet-500/80 text-violet-50",
  activePR: "bg-rose-950/80 border-rose-500 border-[2.5px] text-rose-50",
  targetCommit:
    "bg-amber-950/85 border-amber-400 border-[2.5px] rounded-2xl text-amber-50 shadow-[0_0_24px_rgba(251,191,36,0.18)]",
  trackA: "bg-teal-950/75 border-teal-500/80 text-teal-50",
  trackB: "bg-emerald-950/75 border-emerald-500/80 text-emerald-50",
};

const LEGEND_ITEMS: Array<{ kind: NodeKind; label: string }> = [
  { kind: "upstream", label: "Upstream main" },
  { kind: "baseBranch", label: "Frozen / base" },
  { kind: "mergeNode", label: "Merge" },
  { kind: "activePR", label: "Active PR (no 829c9468)" },
  { kind: "targetCommit", label: "Target 829c9468" },
  { kind: "trackA", label: "Track A: FMA3 & speedups" },
  { kind: "trackB", label: "Track B: Active VCGen" },
];

export function GraphVisualizer({ data }: { data: GraphData }) {
  const viewportRef = useRef<HTMLDivElement>(null);
  const boardRef = useRef<HTMLDivElement>(null);

  const [zoom, setZoom] = useState<number>(1);
  const [selectedId, setSelectedId] = useState<string | null>(null);
  const [query, setQuery] = useState<string>("");
  const [edgePaths, setEdgePaths] = useState<EdgePath[]>([]);
  const [svgSize, setSvgSize] = useState<{ w: number; h: number }>({
    w: 1,
    h: 1,
  });
  const [previewFile, setPreviewFile] = useState<{
    fname: string;
    content: string;
  } | null>(null);
  const [previewError, setPreviewError] = useState<string | null>(null);

  const connectedSet = useMemo(() => {
    if (!selectedId) return null;
    const set = new Set<string>([selectedId]);
    for (const e of data.edges) {
      if (e.from === selectedId) set.add(e.to);
      if (e.to === selectedId) set.add(e.from);
    }
    return set;
  }, [data.edges, selectedId]);

  const queryMatches = useMemo(() => {
    const q = query.trim().toLowerCase();
    if (!q) return null;
    const set = new Set<string>();
    for (const n of data.nodes) {
      const meta = data.metaByNode[n.id];
      const refs = data.groupsByNode[n.id];
      const haystack = [
        n.id,
        n.commit,
        n.title,
        n.desc,
        meta.subject,
        meta.committerDate,
        ...refs.map((r) => `${r.gname} ${r.fname}`),
      ]
        .join(" ")
        .toLowerCase();
      if (haystack.includes(q)) set.add(n.id);
    }
    return set;
  }, [data.groupsByNode, data.metaByNode, data.nodes, query]);

  const recomputeEdges = useCallback(() => {
    const board = boardRef.current;
    if (!board) return;

    const w = board.scrollWidth;
    const h = board.scrollHeight;
    setSvgSize({ w, h });

    const els = new Map<string, HTMLElement>();
    for (const el of board.querySelectorAll<HTMLElement>("[data-node-id]")) {
      const id = el.dataset.nodeId;
      if (id) els.set(id, el);
    }

    const paths: EdgePath[] = [];
    for (const e of data.edges) {
      const fromEl = els.get(e.from);
      const toEl = els.get(e.to);
      if (!fromEl || !toEl) {
        throw new Error(`Missing DOM element for edge ${e.from} -> ${e.to}`);
      }

      const a = {
        left: fromEl.offsetLeft,
        right: fromEl.offsetLeft + fromEl.offsetWidth,
        top: fromEl.offsetTop,
        bottom: fromEl.offsetTop + fromEl.offsetHeight,
        cx: fromEl.offsetLeft + fromEl.offsetWidth / 2,
        cy: fromEl.offsetTop + fromEl.offsetHeight / 2,
      };
      const b = {
        left: toEl.offsetLeft,
        right: toEl.offsetLeft + toEl.offsetWidth,
        top: toEl.offsetTop,
        bottom: toEl.offsetTop + toEl.offsetHeight,
        cx: toEl.offsetLeft + toEl.offsetWidth / 2,
        cy: toEl.offsetTop + toEl.offsetHeight / 2,
      };

      const isNeighbor = Boolean(
        selectedId && (e.from === selectedId || e.to === selectedId),
      );
      const isDimmed = Boolean(selectedId && !isNeighbor);

      let d: string;
      let lx: number;
      let ly: number;

      if (Math.abs(a.cx - b.cx) < 12) {
        const goingDown = b.cy > a.cy;
        const x1 = a.cx;
        const y1 = goingDown ? a.bottom : a.top;
        const x2 = b.cx;
        const y2 = goingDown ? b.top : b.bottom;
        d = `M ${x1} ${y1} L ${x2} ${y2}`;
        lx = x1 + 8;
        ly = (y1 + y2) / 2;
      } else {
        const x1 = a.right;
        const y1 = a.cy;
        const x2 = b.left;
        const y2 = b.cy;
        const dx = Math.max(24, (x2 - x1) * 0.45);
        d = `M ${x1} ${y1} C ${x1 + dx} ${y1}, ${x2 - dx} ${y2}, ${x2} ${y2}`;
        lx = (x1 + x2) / 2;
        ly = (y1 + y2) / 2 - 7;
      }

      paths.push({
        key: `${e.from}->${e.to}`,
        d,
        lx,
        ly,
        label: e.label,
        dashed: e.dashed,
        isNeighbor,
        isDimmed,
      });
    }

    setEdgePaths(paths);
  }, [data.edges, selectedId]);

  useLayoutEffect(() => {
    recomputeEdges();
    const board = boardRef.current;
    if (!board) return;
    const ro = new ResizeObserver(() => recomputeEdges());
    ro.observe(board);
    return () => ro.disconnect();
  }, [recomputeEdges]);

  const handleFit = () => {
    const vp = viewportRef.current;
    const board = boardRef.current;
    if (!vp || !board) return;
    const fit = Math.min(
      1,
      Math.max(0.35, (vp.clientWidth - 28) / board.scrollWidth),
    );
    setZoom(Number(fit.toFixed(2)));
  };

  const openGroupPreview = async (fname: string) => {
    setPreviewError(null);
    const res = await fetch(`/api/group?file=${encodeURIComponent(fname)}`);
    if (!res.ok) {
      const body = await res.text();
      setPreviewError(`Failed to load ${fname}: ${res.status} ${body}`);
      return;
    }
    const json = (await res.json()) as { fname: string; content: string };
    setPreviewFile(json);
  };

  const selectedNode: NodeDef | null = selectedId
    ? (data.nodes.find((n) => n.id === selectedId) ?? null)
    : null;
  const selectedMeta = selectedNode ? data.metaByNode[selectedNode.id] : null;
  const selectedGroups = selectedNode ? data.groupsByNode[selectedNode.id] : [];

  const colCount = data.timelineCols.length;
  const laneCount = data.lanes.length;

  return (
    <div className="flex h-dvh w-screen flex-col overflow-hidden bg-zinc-950 text-zinc-100">
      <header className="shrink-0 border-b border-zinc-800 bg-zinc-900/95 px-4 py-2.5 flex flex-wrap items-center justify-between gap-3">
        <div className="flex items-center gap-2.5">
          <GitBranch className="h-4 w-4 text-amber-400" />
          <h1 className="text-sm font-bold tracking-tight text-zinc-100">
            Kraken P3 / VCGen Branch Tree &amp; Timeline
          </h1>
          <span className="text-xs text-zinc-400 font-mono">
            ({data.nodes.length} commits · {data.groups.length} file groups)
          </span>
        </div>

        <div className="flex flex-wrap items-center gap-1.5 text-[11px]">
          {LEGEND_ITEMS.map((item) => (
            <span
              key={item.kind}
              className={cn(
                "rounded-full border px-2.5 py-0.5 font-medium",
                KIND_CARD_STYLES[item.kind],
              )}
            >
              {item.label}
            </span>
          ))}
        </div>

        <div className="flex items-center gap-2">
          <label className="relative flex items-center">
            <Search className="pointer-events-none absolute left-2.5 h-3.5 w-3.5 text-zinc-400" />
            <input
              type="text"
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Filter hash / branch / G01..."
              className="w-48 rounded-md border border-zinc-700 bg-zinc-950 py-1 pl-8 pr-2 text-xs text-zinc-100 placeholder:text-zinc-500 focus:border-blue-500 focus:outline-none"
            />
          </label>

          <div className="flex items-center gap-1 rounded-md border border-zinc-800 bg-zinc-950 p-0.5">
            {[1, 0.75, 0.55].map((z) => (
              <button
                key={z}
                type="button"
                onClick={() => setZoom(z)}
                className={cn(
                  "rounded px-2 py-1 text-xs font-medium transition-colors",
                  zoom === z
                    ? "bg-zinc-100 text-zinc-950"
                    : "text-zinc-300 hover:bg-zinc-800",
                )}
              >
                {Math.round(z * 100)}%
              </button>
            ))}
            <button
              type="button"
              onClick={handleFit}
              className="inline-flex items-center gap-1 rounded px-2 py-1 text-xs font-medium text-zinc-300 hover:bg-zinc-800"
            >
              <Maximize2 className="h-3 w-3" />
              Fit
            </button>
          </div>
        </div>
      </header>

      <div
        ref={viewportRef}
        className="relative flex-1 min-h-0 w-full overflow-auto bg-zinc-950 p-4"
      >
        <div
          ref={boardRef}
          style={{
            zoom,
            gridTemplateColumns: `200px repeat(${colCount}, 216px)`,
            gridTemplateRows: `repeat(${laneCount}, minmax(112px, auto)) 76px`,
          }}
          className="relative inline-grid gap-x-8 gap-y-4 rounded-xl border border-zinc-800 bg-zinc-900/60 p-4"
        >
          <svg
            width={svgSize.w}
            height={svgSize.h}
            viewBox={`0 0 ${svgSize.w} ${svgSize.h}`}
            className="pointer-events-none absolute inset-0 z-10 overflow-visible"
            aria-hidden="true"
          >
            <defs>
              <marker
                id="arrow-solid"
                viewBox="0 0 10 10"
                refX="8"
                refY="5"
                markerWidth="6.5"
                markerHeight="6.5"
                orient="auto"
              >
                <path d="M 0 1 L 9 5 L 0 9 z" fill="#94a3b8" />
              </marker>
              <marker
                id="arrow-dashed"
                viewBox="0 0 10 10"
                refX="8"
                refY="5"
                markerWidth="6.5"
                markerHeight="6.5"
                orient="auto"
              >
                <path d="M 0 1 L 9 5 L 0 9 z" fill="#64748b" />
              </marker>
              <marker
                id="arrow-active"
                viewBox="0 0 10 10"
                refX="8"
                refY="5"
                markerWidth="7"
                markerHeight="7"
                orient="auto"
              >
                <path d="M 0 1 L 9 5 L 0 9 z" fill="#fbbf24" />
              </marker>
            </defs>

            {edgePaths.map((edge) => (
              <g key={edge.key} style={{ opacity: edge.isDimmed ? 0.16 : 1 }}>
                <path
                  d={edge.d}
                  fill="none"
                  stroke={
                    edge.isNeighbor
                      ? "#fbbf24"
                      : edge.dashed
                        ? "#64748b"
                        : "#94a3b8"
                  }
                  strokeWidth={edge.isNeighbor ? 2.5 : 1.75}
                  strokeDasharray={edge.dashed ? "5,4" : undefined}
                  markerEnd={
                    edge.isNeighbor
                      ? "url(#arrow-active)"
                      : edge.dashed
                        ? "url(#arrow-dashed)"
                        : "url(#arrow-solid)"
                  }
                />
                {edge.label ? (
                  <text
                    x={edge.lx}
                    y={edge.ly}
                    textAnchor="middle"
                    fontSize={10.5}
                    fontWeight={600}
                    fill={edge.isNeighbor ? "#fcd34d" : "#cbd5e1"}
                    stroke="#09090b"
                    strokeWidth={4}
                    paintOrder="stroke"
                  >
                    {edge.label}
                  </text>
                ) : null}
              </g>
            ))}
          </svg>

          {data.timelineCols.map((t) => (
            <div
              key={`guide-${t.col}`}
              style={{
                gridColumn: t.col + 2,
                gridRow: `1 / span ${laneCount}`,
              }}
              className={cn(
                "pointer-events-none -ml-4 z-0 border-l border-dashed",
                t.isTarget
                  ? "border-amber-500/70 bg-amber-500/5 border-l-2"
                  : "border-zinc-800/90",
              )}
            />
          ))}

          <div
            style={{ gridColumn: `1 / span ${colCount + 1}`, gridRow: 3 }}
            className="pointer-events-none -mt-2 z-0 border-t-2 border-zinc-700/80"
          />

          {data.lanes.map((lane) => (
            <div
              key={`lane-${lane.lane}`}
              style={{ gridColumn: 1, gridRow: lane.lane + 1 }}
              className="sticky left-0 z-30 flex flex-col justify-center gap-1 border-r-2 border-zinc-800 bg-zinc-950/95 px-3 py-2 backdrop-blur-sm"
            >
              <span className="text-[10px] font-bold uppercase tracking-wider text-zinc-400">
                {lane.band === "upstream"
                  ? "AeneasVerif/kraken"
                  : "sgraf812/kraken"}
              </span>
              <span className="text-xs font-semibold text-zinc-100">
                {lane.label}
              </span>
            </div>
          ))}

          {data.nodes.map((node) => {
            const meta = data.metaByNode[node.id];
            const refs = data.groupsByNode[node.id];
            const isSelected = selectedId === node.id;
            const isDimmedBySelect = Boolean(
              connectedSet && !connectedSet.has(node.id),
            );
            const isDimmedByQuery = Boolean(
              queryMatches && !queryMatches.has(node.id),
            );
            const isDimmed = isDimmedBySelect || isDimmedByQuery;

            return (
              <button
                key={node.id}
                type="button"
                data-node-id={node.id}
                onClick={() =>
                  setSelectedId((prev) => (prev === node.id ? null : node.id))
                }
                style={{ gridColumn: node.col + 2, gridRow: node.lane + 1 }}
                className={cn(
                  "relative z-20 flex flex-col gap-1 self-center rounded-xl border-2 p-2.5 text-left shadow-sm transition duration-150 hover:-translate-y-0.5 hover:shadow-lg",
                  KIND_CARD_STYLES[node.kind],
                  isSelected &&
                    "ring-2 ring-white ring-offset-2 ring-offset-zinc-950",
                  isDimmed && "opacity-20",
                )}
              >
                <div className="flex items-center justify-between gap-2 text-[11px]">
                  <span className="rounded bg-black/35 px-1.5 py-0.5 font-mono font-bold">
                    {node.commit}
                  </span>
                  <span className="font-mono text-[10.5px] opacity-85">
                    {meta.committerDate}
                  </span>
                </div>
                <div className="text-xs font-bold leading-snug">
                  {node.title}
                </div>
                <div className="text-[11px] leading-snug opacity-90">
                  {node.desc}
                </div>
                <div className="mt-0.5 flex flex-wrap gap-1">
                  {refs.length > 0 ? (
                    refs.map((r) => (
                      <span
                        key={`${r.gname}-${r.shortPath}`}
                        title={r.fname}
                        className="rounded bg-black/35 px-1.5 py-0.5 text-[10px] font-semibold"
                      >
                        {r.gname} · {r.shortPath}
                      </span>
                    ))
                  ) : (
                    <span className="rounded bg-red-950/90 px-1.5 py-0.5 text-[10px] font-semibold text-red-200">
                      MISSING
                    </span>
                  )}
                </div>
              </button>
            );
          })}

          <div
            style={{ gridColumn: 1, gridRow: laneCount + 1 }}
            className="sticky bottom-0 left-0 z-40 flex flex-col justify-center border-t-2 border-r-2 border-zinc-700 bg-zinc-950 px-3 py-2"
          >
            <strong className="text-xs text-zinc-100">Timeline (2026)</strong>
            <span className="text-[10.5px] text-zinc-400">
              Committer dates (L → R)
            </span>
          </div>

          {data.timelineCols.map((t) => (
            <div
              key={`tl-${t.col}`}
              style={{ gridColumn: t.col + 2, gridRow: laneCount + 1 }}
              className={cn(
                "sticky bottom-0 z-30 flex flex-col items-center justify-start gap-0.5 rounded-b-lg border-t-2 px-2 pt-3 pb-1.5 text-center",
                t.isTarget
                  ? "border-t-[3px] border-amber-400 bg-amber-950/90"
                  : "border-zinc-600 bg-zinc-900/95",
              )}
            >
              <span
                className={cn(
                  "absolute -top-[6.5px] h-3 w-3 rounded-full border-2 border-zinc-950",
                  t.isTarget
                    ? "h-3.5 w-3.5 -top-[8px] bg-amber-400"
                    : "bg-zinc-400",
                )}
              />
              <span className="font-mono text-[11px] font-bold text-zinc-100">
                {t.dateLabel}
              </span>
              <span className="text-[10.5px] text-zinc-400 leading-tight">
                {t.subLabel}
              </span>
            </div>
          ))}
        </div>
      </div>

      {selectedNode && selectedMeta ? (
        <aside className="shrink-0 border-t border-zinc-800 bg-zinc-900 px-4 py-3 flex flex-wrap items-start justify-between gap-4">
          <div className="space-y-1 max-w-4xl">
            <div className="flex items-center gap-2">
              <h2 className="text-sm font-bold text-zinc-100">
                {selectedNode.title} ({selectedNode.commit})
              </h2>
              <span className="text-xs font-mono text-zinc-400">
                author: {selectedMeta.authorDate} · committer:{" "}
                {selectedMeta.committerDate}
              </span>
            </div>
            <p className="text-xs text-zinc-300">
              <span className="text-zinc-400">git subject:</span>{" "}
              <code className="rounded bg-zinc-800 px-1.5 py-0.5 font-mono text-[11px]">
                {selectedMeta.subject}
              </code>
            </p>
            <p className="text-xs text-zinc-400">{selectedNode.desc}</p>
            <div className="flex flex-wrap gap-2 pt-1">
              {selectedGroups.map((g) => (
                <button
                  key={`${g.gname}-${g.shortPath}`}
                  type="button"
                  onClick={() => openGroupPreview(g.fname)}
                  className="inline-flex items-center gap-1.5 rounded-md border border-blue-500/40 bg-blue-950/50 px-2.5 py-1 font-mono text-xs text-blue-200 hover:bg-blue-900/60"
                >
                  <FileCode2 className="h-3.5 w-3.5" />
                  {g.gname} ({g.shortPath}, {g.lines} lines) → {g.fname}
                </button>
              ))}
            </div>
            {previewError ? (
              <p className="text-xs text-red-400">{previewError}</p>
            ) : null}
          </div>

          <button
            type="button"
            onClick={() => setSelectedId(null)}
            className="rounded-md border border-zinc-700 bg-zinc-800 p-1.5 text-zinc-300 hover:bg-zinc-700"
            aria-label="Close inspector"
          >
            <X className="h-4 w-4" />
          </button>
        </aside>
      ) : null}

      {previewFile ? (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/75 p-6">
          <div className="flex h-[85vh] w-full max-w-5xl flex-col overflow-hidden rounded-xl border border-zinc-700 bg-zinc-900 shadow-2xl">
            <div className="flex items-center justify-between border-b border-zinc-800 px-4 py-2.5">
              <span className="font-mono text-xs font-semibold text-zinc-100">
                p3_groups/{previewFile.fname}
              </span>
              <button
                type="button"
                onClick={() => setPreviewFile(null)}
                className="rounded-md border border-zinc-700 bg-zinc-800 p-1 text-zinc-300 hover:bg-zinc-700"
              >
                <X className="h-4 w-4" />
              </button>
            </div>
            <pre className="flex-1 overflow-auto p-4 font-mono text-xs leading-relaxed text-zinc-200">
              {previewFile.content}
            </pre>
          </div>
        </div>
      ) : null}
    </div>
  );
}
