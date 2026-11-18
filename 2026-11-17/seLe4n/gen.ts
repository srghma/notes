#!/usr/bin/env bun

import {
  existsSync,
  mkdirSync,
  readdirSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { homedir } from "node:os";
import { join } from "node:path";

const REPO = "/home/srghma/projects/kraken";
const OUT_DIR = join(import.meta.dir, "p3_groups");

interface NodeDef {
  id: string;
  commit: string;
  slug: string;
  label: string;
}

interface PathDef {
  shortPath: string;
  filePart: string;
  fullPath: string;
  isP3: boolean;
}

interface FileEntry {
  nodeIndex: number;
  id: string;
  commit: string;
  slug: string;
  label: string;
  shortPath: string;
  filePart: string;
  fullPath: string;
  isP3: boolean;
  blob: string;
  lines: number;
}

interface Group {
  gname: string;
  fname: string;
  blob: string;
  isP3: boolean;
  firstNodeIndex: number;
  entries: FileEntry[];
}

const NODES: NodeDef[] = [
  { id: "M_125", commit: "881e959", slug: "PR125", label: "PR #125 (upstream base before estatem-kfold)" },
  { id: "M_131", commit: "05cad40", slug: "PR131", label: "PR #131 (upstream snapshot where sgraf812/main froze)" },
  { id: "M_154", commit: "2c56cbd", slug: "PR154", label: "PR #154 (X64/AArch64 split, generic layout, ecancel)" },
  { id: "M_160", commit: "30f5a5f", slug: "PR160", label: "PR #160 (Merge toolchain-nightly-2026-09-21 & module system)" },
  { id: "M_165", commit: "72f3a7a", slug: "PR165", label: "PR #165 (sgraf812/wp-foundation merged to upstream)" },
  { id: "M_179", commit: "6064eec", slug: "PR179", label: "PR #179 (x64-fix-avx-access, base of conj-wp)" },
  { id: "M_247", commit: "0fccb2d", slug: "PR247", label: "PR #247 (Rep-string, delaborators, AArch64 parsers)" },
  { id: "M_HEAD", commit: "b44bf3f", slug: "main", label: "AeneasVerif/main" },
  { id: "PR_166", commit: "4989e1c", slug: "PR166-statewp", label: "sgraf812/statewp · PR #166" },
  { id: "PR_195", commit: "f5a85a1", slug: "PR195-conj-wp", label: "sgraf812/conj-wp · PR #195" },
  { id: "SG_MAIN", commit: "05cad40", slug: "sg-main", label: "sgraf812/kraken main" },
  { id: "EST", commit: "d68f0a4", slug: "estatem-kfold", label: "estatem-kfold" },
  { id: "TN", commit: "1045c33", slug: "nightly-09-21", label: "toolchain-nightly-2026-09-21" },
  { id: "SEP", commit: "12371fd", slug: "sepwp", label: "sgraf812:sepwp · PR #161" },
  { id: "M23B", commit: "23b6409", slug: "23b6409", label: "Merge estatem-kfold + PR #154" },
  { id: "C829", commit: "829c9468", slug: "829c9468", label: "TARGET COMMIT / EXACT FORK POINT" },
  { id: "FMA3", commit: "9209b11", slug: "fma3", label: "sg/fma3-default-limits" },
  { id: "N1014", commit: "9743c3a", slug: "nightly-10-14", label: "sg/nightly-2026-10-14" },
  { id: "SPEED", commit: "a443d2c", slug: "speedups", label: "sg/upstream-speedups" },
  { id: "M63C", commit: "63c72ed", slug: "63c72ed", label: "Merge nightly-2026-09-21 & module system" },
  { id: "M7CF", commit: "7cfd503", slug: "7cfd503", label: "Merge sepwp PR #161" },
  { id: "DROP", commit: "bc85a6a", slug: "drop-framewp", label: "sg/drop-framewp" },
  { id: "VCGEN", commit: "6c2f048", slug: "vcgen", label: "vcgen" },
  { id: "DCC", commit: "dcc8cc1", slug: "dcc8cc1", label: "Merge early vcgen into sg/mem-mapped" },
  { id: "MERGE_VC", commit: "3696f0b", slug: "merge-vcgen", label: "sg/merge-vcgen" },
];

const PATHS: PathDef[] = [
  { shortPath: "old/P3.lean", filePart: "old_P3", fullPath: "Kraken/Examples/P3.lean", isP3: true },
  { shortPath: "P3.lean", filePart: "P3", fullPath: "Kraken/X64/Examples/P3.lean", isP3: true },
  { shortPath: "WP/P3.lean", filePart: "WP_P3", fullPath: "Kraken/X64/Examples/WP/P3.lean", isP3: true },
  { shortPath: "old/Examples.lean", filePart: "old_Examples", fullPath: "Kraken/Examples/Examples.lean", isP3: false },
  { shortPath: "Examples.lean", filePart: "Examples", fullPath: "Kraken/X64/Examples/Examples.lean", isP3: false },
];

function git(args: string[]): { ok: boolean; stdout: string; stderr: string } {
  const res = Bun.spawnSync(["git", "-C", REPO, ...args], {
    stdout: "pipe",
    stderr: "pipe",
  });
  return {
    ok: res.exitCode === 0,
    stdout: res.stdout.toString(),
    stderr: res.stderr.toString(),
  };
}

function gitRaw(args: string[]): Uint8Array {
  const res = Bun.spawnSync(["git", "-C", REPO, ...args], {
    stdout: "pipe",
    stderr: "pipe",
  });
  if (res.exitCode !== 0) {
    throw new Error(`git ${args.join(" ")} failed: ${res.stderr.toString()}`);
  }
  return res.stdout;
}

function uniq<T>(arr: T[]): T[] {
  return [...new Set(arr)];
}

function findMmdr(): string | null {
  const onPath = Bun.which("mmdr");
  if (onPath) return onPath;

  const candidates = [
    join(homedir(), ".local/state/nix/profiles/profile/bin/mmdr"),
    join(homedir(), ".nix-profile/bin/mmdr"),
    join("/etc/profiles/per-user", process.env.USER ?? "", "bin/mmdr"),
  ];
  for (const c of candidates) {
    if (existsSync(c)) return c;
  }
  return null;
}

// 1. Collect commit dates and existing blobs across all nodes and paths
const entries: FileEntry[] = [];
const commitDates = new Map<string, string>();

for (const [nodeIndex, n] of NODES.entries()) {
  const hasCommit = git(["cat-file", "-e", `${n.commit}^{commit}`]).ok;
  if (!hasCommit) {
    console.warn(`WARNING: Missing commit ${n.id} (${n.commit})`);
    continue;
  }

  const dateRes = git(["show", "-s", "--format=%cs", n.commit]);
  commitDates.set(n.id, dateRes.ok ? dateRes.stdout.trim() : "????-??-??");

  for (const p of PATHS) {
    const rev = git(["rev-parse", `${n.commit}:${p.fullPath}`]);
    if (!rev.ok) continue;

    const blob = rev.stdout.trim();
    const content = git(["cat-file", "-p", blob]).stdout;
    const lineCount = content.split("\n").length;

    entries.push({
      nodeIndex,
      id: n.id,
      commit: n.commit,
      slug: n.slug,
      label: n.label,
      shortPath: p.shortPath,
      filePart: p.filePart,
      fullPath: p.fullPath,
      isP3: p.isP3,
      blob,
      lines: lineCount,
    });
  }
}

const dateOf = (id: string) => commitDates.get(id) ?? "????-??-??";

// 2. Group by exact git blob hash, sorted with P3 files first, then node order
const byBlob = new Map<string, FileEntry[]>();
for (const e of entries) {
  const list = byBlob.get(e.blob) ?? [];
  list.push(e);
  byBlob.set(e.blob, list);
}

const rawGroups = [...byBlob.entries()].map(([blob, groupEntries]) => {
  const sortedEntries = [...groupEntries].sort((a, b) => a.nodeIndex - b.nodeIndex);
  const isP3 = sortedEntries.some((e) => e.isP3);
  const firstNodeIndex = sortedEntries[0].nodeIndex;
  return { blob, entries: sortedEntries, isP3, firstNodeIndex };
});

rawGroups.sort((a, b) => {
  if (a.isP3 !== b.isP3) return a.isP3 ? -1 : 1;
  return a.firstNodeIndex - b.firstNodeIndex;
});

const groups: Group[] = rawGroups.map((g, idx) => {
  const num = String(idx + 1).padStart(2, "0");
  const gname = `G${num}`;
  const fileParts = uniq(g.entries.map((e) => e.filePart)).join("_");
  const branchSlugs = uniq(g.entries.map((e) => e.slug)).join("_");
  const fname = `${gname}_${fileParts}_${branchSlugs}.lean`;
  return {
    gname,
    fname,
    blob: g.blob,
    isP3: g.isP3,
    firstNodeIndex: g.firstNodeIndex,
    entries: g.entries,
  };
});

// 3. Build tag map for Mermaid nodes
const tagMap = new Map<string, string>();
for (const n of NODES) {
  const hits: string[] = [];
  for (const g of groups) {
    const matches = g.entries.filter((e) => e.id === n.id);
    if (matches.length > 0) {
      const pnames = matches.map((m) => m.shortPath).join(", ");
      hits.push(`${g.gname} (${pnames})`);
    }
  }
  tagMap.set(n.id, hits.length === 0 ? "MISSING" : hits.join(", "));
}

const tag = (id: string) => tagMap.get(id) ?? "MISSING";

// 4. Write output files (cleaning stale .lean files first)
mkdirSync(OUT_DIR, { recursive: true });
for (const f of readdirSync(OUT_DIR)) {
  if (f.endsWith(".lean")) {
    rmSync(join(OUT_DIR, f));
  }
}

for (const g of groups) {
  const outPath = join(OUT_DIR, g.fname);
  const rawBlob = gitRaw(["cat-file", "-p", g.blob]);
  writeFileSync(outPath, rawBlob);
}

// 5. Generate Mermaid flowchart (Left-to-Right DAG + Chronological Timeline below)
const mermaidDoc = [
  "flowchart LR",
  "    %% Upstream AeneasVerif/kraken main + upstream PR branches",
  '    subgraph UPSTREAM["AeneasVerif/kraken (upstream)"]',
  `        M_125["<b>881e959</b> · PR #125 · ${dateOf("M_125")}<br/><i>Upstream base before</i><br/><i>estatem-kfold branched off</i><br/><b>[${tag("M_125")}]</b>"]`,
  `        M_131["<b>05cad40</b> · PR #131 · ${dateOf("M_131")}<br/><i>Upstream snapshot where</i><br/><i>sgraf812/main froze</i><br/><b>[${tag("M_131")}]</b>"]`,
  `        M_154["<b>2c56cbd</b> · PR #154 · ${dateOf("M_154")}<br/><i>X64/AArch64 split,</i><br/><i>generic layout, ecancel</i><br/><b>[${tag("M_154")}]</b>"]`,
  `        M_160["<b>30f5a5f</b> · PR #160 · ${dateOf("M_160")}<br/><i>Merge toolchain-nightly-09-21</i><br/><i>&amp; Lean module system</i><br/><b>[${tag("M_160")}]</b>"]`,
  `        M_165["<b>72f3a7a</b> · PR #165 · ${dateOf("M_165")}<br/><i>sgraf812/wp-foundation</i><br/><i>merged to upstream</i><br/><b>[${tag("M_165")}]</b>"]`,
  `        M_179["<b>6064eec</b> · PR #179 · ${dateOf("M_179")}<br/><i>x64-fix-avx-access</i><br/><i>(base of conj-wp)</i><br/><b>[${tag("M_179")}]</b>"]`,
  `        M_247["<b>0fccb2d</b> · PR #247 · ${dateOf("M_247")}<br/><i>Rep-string, delaborators,</i><br/><i>AArch64 parsers (synced to vcgen)</i><br/><b>[${tag("M_247")}]</b>"]`,
  `        M_HEAD["<b>AeneasVerif/main</b> (b44bf3f) · ${dateOf("M_HEAD")}<br/><i>Latest upstream main:</i><br/><i>layout &amp; parser fixes (+10 / +245)</i><br/><b>[${tag("M_HEAD")}]</b>"]`,
  "",
  `        PR_166["<b>sgraf812/statewp</b> · PR #166 (4989e1c)<br/>${dateOf("PR_166")} · <i>Program.WP vcgen (kvcgen64),</i><br/><i>Host/step1 (+5; no 829c9468)</i><br/><b>[${tag("PR_166")}]</b>"]`,
  `        PR_195["<b>sgraf812/conj-wp</b> · PR #195 (f5a85a1)<br/>${dateOf("PR_195")} · <i>Conjunctive Program.wp,</i><br/><i>SP call inv (+25; no 829c9468)</i><br/><b>[${tag("PR_195")}]</b>"]`,
  "",
  '        M_125 -->|"+29"| M_131',
  "        M_131 --> M_154",
  "        M_154 --> M_160",
  "        M_160 --> M_165",
  "        M_165 --> M_179",
  "        M_179 --> M_247",
  '        M_247 -->|"+10"| M_HEAD',
  "",
  '        M_165 -->|"+5"| PR_166',
  '        M_179 -->|"+25"| PR_195',
  "    end",
  "",
  "    %% sgraf812/kraken branches",
  '    subgraph SGRAF["sgraf812/kraken"]',
  `        SG_MAIN["<b>main</b> (05cad40) · ${dateOf("SG_MAIN")}<br/><i>Stale fork mirror of PR #131</i><br/><b>[${tag("SG_MAIN")}]</b>"]`,
  `        EST["<b>estatem-kfold</b> (d68f0a4) · ${dateOf("EST")}<br/><i>Open/closed Program.wp,</i><br/><i>Program.WF, blocks (+154)</i><br/><b>[${tag("EST")}]</b>"]`,
  `        TN["<b>toolchain-nightly-09-21</b> (1045c33)<br/>${dateOf("TN")} · <i>Lean module system</i><br/><i>&amp; nightly-09-21 (+75)</i><br/><b>[${tag("TN")}]</b>"]`,
  `        SEP["<b>sgraf812:sepwp</b> · PR #161 (12371fd)<br/>${dateOf("SEP")} · <i>Separation WP (MProp)</i><br/><i>&amp; frame prototype (+5; no 829c9468)</i><br/><b>[${tag("SEP")}]</b>"]`,
  "",
  "        M_131 -.-> SG_MAIN",
  '        M_125 -->|"+154"| EST',
  "        M_154 --> TN",
  '        TN -. "PR #160" .-> M_160',
  '        M_160 -->|"+5"| SEP',
  "",
  "        %% Merge of estatem-kfold + upstream main",
  `        M23B["<b>23b6409</b> (Merge) · ${dateOf("M23B")}<br/><i>Merge estatem-kfold with</i><br/><i>X64/AArch64 split &amp; ecancel</i><br/><b>[${tag("M23B")}]</b>"]`,
  "        EST --> M23B",
  "        M_154 -. merge .-> M23B",
  "",
  "        %% THE TARGET COMMIT = EXACT FORK POINT",
  `        C829(["<b>829c9468</b> · ${dateOf("C829")}<br/>TARGET COMMIT / FORK POINT<br/><i>Algebraic ecancel (SepOps) +</i><br/><i>solveSepSplit frameproc</i><br/><b>[${tag("C829")}]</b>"])`,
  '        M23B -->|"+22"| C829',
  "",
  "        %% Track A: FMA3 -> nightly-2026-10-14 -> upstream-speedups",
  `        FMA3["<b>sg/fma3-default-limits</b> (9209b11)<br/>${dateOf("FMA3")} · <i>FMA3 at default limits</i><br/><i>+ SbrNegOdd64 (+11)</i><br/><b>[${tag("FMA3")}]</b>"]`,
  `        N1014["<b>sg/nightly-2026-10-14</b> (9743c3a)<br/>${dateOf("N1014")} · <i>Nightly 10-14; indirect calls;</i><br/><i>trim MachineWP (+12 / +23)</i><br/><b>[${tag("N1014")}]</b>"]`,
  `        SPEED["<b>sg/upstream-speedups</b> (a443d2c)<br/>${dateOf("SPEED")} · <i>Clean simp/grind forms,</i><br/><i>faster CFG VCs (+14 / +37)</i><br/><b>[${tag("SPEED")}]</b>"]`,
  "",
  '        C829 -->|"+11"| FMA3',
  '        FMA3 -->|"+12"| N1014',
  '        N1014 -->|"+14"| SPEED',
  "",
  "        %% Track B: 63c72ed -> 7cfd503 -> sg/drop-framewp -> vcgen",
  `        M63C["<b>63c72ed</b> (Merge) · ${dateOf("M63C")}<br/><i>Adopt Lean module system</i><br/><i>&amp; nightly-2026-09-21</i><br/><b>[${tag("M63C")}]</b>"]`,
  `        M7CF["<b>7cfd503</b> (Merge) · ${dateOf("M7CF")}<br/><i>Pull sepwp prototype (PR #161)</i><br/><i>over baseline trunk</i><br/><b>[${tag("M7CF")}]</b>"]`,
  `        DROP["<b>sg/drop-framewp</b> (bc85a6a)<br/>${dateOf("DROP")} · <i>CFG-invariant Program.wp;</i><br/><i>drops sep WP &amp; frame inf (+179)</i><br/><b>[${tag("DROP")}]</b>"]`,
  `        VCGEN["<b>vcgen</b> (6c2f048) · ${dateOf("VCGEN")}<br/><i>Main active VCGen: ChangingFrames /</i><br/><i>ManyCalls + upstream sync (+152 / +331)</i><br/><b>[${tag("VCGEN")}]</b>"]`,
  "",
  '        C829 -->|"+21"| M63C',
  "        TN -. merge .-> M63C",
  "        M63C --> M7CF",
  "        SEP -. merge .-> M7CF",
  "        M7CF --> DROP",
  '        DROP -->|"+152"| VCGEN',
  '        M_247 -. "merge (339acd1)" .-> VCGEN',
  "",
  "        %% sg/merge-vcgen combines Track A + early vcgen + drop-framewp",
  `        DCC["<b>dcc8cc1</b> (Merge) · ${dateOf("DCC")}<br/><i>Merge early vcgen (fe604b6)</i><br/><i>into sg/mem-mapped</i><br/><b>[${tag("DCC")}]</b>"]`,
  `        MERGE_VC["<b>sg/merge-vcgen</b> (3696f0b)<br/>${dateOf("MERGE_VC")} · <i>Port Butterflies/FmulSse;</i><br/><i>unify Track A + drop-framewp (+26 / +205)</i><br/><b>[${tag("MERGE_VC")}]</b>"]`,
  "",
  "        FMA3 --> DCC",
  "        DCC --> MERGE_VC",
  "        DROP -. merge .-> MERGE_VC",
  "    end",
  "",
  "    %% Chronological Timeline Axis (below the left-to-right graph)",
  '    subgraph TIMELINE["Timeline (2026, Committer Dates)"]',
  '        T01["<b>Jul 22</b><br/>PR #125"]',
  '        T02["<b>Aug 03</b><br/>PR #131"]',
  '        T03["<b>Aug 14–17</b><br/>estatem / PR #154"]',
  '        T04["<b>Sep 10</b><br/>23b6409"]',
  '        T05(["<b>Sep 18</b><br/>829c9468"])',
  '        T06["<b>Sep 25</b><br/>nightly-09-21"]',
  '        T07["<b>Sep 25–29</b><br/>PR #160 / 63c72ed"]',
  '        T08["<b>Sep 28</b><br/>sepwp"]',
  '        T09["<b>Sep 29–30</b><br/>7cfd503 / FMA3"]',
  '        T10["<b>Oct 16–20</b><br/>10-14 / PR #165"]',
  '        T11["<b>Oct 19–20</b><br/>speedups / PR #166"]',
  '        T12["<b>Oct 26–27</b><br/>dcc8cc1 / drop-framewp"]',
  '        T13["<b>Oct 27</b><br/>merge-vcgen"]',
  '        T14["<b>Nov 02</b><br/>PR #179"]',
  '        T15["<b>Nov 05–11</b><br/>conj-wp / PR #247"]',
  '        T16["<b>Nov 12–16</b><br/>vcgen / main HEAD"]',
  "",
  "        T01 --> T02 --> T03 --> T04 --> T05 --> T06 --> T07 --> T08 --> T09 --> T10 --> T11 --> T12 --> T13 --> T14 --> T15 --> T16",
  "    end",
  "",
  "    %% Invisible rank-pinning links aligning commits above their timeline dates",
  "    M_125 ~~~ T02",
  "    T01 ~~~ M_131",
  "    M_131 ~~~ T03",
  "    T02 ~~~ EST",
  "    T02 ~~~ M_154",
  "    EST ~~~ T04",
  "    M_154 ~~~ T04",
  "    T03 ~~~ M23B",
  "    M23B ~~~ T05",
  "    T04 ~~~ C829",
  "    C829 ~~~ T06",
  "    T05 ~~~ TN",
  "    TN ~~~ T07",
  "    T06 ~~~ M_160",
  "    T06 ~~~ M63C",
  "    M_160 ~~~ T08",
  "    M63C ~~~ T08",
  "    T07 ~~~ SEP",
  "    SEP ~~~ T09",
  "    T08 ~~~ M7CF",
  "    T08 ~~~ FMA3",
  "    M7CF ~~~ T10",
  "    FMA3 ~~~ T10",
  "    T09 ~~~ N1014",
  "    T09 ~~~ M_165",
  "    N1014 ~~~ T11",
  "    M_165 ~~~ T11",
  "    T10 ~~~ SPEED",
  "    T10 ~~~ PR_166",
  "    SPEED ~~~ T12",
  "    PR_166 ~~~ T12",
  "    T11 ~~~ DCC",
  "    T11 ~~~ DROP",
  "    DCC ~~~ T13",
  "    DROP ~~~ T13",
  "    T12 ~~~ MERGE_VC",
  "    MERGE_VC ~~~ T14",
  "    T13 ~~~ M_179",
  "    M_179 ~~~ T15",
  "    T14 ~~~ PR_195",
  "    T14 ~~~ M_247",
  "    PR_195 ~~~ T16",
  "    M_247 ~~~ T16",
  "    T15 ~~~ VCGEN",
  "    T15 ~~~ M_HEAD",
  "",
  "    %% Legend",
  '    subgraph LEGEND["Node Color Legend"]',
  "        direction LR",
  '        L1["Upstream main"]',
  '        L2["Older / frozen base branch"]',
  '        L3["Integration merge"]',
  '        L_PR["Active PR branch (thick rim)"]',
  '        L4(["Target commit / fork point"])',
  '        L5["Track A: FMA3 &amp; speedups"]',
  '        L6["Track B: Active VCGen line"]',
  "    end",
  "",
  "    %% Subgraph backgrounds (clean neutral canvas so node colors pop)",
  "    style UPSTREAM fill:#f8fafc,stroke:#94a3b8,stroke-width:1.5px,color:#0f172a",
  "    style SGRAF fill:#f8fafc,stroke:#94a3b8,stroke-width:1.5px,color:#0f172a",
  "    style TIMELINE fill:#f1f5f9,stroke:#64748b,stroke-width:1.5px,color:#0f172a",
  "    style LEGEND fill:#ffffff,stroke:#cbd5e1,stroke-width:1px,color:#0f172a",
  "",
  "    %% Node-type color classes",
  "    classDef upstream fill:#dbeafe,stroke:#2563eb,stroke-width:2px,color:#0f172a",
  "    classDef baseBranch fill:#f1f5f9,stroke:#64748b,stroke-width:1.5px,color:#0f172a",
  "    classDef mergeNode fill:#ede9fe,stroke:#7c3aed,stroke-width:1.5px,color:#0f172a",
  "    classDef activePR fill:#fce7f3,stroke:#be123c,stroke-width:4.5px,color:#0f172a",
  "    classDef targetCommit fill:#fef08a,stroke:#b45309,stroke-width:4px,color:#0f172a",
  "    classDef trackA fill:#ccfbf1,stroke:#0d9488,stroke-width:2px,color:#0f172a",
  "    classDef trackB fill:#dcfce7,stroke:#15803d,stroke-width:2px,color:#0f172a",
  "    classDef timelineNode fill:#ffffff,stroke:#64748b,stroke-width:1.5px,color:#0f172a",
  "    classDef timelineTarget fill:#fef08a,stroke:#b45309,stroke-width:3px,color:#0f172a",
  "",
  "    class M_125,M_131,M_154,M_160,M_165,M_179,M_247,M_HEAD,L1 upstream",
  "    class SG_MAIN,EST,TN,L2 baseBranch",
  "    class M23B,M63C,M7CF,DCC,L3 mergeNode",
  "    class PR_166,PR_195,SEP,L_PR activePR",
  "    class C829,L4 targetCommit",
  "    class FMA3,N1014,SPEED,L5 trackA",
  "    class DROP,VCGEN,MERGE_VC,L6 trackB",
  "    class T01,T02,T03,T04,T06,T07,T08,T09,T10,T11,T12,T13,T14,T15,T16 timelineNode",
  "    class T05 timelineTarget",
  "",
].join("\n");

const mermaidPath = join(OUT_DIR, "flowchart.mermaid");
const pngPath = join(OUT_DIR, "flowchart.svg");
writeFileSync(mermaidPath, mermaidDoc, "utf8");

// 6. Render flowchart.png with mmdr (mermaid-rs-renderer)
const mmdrBin = findMmdr();
const renderCmd = mmdrBin
  ? [mmdrBin, "-i", mermaidPath, "-o", pngPath, "-e", "svg"]
  : ["nix", "run", "github:1jehuang/mermaid-rs-renderer", "--", "-i", mermaidPath, "-o", pngPath, "-e", "svg"];

console.log(`Rendering PNG via: ${renderCmd.join(" ")}`);
const renderRes = Bun.spawnSync(renderCmd, {
  stdout: "pipe",
  stderr: "pipe",
});

if (renderRes.exitCode !== 0) {
  console.error("mmdr failed:", renderRes.stderr.toString() || renderRes.stdout.toString());
  process.exit(1);
}

// 7. Summary
console.log(`\n=== Created ${OUT_DIR}/ ===`);
for (const f of readdirSync(OUT_DIR).sort()) {
  const size = statSync(join(OUT_DIR, f)).size;
  console.log(`${f} (${size} bytes)`);
}

console.log("\n=== Group files mapping ===");
for (const g of groups) {
  const entriesStr = g.entries.map((e) => `${e.id}:${e.shortPath}`).join(", ");
  console.log(`${g.fname} <- ${entriesStr}`);
}
