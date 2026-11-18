#!/usr/bin/env bun

import { mkdirSync, readdirSync, statSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { validateGraphData } from "../lib/schema";
import { EDGES, LANES, NODES, REPO, TIMELINE_COLS } from "./gen/data";
import { collectGitData } from "./gen/git";
import {
  buildGroups,
  buildNodeGroupRecord,
  writeGroupFiles,
} from "./gen/groups";

const APP_DIR = join(import.meta.dir, "..");
const OUT_DIR = join(APP_DIR, "p3_groups");
const DATA_DIR = join(APP_DIR, "data");
const DATA_JSON_PATH = join(DATA_DIR, "graph.json");

const { entries, metaByNode } = collectGitData();
const groups = buildGroups(entries);
const groupsByNode = buildNodeGroupRecord(groups);

writeGroupFiles(OUT_DIR, groups);

const graphPayload = validateGraphData({
  repo: REPO,
  generatedAt: new Date().toISOString(),
  lanes: LANES,
  timelineCols: TIMELINE_COLS,
  nodes: NODES,
  edges: EDGES,
  metaByNode,
  groupsByNode,
  groups: groups.map((g) => ({
    gname: g.gname,
    fname: g.fname,
    blob: g.blob,
    isP3: g.isP3,
    entries: g.entries.map((e) => ({
      id: e.id,
      shortPath: e.shortPath,
      lines: e.lines,
    })),
  })),
});

mkdirSync(DATA_DIR, { recursive: true });
writeFileSync(
  DATA_JSON_PATH,
  `${JSON.stringify(graphPayload, null, 2)}\n`,
  "utf8",
);

console.log(`=== Wrote ${DATA_JSON_PATH} ===`);
console.log(`=== Created ${OUT_DIR}/ ===`);
for (const f of readdirSync(OUT_DIR).sort()) {
  const size = statSync(join(OUT_DIR, f)).size;
  console.log(`${f} (${size} bytes)`);
}

console.log("\n=== Group files mapping ===");
for (const g of groups) {
  const entriesStr = g.entries.map((e) => `${e.id}:${e.shortPath}`).join(", ");
  console.log(`${g.fname} <- ${entriesStr}`);
}
