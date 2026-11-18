#!/usr/bin/env bun

import { readdirSync, statSync } from "node:fs";
import { join } from "node:path";
import { collectGitData } from "./lib/git";
import { buildGroups, buildNodeGroupMap, writeGroupFiles } from "./lib/groups";
import { renderHtml } from "./lib/renderHtml";

const OUT_DIR = join(import.meta.dir, "p3_groups");

const { entries, metaByNode } = collectGitData();
const groups = buildGroups(entries);
const nodeGroups = buildNodeGroupMap(groups);

writeGroupFiles(OUT_DIR, groups);

const htmlPath = join(OUT_DIR, "index.html");
renderHtml(htmlPath, metaByNode, nodeGroups);

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

console.log(`\nOpen in browser: file://${htmlPath}`);
