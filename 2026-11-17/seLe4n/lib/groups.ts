import { mkdirSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { NODES } from "./data";
import { gitRaw } from "./git";
import type { FileEntry, Group } from "./types";

function uniq<T>(arr: T[]): T[] {
  return [...new Set(arr)];
}

export function buildGroups(entries: FileEntry[]): Group[] {
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

  return rawGroups.map((g, idx) => {
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
}

export interface NodeGroupRef {
  gname: string;
  fname: string;
  shortPath: string;
  fullPath: string;
  lines: number;
}

export function buildNodeGroupMap(groups: Group[]): Map<string, NodeGroupRef[]> {
  const map = new Map<string, NodeGroupRef[]>();
  for (const n of NODES) {
    const refs: NodeGroupRef[] = [];
    for (const g of groups) {
      for (const m of g.entries) {
        if (m.id === n.id) {
          refs.push({
            gname: g.gname,
            fname: g.fname,
            shortPath: m.shortPath,
            fullPath: m.fullPath,
            lines: m.lines,
          });
        }
      }
    }
    map.set(n.id, refs);
  }
  return map;
}

export function writeGroupFiles(outDir: string, groups: Group[]): void {
  mkdirSync(outDir, { recursive: true });
  for (const f of readdirSync(outDir)) {
    if (f.endsWith(".lean")) {
      rmSync(join(outDir, f));
    }
  }
  for (const g of groups) {
    const outPath = join(outDir, g.fname);
    writeFileSync(outPath, gitRaw(["cat-file", "-p", g.blob]));
  }
}
