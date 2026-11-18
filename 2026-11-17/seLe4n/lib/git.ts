import { NODES, PATHS, REPO } from "./data";
import type { CommitMeta, FileEntry } from "./types";

export function git(args: string[]): { ok: boolean; stdout: string; stderr: string } {
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

export function gitRaw(args: string[]): Uint8Array {
  const res = Bun.spawnSync(["git", "-C", REPO, ...args], {
    stdout: "pipe",
    stderr: "pipe",
  });
  if (res.exitCode !== 0) {
    throw new Error(`git ${args.join(" ")} failed: ${res.stderr.toString()}`);
  }
  return res.stdout;
}

export function collectGitData(): {
  entries: FileEntry[];
  metaByNode: Map<string, CommitMeta>;
} {
  const entries: FileEntry[] = [];
  const metaByNode = new Map<string, CommitMeta>();

  for (const [nodeIndex, n] of NODES.entries()) {
    const hasCommit = git(["cat-file", "-e", `${n.commit}^{commit}`]).ok;
    if (!hasCommit) {
      console.warn(`WARNING: Missing commit ${n.id} (${n.commit})`);
      continue;
    }

    const metaRes = git(["show", "-s", "--format=%h%x00%as%x00%cs%x00%s", n.commit]);
    if (metaRes.ok) {
      const [hash, authorDate, committerDate, subject] = metaRes.stdout.trim().split("\0");
      metaByNode.set(n.id, { hash, authorDate, committerDate, subject });
    }

    for (const p of PATHS) {
      const rev = git(["rev-parse", `${n.commit}:${p.fullPath}`]);
      if (!rev.ok) continue;

      const blob = rev.stdout.trim();
      const content = git(["cat-file", "-p", blob]).stdout;
      const lines = content.split("\n").length;

      entries.push({
        nodeIndex,
        id: n.id,
        commit: n.commit,
        slug: n.slug,
        shortPath: p.shortPath,
        filePart: p.filePart,
        fullPath: p.fullPath,
        isP3: p.isP3,
        blob,
        lines,
      });
    }
  }

  return { entries, metaByNode };
}
