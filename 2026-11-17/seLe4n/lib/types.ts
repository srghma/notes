export type NodeKind =
  | "upstream"
  | "baseBranch"
  | "mergeNode"
  | "activePR"
  | "targetCommit"
  | "trackA"
  | "trackB";

export interface NodeDef {
  id: string;
  commit: string;
  slug: string;
  title: string;
  desc: string;
  kind: NodeKind;
  col: number;
  lane: number;
}

export interface EdgeDef {
  from: string;
  to: string;
  label?: string;
  dashed?: boolean;
}

export interface TimelineCol {
  col: number;
  dateLabel: string;
  subLabel: string;
  isTarget?: boolean;
}

export interface LaneDef {
  lane: number;
  band: "upstream" | "sgraf";
  label: string;
}

export interface PathDef {
  shortPath: string;
  filePart: string;
  fullPath: string;
  isP3: boolean;
}

export interface CommitMeta {
  hash: string;
  authorDate: string;
  committerDate: string;
  subject: string;
}

export interface FileEntry {
  nodeIndex: number;
  id: string;
  commit: string;
  slug: string;
  shortPath: string;
  filePart: string;
  fullPath: string;
  isP3: boolean;
  blob: string;
  lines: number;
}

export interface Group {
  gname: string;
  fname: string;
  blob: string;
  isP3: boolean;
  firstNodeIndex: number;
  entries: FileEntry[];
}
