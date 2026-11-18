export type {
  CommitMeta,
  EdgeDef,
  GraphData,
  GroupSummary,
  LaneDef,
  NodeDef,
  NodeGroupRef,
  NodeKind,
  TimelineCol,
} from "./schema";

export interface PathDef {
  shortPath: string;
  filePart: string;
  fullPath: string;
  isP3: boolean;
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
