import { z } from "zod";

export const NodeKindSchema = z.enum([
  "upstream",
  "baseBranch",
  "mergeNode",
  "activePR",
  "targetCommit",
  "trackA",
  "trackB",
]);

export const NodeSchema = z.object({
  id: z.string().min(1),
  commit: z.string().min(1),
  slug: z.string().min(1),
  title: z.string().min(1),
  desc: z.string().min(1),
  kind: NodeKindSchema,
  col: z.number().int().nonnegative(),
  lane: z.number().int().nonnegative(),
});

export const EdgeSchema = z.object({
  from: z.string().min(1),
  to: z.string().min(1),
  label: z.string().min(1).optional(),
  dashed: z.boolean().optional(),
});

export const TimelineColSchema = z.object({
  col: z.number().int().nonnegative(),
  dateLabel: z.string().min(1),
  subLabel: z.string().min(1),
  isTarget: z.boolean().optional(),
});

export const LaneSchema = z.object({
  lane: z.number().int().nonnegative(),
  band: z.enum(["upstream", "sgraf"]),
  label: z.string().min(1),
});

export const CommitMetaSchema = z.object({
  hash: z.string().min(1),
  authorDate: z.string().regex(/^\d{4}-\d{2}-\d{2}$/),
  committerDate: z.string().regex(/^\d{4}-\d{2}-\d{2}$/),
  subject: z.string().min(1),
});

export const NodeGroupRefSchema = z.object({
  gname: z.string().min(1),
  fname: z.string().min(1),
  shortPath: z.string().min(1),
  fullPath: z.string().min(1),
  lines: z.number().int().positive(),
});

export const GroupSummarySchema = z.object({
  gname: z.string().min(1),
  fname: z.string().min(1),
  blob: z.string().min(1),
  isP3: z.boolean(),
  entries: z.array(
    z.object({
      id: z.string().min(1),
      shortPath: z.string().min(1),
      lines: z.number().int().positive(),
    }),
  ),
});

export const GraphDataSchema = z.object({
  repo: z.string().min(1),
  generatedAt: z.string().min(1),
  lanes: z.array(LaneSchema).min(1),
  timelineCols: z.array(TimelineColSchema).min(1),
  nodes: z.array(NodeSchema).min(1),
  edges: z.array(EdgeSchema),
  metaByNode: z.record(z.string(), CommitMetaSchema),
  groupsByNode: z.record(z.string(), z.array(NodeGroupRefSchema)),
  groups: z.array(GroupSummarySchema),
});

export type NodeKind = z.infer<typeof NodeKindSchema>;
export type NodeDef = z.infer<typeof NodeSchema>;
export type EdgeDef = z.infer<typeof EdgeSchema>;
export type TimelineCol = z.infer<typeof TimelineColSchema>;
export type LaneDef = z.infer<typeof LaneSchema>;
export type CommitMeta = z.infer<typeof CommitMetaSchema>;
export type NodeGroupRef = z.infer<typeof NodeGroupRefSchema>;
export type GroupSummary = z.infer<typeof GroupSummarySchema>;
export type GraphData = z.infer<typeof GraphDataSchema>;

export function validateGraphData(raw: unknown): GraphData {
  const data = GraphDataSchema.parse(raw);

  const nodeIds = new Set<string>();
  const cellKeys = new Set<string>();
  const colIndices = new Set(data.timelineCols.map((c) => c.col));
  const laneIndices = new Set(data.lanes.map((l) => l.lane));

  for (const n of data.nodes) {
    if (nodeIds.has(n.id)) {
      throw new Error(`Duplicate node id: ${n.id}`);
    }
    nodeIds.add(n.id);

    if (!colIndices.has(n.col)) {
      throw new Error(`Node ${n.id} references unknown col ${n.col}`);
    }
    if (!laneIndices.has(n.lane)) {
      throw new Error(`Node ${n.id} references unknown lane ${n.lane}`);
    }

    const cell = `${n.col}:${n.lane}`;
    if (cellKeys.has(cell)) {
      throw new Error(`Grid collision at cell ${cell} for node ${n.id}`);
    }
    cellKeys.add(cell);

    if (!data.metaByNode[n.id]) {
      throw new Error(`Missing commit metadata for node ${n.id}`);
    }
    if (!data.groupsByNode[n.id]) {
      throw new Error(`Missing groups entry for node ${n.id}`);
    }
  }

  for (const e of data.edges) {
    if (!nodeIds.has(e.from)) {
      throw new Error(`Edge references unknown 'from' node: ${e.from}`);
    }
    if (!nodeIds.has(e.to)) {
      throw new Error(`Edge references unknown 'to' node: ${e.to}`);
    }
  }

  return data;
}
