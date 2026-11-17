import React, { useMemo, useState } from "react";

/* ============================================================================
   TYPE-SPACE DATA
   ----------------------------------------------------------------------------
   Every learnable Zig type in this app is keyed by its literal spelling
   ("Node", "*Node", "?*Node", ...). Vector / matrix / cube all just render
   pointers into this one map, so clicking the same type from two different
   sections (e.g. "*Node" in both the matrix and the cube) shows identical
   content -- there's exactly one source of truth per type.
   ========================================================================== */

const EXAMPLES = {
  Node: {
    formula: "Node",
    title: "Plain value",
    blurb: "The struct itself. Copying it copies every field.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

pub fn main() void {
    // \`Node\` is a plain value: it lives wherever you put it
    // (stack, another struct, ...) and copying it copies the
    // whole struct.
    var n: Node = .{ .value = 10 };
    n.value += 5;
    std.debug.print("n.value = {d}\\n", .{n.value});
}`,
  },
  "?Node": {
    formula: "?Node",
    title: "Optional value",
    blurb: "The whole struct, plus one extra bit for \u201cpresent or not\u201d. Still not a pointer.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

pub fn main() void {
    // \`?Node\` is an *optional value*, not a pointer: it's the
    // whole struct plus one bit saying "present or not".
    var maybe: ?Node = Node{ .value = 3 };

    if (maybe) |n| {
        std.debug.print("present: {d}\\n", .{n.value});
    }

    maybe = null;
    std.debug.print("is null now: {}\\n", .{maybe == null});
}`,
  },
  "*Node": {
    formula: "*Node",
    title: "Non-null pointer",
    blurb: "Must point at a real Node. No unwrapping, ever.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn bump(n: *Node) void {
    // \`n\` is guaranteed non-null: no unwrapping required.
    n.value += 1;
}

pub fn main() void {
    var n = Node{ .value = 1 };
    bump(&n);
    std.debug.print("n.value = {d}\\n", .{n.value});
}`,
  },
  "*?Node": {
    formula: "*?Node",
    title: "Non-null pointer to an optional value",
    blurb: "The pointer can't be null \u2014 but the value it points at can be empty.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn clearSlot(slot: *?Node) void {
    // \`slot\` itself can never be null, but the *value it
    // points at* can be empty.
    slot.* = null;
}

pub fn main() void {
    var slot: ?Node = Node{ .value = 7 };
    clearSlot(&slot);
    std.debug.print("slot is null: {}\\n", .{slot == null});
}`,
  },
  "?*Node": {
    formula: "?*Node",
    title: "Nullable pointer",
    blurb: "The classic linked-list \u201cnext\u201d field: either a real Node or nothing.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
    next: ?*Node = null,
};

pub fn main() void {
    var b = Node{ .value = 2 };
    var a = Node{ .value = 1, .next = &b };

    var walk: ?*Node = &a;
    while (walk) |n| : (walk = n.next) {
        std.debug.print("{d}\\n", .{n.value});
    }
}`,
  },
  "?*?Node": {
    formula: "?*?Node",
    title: "Nullable pointer to an optional value",
    blurb: "Two independent maybes stacked: the pointer might be absent, and so might the value.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn maybeClear(slot: ?*?Node) void {
    if (slot) |s| {
        s.* = null;
    }
}

pub fn main() void {
    var value: ?Node = Node{ .value = 9 };
    maybeClear(&value);
    std.debug.print("value is null: {}\\n", .{value == null});
}`,
  },
  "**Node": {
    formula: "**Node",
    title: "Non-null pointer to a non-null pointer",
    blurb: "Both levels are guaranteed non-null. Not the good-taste.md trick \u2014 see the callout below.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn bumpIndirect(pp: **Node) void {
    // both levels are guaranteed non-null
    pp.*.*.value += 100;
}

pub fn main() void {
    var n = Node{ .value = 1 };
    var p: *Node = &n;
    bumpIndirect(&p);
    std.debug.print("n.value = {d}\\n", .{n.value});
}`,
  },
  "**?Node": {
    formula: "**?Node",
    title: "Non-null pointer to a non-null pointer to an optional value",
    blurb: "Two guaranteed pointer hops, landing on a slot that may or may not hold a Node.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn clearIndirect(pp: **?Node) void {
    pp.*.* = null;
}

pub fn main() void {
    var slot: ?Node = Node{ .value = 4 };
    var p: *?Node = &slot;
    clearIndirect(&p);
    std.debug.print("slot is null: {}\\n", .{slot == null});
}`,
  },
  linus: {
    formula: "*?*Node",
    title: "The good-taste.md trick",
    blurb:
      "A non-null pointer to a nullable pointer. This \u2014 not **Node \u2014 is the real Zig translation of Linus's indirect-pointer remove(): the outer pointer (p) can never be null, but the slot it points at (head, or some node's .next) legitimately can be.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
    next: ?*Node = null,
};

// Zig translation of remove_list_entry_fast() from good-taste.md.
// p's type is *?*Node: p itself is never null, but *p (a head
// pointer or a .next field) legitimately can be.
fn removeEntry(head: *?*Node, entry: *Node) void {
    var p: *?*Node = head;
    while (p.* != entry) : (p = &p.*.?.next) {}
    p.* = entry.next;
}

pub fn main() void {
    var c = Node{ .value = 3 };
    var b = Node{ .value = 2, .next = &c };
    var a = Node{ .value = 1, .next = &b };
    var head: ?*Node = &a;

    removeEntry(&head, &b); // unlink the middle node

    var walk = head;
    while (walk) |n| : (walk = n.next) {
        std.debug.print("{d}\\n", .{n.value});
    }
}`,
  },
};

const ZIG_PLAY_URL = "https://zig-play.dev/";

/* ============================================================================
   VECTOR + MATRIX DATA
   ========================================================================== */

const VECTOR_ITEMS = ["Node", "?Node"];

const MATRIX_ROWS = [
  { key: "ptr", label: "Ptr (*)" },
  { key: "optptr", label: "Opt-Ptr (?*)" },
];
const MATRIX_COLS = [
  { key: "val", label: "Value (Node)" },
  { key: "optval", label: "Opt-Value (?Node)" },
];
const MATRIX_CELLS = {
  "ptr:val": "*Node",
  "ptr:optval": "*?Node",
  "optptr:val": "?*Node",
  "optptr:optval": "?*?Node",
};

/* ============================================================================
   CUBE GEOMETRY
   ----------------------------------------------------------------------------
   Static isometric projection (no rotation, no CSS 3D). Axes:
     a (x, screen-right-down)  -> pointer present?
     b (y, screen-left-down)   -> pointer-to-pointer present?
     c (z, screen-up)          -> Optional-of-Node?
   a=0,b=1 is geometrically drawn but logically invalid: you can't have a
   second pointer level without a first.
   ========================================================================== */

const COS30 = Math.cos(Math.PI / 6);
const SIN30 = Math.sin(Math.PI / 6);
const S = 100; // ground (a,b) unit scale
const SZ = 78; // vertical (c) unit scale -- deliberately != S so opposite
// corners (0,0,0) and (1,1,1) never land on the same pixel.

function project(a, b, c) {
  return {
    x: (a - b) * S * COS30,
    y: (a + b) * S * SIN30 - c * SZ,
  };
}

function cubeType(a, b, c) {
  if (a === 0 && b === 1) return { invalid: true };
  const depth = a === 0 ? 0 : b === 0 ? 1 : 2;
  const type = "*".repeat(depth) + (c === 1 ? "?Node" : "Node");
  return { invalid: false, type };
}

const CUBE_VERTICES = [];
for (const a of [0, 1]) {
  for (const b of [0, 1]) {
    for (const c of [0, 1]) {
      CUBE_VERTICES.push({ a, b, c, ...project(a, b, c), ...cubeType(a, b, c) });
    }
  }
}

const CUBE_EDGES = [];
for (let i = 0; i < CUBE_VERTICES.length; i++) {
  for (let j = i + 1; j < CUBE_VERTICES.length; j++) {
    const v1 = CUBE_VERTICES[i];
    const v2 = CUBE_VERTICES[j];
    const diff =
      Math.abs(v1.a - v2.a) + Math.abs(v1.b - v2.b) + Math.abs(v1.c - v2.c);
    if (diff === 1) CUBE_EDGES.push([v1, v2]);
  }
}

/* ============================================================================
   COMPONENT
   ========================================================================== */

export default function ZigTypeSpace() {
  const [selected, setSelected] = useState("linus");
  const example = EXAMPLES[selected];

  const [copied, setCopied] = useState(false);
  const copy = () => {
    navigator.clipboard?.writeText(example.code).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    });
  };

  return (
    <div style={styles.app}>
      <style>{css}</style>

      <header style={styles.header}>
        <h1 style={styles.h1}>
          <span style={styles.h1Accent}>zig</span> type space
        </h1>
        <p style={styles.sub}>
          value &rarr; pointer &rarr; pointer-to-pointer, crossed with Optional. Click any type to load a
          runnable example.
        </p>
      </header>

      <div style={styles.layout}>
        <main style={styles.main}>
          {/* 1. VECTOR */}
          <Section
            index="01"
            title="the vector"
            hint="Node vs. ?Node \u2014 value, or optional value. No pointer yet."
          >
            <div style={styles.vectorRow}>
              {VECTOR_ITEMS.map((k) => (
                <TypeChip key={k} typeKey={k} selected={selected} onSelect={setSelected} size="lg" />
              ))}
            </div>
          </Section>

          {/* 2. MATRIX */}
          <Section
            index="02"
            title="the matrix"
            hint="One pointer level, crossed with pointer-nullability and value-optionality."
          >
            <table style={styles.table}>
              <thead>
                <tr>
                  <th style={styles.thCorner} />
                  {MATRIX_COLS.map((col) => (
                    <th key={col.key} style={styles.th}>
                      {col.label}
                    </th>
                  ))}
                </tr>
              </thead>
              <tbody>
                {MATRIX_ROWS.map((row) => (
                  <tr key={row.key}>
                    <td style={styles.thRow}>{row.label}</td>
                    {MATRIX_COLS.map((col) => {
                      const type = MATRIX_CELLS[`${row.key}:${col.key}`];
                      return (
                        <td key={col.key} style={styles.td}>
                          <TypeChip typeKey={type} selected={selected} onSelect={setSelected} size="md" />
                        </td>
                      );
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </Section>

          {/* 3. CUBE */}
          <Section
            index="03"
            title="the cube"
            hint="x = pointer \u00b7 y = pointer-to-pointer \u00b7 z (up) = Optional. Static \u2014 nothing spins."
          >
            <div style={styles.cubeWrap}>
              <svg viewBox="-140 -130 280 270" style={styles.cubeSvg}>
                {CUBE_EDGES.map(([v1, v2], i) => {
                  const dashed = v1.invalid || v2.invalid;
                  return (
                    <line
                      key={i}
                      x1={v1.x}
                      y1={v1.y}
                      x2={v2.x}
                      y2={v2.y}
                      stroke={dashed ? T.rule : T.edge}
                      strokeWidth={1.5}
                      strokeDasharray={dashed ? "3 4" : undefined}
                    />
                  );
                })}

                {/* axis indicators from the origin (0,0,0) = plain Node */}
                <AxisLabel x={120} y={72} color={T.cyan} label="x \u00b7 pointer" />
                <AxisLabel x={-124} y={72} color={T.violet} anchor="end" label="y \u00b7 ptr-to-ptr" />
                <AxisLabel x={0} y={-104} color={T.green} anchor="middle" label="z \u00b7 Optional" />

                {CUBE_VERTICES.map((v, i) => (
                  <CubeVertex key={i} v={v} selected={selected} onSelect={setSelected} />
                ))}
              </svg>
            </div>
            <p style={styles.cubeFoot}>
              Dashed vertices (x=0, y=1) are geometrically present but not legal types: you can't have a
              second pointer indirection without a first.
            </p>
          </Section>

          {/* CALLOUT */}
          <Section index="04" title="the actual good-taste.md type" hint="Where the cube's **Node quietly diverges from the real trick.">
            <button
              style={{
                ...styles.linusCard,
                ...(selected === "linus" ? styles.linusCardActive : {}),
              }}
              onClick={() => setSelected("linus")}
            >
              <code style={styles.linusFormula}>*?*Node</code>
              <span style={styles.linusText}>
                Non-null pointer to a nullable pointer &mdash; not <code>**Node</code>. The outer pointer
                (p) can never be null; the slot it points at (head, or a node's .next) legitimately can be.
              </span>
            </button>
          </Section>
        </main>

        {/* SIDEBAR */}
        <aside style={styles.sidebar}>
          <div style={styles.sidebarInner}>
            <span style={styles.sidebarEyebrow}>selected type</span>
            <code style={styles.sidebarFormula}>{example.formula}</code>
            <h3 style={styles.sidebarTitle}>{example.title}</h3>
            <p style={styles.sidebarBlurb}>{example.blurb}</p>

            <pre style={styles.codeBlock}>
              <code>{example.code}</code>
            </pre>

            <div style={styles.sidebarActions}>
              <button style={styles.copyBtn} onClick={copy}>
                {copied ? "copied \u2713" : "copy code"}
              </button>
              <a href={ZIG_PLAY_URL} target="_blank" rel="noreferrer" style={styles.playLink}>
                open zig-play.dev &rarr;
              </a>
            </div>
            <p style={styles.sidebarNote}>Paste the copied snippet into zig-play.dev's editor and run it.</p>
          </div>
        </aside>
      </div>
    </div>
  );
}

function Section({ index, title, hint, children }) {
  return (
    <section style={styles.section}>
      <div style={styles.sectionHead}>
        <span style={styles.sectionIndex}>{index}</span>
        <div>
          <h2 style={styles.sectionTitle}>{title}</h2>
          <p style={styles.sectionHint}>{hint}</p>
        </div>
      </div>
      {children}
    </section>
  );
}

function TypeChip({ typeKey, selected, onSelect, size }) {
  const isSel = selected === typeKey;
  return (
    <button
      onClick={() => onSelect(typeKey)}
      style={{
        ...styles.chip,
        ...(size === "lg" ? styles.chipLg : styles.chipMd),
        ...(isSel ? styles.chipActive : {}),
      }}
    >
      {typeKey}
    </button>
  );
}

function AxisLabel({ x, y, color, label, anchor = "start" }) {
  return (
    <text x={x} y={y} fill={color} fontSize="11" fontWeight="600" textAnchor={anchor} style={{ fontFamily: "'IBM Plex Mono', monospace" }}>
      {label}
    </text>
  );
}

function CubeVertex({ v, selected, onSelect }) {
  const key = v.invalid ? null : v.type;
  const isSel = key && selected === key;
  const color = v.invalid ? T.rule : v.c === 1 ? T.green : T.cyan;
  const labelDx = v.a === 0 && v.b === 0 ? -6 : 6;
  const anchor = v.a === 0 && v.b === 0 ? "end" : "start";

  return (
    <g
      onClick={() => key && onSelect(key)}
      style={{ cursor: key ? "pointer" : "default" }}
    >
      <circle
        cx={v.x}
        cy={v.y}
        r={isSel ? 8 : 6}
        fill={v.invalid ? T.bg : isSel ? color : T.panel}
        stroke={color}
        strokeWidth={isSel ? 2.5 : 1.5}
        strokeDasharray={v.invalid ? "2 2" : undefined}
      />
      <text
        x={v.x + labelDx}
        y={v.y - 10}
        fontSize={v.invalid ? 9 : 11}
        fontWeight={isSel ? 700 : 600}
        fill={v.invalid ? T.inkDim : isSel ? color : T.ink}
        textAnchor={anchor}
        style={{ fontFamily: "'IBM Plex Mono', monospace" }}
      >
        {v.invalid ? "n/a" : v.type}
      </text>
    </g>
  );
}

/* ============================================================================
   DESIGN TOKENS
   ========================================================================== */

const T = {
  bg: "#0b0d10",
  panel: "#14171c",
  panelAlt: "#181c22",
  rule: "#262c34",
  edge: "#3a4552",
  ink: "#d7dee6",
  inkDim: "#717d8a",
  amber: "#f2a93c", // zig's brand tone, used sparingly
  cyan: "#5ec4d6",
  violet: "#9d8cf0",
  green: "#7fd99a",
};

const css = `
  @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500;600;700&family=IBM+Plex+Sans:wght@500;600;700&display=swap');
  * { box-sizing: border-box; }
  button { font-family: inherit; cursor: pointer; }
  ::selection { background: ${T.amber}44; }
`;

const styles = {
  app: {
    minHeight: "100vh",
    background: T.bg,
    color: T.ink,
    fontFamily: "'IBM Plex Sans', sans-serif",
    padding: "28px 28px 60px",
  },
  header: { marginBottom: "24px" },
  h1: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "24px",
    fontWeight: 700,
    margin: 0,
    letterSpacing: "-0.01em",
  },
  h1Accent: { color: T.amber },
  sub: { color: T.inkDim, fontSize: "13px", marginTop: "6px", maxWidth: "560px", lineHeight: 1.5 },
  layout: { display: "grid", gridTemplateColumns: "1fr 320px", gap: "24px", alignItems: "start" },
  main: { display: "flex", flexDirection: "column", gap: "8px" },
  section: {
    borderTop: `1px solid ${T.rule}`,
    padding: "24px 0",
  },
  sectionHead: { display: "flex", gap: "14px", marginBottom: "16px" },
  sectionIndex: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "12px",
    color: T.amber,
    fontWeight: 700,
    paddingTop: "3px",
  },
  sectionTitle: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "16px",
    fontWeight: 700,
    margin: 0,
    textTransform: "lowercase",
  },
  sectionHint: { color: T.inkDim, fontSize: "12.5px", marginTop: "3px", maxWidth: "520px" },
  vectorRow: { display: "flex", gap: "12px" },
  chip: {
    fontFamily: "'IBM Plex Mono', monospace",
    background: T.panel,
    border: `1px solid ${T.rule}`,
    color: T.ink,
    borderRadius: "7px",
    fontWeight: 600,
  },
  chipLg: { padding: "16px 22px", fontSize: "17px" },
  chipMd: { padding: "10px 14px", fontSize: "13px", width: "100%" },
  chipActive: { borderColor: T.amber, color: T.amber, background: T.amber + "14" },
  table: { borderCollapse: "collapse", width: "100%", maxWidth: "520px" },
  thCorner: { border: `1px solid ${T.rule}`, background: T.panelAlt },
  th: {
    border: `1px solid ${T.rule}`,
    background: T.panelAlt,
    padding: "10px",
    fontSize: "11.5px",
    color: T.inkDim,
    fontWeight: 600,
    textTransform: "uppercase",
    letterSpacing: "0.04em",
  },
  thRow: {
    border: `1px solid ${T.rule}`,
    background: T.panelAlt,
    padding: "10px",
    fontSize: "11.5px",
    color: T.inkDim,
    fontWeight: 600,
    whiteSpace: "nowrap",
  },
  td: { border: `1px solid ${T.rule}`, padding: "10px" },
  cubeWrap: { display: "flex", justifyContent: "center" },
  cubeSvg: { width: "100%", maxWidth: "460px", height: "auto" },
  cubeFoot: { color: T.inkDim, fontSize: "11.5px", textAlign: "center", marginTop: "6px", maxWidth: "480px", marginLeft: "auto", marginRight: "auto" },
  linusCard: {
    display: "flex",
    flexDirection: "column",
    gap: "8px",
    alignItems: "flex-start",
    textAlign: "left",
    width: "100%",
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderLeft: `3px solid ${T.amber}`,
    borderRadius: "8px",
    padding: "16px 18px",
  },
  linusCardActive: { background: T.amber + "12", borderColor: T.amber },
  linusFormula: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "20px",
    fontWeight: 700,
    color: T.amber,
  },
  linusText: { color: T.ink, fontSize: "13px", lineHeight: 1.6 },
  sidebar: { position: "sticky", top: "24px" },
  sidebarInner: {
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderRadius: "10px",
    padding: "18px",
    display: "flex",
    flexDirection: "column",
    gap: "8px",
  },
  sidebarEyebrow: {
    fontSize: "10px",
    textTransform: "uppercase",
    letterSpacing: "0.1em",
    color: T.inkDim,
    fontWeight: 600,
  },
  sidebarFormula: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "26px",
    fontWeight: 700,
    color: T.amber,
  },
  sidebarTitle: { fontSize: "14px", margin: "2px 0 0", fontWeight: 700 },
  sidebarBlurb: { fontSize: "12.5px", color: T.inkDim, lineHeight: 1.55, margin: 0 },
  codeBlock: {
    background: T.bg,
    border: `1px solid ${T.rule}`,
    borderRadius: "7px",
    padding: "12px",
    fontSize: "11px",
    lineHeight: 1.6,
    overflowX: "auto",
    color: T.ink,
    fontFamily: "'IBM Plex Mono', monospace",
    margin: "6px 0",
    maxHeight: "440px",
  },
  sidebarActions: { display: "flex", gap: "8px", alignItems: "center" },
  copyBtn: {
    background: T.panelAlt,
    border: `1px solid ${T.rule}`,
    color: T.ink,
    borderRadius: "6px",
    padding: "8px 12px",
    fontSize: "11.5px",
    fontWeight: 600,
    fontFamily: "'IBM Plex Mono', monospace",
  },
  playLink: {
    color: T.cyan,
    fontSize: "11.5px",
    fontWeight: 600,
    fontFamily: "'IBM Plex Mono', monospace",
    textDecoration: "none",
  },
  sidebarNote: { fontSize: "10.5px", color: T.inkDim, marginTop: "2px" },
};
