import { readFileSync } from "node:fs";
import { join } from "node:path";
import { NextResponse } from "next/server";
import { loadGraphData } from "@/lib/loadGraph";

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url);
  const file = searchParams.get("file");
  if (!file) {
    return NextResponse.json(
      { error: "Missing ?file= parameter" },
      { status: 400 },
    );
  }

  const graph = loadGraphData();
  const known = graph.groups.find((g) => g.fname === file);
  if (!known) {
    return NextResponse.json(
      { error: `Unknown group file: ${file}` },
      { status: 404 },
    );
  }

  const fullPath = join(process.cwd(), "p3_groups", known.fname);
  const content = readFileSync(fullPath, "utf8");
  return NextResponse.json({ fname: known.fname, content });
}
