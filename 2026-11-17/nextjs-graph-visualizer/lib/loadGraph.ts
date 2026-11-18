import rawGraphJson from "@/data/graph.json";
import { type GraphData, validateGraphData } from "./schema";

export function loadGraphData(): GraphData {
  return validateGraphData(rawGraphJson);
}
