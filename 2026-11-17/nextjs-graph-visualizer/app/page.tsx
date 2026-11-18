import { GraphVisualizer } from "@/components/GraphVisualizer";
import { loadGraphData } from "@/lib/loadGraph";

export default function HomePage() {
  const data = loadGraphData();
  return <GraphVisualizer data={data} />;
}
