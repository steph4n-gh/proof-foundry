const labels = {
  open: "Awaiting submission", infra: "Infrastructure lane", judge: "Donor classified",
  decide: "Artifact verified", eligible: "Eligible on sampled main", enabled: "Auto-merge requested",
  review: "Needs maintainer", stopped: "Stopped", merged: "Landed", adopted: "Maintainer lands edit",
};

export const title = "Two donor PRs compete on one frozen minimization hunt";
export const state = v => ({ PR1: labels[v.runs[1].phase], PR2: labels[v.runs[2].phase] });
export function step(action, from, to) {
  const pr = from.runs[1].phase !== to.runs[1].phase ? 1 : 2;
  const phase = to.runs[pr].phase;
  switch (action) {
    case "Classify": {
      const payload = to.runs[pr].payload;
      if (phase !== "judge") return phase === "infra" ? "route outside donor lane" : "reject diff";
      return `classify ${payload[1]} ${payload[2]}`;
    }
    case "InfraGate": return phase === "adopted" ? "land adopted statement edit" : "outside donor lane";
    case "Judge": return phase === "decide" ? "verify pinned artifact" : "judge withholds approval";
    case "Decide": return phase === "eligible" ? "score improves current main" : "withhold auto-merge";
    case "EnableAutoMerge": return phase === "enabled" ? "pin verified head" : "head changed";
    case "Merge": return phase === "merged" ? "land on current base" : "head or base changed";
    case "MoveHead": return "head changes";
    case "Done": return "both runs finished";
  }
}
