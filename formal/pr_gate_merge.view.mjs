const phases = {
  classify: "Awaiting classification",
  judge: "Donor diff classified",
  decide: "Judge passed",
  eligible: "Eligible on sampled main",
  enabled: "Auto-merge requested",
  merged: "Merged",
  stopped: "Stopped",
};

export const title = "A donor submission from classification to merge";
export const state = (v) => phases[v.phase];
export function step(action, from, to) {
  switch (action) {
    case "ClassifyDonor": return "classify donor diff";
    case "JudgeOK": return "judge accepts submission";
    case "FailCheck": return "check fails";
    case "Decide":
      if (to.phase === "eligible") return "accept current bounty or score";
      return from.head === "H0" ? "competing claim already on main" : "head differs from run";
    case "EnableAutoMerge":
      return to.phase === "enabled" ? "match expected head" : "head differs from decision";
    case "Merge":
      if (to.phase === "merged") return "merge PR";
      return from.head === "H0" ? "base advanced" : "head changed";
    case "MoveHead": return "PR head changes";
    case "AdvanceMain": return "another PR lands";
    case "Done": return "run finished";
  }
}
