const labels = {
  dead: "Barrier recorded",
  checked: "Proof accepted",
  refuted: "Refutation accepted",
  contradiction: "Contradiction",
};

export const title = "Ownership and verdicts for one claim";
export function state(v) {
  if (v.status !== "open") return labels[v.status];
  const holder = v.owner.target;
  return holder === "none" ? "Unclaimed" : `Held by seat ${holder}`;
}

export function step(action, from, to) {
  switch (action) {
    case "Assign":
      if (to.owner.target === "none") return "owner takes other claim";
      return from.owner.target === "none" ? "seat claims work" : "transfer claim";
    case "JudgeProof": return "proof arrives";
    case "JudgeRefutation": return "refutation arrives";
    case "Barrier": return "record barrier";
    case "Done": return "verdict settled";
  }
}
