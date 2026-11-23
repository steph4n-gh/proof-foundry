const transportLabels = {
  boot: "Booting catalog",
  live_connecting: "Connecting stream",
  live_connected: "Live stream healthy",
  live_reconnecting: "Stream reconnecting",
  static_loading: "Loading static snapshot",
  static_ready: "Static snapshot ready",
  error: "Offline error",
};

const overlayLabels = {
  none: "no overlay",
  dossier: "dossier drawer",
  attempt: "attempt modal",
  search: "search palette",
};

export const title = "Frontend transport, route, and single-overlay state machine";

export function state(v) {
  const t = transportLabels[v.transportStatus] || v.transportStatus;
  const m = v.activeMission === "none" ? "uncommitted" : `mission ${v.activeMission}`;
  const o = overlayLabels[v.overlayKind] || v.overlayKind;
  return `${t} · ${m} · ${o}`;
}

export function step(action, from, to) {
  switch (action) {
    case "CatalogLoaded":
      return to.mode === "static" ? "catalog loads (static)" : "catalog loads (live)";
    case "CatalogFailed":
      return "catalog fetch fails";
    case "MissionRequested":
      return from.activeMission === "none" ? "request initial mission" : "request mission switch";
    case "MissionLoaded":
      if (to.monitor.kind === "stale_mission") return "stale mission snapshot arrives";
      return "mission snapshot commits";
    case "MissionFailed":
      if (to.monitor.kind === "stale_mission") return "stale mission error arrives";
      return from.activeMission === "none" ? "initial mission fails" : "mission switch fails";
    case "SseOpen":
      return to.transportStatus !== from.transportStatus ? "SSE stream opens" : "stale SSE open ignored";
    case "SseError":
      return to.transportStatus !== from.transportStatus ? "SSE stream drops" : "stale SSE error ignored";
    case "Retry":
      return "retry boot";
    case "OpenDossier":
      return to.routeClaim !== "none" ? "open routed dossier" : "open cross-mission dossier";
    case "DossierLoaded":
      return to.monitor.kind === "stale_dossier" ? "stale dossier receipt arrives" : "dossier receipt loads";
    case "DossierFailed":
      return to.monitor.kind === "stale_dossier" ? "stale dossier error arrives" : "dossier load fails";
    case "OpenAttempt":
      return "open attempt modal";
    case "OpenSearch":
      return "open search palette";
    case "CloseOverlay":
      return "close overlay";
    case "RouteNavigate":
      return "navigate view";
    case "RouteSync":
      return from.overlayKind === "dossier" ? "history sync closes dossier" : "history sync";
    case "Done":
      return "request budgets settled";
  }
}
