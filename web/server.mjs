#!/usr/bin/env node
/**
 * web/server.mjs — Multi-Mission Open-Science Live Dashboard Server (Zero Dependencies).
 * Serves static UI + multi-mission JSON API + real-time SSE (/api/stream?mission=<slug>).
 */
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import {
  ROOT,
  MISSIONS_DIR,
  DEFAULT_MISSION,
  listMissionSlugs,
  loadMission,
  loadAllMissionsSummary,
  readAllowedArtifactFile,
} from "../hub/missions.mjs";
import { buildMissionSnapshot, fetchOpenPRs, renderMasterProofsMarkdown } from "../hub/build_site.mjs";

const PUBLIC_DIR = path.join(ROOT, "web", "public");
const PORT = Number(process.env.PORT || 4321);
let cachedPrSnap = { ok: false, fetched_at: null, by_claim: {} };
let lastPrFetchMs = 0;
function getCachedPrSnap(repo) {
  const now = Date.now();
  if (now - lastPrFetchMs > 60000) {
    lastPrFetchMs = now;
    cachedPrSnap = fetchOpenPRs(repo);
  }
  return cachedPrSnap;
}

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "application/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
  ".png": "image/png",
};

const CSP_HEADER =
  "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src 'self' https://fonts.gstatic.com; img-src 'self' data:; connect-src 'self'";

function isAllowedHost(hostHeader) {
  if (!hostHeader) return true;
  const host = String(hostHeader).toLowerCase().split(":")[0];
  return host === "127.0.0.1" || host === "localhost" || host === "[::1]";
}

function safeSlug(raw) {
  const slugs = listMissionSlugs();
  if (raw && slugs.includes(raw)) return raw;
  return slugs.includes(DEFAULT_MISSION) ? DEFAULT_MISSION : slugs[0] || DEFAULT_MISSION;
}

function snapshotFor(slug) {
  try {
    const mission = loadMission(safeSlug(slug));
    return buildMissionSnapshot(mission, getCachedPrSnap(mission.github_repo));
  } catch {
    return { ready: false };
  }
}

// Per-mission SSE client registry: Map<res, { slug, lastHash }>
const clients = new Map();

function broadcastMission(slug, force = false) {
  const targets = [];
  for (const [res, info] of clients.entries()) {
    if (info.slug === slug) targets.push([res, info]);
  }
  if (!targets.length) return;
  const payload = JSON.stringify(snapshotFor(slug));
  const msg = `event: snapshot\ndata: ${payload}\n\n`;
  for (const [res, info] of targets) {
    if (!force && info.lastHash === payload) continue;
    info.lastHash = payload;
    try {
      res.write(msg);
    } catch {
      clients.delete(res);
    }
  }
}

// Watch each mission directory for live updates
const watchers = new Map();
function ensureMissionWatcher(slug) {
  if (watchers.has(slug)) return;
  const dir = path.join(MISSIONS_DIR, slug);
  if (!fs.existsSync(dir)) return;
  let timer = null;
  try {
    const w = fs.watch(dir, (_ev, filename) => {
      if (!filename || filename.startsWith(".state.lock") || filename.includes(".tmp.")) return;
      clearTimeout(timer);
      timer = setTimeout(() => broadcastMission(slug, false), 140);
    });
    watchers.set(slug, w);
  } catch {}
}

setInterval(() => {
  if (clients.size === 0) return;
  const activeSlugs = new Set([...clients.values()].map((i) => i.slug));
  for (const slug of activeSlugs) broadcastMission(slug, false);
  for (const res of clients.keys()) {
    try {
      res.write(`: heartbeat ${Date.now()}\n\n`);
    } catch {
      clients.delete(res);
    }
  }
}, 2500);

const server = http.createServer((req, res) => {
  if (!isAllowedHost(req.headers.host)) {
    res.writeHead(403, { "Content-Type": "text/plain" });
    res.end("Forbidden host");
    return;
  }

  let url;
  let pathname;
  try {
    url = new URL(req.url || "/", `http://127.0.0.1:${PORT}`);
    pathname = decodeURIComponent(url.pathname);
  } catch {
    res.writeHead(400, { "Content-Type": "text/plain" });
    res.end("Malformed URL");
    return;
  }

  const slug = safeSlug(url.searchParams.get("mission"));

  if (pathname === "/PROOFS.md") {
    const snaps = listMissionSlugs().map((s) => snapshotFor(s)).filter((s) => s.ready);
    res.writeHead(200, { "Content-Type": "text/markdown; charset=utf-8", "X-Content-Type-Options": "nosniff" });
    res.end(renderMasterProofsMarkdown(snaps));
    return;
  }

  if (pathname === "/api/missions") {
    res.writeHead(200, {
      "Content-Type": "application/json; charset=utf-8",
      "X-Content-Type-Options": "nosniff",
    });
    res.end(JSON.stringify({ missions: loadAllMissionsSummary(), default: DEFAULT_MISSION, static: false }));
    return;
  }

  if (pathname === "/api/stream") {
    ensureMissionWatcher(slug);
    res.writeHead(200, {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache, no-transform",
      Connection: "keep-alive",
      "X-Content-Type-Options": "nosniff",
    });
    const payload = JSON.stringify(snapshotFor(slug));
    clients.set(res, { slug, lastHash: payload });
    res.write(`event: snapshot\ndata: ${payload}\n\n`);
    req.on("close", () => clients.delete(res));
    return;
  }

  if (pathname === "/api/state") {
    res.writeHead(200, {
      "Content-Type": "application/json; charset=utf-8",
      "X-Content-Type-Options": "nosniff",
    });
    res.end(JSON.stringify(snapshotFor(slug)));
    return;
  }

  if (pathname.startsWith("/api/lemma/")) {
    const id = pathname.slice("/api/lemma/".length);
    const mission = loadMission(slug);
    const snap = snapshotFor(slug);
    const lemma = snap?.lemmas?.find((l) => l.id === id);
    if (!lemma) {
      res.writeHead(404, { "Content-Type": "application/json" });
      res.end(JSON.stringify({ error: "Claim not found" }));
      return;
    }
    const leanSource = readAllowedArtifactFile(mission, lemma.lean_file);
    const refutationSource = readAllowedArtifactFile(mission, lemma.refutation?.counterexample_file);
    const statementSource = lemma.statement_file ? readAllowedArtifactFile(mission, lemma.statement_file) : null;
    const relatedMessages = (snap.messages || []).filter((m) => m.lemma_id === id);
    const relatedRuns = (snap.checker_runs || []).filter((r) => r.lemma_id === id);
    const dependents = (snap.lemmas || [])
      .filter((other) => (other.deps || []).includes(id))
      .map((other) => ({ id: other.id, title: other.title, status: other.status, seal: other.seal }));

    res.writeHead(200, {
      "Content-Type": "application/json; charset=utf-8",
      "X-Content-Type-Options": "nosniff",
    });
    res.end(
      JSON.stringify({
        lemma,
        leanSource,
        refutationSource,
        statementSource,
        relatedMessages,
        relatedRuns,
        dependents,
      })
    );
    return;
  }

  // Static files
  let filePath = path.resolve(PUBLIC_DIR, pathname === "/" ? "index.html" : pathname.replace(/^\/+/, ""));
  if (!filePath.startsWith(PUBLIC_DIR + path.sep) && filePath !== PUBLIC_DIR) {
    res.writeHead(403, { "Content-Type": "text/plain" });
    res.end("Forbidden");
    return;
  }
  try {
    if (!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) {
      filePath = path.join(PUBLIC_DIR, "index.html");
    }
  } catch {
    res.writeHead(404, { "Content-Type": "text/plain" });
    res.end("Not found");
    return;
  }

  const ext = path.extname(filePath);
  const headers = {
    "Content-Type": MIME[ext] || "application/octet-stream",
    "X-Content-Type-Options": "nosniff",
  };
  if (ext === ".html") headers["Content-Security-Policy"] = CSP_HEADER;

  const stream = fs.createReadStream(filePath);
  stream.on("error", () => {
    if (!res.headersSent) res.writeHead(500, { "Content-Type": "text/plain" });
    res.end("Read error");
  });
  res.writeHead(200, headers);
  stream.pipe(res);
});

server.listen(PORT, "127.0.0.1", () => {
  console.log(`Open Science Fleet Dashboard listening at http://127.0.0.1:${PORT} (missions: ${listMissionSlugs().join(", ")})`);
});
