require("dotenv").config();

const express = require("express");
const cors = require("cors");
const helmet = require("helmet");
const compression = require("compression");
const rateLimit = require("express-rate-limit");
const pino = require("pino");
const pinoHttp = require("pino-http");
const { Readable } = require("node:stream");
const { pipeline } = require("node:stream/promises");
const { spawn, execFile } = require("node:child_process");
const { randomUUID } = require("node:crypto");

const BROWSER_UA =
  "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36";

// YouTube InnerTube "WEB" client with its well-known public API key.
const YT_INNERTUBE_KEY = "AIzaSyAO_FJ2SlqU8Q4STEHLGCilw_Y9_11qcW8";

// Short-lived in-memory resolution cache (reduces load on third-party free
// APIs and makes repeated downloads feel instant).
const cache = new Map();

// yt-dlp + helper binaries (optional, only needed for YouTube).
const YTDLP_PATH = process.env.YTDLP_PATH || "yt-dlp";
const DENO_PATH = process.env.DENO_PATH;          // e.g. path to deno.exe (YouTube JS runtime)
const FFMPEG_LOCATION = process.env.FFMPEG_LOCATION; // dir/full path to ffmpeg for merging DASH streams

function ytdlpBaseArgs() {
  const args = ["--no-playlist", "--no-warnings", "--no-cache-dir"];
  if (DENO_PATH) args.push("--js-runtimes", `deno:${DENO_PATH}`);
  if (FFMPEG_LOCATION) args.push("--ffmpeg-location", FFMPEG_LOCATION);
  return args;
}

/**
 * Full argument list for streaming a YouTube video through yt-dlp `-o -`.
 * yt-dlp + ffmpeg merge the best video + audio into a single MP4 piped to stdout.
 */
function buildYtDlpStreamArgs(selector, url) {
  return [
    ...ytdlpBaseArgs(),
    "-f", selector,
    "--merge-output-format", "mp4",
    "--progress", "none",
    "--no-part",
    "-o", "-",
    url
  ];
}

function cacheGet(key) {
  const hit = cache.get(key);
  if (hit && hit.exp > Date.now()) return hit.value;
  cache.delete(key);
  return undefined;
}

function cacheSet(key, value, ttlMs = 10 * 60 * 1000) {
  cache.set(key, { value, exp: Date.now() + ttlMs });
}

// Decode JSON/HTML entities that appear inside script-embedded URLs.
function decodeEntities(str = "") {
  return str
    .replace(/\\u002F/gi, "/")
    .replace(/\\u0026/gi, "&")
    .replace(/\\u003D/gi, "=")
    .replace(/\\u003F/gi, "?")
    .replace(/\\u0025/gi, "%")
    .replace(/\\u0022/gi, '"')
    .replace(/&amp;/g, "&")
    .replace(/&quot;/g, '"')
    .replace(/&#x27;/g, "'");
}

/**
 * Detect which video platform a page URL belongs to.
 * Returns a platform key or null when it is a direct media URL (passthrough).
 */
function detectPlatform(url) {
  try {
    const u = new URL(url);
    const host = u.hostname.toLowerCase();
    if (host.endsWith("tiktok.com")) return "tiktok";
    if (host.endsWith("youtube.com") || host.endsWith("youtu.be") || host.endsWith("youtube-nocookie.com")) return "youtube";
    if (host.endsWith("instagram.com")) return "instagram";
    if (host === "x.com" || host === "www.x.com" || host.endsWith("twitter.com")) return "x";
  } catch {
    return null;
  }
  return null;
}

/* ------------------------------------------------------------------ */
/* YouTube                                                              */
/* ------------------------------------------------------------------ */

function extractYouTubeId(url) {
  try {
    const u = new URL(url);
    if (u.hostname === "youtu.be") return u.pathname.split("/").filter(Boolean)[0] || null;
    const v = u.searchParams.get("v");
    if (v) return v;
    const m = u.pathname.match(/\/(?:shorts|embed|live|v|watch)\/([A-Za-z0-9_-]{11})/);
    if (m) return m[1];
    const m2 = u.pathname.match(/^\/watch\/([A-Za-z0-9_-]{11})/);
    if (m2) return m2[1];
  } catch {
    return null;
  }
  return null;
}

/**
 * Strategy 1 — yt-dlp (best reliability, recommended for production).
 * Modern YouTube only serves DASH (video-only + audio-only) streams, so the
 * actual MP4 with audio is produced during /api/stream by piping
 * `yt-dlp -f "bv*+ba" --merge-output-format mp4 -o -` through ffmpeg.
 * At resolve time we just verify the video is extractable and grab its title.
 */
function fetchYtDlpTitle(pageUrl) {
  return new Promise((resolve, reject) => {
    const args = [
      ...ytdlpBaseArgs(),
      "--skip-download",
      "--print", "TITLE:%(title)s",
      pageUrl
    ];
    execFile(
      YTDLP_PATH,
      args,
      { timeout: 25_000, maxBuffer: 1024 * 1024, windowsHide: true },
      (error, stdout) => {
        if (error) {
          const hint = /ENOENT/i.test(error.message)
            ? "yt-dlp is not installed. Install yt-dlp on the server or set YTDLP_PATH."
            : `yt-dlp could not resolve this video (${error.message.slice(0, 120)}).`;
          reject(new Error(hint));
          return;
        }
        const titleLine = String(stdout).split("\n").map((l) => l.trim()).find((l) => l.startsWith("TITLE:"));
        resolve(titleLine ? titleLine.slice(6) : "youtube_video");
      }
    );
  });
}

/**
 * Strategy 2 — YouTube InnerTube player API (no server dependency).
 * Kept as a fallback; YouTube now frequently blocks anonymous WEB clients.
 */
async function resolveYouTubeInnerTube(pageUrl) {
  const videoId = extractYouTubeId(pageUrl);
  if (!videoId) throw new Error("Could not find a YouTube video ID in that link.");

  const res = await fetch(
    `https://www.youtube.com/youtubei/v1/player?key=${YT_INNERTUBE_KEY}&videoId=${videoId}`,
    {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "User-Agent": BROWSER_UA,
        "Referer": "https://www.youtube.com/",
        "X-YouTube-Client-Name": "1",
        "X-YouTube-Client-Version": "2.20250415.01.02"
      },
      body: JSON.stringify({
        context: {
          client: {
            clientName: "WEB",
            clientVersion: "2.20250415.01.02",
            hl: "en",
            gl: "US"
          }
        },
        videoId
      }),
      signal: AbortSignal.timeout(15_000)
    }
  );

  if (!res.ok) throw new Error(`YouTube API returned HTTP ${res.status}.`);

  const json = await res.json();
  const status = json.playabilityStatus && json.playabilityStatus.status;
  if (status && status !== "OK") {
    const reason = json.playabilityStatus.reason || "";
    throw new Error(
      `YouTube could not play this video${reason ? ` (${reason})` : ""}. It may be private, age-restricted, removed, or region-blocked.`
    );
  }

  const data = json.streamingData;
  if (!data) throw new Error("No downloadable streams found for this YouTube video.");

  // Progressive (muxed audio+video) MP4 formats are streamable as a single URL.
  const formats = ((data.formats || [])).filter(
    (f) => f.url && f.mimeType && f.mimeType.includes("video/mp4") && !f.mimeType.includes("webm")
  );
  if (!formats.length) throw new Error("No single-file MP4 stream was returned for this YouTube video.");

  formats.sort((a, b) => (b.height || 0) - (a.height || 0));
  const best = formats[0];
  const fallback = formats[formats.length - 1];
  const title = (json.videoDetails && json.videoDetails.title) || "youtube_video";

  return {
    platform: "youtube",
    title,
    sdUrl: fallback.url,
    hdUrl: best.url,
    height: best.height || 0
  };
}

async function resolveYouTube(pageUrl, { hd = false } = {}) {
  // Preferred: yt-dlp (accurate + reliable). Returns streaming metadata that
  // /api/stream uses to pipe a merged MP4 out of yt-dlp.
  try {
    const title = await fetchYtDlpTitle(pageUrl);
    const selector = hd
      ? "bv*+ba/b"
      : "bv*[height<=360]+ba/b[height<=360]/b";
    return {
      platform: "youtube",
      title,
      kind: "yt-dlp",
      selector,
      height: hd ? 1080 : 360,
      sdUrl: "",
      hdUrl: ""
    };
  } catch (ytError) {
    // Fallback: dependency-free InnerTube attempt (rarely works in 2026).
    try {
      return await resolveYouTubeInnerTube(pageUrl);
    } catch (innerTubeError) {
      throw new Error(`${ytError.message} ${innerTubeError.message}`.trim());
    }
  }
}

/* ------------------------------------------------------------------ */
/* Instagram (Reels / Posts / TV)                                      */
/* ------------------------------------------------------------------ */

function extractInstagramShortCode(url) {
  try {
    const u = new URL(url);
    const parts = u.pathname.split("/").filter(Boolean);
    const idx = parts.findIndex((p) => ["p", "reel", "reels", "tv", "stories"].includes(p));
    if (idx !== -1 && parts[idx + 1]) return parts[idx + 1];
    if (parts.length && /^[a-zA-Z0-9_-]{5,}$/.test(parts[parts.length - 1])) {
      return parts[parts.length - 1];
    }
  } catch {
    return null;
  }
  return null;
}

async function fetchInstagramHtml(shortCode) {
  const res = await fetch(`https://www.instagram.com/p/${shortCode}/`, {
    headers: {
      "User-Agent": BROWSER_UA,
      Accept: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
      "Accept-Language": "en-US,en;q=0.9"
    },
    redirect: "follow",
    signal: AbortSignal.timeout(15_000)
  });
  if (!res.ok) throw new Error(`Instagram returned HTTP ${res.status}.`);
  return res.text();
}

function ytDlpHasVideo(pageUrl) {
  return new Promise((resolve) => {
    const args = [...ytdlpBaseArgs(), "--skip-download", "-F", pageUrl];
    execFile(
      YTDLP_PATH,
      args,
      { timeout: 30_000, maxBuffer: 4 * 1024 * 1024, windowsHide: true },
      (error, stdout) => {
        if (error) return resolve(false);
        const hasVideo = /\s(mp4|webm|m4v)\s+\d{2,4}x\d{2,4}/.test(stdout);
        resolve(hasVideo);
      }
    );
  });
}

async function resolveInstagram(pageUrl, { hd = false } = {}) {
  const shortCode = extractInstagramShortCode(pageUrl);
  if (!shortCode) throw new Error("Could not find an Instagram post or Reel in that link.");

  // Preferred: yt-dlp. Instagram's web pages are login-gated in 2026, but
  // yt-dlp can still fetch public Reels/Posts and DASH-merge them like YouTube.
  try {
    const hasVideo = await ytDlpHasVideo(pageUrl);
    if (hasVideo) {
      const title = await fetchYtDlpTitle(pageUrl);
      const selector = hd
        ? "bv*+ba/b"
        : "bv*[height<=360]+ba/b[height<=360]/b";
      return {
        platform: "instagram",
        title,
        kind: "yt-dlp",
        selector,
        height: hd ? 1080 : 360,
        sdUrl: "",
        hdUrl: ""
      };
    }
  } catch {
    // fall through to the HTML scrape below
  }

  const html = await fetchInstagramHtml(shortCode);

  const titleMatch = html.match(
    /<meta[^>]+property=["']og:title["'][^>]*content=["']([^"']*)["']/i
  );

  let formats = [];

  // Strategy 1: embedded "video_versions" JSON array (multiple qualities).
  const vvMatch = html.match(/"video_versions"\s*:\s*(\[[\s\S]*?\])\s*[,}]/);
  if (vvMatch) {
    try {
      const arr = JSON.parse(vvMatch[1]);
      const versions = arr
        .map((v) => ({ height: Number(v.height) || 0, url: v.url || "" }))
        .filter((v) => v.url)
        .sort((a, b) => a.height - b.height);
      if (versions.length) {
        formats = versions.map((v, i) => ({
          id: `ig${i}`,
          quality: v.height ? `${v.height}p` : "sd",
          height: v.height,
          url: v.url
        }));
      }
    } catch {
      // fall through to next strategy
    }
  }

  // Strategy 2: OpenGraph video meta tags.
  if (!formats.length) {
    const ogSecure = html.match(/<meta[^>]+property=["']og:video:secure_url["'][^>]*content=["']([^"']+)["']/i);
    const og = html.match(/<meta[^>]+property=["']og:video["'][^>]*content=["']([^"']+)["']/i);
    const url = ogSecure ? ogSecure[1] : og ? og[1] : null;
    if (url) {
      formats.push({ id: "ig0", quality: "hd", height: 0, url: url });
    }
  }

  // Strategy 3: single embedded "video_url".
  if (!formats.length) {
    const single = html.match(/"video_url"\s*:\s*"([^"]+)"/);
    if (single) {
      formats.push({ id: "ig0", quality: "hd", height: 0, url: decodeEntities(single[1]) });
    }
  }

  if (!formats.length) {
    throw new Error(
      "Could not find a downloadable video on that Instagram post. The account may be private, or the post is an image instead of a video."
    );
  }

  formats.sort((a, b) => a.height - b.height);
  const best = formats[formats.length - 1];
  const fallback = formats[0];

  return {
    platform: "instagram",
    title: (titleMatch ? titleMatch[1].trim() : "") || "instagram_video",
    sdUrl: fallback.url,
    hdUrl: best.url,
    height: best.height || 0
  };
}

/* ------------------------------------------------------------------ */
/* X / Twitter                                                          */
/* ------------------------------------------------------------------ */

function extractTweetId(url) {
  const m = String(url).match(/\/(?:status|statuses)\/(\d+)/);
  return m ? m[1] : null;
}

async function resolveX(pageUrl) {
  const tweetId = extractTweetId(pageUrl);
  if (!tweetId) throw new Error("Could not find a tweet/post ID in that X or Twitter link.");

  const variants = [];

  // Strategy 1: public Twitter syndication endpoint.
  try {
    const res = await fetch(
      `https://cdn.syndication.twimg.com/tweet-result?id=${tweetId}&lang=en&token=${tweetId}`,
      {
        headers: { "User-Agent": BROWSER_UA },
        signal: AbortSignal.timeout(12_000)
      }
    );
    if (res.ok) {
      const json = await res.json();
      const details = Array.isArray(json.mediaDetails) ? json.mediaDetails : [];
      for (const md of details) {
        if (md.type !== "video" || !md.video_info || !Array.isArray(md.video_info.variants)) continue;
        for (const v of md.video_info.variants) {
          if (v.content_type === "video/mp4" && v.url) {
            variants.push({ bitrate: Number(v.bitrate) || 0, url: v.url });
          }
        }
      }
    }
  } catch {
    // fall back to page scrape
  }

  // Strategy 2: scrape the status page for video.twimg.com mp4 URLs.
  if (!variants.length) {
    try {
      const res = await fetch(`https://x.com/i/status/${tweetId}`, {
        headers: {
          "User-Agent": BROWSER_UA,
          Accept: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
          "Accept-Language": "en-US,en;q=0.9"
        },
        signal: AbortSignal.timeout(12_000)
      });
      if (res.ok) {
        const html = await res.text();
        const re = /"url"\s*:\s*"(https:\\\/\\\/video\.twimg\.com[^"]+?\.mp4[^"]*?)"/g;
        let m;
        while ((m = re.exec(html)) !== null) {
          variants.push({ bitrate: 0, url: decodeEntities(m[1]) });
        }
      }
    } catch {
      // give up on scrape too
    }
  }

  if (!variants.length) {
    throw new Error(
      "Could not resolve a video from that X/Twitter post. It may not contain a video, or the account may be protected/private."
    );
  }

  const unique = [...new Map(variants.map((v) => [v.url, v])).values()];
  unique.sort((a, b) => b.bitrate - a.bitrate);
  const best = unique[0];
  const fallback = unique[unique.length - 1];

  return {
    platform: "x",
    title: "twitter_x_video",
    sdUrl: fallback.url,
    hdUrl: best.url,
    height: 0
  };
}

/* ------------------------------------------------------------------ */
/* TikTok (kept from original server, adapted)                          */
/* ------------------------------------------------------------------ */

async function resolveTikTok(pageUrl) {
  const body = new URLSearchParams({ url: pageUrl, hd: "1" });
  const res = await fetch("https://www.tikwm.com/api/", {
    method: "POST",
    headers: {
      "Content-Type": "application/x-www-form-urlencoded",
      "User-Agent": BROWSER_UA,
      "Referer": "https://www.tikwm.com/"
    },
    body,
    signal: AbortSignal.timeout(15_000)
  });
  if (!res.ok) throw new Error(`TikTok resolver returned HTTP ${res.status}.`);

  const json = await res.json();
  if (!json.data || json.code !== 0) {
    throw new Error(json.msg || "Could not resolve the TikTok video. The link may be private or invalid.");
  }

  const data = json.data;
  const formats = [];
  if (data.hdplay) formats.push({ height: 1080, url: data.hdplay });
  if (data.play && (formats.length === 0 || data.play !== formats[formats.length - 1].url)) {
    formats.push({ height: 540, url: data.play });
  }
  if (data.wmplay && formats.length === 0) {
    formats.push({ height: 540, url: data.wmplay });
  }
  if (!formats.length) throw new Error("TikTok video URL not found in resolver response.");

  formats.sort((a, b) => a.height - b.height);
  const best = formats[formats.length - 1];

  return {
    platform: "tiktok",
    title: data.title || "tiktok_video",
    sdUrl: formats[0].url,
    hdUrl: best.url,
    height: best.height || 0
  };
}

/* ------------------------------------------------------------------ */
/* Dispatcher                                                           */
/* ------------------------------------------------------------------ */

/**
 * Resolve a platform page URL to direct playable CDN URLs.
 * Returns { platform, title, sdUrl, hdUrl, height } or null when the URL is
 * not a recognized platform page (caller may passthrough raw media URLs).
 */
async function resolveVideo(pageUrl, options = {}) {
  const platform = detectPlatform(pageUrl);
  if (!platform) return null;

  const key = `${platform}::${pageUrl}::${options.hd ? "HD" : "SD"}`;
  const cached = cacheGet(key);
  if (cached) return cached;

  let result;
  switch (platform) {
    case "youtube":
      result = await resolveYouTube(pageUrl, options);
      break;
    case "instagram":
      result = await resolveInstagram(pageUrl, options);
      break;
    case "x":
      result = await resolveX(pageUrl);
      break;
    case "tiktok":
      result = await resolveTikTok(pageUrl);
      break;
    default:
      return null;
  }

  cacheSet(key, result);
  return result;
}

const app = express();
const logger = pino({ level: process.env.LOG_LEVEL || "info" });

const PORT = Number(process.env.PORT || 8080);
const MAX_DOWNLOAD_MB = Number(process.env.MAX_DOWNLOAD_MB || 250);
const MAX_DOWNLOAD_BYTES = MAX_DOWNLOAD_MB * 1024 * 1024;

// Short-lived in-memory store for resolved download tokens (one-time use, 2 min TTL)
const downloadTokens = new Map();

// Daily HD Download Tracker: IP -> { count: number, date: string }
const dailyHdUsage = new Map();

function getTodayString() {
  return new Date().toISOString().slice(0, 10); // "YYYY-MM-DD"
}

function checkAndIncrementHdUsage(ip) {
  const today = getTodayString();
  const usage = dailyHdUsage.get(ip);

  if (!usage || usage.date !== today) {
    dailyHdUsage.set(ip, { count: 1, date: today });
    return { allowed: true, remaining: 1, resetDate: today };
  }

  if (usage.count >= 2) {
    return { allowed: false, remaining: 0, resetDate: today };
  }

  usage.count += 1;
  return { allowed: true, remaining: 2 - usage.count, resetDate: today };
}

function getHdUsageStatus(ip) {
  const today = getTodayString();
  const usage = dailyHdUsage.get(ip);
  if (!usage || usage.date !== today) {
    return { count: 0, remaining: 2, limit: 2 };
  }
  return { count: usage.count, remaining: Math.max(0, 2 - usage.count), limit: 2 };
}

app.disable("x-powered-by");
app.set("trust proxy", 1);

app.use(helmet({
  crossOriginResourcePolicy: { policy: "cross-origin" }
}));
// Skip compression for binary download streams — gzip would corrupt Content-Length
app.use(compression({
  filter: (req, res) => {
    if (req.path.startsWith("/api/stream")) return false;
    return compression.filter(req, res);
  }
}));
app.use(express.json({ limit: "32kb" }));
app.use(pinoHttp({ logger }));

const allowedOrigin = process.env.FRONTEND_ORIGIN || "http://localhost:3000";

app.use(cors({
  origin: allowedOrigin,
  methods: ["GET", "POST", "OPTIONS"],
  allowedHeaders: ["Content-Type", "Range"]
}));

const limiter = rateLimit({
  windowMs: 60 * 1000,
  limit: 60,
  standardHeaders: "draft-7",
  legacyHeaders: false,
  message: { error: "Too many requests. Please try again shortly." }
});

app.use("/api", limiter);

app.get("/health", (req, res) => {
  res.json({ ok: true, service: "free-video-downloader-api" });
});

app.get("/api/health", (req, res) => {
  res.json({ ok: true, uptime: process.uptime() });
});

function isHttpUrl(value) {
  try {
    const u = new URL(value);
    return u.protocol === "https:" || u.protocol === "http:";
  } catch {
    return false;
  }
}

/**
 * GET /api/usage
 * Returns HD quota usage for the caller's IP address.
 */
app.get("/api/usage", (req, res) => {
  const usage = getHdUsageStatus(req.ip);
  res.json(usage);
});

/**
 * STEP 1 — POST /api/resolve
 * Accepts quality: "SD" (free unlimited) or "HD" (free 2/day, then paid/blocked)
 */
app.post("/api/resolve", async (req, res) => {
  const { mediaUrl, quality = "SD" } = req.body || {};

  if (!mediaUrl || !isHttpUrl(mediaUrl)) {
    return res.status(400).json({ error: "Please provide a valid HTTP(S) media URL." });
  }

  const isHdRequested = String(quality).toUpperCase() === "HD";
  let hdStatus = { allowed: true, remaining: 2 };

  if (isHdRequested) {
    const check = checkAndIncrementHdUsage(req.ip);
    if (!check.allowed) {
      return res.status(402).json({
        error: "DAILY_HD_LIMIT_REACHED",
        message: "You have used your 2 free HD downloads for today. Upgrade to Premium HD or download in Free SD quality.",
        remaining: 0,
        paywall: true
      });
    }
    hdStatus = check;
  }

  let cdnUrl, filename, video;
  let resolvedPlatform = null;
  const qualityPrefix = isHdRequested ? "HD_" : "SD_";

  const detected = detectPlatform(mediaUrl);

  if (detected) {
    try {
      video = await resolveVideo(mediaUrl, { hd: isHdRequested });
      if (!video) throw new Error("Unsupported video URL.");
      resolvedPlatform = video.platform;
      cdnUrl = isHdRequested && video.hdUrl ? video.hdUrl : video.sdUrl || video.hdUrl;
      if (!cdnUrl && video.kind !== "yt-dlp") {
        throw new Error("No downloadable video stream was found for that link.");
      }
      const rawTitle = video.title || `${video.platform}_video`;
      const safeTitle = rawTitle.replace(/[^a-zA-Z0-9._-]/g, "_").slice(0, 80);
      filename = `${qualityPrefix}${safeTitle}.mp4`;
    } catch (err) {
      return res.status(502).json({ error: err.message || "Failed to resolve the video." });
    }
  } else {
    if (!isHttpUrl(mediaUrl)) return res.status(400).json({ error: "Invalid media URL." });
    cdnUrl = mediaUrl;
    filename = "video.mp4";
  }

  // Issue a one-time token valid for 2 minutes
  const token = randomUUID();
  const entry = { filename, exp: Date.now() + 120_000 };
  if (video && video.kind === "yt-dlp") {
    entry.ytDlp = { url: mediaUrl, selector: video.selector };
  } else {
    entry.cdnUrl = cdnUrl;
  }
  downloadTokens.set(token, entry);
  setTimeout(() => downloadTokens.delete(token), 120_000);

  logger.info({ token, filename, quality, platform: resolvedPlatform || "direct", ip: req.ip }, "Download token issued");
  res.json({
    token,
    filename,
    quality: isHdRequested ? "HD" : "SD",
    platform: resolvedPlatform || "direct",
    remainingHd: getHdUsageStatus(req.ip).remaining
  });
});

/**
 * STEP 2 — GET /api/stream/:token
 * Streams the video file directly to browser natively.
 * Two modes:
 *   - URL proxy (cdUrl): simple upstream fetch → pipe to client.
 *   - yt-dlp (entry.ytDlp): runs yt-dlp+ffmpeg on the fly, pipes merged MP4
 *     to client — needed for YouTube DASH (video-only + audio-only) merges.
 */
app.get("/api/stream/:token", async (req, res) => {
  const entry = downloadTokens.get(req.params.token);
  if (!entry || Date.now() > entry.exp) {
    return res.status(404).json({ error: "Download link expired or invalid. Please try again." });
  }
  downloadTokens.delete(req.params.token);

  const safeName = String(entry.filename)
    .replace(/[^a-zA-Z0-9._-]/g, "_")
    .slice(0, 120) || "video.mp4";

  /* ---- Mode 1: yt-dlp merge stream (YouTube) ---- */
  if (entry.ytDlp) {
    const args = buildYtDlpStreamArgs(entry.ytDlp.selector, entry.ytDlp.url);
    const child = spawn(YTDLP_PATH, args, { windowsHide: true, stdio: ["ignore", "pipe", "pipe"] });

    let stderrBuf = "";
    child.stderr.on("data", (d) => (stderrBuf += String(d)));
    const safetyTimer = setTimeout(() => { child.kill("SIGKILL"); }, 20 * 60 * 1000);

    res.setHeader("Content-Type", "video/mp4");
    res.setHeader("Content-Disposition", `attachment; filename="${safeName}"`);
    res.setHeader("Cache-Control", "no-store");
    res.setHeader("X-Content-Type-Options", "nosniff");

    logger.info({ kind: "yt-dlp", selector: entry.ytDlp.selector, filename: safeName }, "streaming yt-dlp");

    req.on("close", () => child.kill("SIGKILL"));

    try {
      await pipeline(child.stdout, res);
    } catch (err) {
      req.log?.warn({ err: err.message }, "yt-dlp stream ended");
    } finally {
      clearTimeout(safetyTimer);
      child.kill("SIGKILL");
      if (!stderrBuf.includes("[download]") && child.exitCode !== 0) {
        req.log?.error({ stderr: stderrBuf.slice(0, 500) }, "yt-dlp non-zero exit");
        if (!res.headersSent) {
          return res.status(502).json({ error: "yt-dlp could not complete the download." });
        }
      }
    }
    return;
  }

  /* ---- Mode 2: direct URL proxy (TikTok / Instagram / X / passthrough) ---- */
  if (!entry.cdnUrl) {
    return res.status(422).json({ error: "No stream source available for this token." });
  }

  let parsed;
  try {
    parsed = new URL(entry.cdnUrl);
  } catch {
    return res.status(502).json({ error: "Resolved URL is invalid." });
  }

  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 60_000);

  try {
    const upstream = await fetch(parsed, {
      signal: controller.signal,
      redirect: "follow",
      headers: {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
        "Accept": "video/*,*/*;q=0.9",
        "Accept-Language": "en-US,en;q=0.9"
      }
    });

    if (!upstream.ok || !upstream.body) {
      return res.status(502).json({ error: `The media source could not be reached. (HTTP ${upstream.status})` });
    }

    const contentType = upstream.headers.get("content-type") || "video/mp4";

    if (contentType.includes("text/html") || contentType.includes("application/json")) {
      return res.status(422).json({
        error: `The URL returned ${contentType} instead of a video.`
      });
    }

    const contentLength = Number(upstream.headers.get("content-length") || 0);
    if (contentLength && contentLength > MAX_DOWNLOAD_BYTES) {
      return res.status(413).json({ error: `Media exceeds the ${MAX_DOWNLOAD_MB} MB limit.` });
    }

    res.setHeader("Content-Type", contentType === "application/octet-stream" ? "video/mp4" : contentType);
    res.setHeader("Content-Disposition", `attachment; filename="${safeName}"`);
    res.setHeader("Cache-Control", "no-store");
    res.setHeader("X-Content-Type-Options", "nosniff");
    if (contentLength) res.setHeader("Content-Length", String(contentLength));

    logger.info({ url: parsed.href, contentType, contentLength, filename: safeName }, "streaming download");

    req.on("close", () => controller.abort());
    await pipeline(Readable.fromWeb(upstream.body), res);
  } catch (error) {
    if (!res.headersSent) {
      const status = error.name === "AbortError" ? 504 : 502;
      return res.status(status).json({ error: "The download stream ended unexpectedly." });
    }
    req.log?.warn({ err: error }, "download stream ended");
  } finally {
    clearTimeout(timeout);
  }
});

app.use((err, req, res, next) => {
  const route = req.url || req.originalUrl || "";
  console.error("[unhandled-error]", route, err && err.message, err && err.stack);
  req.log?.error({ err, url: route }, "Unhandled error");
  if (res.headersSent) return next(err);
  res.status(500).json({ error: "Internal server error." });
});

const server = app.listen(PORT, () => {
  logger.info({ port: PORT }, "API server started");
});

const shutdown = (signal) => {
  logger.info({ signal }, "Shutting down");
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(1), 10_000).unref();
};

process.on("SIGTERM", () => shutdown("SIGTERM"));
process.on("SIGINT", () => shutdown("SIGINT"));