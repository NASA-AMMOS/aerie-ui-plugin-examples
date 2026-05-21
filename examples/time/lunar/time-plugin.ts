import { Spice } from "timecraftjs";

type SpacecraftConfig = {
  name: string;
  spiceId?: number;
  sclkKernel?: string;
};

type LunarTimeConfig = {
  landingEpochUtc?: string;
  defaultPlanDurationDays?: number;
  lskKernel?: string;
  spacecraft: SpacecraftConfig[];
};

const CONFIG_URL = "/resources/lunar-time-config.json";
const DEFAULT_LSK = "/resources/kernels/naif0012.tls";
const DEFAULT_PLAN_DAYS = 14;
const CAL_UTC_RE = /^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(\.\d+)?$/;
const DOY_UTC_RE = /^(\d{4})-(\d{3})T(\d{2}):(\d{2}):(\d{2})(\.\d+)?$/;

let spiceInstance: any = undefined;
const loadedSpiceIds = new Set<number>();
const warnedSpiceIds = new Set<number>();

async function loadConfig(): Promise<LunarTimeConfig> {
  try {
    const res = await fetch(CONFIG_URL);
    if (!res.ok) {
      throw new Error(`HTTP ${res.status}`);
    }
    const cfg = (await res.json()) as LunarTimeConfig;
    if (!Array.isArray(cfg.spacecraft)) {
      cfg.spacecraft = [];
    }
    return cfg;
  } catch (err) {
    console.warn(
      `Lunar Time Plugin: could not load ${CONFIG_URL} (${err}). Falling back to UTC-only.`
    );
    return { spacecraft: [] };
  }
}

async function fetchKernel(url: string): Promise<ArrayBuffer> {
  const res = await fetch(url);
  if (!res.ok) {
    throw new Error(`Failed to fetch ${url}: HTTP ${res.status}`);
  }
  return res.arrayBuffer();
}

async function initializeSpice(config: LunarTimeConfig): Promise<boolean> {
  const sclkSpacecraft = config.spacecraft.filter(
    (sc) => sc.spiceId != null && sc.sclkKernel
  );
  if (sclkSpacecraft.length === 0) {
    return false;
  }

  try {
    const inst = await new Spice().init();

    // Use RETURN action so SPICE doesn't print on its own; we check failed() explicitly.
    inst.erract("SET", "RETURN");
    inst.onStdErr = (err: string) => console.error("[SPICE]", err);
    inst.onStdOut = (s: string) => console.log("[SPICE]", s);

    const lskUrl = config.lskKernel || DEFAULT_LSK;
    const lskBuffer = await fetchKernel(lskUrl);
    inst.loadKernel(lskBuffer);
    if (inst.failed()) {
      console.error("Lunar Time Plugin: LSK load failed:", inst.getmsg("LONG"));
      inst.reset();
      return false;
    }

    for (const sc of sclkSpacecraft) {
      try {
        const buf = await fetchKernel(sc.sclkKernel!);
        inst.loadKernel(buf);
        if (inst.failed()) {
          console.error(
            `Lunar Time Plugin: SCLK load failed for ${sc.name}:`,
            inst.getmsg("LONG")
          );
          inst.reset();
          continue;
        }
        loadedSpiceIds.add(sc.spiceId!);
      } catch (err) {
        console.error(
          `Lunar Time Plugin: failed to fetch SCLK kernel for ${sc.name} (${sc.sclkKernel}): ${err}`
        );
      }
    }

    // After init, silence SPICE's automatic printing — the timeline calls SCLK
    // per tick, and out-of-coverage dates would otherwise flood the console.
    // Each wrapper below checks failed() explicitly and warns once per spacecraft.
    inst.errprt("SET", "NONE");
    spiceInstance = inst;

    console.log("Lunar Time Plugin: Spice initialized");
    return true;
  } catch (err) {
    console.error("Lunar Time Plugin: Spice init failed:", err);
    return false;
  }
}

function warnSclkOnce(spiceId: number, name: string): void {
  if (warnedSpiceIds.has(spiceId)) return;
  warnedSpiceIds.add(spiceId);
  console.warn(
    `Lunar Time Plugin: SCLK for ${name} (${spiceId}) returned null — likely outside this kernel's coverage. ` +
      `Check landingEpochUtc and the plan timeline range.`
  );
}

function formatUTC(date: Date): string {
  // DOY (ordinal date) format YYYY-DDDTHH:mm:ss — matches Aerie UI's native default.
  const year = date.getUTCFullYear();
  const startOfYear = Date.UTC(year, 0, 1);
  const doy =
    Math.floor((date.getTime() - startOfYear) / 86400000) + 1;
  const pad = (n: number, w: number) => String(n).padStart(w, "0");
  return (
    `${year}-${pad(doy, 3)}T` +
    `${pad(date.getUTCHours(), 2)}:${pad(date.getUTCMinutes(), 2)}:${pad(date.getUTCSeconds(), 2)}`
  );
}

// Aerie calls formatShort in space-constrained places (Plans table, tooltips).
// We return just the date portion (YYYY-DDD) for compact scanning. Exact times
// are visible in the timeline view; the table just needs date-level granularity.
function formatUTCShort(date: Date): string {
  const year = date.getUTCFullYear();
  const startOfYear = Date.UTC(year, 0, 1);
  const doy = Math.floor((date.getTime() - startOfYear) / 86400000) + 1;
  return `${year}-${String(doy).padStart(3, "0")}`;
}

function parseUTC(value: string): Date | null {
  const cal = value.match(CAL_UTC_RE);
  if (cal) {
    const d = new Date(value + "Z");
    return isNaN(d.getTime()) ? null : d;
  }
  const doy = value.match(DOY_UTC_RE);
  if (doy) {
    const year = parseInt(doy[1], 10);
    const ord = parseInt(doy[2], 10);
    if (ord < 1 || ord > 366) {
      return null;
    }
    const hours = parseInt(doy[3], 10);
    const minutes = parseInt(doy[4], 10);
    const seconds = parseInt(doy[5], 10);
    const ms = doy[6] ? Math.floor(parseFloat(doy[6]) * 1000) : 0;
    const d = new Date(Date.UTC(year, 0, ord, hours, minutes, seconds, ms));
    return isNaN(d.getTime()) ? null : d;
  }
  return null;
}

function validateUTC(value: string): Promise<null | string> {
  if (CAL_UTC_RE.test(value) || DOY_UTC_RE.test(value)) {
    return Promise.resolve(null);
  }
  return Promise.resolve(
    "DOY or UTC format required: YYYY-DDDTHH:mm:ss or YYYY-MM-DDTHH:mm:ss"
  );
}

function formatMET(date: Date, epoch: Date): string {
  const diffMs = date.getTime() - epoch.getTime();
  const sign = diffMs < 0 ? "T-" : "T+";
  const totalSeconds = Math.floor(Math.abs(diffMs) / 1000);
  const days = Math.floor(totalSeconds / 86400);
  const hours = Math.floor((totalSeconds % 86400) / 3600);
  const minutes = Math.floor((totalSeconds % 3600) / 60);
  const seconds = totalSeconds % 60;
  const pad = (n: number) => String(n).padStart(2, "0");
  return `${sign}${days}:${pad(hours)}:${pad(minutes)}:${pad(seconds)}`;
}

function ephemerisToSCLK(date: Date, spiceId: number): string | null {
  if (!spiceInstance) return null;

  const et = spiceInstance.str2et(date.toISOString().slice(0, -1));
  if (spiceInstance.failed()) {
    spiceInstance.reset();
    return null;
  }

  const sclkStr = spiceInstance.sce2s(spiceId, et);
  if (spiceInstance.failed()) {
    spiceInstance.reset();
    return null;
  }

  // SPICE SCLK string is typically "1/<ticks>-<subticks>"; reduce to a numeric form.
  const body = sclkStr.includes("/") ? sclkStr.split("/")[1] : sclkStr;
  const parts = body.split("-");
  const ticks = parseInt(parts[0], 10);
  const subticks = parts[1] ? parseInt(parts[1], 10) / Math.pow(2, 16) : 0;
  if (!Number.isFinite(ticks)) return null;
  return (ticks + subticks).toFixed();
}

export async function getPlugin() {
  const config = await loadConfig();
  const durationDays = config.defaultPlanDurationDays ?? DEFAULT_PLAN_DAYS;
  const spiceReady = await initializeSpice(config);

  const additional: Array<{
    format: (date: Date) => string | null;
    label: string;
  }> = [];

  if (config.landingEpochUtc) {
    const epoch = parseUTC(config.landingEpochUtc);
    if (epoch) {
      additional.push({
        format: (date: Date) => formatMET(date, epoch),
        label: "MET",
      });
    } else {
      console.warn(
        `Lunar Time Plugin: invalid landingEpochUtc "${config.landingEpochUtc}", MET row disabled`
      );
    }
  }

  if (spiceReady) {
    for (const sc of config.spacecraft) {
      if (sc.spiceId != null && loadedSpiceIds.has(sc.spiceId)) {
        const id = sc.spiceId;
        const name = sc.name;
        additional.push({
          format: (date: Date) => {
            const result = ephemerisToSCLK(date, id);
            if (result === null) warnSclkOnce(id, name);
            return result;
          },
          label: `${name} SCLK`,
        });
      }
    }
  }

  return {
    time: {
      enableDatePicker: true,
      getDefaultPlanEndDate: (start: Date) =>
        new Date(start.getTime() + durationDays * 86400 * 1000),
      primary: {
        format: formatUTC,
        formatShort: formatUTCShort,
        formatString: "YYYY-DDDTHH:mm:ss",
        label: "UTC",
        parse: parseUTC,
        validate: validateUTC,
      },
      additional,
    },
  };
}
