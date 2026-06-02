const CAL_UTC_RE = /^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(\.\d+)?$/;
const DOY_UTC_RE = /^(\d{4})-(\d{3})T(\d{2}):(\d{2}):(\d{2})(\.\d+)?$/;
const DEFAULT_PLAN_DAYS = 14;

// LST midnight in UTC for south pole landing at 0° longitude (placeholder).
const LST_LOCAL_MIDNIGHT_UTC = "2028-09-18T18:22:00";
// The lunar mean solar day is ~29.5306 Earth days.
const LUNAR_SOL_SECONDS = 29.530589 * 86400;

const PT_FMT = new Intl.DateTimeFormat("en-CA", {
  timeZone: "America/Los_Angeles",
  year: "numeric",
  month: "2-digit",
  day: "2-digit",
  hour: "2-digit",
  minute: "2-digit",
  second: "2-digit",
  hourCycle: "h23",
});

function formatUTC(date: Date): string {
  // DOY (ordinal date) format YYYY-DDDTHH:mm:ss — matches PlanDev UI's native default.
  const year = date.getUTCFullYear();
  const startOfYear = Date.UTC(year, 0, 1);
  const doy = Math.floor((date.getTime() - startOfYear) / 86400000) + 1;
  const pad = (n: number, w: number) => String(n).padStart(w, "0");
  return (
    `${year}-${pad(doy, 3)}T` +
    `${pad(date.getUTCHours(), 2)}:${pad(date.getUTCMinutes(), 2)}:${pad(date.getUTCSeconds(), 2)}`
  );
}

// PlanDev calls formatShort in space-constrained places (Plans table, tooltips).
// We return just the date portion (YYYY-DDD) for compact scanning.
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

function formatPDT(date: Date): string {
  const parts = PT_FMT.formatToParts(date);
  const get = (t: string) => parts.find((p) => p.type === t)?.value ?? "";
  return (
    `${get("year")}-${get("month")}-${get("day")} ` +
    `${get("hour")}:${get("minute")}:${get("second")}`
  );
}

function formatLST(date: Date, localMidnight: Date): string {
  const elapsedSec = (date.getTime() - localMidnight.getTime()) / 1000;
  const solsRaw = elapsedSec / LUNAR_SOL_SECONDS;
  const sols = Math.floor(solsRaw);
  const fraction = ((solsRaw % 1) + 1) % 1;
  const totalSeconds = Math.floor(fraction * 86400);
  const hours = Math.floor(totalSeconds / 3600);
  const minutes = Math.floor((totalSeconds % 3600) / 60);
  const seconds = totalSeconds % 60;
  const pad = (n: number) => String(n).padStart(2, "0");
  const solStr =
    sols < 0
      ? "-" + String(-sols).padStart(4, "0")
      : String(sols).padStart(5, "0");
  return `${solStr}L${pad(hours)}:${pad(minutes)}:${pad(seconds)}`;
}

export async function getPlugin() {
  const lstMidnight = parseUTC(LST_LOCAL_MIDNIGHT_UTC);
  const additional: Array<{
    format: (date: Date) => string | null;
    label: string;
  }> = [
    { format: formatPDT, label: "PDT" },
  ];
  if (lstMidnight) {
    additional.push({
      format: (date: Date) => formatLST(date, lstMidnight),
      label: "LST",
    });
  }
  return {
    time: {
      enableDatePicker: true,
      getDefaultPlanEndDate: (start: Date) =>
        new Date(start.getTime() + DEFAULT_PLAN_DAYS * 86400 * 1000),
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
