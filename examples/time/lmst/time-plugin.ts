import { bisector, range } from "d3-array";
import { Spice } from "timecraftjs";

// const LMST_SPACECRAFT_ID: number = -168900; // Perseverence Rover Spacecraft ID
const SPACECRAFT_ID: number = 168; // Perseverence Rover Spacecraft ID
const LMST_SPACECRAFT_ID = parseInt(`-${SPACECRAFT_ID}900 `, 10);
const SPICE_LMST_RE: RegExp = /^\d\/(\d+):(\d{2}):(\d{2}):(\d{2}):(\d+)?$/;
const DISPLAY_LMST_RE: RegExp =
  /^(Sol-)?(\d+)M(\d{2}):(\d{2}):(\d{2})(.(\d*))?$/;
const LMST_FORMAT_STRING: string = "DDDDDMHH:MM:SS";
// const SCLK_REGEX: RegExp =
//   /^\d\/(?<seconds>\d+)(-|\\.|:|,|\\s)(?<fraction>\d+)$/;

let spiceInstance: any = undefined;

// Mars seconds since Sol-0
function msss0(lmst: string): number {
  const sols = +lmst.split("M")[0];
  const hours = +lmst.split("M")[1].split(":")[0];
  const minutes = +lmst.split("M")[1].split(":")[1];
  const seconds = +lmst.split("M")[1].split(":")[2];
  const sss0 = sols * 86400 + hours * 3600 + minutes * 60 + seconds;
  return sss0;
}

function msss0_to_lmst(msss0: number): string {
  let sols = String(Math.floor(msss0 / 86400));
  let secondsLeft = msss0 % 86400;
  let hours = String(Math.floor(secondsLeft / 3600));
  secondsLeft = secondsLeft % 3600;
  let minutes = String(Math.floor(secondsLeft / 60));
  secondsLeft = secondsLeft % 60;
  let seconds = String(secondsLeft.toFixed(2));
  while (sols.length < 5) {
    sols = "0" + sols;
  }
  while (hours.length < 2) {
    hours = "0" + hours;
  }
  while (minutes.length < 2) {
    minutes = "0" + minutes;
  }
  while (seconds.length < 5) {
    seconds = "0" + seconds;
  }
  const lmst = sols + "M" + hours + ":" + minutes + ":" + seconds;
  return lmst;
}

function trimLeadingZeroes(s: string): string {
  return parseInt(s, 10).toString(10);
}

function lmstToEphemeris(lmst: string): number {
  const matcher = lmst.match(DISPLAY_LMST_RE);
  if (!matcher) {
    return NaN;
  }

  const sol = trimLeadingZeroes(matcher[2] || "");
  const hour = matcher[3] || "";
  const mins = matcher[4] || "";
  const secs = matcher[5] || "";
  const subsecs = parseFloat(matcher[6] || "0")
    .toFixed(5)
    .substring(2);
  const sclkch = `${sol}:${hour}:${mins}:${secs}:${subsecs}`;
  // const sclkch = sol + ':' + hour + ':' + mins + ':' + secs + ':' + subsecs;
  return spiceInstance.scs2e(LMST_SPACECRAFT_ID, sclkch);
}

function ephemerisToLMST(et: number): string {
  const lmst = spiceInstance.sce2s(LMST_SPACECRAFT_ID, et);
  // something like "1/01641:07:16:13:65583"
  const m = lmst.match(SPICE_LMST_RE);
  if (m) {
    const sol = trimLeadingZeroes(m[1]);
    const hour = m[2];
    const mins = m[3];
    const secs = m[4];
    const subsecs = m[5] || "0";
    return sol + "M" + hour + ":" + mins + ":" + secs + "." + subsecs;
  }
  return "";
}

function ephemerisToSCLK(et: number): string {
  const sclkStr = spiceInstance.sce2s(SPACECRAFT_ID, et);
  // sclkStr = "1/0436236010-12059"
  const split: string[] = sclkStr.substring(2).split("-");
  const sclk =
    parseInt(split[0], 10) + parseInt(split[1], 10) / Math.pow(2, 16);
  return sclk.toString();
}

function ephemerisToUTC(et: number): Date {
  return new Date(spiceInstance.et2utc(et, "ISOC", 100) + "Z");
}

function lmstToUTC(lmst: string): Date {
  if (spiceInstance) {
    try {
      const et = lmstToEphemeris(lmst);
      return ephemerisToUTC(et);
    } catch (error) {
      console.log("error :>> ", error);
    }
  }
  return new Date();
}

function utcStringToLmst(utc: string): string {
  if (spiceInstance) {
    try {
      const et = spiceInstance.str2et(utc);
      return ephemerisToLMST(et);
    } catch (error) {
      console.error(error);
      return "";
    }
  }
  return "no spice";
}

function utcStringToSCLK(utc: string): string {
  if (spiceInstance) {
    try {
      const et = spiceInstance.str2et(utc);
      return ephemerisToSCLK(et);
    } catch (error) {
      console.error(error);
      return "";
    }
  }
  return "no spice";
}

export function lmstTicks(start: Date, stop: Date, tickCount: number): Date[] {
  const lmstStart = utcStringToLmst(start.toISOString().slice(0, -1));
  const lmstEnd = utcStringToLmst(stop.toISOString().slice(0, -1));
  const lsmtStartSeconds = msss0(lmstStart);
  const lsmtStartSols = lsmtStartSeconds / 60 / 60 / 24;
  const lsmtEndSeconds = msss0(lmstEnd);
  const lsmtEndSols = lsmtEndSeconds / 60 / 60 / 24;
  // TODO handle duration = 0 case
  const lmstDurationSeconds = lsmtEndSeconds - lsmtStartSeconds;
  let stepSize;
  const stepSizeSols = lmstDurationSeconds / 60 / 60 / 24 / tickCount;
  const dayInSeconds = 86400;

  const lmstSteps = [
    0.1 / dayInSeconds,
    0.5 / dayInSeconds,
    1 / dayInSeconds,
    2 / dayInSeconds,
    5 / dayInSeconds,
    10 / dayInSeconds,
    15 / dayInSeconds,
    20 / dayInSeconds,
    30 / dayInSeconds,
    (1 * 60) / dayInSeconds,
    (2 * 60) / dayInSeconds,
    (5 * 60) / dayInSeconds,
    (10 * 60) / dayInSeconds,
    (15 * 60) / dayInSeconds,
    (20 * 60) / dayInSeconds,
    (30 * 60) / dayInSeconds,
    (1 * 60 * 60) / dayInSeconds,
    (2 * 60 * 60) / dayInSeconds,
    (3 * 60 * 60) / dayInSeconds,
    (4 * 60 * 60) / dayInSeconds,
    (6 * 60 * 60) / dayInSeconds,
    (8 * 60 * 60) / dayInSeconds,
    (12 * 60 * 60) / dayInSeconds,
    1,
    2,
    5,
    10,
    25,
    50,
    100,
    250,
    500,
    1000,
    2500,
    5000,
    1000,
  ];

  const bisectTicks = bisector((d) => d).left;
  const i = bisectTicks(lmstSteps, stepSizeSols, 0);
  stepSize = lmstSteps[i];

  // round the domain to nearest step size values
  const minValRounded = Math.round(lsmtStartSols / stepSize) * stepSize;
  const maxValRounded = Math.round(lsmtEndSols / stepSize) * stepSize;

  const ticks = range(minValRounded, maxValRounded, stepSize)
    .map((x) => lmstToUTC(msss0_to_lmst(x * 24 * 60 * 60)))
    .filter(
      (date) =>
        date.getTime() >= start.getTime() && date.getTime() <= stop.getTime()
    );

  return ticks;
}

async function initializeSpice() {
  try {
    const initializingSpice = await new Spice().init();

    // Load the kernels
    // TODO ensure this works when ui is deployed under a sub path
    // may need to pass in a base path
    const kernelBuffers = await Promise.all(
      [
        "/resources/kernels/m2020_lmst_ops210303_v1.tsc",
        "/resources/kernels/m2020.tls",
        "/resources/kernels/m2020.tsc",
      ].map((url) => fetch(url).then((res) => res.arrayBuffer()))
    );

    // Load the kernels into Spice
    for (let i = 0; i < kernelBuffers.length; i++) {
      initializingSpice.loadKernel(kernelBuffers[i]);
    }
    spiceInstance = initializingSpice;
    console.log("Spice initialized");
    return true;
  } catch (error) {
    console.log("Error initializing Spice:", error);
    return false;
  }
}

function validateLMSTString(value: string): Promise<null | string> {
  return new Promise((resolve) => {
    const match = DISPLAY_LMST_RE.exec(value);
    const error = `LMST format required: ${LMST_FORMAT_STRING}`;
    return match ? resolve(null) : resolve(error);
  });
}

export async function getPlugin() {
  const success = await initializeSpice();
  if (success) {
    return {
      time: {
        primary: {
          format: (date: Date) => {
            const dateWithoutTZ = date.toISOString().slice(0, -1);
            return utcStringToLmst(dateWithoutTZ).slice(0, -6);
          },
          formatString: LMST_FORMAT_STRING,
          label: "LMST",
          parse: lmstToUTC,
          validate: validateLMSTString,
        },
        secondary: {
          format: (date: Date) => date.toISOString().slice(0, -5),
          label: "UTC",
          parse: (string: string) => new Date(string),
        },
        tertiary: {
          format: (date: Date) => {
            const dateWithoutTZ = date.toISOString().slice(0, -1);
            return utcStringToSCLK(dateWithoutTZ);
          },
          label: "SCLK",
          parse: (string: string) => new Date(string),
        },
        ticks: {
          getTicks: lmstTicks,
          tickLabelWidth: 110,
        },
      },
    };
  } else {
    return {};
  }
}
