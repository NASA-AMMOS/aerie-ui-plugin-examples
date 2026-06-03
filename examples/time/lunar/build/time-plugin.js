/******************************************************************************
Copyright (c) Microsoft Corporation.

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
***************************************************************************** */
/* global Reflect, Promise, SuppressedError, Symbol, Iterator */


function __awaiter(thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
}

function __generator(thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g = Object.create((typeof Iterator === "function" ? Iterator : Object).prototype);
    return g.next = verb(0), g["throw"] = verb(1), g["return"] = verb(2), typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (g && (g = 0, op[0] && (_ = 0)), _) try {
            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [op[0] & 2, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
}

typeof SuppressedError === "function" ? SuppressedError : function (error, suppressed, message) {
    var e = new Error(message);
    return e.name = "SuppressedError", e.error = error, e.suppressed = suppressed, e;
};

var CAL_UTC_RE = /^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(\.\d+)?$/;
var DOY_UTC_RE = /^(\d{4})-(\d{3})T(\d{2}):(\d{2}):(\d{2})(\.\d+)?$/;
var DEFAULT_PLAN_DAYS = 14;
// LMST midnight in UTC for south pole landing.
// 24-hour-per-lunar-sol uniform mean clock. True apparent solar position drifts
// from this by up to ~±30 LMST minutes peak due to lunar orbital eccentricity
// (e≈0.055, 3× Earth's). Adequate for phase-of-day indication; not a precision
// solar clock. The lunar mean solar day is ~29.5306 Earth days.
// Compute lunar midnight from an earth midnight + given LMST,
// ex: say the lunar solar time is 05:00 on 10/21/2028 00:00 UTC Earth.
var LUNAR_SOL_SECONDS = 29.530589 * 86400;
var LUNAR_HOUR_SECONDS = (29.530589 * 86400) / 24;
var TARGET_EARTH_MIDNIGHT = "2028-10-21T00:00:00Z";
var LUNAR_HOURS_AFTER_LUNAR_MIDNIGHT = 5;
var LMST_LOCAL_MIDNIGHT_UTC = new Date(new Date(TARGET_EARTH_MIDNIGHT).getTime() -
    LUNAR_HOURS_AFTER_LUNAR_MIDNIGHT * LUNAR_HOUR_SECONDS * 1000)
    .toISOString()
    .replace("Z", "");
// Alternatively you can just specify a known LMST midnight in UTC.
// const LMST_LOCAL_MIDNIGHT_UTC = "2028-10-14T20:21:00";
var PT_FMT = new Intl.DateTimeFormat("en-CA", {
    timeZone: "America/Los_Angeles",
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
    hour: "2-digit",
    minute: "2-digit",
    second: "2-digit",
    hourCycle: "h23",
});
function formatUTC(date) {
    // DOY (ordinal date) format YYYY-DDDTHH:mm:ss — matches PlanDev UI's native default.
    var year = date.getUTCFullYear();
    var startOfYear = Date.UTC(year, 0, 1);
    var doy = Math.floor((date.getTime() - startOfYear) / 86400000) + 1;
    var pad = function (n, w) { return String(n).padStart(w, "0"); };
    return ("".concat(year, "-").concat(pad(doy, 3), "T") +
        "".concat(pad(date.getUTCHours(), 2), ":").concat(pad(date.getUTCMinutes(), 2), ":").concat(pad(date.getUTCSeconds(), 2)));
}
// PlanDev calls formatShort in space-constrained places (Plans table, tooltips).
// We return just the date portion (YYYY-DDD) for compact scanning.
function formatUTCShort(date) {
    var year = date.getUTCFullYear();
    var startOfYear = Date.UTC(year, 0, 1);
    var doy = Math.floor((date.getTime() - startOfYear) / 86400000) + 1;
    return "".concat(year, "-").concat(String(doy).padStart(3, "0"));
}
function parseUTC(value) {
    var cal = value.match(CAL_UTC_RE);
    if (cal) {
        var d = new Date(value + "Z");
        return isNaN(d.getTime()) ? null : d;
    }
    var doy = value.match(DOY_UTC_RE);
    if (doy) {
        var year = parseInt(doy[1], 10);
        var ord = parseInt(doy[2], 10);
        if (ord < 1 || ord > 366) {
            return null;
        }
        var hours = parseInt(doy[3], 10);
        var minutes = parseInt(doy[4], 10);
        var seconds = parseInt(doy[5], 10);
        var ms = doy[6] ? Math.floor(parseFloat(doy[6]) * 1000) : 0;
        var d = new Date(Date.UTC(year, 0, ord, hours, minutes, seconds, ms));
        return isNaN(d.getTime()) ? null : d;
    }
    return null;
}
function validateUTC(value) {
    if (CAL_UTC_RE.test(value) || DOY_UTC_RE.test(value)) {
        return Promise.resolve(null);
    }
    return Promise.resolve("DOY or UTC format required: YYYY-DDDTHH:mm:ss or YYYY-MM-DDTHH:mm:ss");
}
function formatPDT(date) {
    var parts = PT_FMT.formatToParts(date);
    var get = function (t) { var _a, _b; return (_b = (_a = parts.find(function (p) { return p.type === t; })) === null || _a === void 0 ? void 0 : _a.value) !== null && _b !== void 0 ? _b : ""; };
    return ("".concat(get("year"), "-").concat(get("month"), "-").concat(get("day"), " ") +
        "".concat(get("hour"), ":").concat(get("minute"), ":").concat(get("second")));
}
/**
 *
 * @param date Earth Date UTC
 * @param localMidnight local lunar midnight
 * @returns
 */
function formatLMST(date, localMidnight) {
    var elapsedSec = (date.getTime() - localMidnight.getTime()) / 1000; // earth seconds between date and lunar midnight
    var solsRaw = elapsedSec / LUNAR_SOL_SECONDS; // lunar sols between date and lunar midnight, can be fractional and negative
    var sols = Math.floor(solsRaw); // whole lunar sols between date and lunar midnight, can be negative
    var fraction = ((solsRaw % 1) + 1) % 1; // fractional part of lunar sol delta, in range [0, 1)
    var totalSeconds = Math.floor(fraction * 86400); // lunar seconds since last lunar midnight, in range [0, 86400)
    var hours = Math.floor(totalSeconds / 3600); // lunar hours since last lunar midnight, in range [0, 24)
    var minutes = Math.floor((totalSeconds % 3600) / 60); // lunar minutes since last lunar hour, in range [0, 60)
    var seconds = totalSeconds % 60; // lunar seconds since last lunar minute, in range [0, 60)
    var pad = function (n) { return String(n).padStart(2, "0"); };
    var solStr = sols < 0
        ? "-" + String(-sols).padStart(4, "0")
        : String(sols).padStart(5, "0");
    return "".concat(solStr, "L").concat(pad(hours), ":").concat(pad(minutes), ":").concat(pad(seconds));
}
function getPlugin() {
    return __awaiter(this, void 0, void 0, function () {
        var lmstMidnight, additional;
        return __generator(this, function (_a) {
            lmstMidnight = parseUTC(LMST_LOCAL_MIDNIGHT_UTC);
            additional = [{ format: formatPDT, label: "PDT" }];
            if (lmstMidnight) {
                additional.push({
                    format: function (date) { return formatLMST(date, lmstMidnight); },
                    label: "LMST",
                });
            }
            return [2 /*return*/, {
                    time: {
                        enableDatePicker: true,
                        getDefaultPlanEndDate: function (start) {
                            return new Date(start.getTime() + DEFAULT_PLAN_DAYS * 86400 * 1000);
                        },
                        primary: {
                            format: formatUTC,
                            formatShort: formatUTCShort,
                            formatString: "YYYY-DDDTHH:mm:ss",
                            label: "UTC",
                            parse: parseUTC,
                            validate: validateUTC,
                        },
                        additional: additional,
                    },
                }];
        });
    });
}

export { getPlugin };
