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
/* global Reflect, Promise, SuppressedError, Symbol */


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
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
    return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
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

function ascending(a, b) {
  return a == null || b == null ? NaN : a < b ? -1 : a > b ? 1 : a >= b ? 0 : NaN;
}

function descending(a, b) {
  return a == null || b == null ? NaN
    : b < a ? -1
    : b > a ? 1
    : b >= a ? 0
    : NaN;
}

function bisector(f) {
  let compare1, compare2, delta;

  // If an accessor is specified, promote it to a comparator. In this case we
  // can test whether the search value is (self-) comparable. We can’t do this
  // for a comparator (except for specific, known comparators) because we can’t
  // tell if the comparator is symmetric, and an asymmetric comparator can’t be
  // used to test whether a single value is comparable.
  if (f.length !== 2) {
    compare1 = ascending;
    compare2 = (d, x) => ascending(f(d), x);
    delta = (d, x) => f(d) - x;
  } else {
    compare1 = f === ascending || f === descending ? f : zero;
    compare2 = f;
    delta = f;
  }

  function left(a, x, lo = 0, hi = a.length) {
    if (lo < hi) {
      if (compare1(x, x) !== 0) return hi;
      do {
        const mid = (lo + hi) >>> 1;
        if (compare2(a[mid], x) < 0) lo = mid + 1;
        else hi = mid;
      } while (lo < hi);
    }
    return lo;
  }

  function right(a, x, lo = 0, hi = a.length) {
    if (lo < hi) {
      if (compare1(x, x) !== 0) return hi;
      do {
        const mid = (lo + hi) >>> 1;
        if (compare2(a[mid], x) <= 0) lo = mid + 1;
        else hi = mid;
      } while (lo < hi);
    }
    return lo;
  }

  function center(a, x, lo = 0, hi = a.length) {
    const i = left(a, x, lo, hi - 1);
    return i > lo && delta(a[i - 1], x) > -delta(a[i], x) ? i - 1 : i;
  }

  return {left, center, right};
}

function zero() {
  return 0;
}

function range(start, stop, step) {
  start = +start, stop = +stop, step = (n = arguments.length) < 2 ? (stop = start, start = 0, 1) : n < 3 ? 1 : +step;

  var i = -1,
      n = Math.max(0, Math.ceil((stop - start) / step)) | 0,
      range = new Array(n);

  while (++i < n) {
    range[i] = start + i * step;
  }

  return range;
}

const ASM_SPICE_LITE = 0;
const ASM_SPICE_FULL = 1;

const INT_SIZE = 4;
const INT_TYPE = 'i32';

const DOUBLE_SIZE = 8;
const DOUBLE_TYPE = 'double';

let bufferFileCount = 0;
class Spice {
    constructor() {
        this._fileMap = {};
        this._readyResolve = null;
        this.module = null;
        this.ready = false;
        this.whenReady = new Promise(resolve => {
            this._readyResolve = resolve;
        });
        this.onStdOut = (...args) => console.log(...args);
        this.onStdErr = (...args) => console.error(...args);
    }

    // initialize the module
    init(type = ASM_SPICE_LITE) {
        if (this.module !== null) {
            throw new Error('Spice: Class already initialized with an existing Module.');
        }

        let promise;
        switch(type) {
            case ASM_SPICE_LITE:
                promise = import('./asm_lite-gdeoKYMt.js');
                break;
            case ASM_SPICE_FULL:
                promise = import('./asm_full-C-bKvsyY.js');
                break;
            default:
                throw new Error(`Spice: Unsupported SPICE module type enumeration ${type}`);
        }

        return promise.then(m => {
            return this.initFromFactory(m.default);
        });
    }

    initFromFactory(createModule) {
        if (this.module !== null) {
            throw new Error('Spice: Class already initialized with an existing Module.');
        }

        return createModule({
            print: (...args) => this.onStdOut(...args),
            printErr: (...args) => this.onStdErr(...args),
        }).then(module => {
            this.module = module;
            this.ready = true;
            this._readyResolve(this);
            return this;
        });
    }

    // Convenience Functions
    // loading kernels
    loadKernel(buffer, key = null) {
        const Module = this.module;
        const FS = Module.FS;
        const fileMap = this._fileMap;

        if (key !== null && key in fileMap) {
            throw new Error(`Kernel with key "${key}" has already been loaded.`);
        }

        if (buffer instanceof ArrayBuffer) {
            buffer = new Uint8Array(buffer);
        }

        const path = `_buffer_${ bufferFileCount }.bin`;
        bufferFileCount++;

        if (key !== null) {
            fileMap[key] = path;
        }

        FS.writeFile(path, buffer, { encoding: 'binary' });
        this.furnsh(path);
    }

    // unloading kernel
    unloadKernel(key) {
        const Module = this.module;
        const FS = Module.FS;
        const fileMap = this._fileMap;

        if (!(key in fileMap)) {
            throw new Error();
        }

        this.unload(fileMap[key]);
        FS.unlink(fileMap[key]);
        delete fileMap[key];
    }

    // Chronos CLI
    // https://naif.jpl.nasa.gov/pub/naif/toolkit_docs/C/ug/chronos.html
    chronos(inptim, cmdlin) {
        const Module = this.module;
        const outtim_ptr = Module._malloc(256);
        const intptr = Module._malloc(4);

        Module.setValue(intptr, 1, 'i32');
        Module.ccall(
            'cronos_',
            'number',
            ['string', 'number', 'string', 'number', 'number', 'number', 'number'],
            [cmdlin, intptr, inptim, outtim_ptr, cmdlin.length, inptim.length, 256],
        );

        const ret = Module.UTF8ToString(outtim_ptr, 256);
        Module._free(outtim_ptr);
        Module._free(intptr);

        return ret.trim();
    }

    // Wrapped spice functions
    /**
     * @func b1900
     * @desc Return the Julian Date corresponding to Besselian Date 1900.0.
     * @returns {number} 2415020.31352
     */
    b1900() {
        const Module = this.module;
        return Module.ccall(
            'b1900_c',
            'number',
            [],
            [],
        );
    }

    /**
     * @func b1950
     * @desc Return the Julian Date corresponding to Besselian Date 1950.0.
     * @returns {number} 2433282.42345905
    */
    b1950() {
        const Module = this.module;
        return Module.ccall(
            'b1950_c',
            'number',
            [],
            [],
        );
    }

    /**
     * @func bodc2n
     * @desc Translate the SPICE integer code of a body into a common name
     * @param {number} code - The NAIF ID code of then body.
     * @returns {string | undefined} The name of the body if it exists, otherwise undefined.
     */
    bodc2n(code) {
        const Module = this.module;
        const name_ptr = Module._malloc(100);
        const found_ptr = Module._malloc(INT_SIZE);
        Module.ccall(
            'bodc2n_c',
            null,
            ['number', 'number', 'number', 'number'],
            [code, 100, name_ptr, found_ptr],
        );
        const found = Module.getValue(found_ptr, INT_TYPE);
        const name = Module.UTF8ToString(name_ptr, 100);
        Module._free(name_ptr);
        Module._free(found_ptr);

        return { name, found };
    }

    /**
     * @func bodc2s
     * @desc Translate a body ID code to either the corresponding name or if no
    name to ID code mapping exists, the string representation of the
    body ID value.
    * @param {number} code - The NAIF ID code of then body.
    * @returns {string} The name of the body if it exists, otherwise the number as a string.
    */
    bodc2s(code) {
        const Module = this.module;
        const name_ptr = Module._malloc(100);
        Module.ccall(
            'bodc2s_c',
            null,
            ['number', 'number', 'number'],
            [code, 100, name_ptr],
        );
        const name = Module.UTF8ToString(name_ptr, 100);
        Module._free(name_ptr);
        return name;
    }

    /* boddef:    Define a body name/ID code pair for later translation via
    bodn2c_c or bodc2n_c.
    */
    /**
     * @todo Document and test this!
     */
    boddef(name, code) {
        const Module = this.module;
        Module.ccall(
            'boddef_c',
            null,
            ['string', 'number'],
            [name, code],
        );
    }

    /* bodfnd:    Determine whether values exist for some item for any body
    in the kernel pool.
    */
    /**
     * @todo Document and test this!
     */
    bodfnd(body, item) {
        const Module = this.module;
        return Module.ccall(
            'bodfnd_c',
            'number',
            ['number', 'string'],
            [body, item],
        );
    }

    /* bodn2c:    Translate the name of a body or object to the corresponding SPICE
    integer ID code.
    */
    /**
     * @func bodn2c
     * @desc Translate the name of a body or object to the corresponding SPICE integer ID code.
     * @param {name} name - The common name of the body.
     * @returns {number | undefined} The SPICE ID of the body if it exists, otherwise undefined.
     */
    bodn2c(name) {
        const Module = this.module;
        const code_ptr = Module._malloc(INT_SIZE);
        const found_ptr = Module._malloc(INT_SIZE);
        Module.ccall(
            'bodn2c_c',
            null,
            ['string', 'number', 'number'],
            [name, code_ptr, found_ptr],
        );
        const found = Module.getValue(found_ptr, INT_TYPE);
        const code = Module.getValue(code_ptr, INT_TYPE);
        Module._free(found_ptr);
        Module._free(code_ptr);

        return { code, found };
    }

    /* bods2c:    Translate a string containing a body name or ID code to an integer
    code.
    */
    /**
     * @func bods2c
     * @desc Translate the name of a body or object to the corresponding SPICE integer ID code.
     * @param {name} name - The common name of a body or its code as a string.
     * @returns {number | undefined} If a body name was passed in, the SPICE ID of the body if it exists, otherwise undefined. If a string number was passed in, the number as an integer.
     */
    bods2c(name) {
        const Module = this.module;
        const code_ptr = Module._malloc(INT_SIZE);
        const found_ptr = Module._malloc(INT_SIZE);
        Module.ccall(
            'bods2c_c',
            null,
            ['string', 'number', 'number'],
            [name, code_ptr, found_ptr],
        );
        const found = Module.getValue(found_ptr, INT_TYPE);
        const code = Module.getValue(code_ptr, INT_TYPE);
        Module._free(code_ptr);
        Module._free(found_ptr);

        return { code, found };
    }

    /* bodvcd:
    Fetch from the kernel pool the double precision values of an item
    associated with a body, where the body is specified by an integer ID
    code.
    */
    /**
     * @todo Document and test this!
     */
    bodvcd(bodyid, item, maxn) {
        const Module = this.module;
        const dim_ptr = Module._malloc(DOUBLE_SIZE);
        const values_ptr = Module._malloc(DOUBLE_SIZE * maxn);
        Module.ccall(
            'bodvcd_c',
            null,
            ['number', 'string', 'number', 'number', 'number'],
            [bodyid, item, maxn, dim_ptr, values_ptr],
        );
        const ret = [];
        for (let i = 0; i < Module.getValue(dim_ptr, INT_TYPE); i++) {
            const Module = this.module;
            ret.push(Module.getValue(values_ptr + i * DOUBLE_SIZE, DOUBLE_TYPE));
        }
        Module._free(dim_ptr);
        Module._free(values_ptr);

        return ret;
    }

    /* bodvrd:
    Fetch from the kernel pool the double precision values
    of an item associated with a body.
    */
    /**
     * @todo Document and test this!
     */
    bodvrd(body, item, maxn) {
        const Module = this.module;
        const valuesptr = Module._malloc(DOUBLE_SIZE * maxn);
        const dimptr = Module._malloc(INT_SIZE);
        Module.ccall(
            'bodvrd_c',
            null,
            ['string', 'string', 'number', 'number', 'number'],
            [body, item, maxn, dimptr, valuesptr],
        );
        const ret = [];
        for (let i = 0; i < Module.getValue(dimptr, INT_TYPE); i++) {
            const Module = this.module;
            ret.push(Module.getValue(valuesptr + i * DOUBLE_SIZE, DOUBLE_TYPE));
        }
        Module._free(valuesptr);
        Module._free(dimptr);

        return ret;
    }

    /* convrt:
        Take a measurement X, the units associated with
        X, and units to which X should be converted; return Y ---
        the value of the measurement in the output units.
    */
    /**
     * @func convrt
     * @desc Take a measurement X, the units associated with X, and units to which X should be converted; return the value of the measurement in the output units.
     * @param {number} x - The number in units of in_var to convert.
     * @param {string} in_var - The kind of units x is in. Acceptable units are:

        Angles:                 "RADIANS"
                                "DEGREES"
                                "ARCMINUTES"
                                "ARCSECONDS"
                                "HOURANGLE"
                                "MINUTEANGLE"
                                "SECONDANGLE"

        Metric Distances:       "METERS"
                                "KM"
                                "CM"
                                "MM"

        English Distances:      "FEET"
                                "INCHES"
                                "YARDS"
                                "STATUTE_MILES"
                                "NAUTICAL_MILES"

        Astrometric Distances:  "AU"
                                "PARSECS"
                                "LIGHTSECS"
                                "LIGHTYEARS" julian lightyears

        Time:                   "SECONDS"
                                "MINUTES"
                                "HOURS"
                                "DAYS"
                                "JULIAN_YEARS"
                                "TROPICAL_YEARS"
                                "YEARS" (same as julian years)

        The case of the string in is not significant.
    * @param {string} out - The kind of units for the output to be in. The same kinds of units are valid.
    * @returns {number} The value of x measure in the new units.
    */
    convrt(x, in_var, out) {
        const Module = this.module;
        const y_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'convrt_c',
            null,
            ['number', 'string', 'string', 'number'],
            [x, in_var, out, y_ptr],
        );
        const ret = Module.getValue(y_ptr, DOUBLE_TYPE);
        Module._free(y_ptr);
        return ret;
    }

    /**
     * @func deltet
     * @desc Return the value of Delta ET (ET-UTC) for an input epoch.
     * @param {number} epoch - Input epoch (seconds past J2000).
     * @param {string} eptype - Type of input epoch ("UTC" or "ET"). "UTC": epoch is in UTC seconds past J2000 UTC. "ET": epoch is in Ephemeris seconds past J2000 TDB.
     * @returns {number} Delta ET (ET-UTC) at input epoch
     */
    deltet(epoch, eptype) {
        const Module = this.module;
        const delta_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'deltet_c',
            null,
            ['number', 'string', 'number'],
            [epoch, eptype, delta_ptr],
        );
        const delta = Module.getValue(delta_ptr, DOUBLE_TYPE);
        Module._free(delta_ptr);
        return delta;
    }

    /* erract:    Retrieve or set the default error action.
    */
    /**
     * @todo Document and test this!
     */
    erract(op, action = '') {
        const Module = this.module;
        const action_ptr = Module._malloc(100);
        Module.stringToUTF8(action, action_ptr, 100);

        Module.ccall(
            'erract_c',
            null,
            ['string', 'number', 'number'],
            [op, 100, action_ptr],
        );

        const result = Module.UTF8ToString(action_ptr, 100);
        Module._free(action_ptr);
        return result;
    }

    errprt(op, list = '') {
        const Module = this.module;
        const list_ptr = Module._malloc(100);
        Module.stringToUTF8(list, list_ptr, 100);

        Module.ccall(
            'errprt_c',
            null,
            /* ConstSpiceChar op, SpiceInt lenout, SpiceChar list */
            ['string', 'number', 'number' ],
            [op, 100, list_ptr],
        );

        const result = Module.UTF8ToString(list_ptr, 100);
        Module._free(list_ptr);
        return result;
    }

    /* et2lst:
    Given an ephemeris epoch, compute the local solar time for
    an object on the surface of a body at a specified longitude.
    */
    /**
     * @func et2lst
     * @summary Given an ephemeris epoch, compute the local true solar time for an object on the surface of a body at a specified longitude.
     * @desc  In the planetographic coordinate system, longitude is defined using
    the spin sense of the body.  Longitude is positive to the west if
    the spin is prograde and positive to the east if the spin is
    retrograde.  The spin sense is given by the sign of the first degree
    term of the time-dependent polynomial for the body's prime meridian
    Euler angle "W":  the spin is retrograde if this term is negative
    and prograde otherwise.  For the sun, planets, most natural
    satellites, and selected asteroids, the polynomial expression for W
    may be found in a SPICE PCK kernel.

    The earth, moon, and sun are exceptions: planetographic longitude
    is measured positive east for these bodies.
    * @param {number} et - The time to convert in Ephemeris seconds past J2000.
    * @param {number} body - The NAIF ID of the body to find the local solar time on.
    * @param {number} lon - The longitude to observe from, measured in radians.
    * @param {string} type - "PLANETOCENTRIC" or "PLANETOGRAPHIC".
    * @returns {object} An object with the following valued: hr - the number of hours (24 hours lock), mn - the number of minutes, sc - the number of seconds, time - the local true solar time string in a 24 hour clock, and ampm - then local true solar time string in a 12 hour clock.
    */
    et2lst(et, body, lon, type) {
        const Module = this.module;
        const hr_ptr = Module._malloc(INT_SIZE);
        const mn_ptr = Module._malloc(INT_SIZE);
        const sc_ptr = Module._malloc(INT_SIZE);
        const time_ptr = Module._malloc(100);
        const ampm_ptr = Module._malloc(100);
        Module.ccall(
            'et2lst_c',
            null,
            ['number', 'number', 'number', 'string', 'number', 'number', 'number', 'number', 'number', 'number', 'number'],
            [et, body, lon, type, 100, 100, hr_ptr, mn_ptr, sc_ptr, time_ptr, ampm_ptr],
        );
        const ampm = Module.UTF8ToString(ampm_ptr, 100);
        const time = Module.UTF8ToString(time_ptr, 100);
        const sc = Module.getValue(sc_ptr, INT_TYPE);
        const mn = Module.getValue(mn_ptr, INT_TYPE);
        const hr = Module.getValue(hr_ptr, INT_TYPE);
        Module._free(hr_ptr);
        Module._free(mn_ptr);
        Module._free(sc_ptr);
        Module._free(time_ptr);
        Module._free(ampm_ptr);

        return { hr, mn, sc, time, ampm };
    }

    /**
     * @func et2utc
     * @desc Convert an input time from ephemeris seconds past J2000 to Calendar, Day-of-Year, or Julian Date format, UTC.
     * @param {number} et - Input epoch, given in ephemeris seconds past J2000.
     * @param {string} format - Format of output epoch. May be any of the following:
     *
     *        "C" - Calendar format, UTC.
     *
     *        "D" - Day-of-Year format, UTC.
     *
     *        "J" - Julian Date format, UTC.
     *
     *        "ISOC" - ISO Calendar format, UTC.
     *
     *        "ISOD" - ISO Day-of-Year format, UTC.
     * @param {number} prec - Digits of precision in fractional seconds or days. Must be between 0 and 14, inclusive. Determines to how many decimal places the UTC time will be calculated.
     * @returns {string} The corresponding time in UTC.
     */
    et2utc(et, format, prec) {
        const Module = this.module;
        const utcstr_ptr = Module._malloc(100);
        Module.ccall(
            'et2utc_c',
            null,
            ['number', 'string', 'number', 'number', 'number'],
            [et, format, prec, 100, utcstr_ptr],
        );
        const utcstr = Module.UTF8ToString(utcstr_ptr, 100);
        Module._free(utcstr_ptr);
        return utcstr;
    }

    /* etcal:    Convert from an ephemeris epoch measured in seconds past
    the epoch of J2000 to a calendar string format using a
    formal calendar free of leapseconds.
    */
    /**
     * @func etcal
     * @desc Convert from an ephemeris epoch measured in seconds past the epoch of J2000 to a calendar string format using a formal calendar free of leapseconds.
     * @param {number} et - An ephemeris epoch in seconds past J2000
     * @ returns {string} The corresponding time in calendar format (Year Month Day Time)
     */
    etcal(et) {
        const Module = this.module;
        const string_ptr = Module._malloc(100);
        Module.ccall(
            'etcal_c',
            null,
            ['number', 'number', 'number'],
            [et, 100, string_ptr],
        );
        const string = Module.UTF8ToString(string_ptr, 100);
        Module._free(string_ptr);
        return string;
    }

    /* failed: True if an error condition has been signaled via sigerr_c.
    failed_c is the CSPICE status indicator
    */
    /**
     * @todo Document and test this!
     */
    failed() {
        const Module = this.module;
        return Module.ccall(
            'failed_c',
            'number',
            [],
            [],
        );
    }

    // Provide SPICE one or more kernels to load
    /**
     * @func furnsh(kernelPaths)/furnish
     * @desc Load one or more SPICE kernels into a program. Files must exists in the memory system or an error will occur.
     * @param {string | array} kernelPaths - Path or array of paths to kernel files.
     */
    furnsh(kernelPath) {
        const Module = this.module;
        Module.ccall(
            'furnsh_c',
            null,
            ['string'],
            [kernelPath],
        );
    }

    unload(kernelPath) {
        const Module = this.module;
        Module.ccall(
            'unload_c',
            null,
            ['string'],
            [kernelPath],
        );
    }

    /* getmsg:
    Retrieve the current short error message,
    the explanation of the short error message, or the
    long error message.
    */
    getmsg(option) {
        const Module = this.module;
        const msg_ptr = Module._malloc(1841);
        Module.ccall(
            'getmsg_c',
            null,
            ['string', 'number', 'number'],
            [option, 1841, msg_ptr],
        );
        const msg = Module.UTF8ToString(msg_ptr, 1841);
        Module._free(msg_ptr);
        return msg;
    }

    /* j1900:    Return the Julian Date of 1899 DEC 31 12:00:00 (1900 JAN 0.5).
    */
    /**
     * @func j1900
     * @desc Return the Julian Date of 1899 DEC 31 12:00:00 (1900 JAN 0.5).
     * @returns {number} 2415020.0
    */
    j1900() {
        const Module = this.module;
        return Module.ccall(
            'j1900_c',
            'number',
            [],
            [],
        );
    }

    /* j1950:    Return the Julian Date of 1950 JAN 01 00:00:00 (1950 JAN 1.0).
    */
    /**
     * @func j1950
     * @desc Return the Julian Date of 1950 JAN 01 00:00:00 (1950 JAN 1.0).
     * @returns {number} 2433282.5
    */
    j1950() {
        const Module = this.module;
        return Module.ccall(
            'j1950_c',
            'number',
            [],
            [],
        );
    }

    /* j2000:    Return the Julian Date of 2000 JAN 01 12:00:00 (2000 JAN 1.5).
    */
    /**
     * @func j2000
     * @desc Return the Julian Date of 2000 JAN 01 12:00:00 (2000 JAN 1.5).
     * @returns {number} 2451545.0
    */
    j2000() {
        const Module = this.module;
        return Module.ccall(
            'j2000_c',
            'number',
            [],
            [],
        );
    }

    /* j2100:    Return the Julian Date of 2100 JAN 01 12:00:00 (2100 JAN 1.5).
    */
    /**
     * @func j2100
     * @desc Return the Julian Date of 2100 JAN 01 12:00:00 (2100 JAN 1.5).
     * @returns {number} 2488070.0
    */
    j2100() {
        const Module = this.module;
        return Module.ccall(
            'j2100_c',
            'number',
            [],
            [],
        );
    }

    /* jyear:    Return the number of seconds in a julian year.
    */
    /**
     * @func jyear
     * @desc Return the number of seconds in a julian year.
     * @returns {number} 31557600
    */
    jyear() {
        const Module = this.module;
        return Module.ccall(
            'jyear_c',
            'number',
            [],
            [],
        );
    }

    /* ltime:
    This routine computes the transmit (or receive) time
    of a signal at a specified target, given the receive
    (or transmit) time at a specified observer. The elapsed
    time between transmit and receive is also returned.
    */
    /**
     * @todo Document and test this!
     */
    ltime(etobs, obs, dir, targ) {
        const Module = this.module;
        const ettarg_ptr = Module._malloc(8);
        const elapsd_ptr = Module._malloc(8);
        Module.ccall(
            'ltime_c',
            null,
            ['number', 'number', 'string', 'number', 'number', 'number'],
            [etobs, obs, dir, targ, ettarg_ptr, elapsd_ptr],
        );
        const elapsd = Module.getValue(elapsd_ptr, 'double');
        const ettarg = Module.getValue(ettarg_ptr, 'double');
        Module._free(elapsd_ptr);
        Module._free(ettarg_ptr);
        return { ettarg, elapsd };
    }

    /* reset:
    Reset the CSPICE error status to a value of "no error."
    As a result, the status routine, failed_c, will return a value
    of SPICEFALSE
    */
    /**
     * @todo Document and test this!
     */
    reset() {
        const Module = this.module;
        Module.ccall(
            'reset_c',
            null,
            [],
            [],
        );
    }

    /* scdecd:
    Convert double precision encoding of spacecraft clock time into
    a character representation.
    */
    /**
     * @func scdecd
     * @desc Spacecraft - decode: Convert double precision encoding of spacecraft clock time into a character representation.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} sclkdp - SCLK time to convert in ticks.
     * @returns {string} The character encoding of time sclkdp for spacecraft sc.
     */
    scdecd(sc, sclkdp) {
        const Module = this.module;
        const sclkch_ptr = Module._malloc(100);
        Module.ccall(
            'scdecd_c',
            null,
            ['number', 'number', 'number', 'number'],
            [sc, sclkdp, 100, sclkch_ptr],
        );
        const sclkch = Module.UTF8ToString(sclkch_ptr, 100);
        Module._free(sclkch_ptr);
        return sclkch;
    }

    /* sce2c:
    Convert ephemeris seconds past J2000 (ET) to continuous encoded
    spacecraft clock (`ticks').  Non-integral tick values may be
    returned.
    */
    /**
     * @func sce2c
     * @desc Spacecraft - ephemeris to clock: Convert ephemeris seconds past J2000 (ET) to continuous encoded spacecraft clock (`ticks').  Non-integral tick values may be returned.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} et - Ephemeris seconds past J2000
     * @returns {number} The corresponding SCLK time for spacecraft sc in clock ticks.
     */
    sce2c(sc, et) {
        const Module = this.module;
        const sclkdp_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'sce2c_c',
            null,
            ['number', 'number', 'number'],
            [sc, et, sclkdp_ptr],
        );
        const sclkdp = Module.getValue(sclkdp_ptr, DOUBLE_TYPE);
        Module._free(sclkdp_ptr);
        return sclkdp;
    }

    /* sce2s:
    Convert an epoch specified as ephemeris seconds past J2000 (ET) to a
    character string representation of a spacecraft clock value (SCLK).
    */
    /**
     * @func sce2s
     * @desc Spacecraft - ephemeris to clock string: Convert an epoch specified as ephemeris seconds past J2000 (ET) to a character string representation of a spacecraft clock value (SCLK).
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} et - Ephemeris seconds past J2000
     * @returns {string} The corresponding SCLK time for spacecraft sc in SLCK string encoding.
     */
    sce2s(sc, et) {
        const Module = this.module;
        const sclkch_ptr = Module._malloc(100);
        Module.ccall(
            'sce2s_c',
            null,
            ['number', 'number', 'number', 'number'],
            [sc, et, 100, sclkch_ptr],
        );
        const sclkch = Module.UTF8ToString(sclkch_ptr, 100);
        Module._free(sclkch_ptr);
        return sclkch;
    }

    /* sce2t:
    Convert ephemeris seconds past J2000 (ET) to integral
    encoded spacecraft clock (`ticks'). For conversion to
    fractional ticks, (required for C-kernel production), see
    the routine sce2c_c.
    */
    /**
     * @func sce2t
     * @desc Spacecraft - ephemeris to ticks: Convert ephemeris seconds past J2000 (ET) to integral encoded spacecraft clock (`ticks'). For conversion to fractional ticks, (required for C-kernel production), see the routine sce2c.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} et - Ephemeris seconds past J2000
     * @returns {number} The corresponding SCLK time for spacecraft sc in clock ticks to the closest integer.
     */
    sce2t(sc, et) {
        const Module = this.module;
        const sclkdp_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'sce2t_c',
            null,
            ['number', 'number', 'number'],
            [sc, et, sclkdp_ptr],
        );
        const ret = Module.getValue(sclkdp_ptr, DOUBLE_TYPE);
        Module._free(sclkdp_ptr);
        return ret;
    }

    /* scencd:
    Encode character representation of spacecraft clock time into a
    double precision number.
    */
    /**
     * @func scencd
     * @desc Spacecraft - encode: Encode character representation of spacecraft clock time into a double precision number.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} sclkch - SCLK time in character encoding.
     * @returns {number} Sclkch in spacecraft ticks.
     */
    scencd(sc, sclkch) {
        const Module = this.module;
        const sclkdp_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'scencd_c',
            null,
            ['number', 'string', 'number'],
            [sc, sclkch, sclkdp_ptr],
        );
        const sclkdp = Module.getValue(sclkdp_ptr, DOUBLE_TYPE);
        Module._free(sclkdp_ptr);
        return sclkdp;
    }

    /* scfmt:
    Convert encoded spacecraft clock ticks to character clock format.
    */
    /**
     * @func scfmt
     * @desc Spacecraft - format: Convert encoded spacecraft clock ticks to character clock format.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} ticks - SCLK time (in ticks) to convert.
     * @returns {string} A string encoding of time ticks for spacecraft sc. Note the important difference between scfmt and scdecd. scdecd converts some number of ticks since the spacecraft clock start
     * time to a character string which includes a partition number. scfmt, which is called by scdecd, does not make use of partition information.
     */
    scfmt(sc, ticks) {
        const Module = this.module;
        const clkstr_ptr = Module._malloc(100);
        Module.ccall(
            'scfmt_c',
            null,
            ['number', 'number', 'number', 'number'],
            [sc, ticks, 100, clkstr_ptr],
        );
        const clkstr = Module.UTF8ToString(clkstr_ptr, 100);
        Module._free(clkstr_ptr);
        return clkstr;
    }

    /* scpart:
    Get spacecraft clock partition information from a spacecraft
    clock kernel file.
    */
    /**
     * @func scpart
     * @desc Get spacecraft clock partition information from a spacecraft clock kernel file.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @returns {object} An object containing two arrays: pstart and pstop. pstart contains the list of partition start times for spacecraft sc and pstop contains the partition stop times.
     */
    scpart(sc) {
        const Module = this.module;
        const nparts_ptr = Module._malloc(INT_SIZE);
        const pstart_ptr = Module._malloc(9999 * DOUBLE_SIZE);
        const pstop_ptr = Module._malloc(9999 * DOUBLE_SIZE);
        Module.ccall(
            'scpart_c',
            null,
            ['number', 'number', 'number', 'number'],
            [sc, nparts_ptr, pstart_ptr, pstop_ptr],
        );
        const pstop = [];
        const pstart = [];
        for (let i = 0; i < Module.getValue(nparts_ptr, INT_TYPE); i++) {
            const Module = this.module;
            pstop.push(Module.getValue(pstop_ptr + i * DOUBLE_SIZE, DOUBLE_TYPE));
            pstart.push(Module.getValue(pstart_ptr + i * DOUBLE_SIZE, DOUBLE_TYPE));
        }
        Module._free(nparts_ptr);
        Module._free(pstart_ptr);
        Module._free(pstop_ptr);

        return { pstart, pstop };
    }

    /* scs2e:
    Convert a spacecraft clock string to ephemeris seconds past
    J2000 (ET).
    */
    /**
     * @func scs2e
     * @desc Spacecraft - string to ephemeris. Convert a spacecraft clock string to ephemeris seconds past J2000 (ET).
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {string} sclkch - String encoded SCLK time
     * @returns {number} The corresponding time in ET seconds past J2000
     */
    scs2e(sc, sclkch) {
        const Module = this.module;
        const et_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'scs2e_c',
            null,
            ['number', 'string', 'number'],
            [sc, sclkch, et_ptr],
        );
        const et = Module.getValue(et_ptr, DOUBLE_TYPE);
        Module._free(et_ptr);
        return et;
    }

    /* sct2e:
    Convert encoded spacecraft clock (`ticks') to ephemeris
    seconds past J2000 (ET).
    */
    /**
     * @func sct2e
     * @desc Spacecraft - ticks to ephemeris. Convert encoded spacecraft clock (`ticks') to ephemeris seconds past J2000 (ET).
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} sclkdp - SCLK time in ticks
     * @returns {number} The corresponding time in ET seconds past J2000
     */
    sct2e(sc, sclkdp) {
        const Module = this.module;
        const et_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'sct2e_c',
            null,
            ['number', 'number', 'number'],
            [sc, sclkdp, et_ptr],
        );
        const et = Module.getValue(et_ptr, DOUBLE_TYPE);
        Module._free(et_ptr);
        return et;
    }

    /* sctiks:
    Convert a spacecraft clock format string to number of "ticks".
    */
    /**
     * @func sctiks
     * @desc Spacecraft - ticks: Convert character representation of spacecraft clock time into a double precision number of ticks.
     * @param {number} sc - NAIF ID of the spacecraft.
     * @param {number} clkstr - SCLK time in character encoding.
     * @returns {number} Corresponding time in SCLK ticks. Note the important difference between scencd and sctiks. scencd converts a clock string to the number of ticks it represents
     * since the beginning of the mission, and so uses partition information. sctiks_c just converts to absolute ticks.
     */
    sctiks(sc, clkstr) {
        const Module = this.module;
        const ticks_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'sctiks_c',
            null,
            ['number', 'string', 'number'],
            [sc, clkstr, ticks_ptr],
        );
        const ticks = Module.getValue(ticks_ptr, DOUBLE_TYPE);
        Module._free(ticks_ptr);
        return ticks;
    }

    /* spd:    Return the number of seconds in a day.
    */
    /**
     * @func spd
     * @desc Return the number of seconds in a day.
     * @returns {number} 86400
    */
    spd() {
        const Module = this.module;
        return Module.ccall(
            'spd_c',
            'number',
            [],
            [],
        );
    }

    /* str2et:    Convert a string representing an epoch to a double precision
    value representing the number of TDB seconds past the J2000
    epoch corresponding to the input epoch.
    */
    /**
     * @func str2et
     * @desc Convert a string representing an epoch in UTC to a double precision value representing the number of TDB seconds past the J2000 epoch corresponding to the input epoch.
     * @param {string} str - A UTC epoch in calendar format
     * @returns {number} The corresponding time in ET seconds past J2000.
     */
    str2et(str) {
        const Module = this.module;
        const et_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'str2et_c',
            null,
            ['string', 'number'],
            [str, et_ptr],
        );
        const et = Module.getValue(et_ptr, DOUBLE_TYPE);
        Module._free(et_ptr);
        return et;
    }

    /* timdef:
    Set and retrieve the defaults associated with calendar
    input strings.
    */
    /**
     * @todo Document and test this!
     */
    timdef(action, item, value) {
        const Module = this.module;
        const value_ptr = Module._malloc(100);
        Module.stringToUTF8(value, value_ptr, 100);
        Module.ccall(
            'timdef_c',
            null,
            ['string', 'string', 'number', 'number'],
            [action, item, 100, value_ptr],
        );

        const valueOut = Module.UTF8ToString(value_ptr, 100);
        Module._free(value_ptr);
        return valueOut;
    }

    /* timout:
    This routine converts an input epoch represented in TDB seconds
    past the TDB epoch of J2000 to a character string formatted to
    the specifications of a user's format picture.
    */
    /**
     * @func timout
     * @desc This routine converts an input epoch represented in TDB seconds past the TDB epoch of J2000 to a character string formatted to the specifications of a user's format picture.
     * @param {number} et - Time in ET seconds past J2000.
     * @param {string} pictur - The format describing how the time should returned. For example, "Mon DD, YYYY AP:MN:SC AMPM" might result in "Nov 19, 2014 06:12:08 P.M.".
     * @returns {string} The time formatted to fit to pictur.
     */
    timout(et, pictur) {
        const Module = this.module;
        const output_ptr = Module._malloc(100);
        Module.ccall(
            'timout_c',
            null,
            ['number', 'string', 'number', 'number'],
            [et, pictur, 100, output_ptr],
        );
        const output = Module.UTF8ToString(output_ptr, 100);
        Module._free(output_ptr);
        return output;
    }

    /* tparse:
    Parse a time string and return seconds past the J2000 epoch
    on a formal calendar.
    */
    /**
     * @todo Document and test this!
     */
    tparse(string) {
        const Module = this.module;
        const sp2000_ptr = Module._malloc(DOUBLE_SIZE);
        const errmsg_ptr = Module._malloc(2000);
        Module.ccall(
            'tparse_c',
            null,
            ['string', 'number', 'number', 'number'],
            [string, 2000, sp2000_ptr, errmsg_ptr],
        );
        const errmsg = Module.UTF8ToString(errmsg_ptr, 2000);
        const sp2000 = Module.getValue(sp2000_ptr, DOUBLE_TYPE);
        Module._free(errmsg_ptr);
        Module._free(sp2000_ptr);

        return { sp2000, errmsg };
    }

    /* tpictr:
    Given a sample time string, create a time format picture
    suitable for use by the routine timout_c.
    */
    /**
     * @func tpictr
     * @desc Given a sample time string, create a time format picture suitable for use by the routine timout.
     * @param {string} sample - A time string that conforms to the desired format. For example, "Oct 24, 1994 23:45:12 PM" becomes "Mon DD, YYYY AP:MN:SC AMPM".
     * @returns {string} A correctly formatted picture to be passed into timout for time conversion.
     */
    tpictr(sample) {
        const Module = this.module;
        const picture_ptr = Module._malloc(100);
        const ok_ptr = Module._malloc(INT_SIZE);
        const errmsg_ptr = Module._malloc(2000);
        Module.ccall(
            'tpictr_c',
            null,
            ['string', 'number', 'number', 'number', 'number', 'number'],
            [sample, 100, 2000, picture_ptr, ok_ptr, errmsg_ptr],
        );
        const picture = Module.UTF8ToString(picture_ptr, 100);
        const ok = Module.getValue(ok_ptr, INT_TYPE);
        const errmsg = Module.UTF8ToString(errmsg_ptr, 2000);
        Module._free(picture_ptr);
        Module._free(ok_ptr);
        Module._free(errmsg_ptr);

        return { picture, ok, errmsg };
    }

    /* tsetyr:   Set the lower bound on the 100 year range
    */
    /**
     * @todo Document and test this!
     */
    tsetyr(year) {
        const Module = this.module;
        Module.ccall(
            'tsetyr_c',
            null,
            ['number' ],
            [year],
        );
    }

    /* tyear:
    Return the number of seconds in a tropical year.
    */
    /**
     * @func tyear
     * @desc Return the number of seconds in a tropical year.
     * @returns {number} 31556925.9747
    */
    tyear() {
        const Module = this.module;
        return Module.ccall(
            'tyear_c',
            'number',
            [],
            [],
        );
    }

    /* unitim:    Transform time from one uniform scale to another.  The uniform
    time scales are TAI, TDT, TDB, ET, JED, JDTDB, JDTDT.
    */
    /**
     * @fund unitim
     * @desc Transform time from one uniform scale to another. The uniform time scales are TAI, TDT, TDB, ET, JED, JDTDB, JDTDT.
     * @param {number} epoch - The epoch to convert from
     * @param {string} insys - The time system the input epoch is in ("TAI", "TDT", "TDB", "ET", "JED", "JDTDB", or "JDTDT").
     * @param {string} outsys - The time system the output should be in ("TAI", "TDT", "TDB", "ET", "JED", "JDTDB", or "JDTDT").
     * @returns {number} The corresponding time in the outsys scale.
     */
    unitim(epoch, insys, outsys) {
        const Module = this.module;
        return Module.ccall(
            'unitim_c',
            'number',
            ['number', 'string', 'string'],
            [epoch, insys, outsys],
        );
    }

    /* utc2et:    Convert an input time from Calendar or Julian Date format, UTC,
    to ephemeris seconds past J2000.
    */
    /**
     * @func utc2et
     * @desc Convert an input time from Calendar or Julian Date format, UTC, to ephemeris seconds past J2000.
     * @param {string} utcstr - A UTC time in calendar or Julian date format
     * @returns {number} The corresponding time in ET seconds past J2000.
     */
    utc2et(utcstr) {
        const Module = this.module;
        const et_ptr = Module._malloc(DOUBLE_SIZE);
        Module.ccall(
            'utc2et_c',
            null,
            ['string', 'number'],
            [utcstr, et_ptr],
        );
        const et = Module.getValue(et_ptr, DOUBLE_TYPE);
        Module._free(et_ptr);
        return et;
    }

    spkpos(targ, et, ref, abcorr, obs) {
        const Module = this.module;
        // create output pointers
        const ptarg_ptr = Module._malloc(DOUBLE_SIZE * 3);
        const lt_ptr = Module._malloc(DOUBLE_SIZE);

        Module.ccall(
            'spkpos_c',
            null,
            /* ConstSpiceChar targ, SpiceDouble et, ConstSpiceChar ref, ConstSpiceChar abcorr, ConstSpiceChar obs, SpiceDouble ptarg, SpiceDouble lt */
            [ 'string', 'number', 'string', 'string', 'string', 'number', 'number' ],
            [ targ, et, ref, abcorr, obs, ptarg_ptr, lt_ptr ],
        );

        // read and free output pointers
        const ptarg = [
            Module.getValue( ptarg_ptr + DOUBLE_SIZE * 0, 'double' ),
            Module.getValue( ptarg_ptr + DOUBLE_SIZE * 1, 'double' ),
            Module.getValue( ptarg_ptr + DOUBLE_SIZE * 2, 'double' ),
        ];
        Module._free( ptarg_ptr );

        const lt = Module.getValue( lt_ptr, 'double' );
        Module._free( lt_ptr );

        return { ptarg, lt };
    }

}

// const LMST_SPACECRAFT_ID: number = -168900; // Perseverence Rover Spacecraft ID
var SPACECRAFT_ID = 168; // Perseverence Rover Spacecraft ID
var LMST_SPACECRAFT_ID = parseInt("-".concat(SPACECRAFT_ID, "900 "), 10);
var SPICE_LMST_RE = /^\d\/(\d+):(\d{2}):(\d{2}):(\d{2}):(\d+)?$/;
var DISPLAY_LMST_RE = /^(Sol-)?(\d+)M(\d{2}):(\d{2}):(\d{2})(.(\d*))?$/;
var LMST_FORMAT_STRING = "DDDDDMHH:MM:SS";
// const SCLK_REGEX: RegExp =
//   /^\d\/(?<seconds>\d+)(-|\\.|:|,|\\s)(?<fraction>\d+)$/;
var spiceInstance = undefined;
// Mars seconds since Sol-0
function msss0(lmst) {
    var sols = +lmst.split("M")[0];
    var hours = +lmst.split("M")[1].split(":")[0];
    var minutes = +lmst.split("M")[1].split(":")[1];
    var seconds = +lmst.split("M")[1].split(":")[2];
    var sss0 = sols * 86400 + hours * 3600 + minutes * 60 + seconds;
    return sss0;
}
function msss0_to_lmst(msss0) {
    var sols = String(Math.floor(msss0 / 86400));
    var secondsLeft = msss0 % 86400;
    var hours = String(Math.floor(secondsLeft / 3600));
    secondsLeft = secondsLeft % 3600;
    var minutes = String(Math.floor(secondsLeft / 60));
    secondsLeft = secondsLeft % 60;
    var seconds = String(secondsLeft.toFixed(2));
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
    var lmst = sols + "M" + hours + ":" + minutes + ":" + seconds;
    return lmst;
}
function trimLeadingZeroes(s) {
    return parseInt(s, 10).toString(10);
}
function lmstToEphemeris(lmst) {
    var matcher = lmst.match(DISPLAY_LMST_RE);
    if (!matcher) {
        return NaN;
    }
    var sol = trimLeadingZeroes(matcher[2] || "");
    var hour = matcher[3] || "";
    var mins = matcher[4] || "";
    var secs = matcher[5] || "";
    var subsecs = parseFloat(matcher[6] || "0")
        .toFixed(5)
        .substring(2);
    var sclkch = "".concat(sol, ":").concat(hour, ":").concat(mins, ":").concat(secs, ":").concat(subsecs);
    // const sclkch = sol + ':' + hour + ':' + mins + ':' + secs + ':' + subsecs;
    return spiceInstance.scs2e(LMST_SPACECRAFT_ID, sclkch);
}
function ephemerisToLMST(et) {
    var lmst = spiceInstance.sce2s(LMST_SPACECRAFT_ID, et);
    // something like "1/01641:07:16:13:65583"
    var m = lmst.match(SPICE_LMST_RE);
    if (m) {
        var sol = trimLeadingZeroes(m[1]);
        var hour = m[2];
        var mins = m[3];
        var secs = m[4];
        var subsecs = m[5] || "0";
        return sol + "M" + hour + ":" + mins + ":" + secs + "." + subsecs;
    }
    return "";
}
function ephemerisToUTC(et) {
    return new Date(spiceInstance.et2utc(et, "ISOC", 100) + "Z");
}
function lmstToUTC(lmst) {
    if (spiceInstance) {
        try {
            var et = lmstToEphemeris(lmst);
            return ephemerisToUTC(et);
        }
        catch (error) {
            console.log("error :>> ", error);
        }
    }
    return new Date();
}
function utcStringToLmst(utc) {
    if (spiceInstance) {
        try {
            var et = spiceInstance.str2et(utc);
            return ephemerisToLMST(et);
        }
        catch (error) {
            console.error(error);
            return "";
        }
    }
    return "no spice";
}
function lmstTicks(start, stop, tickCount) {
    var lmstStart = utcStringToLmst(start.toISOString().slice(0, -1));
    var lmstEnd = utcStringToLmst(stop.toISOString().slice(0, -1));
    var lsmtStartSeconds = msss0(lmstStart);
    var lsmtStartSols = lsmtStartSeconds / 60 / 60 / 24;
    var lsmtEndSeconds = msss0(lmstEnd);
    var lsmtEndSols = lsmtEndSeconds / 60 / 60 / 24;
    // TODO handle duration = 0 case
    var lmstDurationSeconds = lsmtEndSeconds - lsmtStartSeconds;
    var stepSize;
    var stepSizeSols = lmstDurationSeconds / 60 / 60 / 24 / tickCount;
    var dayInSeconds = 86400;
    var lmstSteps = [
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
    var bisectTicks = bisector(function (d) { return d; }).left;
    var i = bisectTicks(lmstSteps, stepSizeSols, 0);
    stepSize = lmstSteps[i];
    // round the domain to nearest step size values
    var minValRounded = Math.round(lsmtStartSols / stepSize) * stepSize;
    var maxValRounded = Math.round(lsmtEndSols / stepSize) * stepSize;
    var ticks = range(minValRounded, maxValRounded, stepSize)
        .map(function (x) { return lmstToUTC(msss0_to_lmst(x * 24 * 60 * 60)); })
        .filter(function (date) {
        return date.getTime() >= start.getTime() && date.getTime() <= stop.getTime();
    });
    return ticks;
}
function initializeSpice() {
    return __awaiter(this, void 0, void 0, function () {
        var initializingSpice, kernelBuffers, i, error_1;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    _a.trys.push([0, 3, , 4]);
                    return [4 /*yield*/, new Spice().init()];
                case 1:
                    initializingSpice = _a.sent();
                    return [4 /*yield*/, Promise.all([
                            "/resources/kernels/m2020_lmst_ops210303_v1.tsc",
                            "/resources/kernels/m2020.tls",
                            "/resources/kernels/m2020.tsc",
                        ].map(function (url) { return fetch(url).then(function (res) { return res.arrayBuffer(); }); }))];
                case 2:
                    kernelBuffers = _a.sent();
                    // Load the kernels into Spice
                    for (i = 0; i < kernelBuffers.length; i++) {
                        initializingSpice.loadKernel(kernelBuffers[i]);
                    }
                    spiceInstance = initializingSpice;
                    console.log("Spice initialized");
                    return [2 /*return*/, true];
                case 3:
                    error_1 = _a.sent();
                    console.log("Error initializing Spice:", error_1);
                    return [2 /*return*/, false];
                case 4: return [2 /*return*/];
            }
        });
    });
}
function validateLMSTString(value) {
    return new Promise(function (resolve) {
        var match = DISPLAY_LMST_RE.exec(value);
        var error = "LMST format required: ".concat(LMST_FORMAT_STRING);
        return match ? resolve(null) : resolve(error);
    });
}
function getPlugin() {
    return __awaiter(this, void 0, void 0, function () {
        var success;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0: return [4 /*yield*/, initializeSpice()];
                case 1:
                    success = _a.sent();
                    if (success) {
                        return [2 /*return*/, {
                                time: {
                                    primary: {
                                        format: function (date) {
                                            var dateWithoutTZ = date.toISOString().slice(0, -1);
                                            return utcStringToLmst(dateWithoutTZ).slice(0, -6);
                                        },
                                        formatString: LMST_FORMAT_STRING,
                                        label: "LMST",
                                        parse: lmstToUTC,
                                        validate: validateLMSTString,
                                    },
                                    secondary: {
                                        format: function (date) { return date.toISOString().slice(0, -5); },
                                        label: "UTC",
                                        parse: function (string) { return new Date(string); },
                                    },
                                    // tertiary: {
                                    //   format: (date: Date) => {
                                    //     const dateWithoutTZ = date.toISOString().slice(0, -1);
                                    //     return utcStringToSCLK(dateWithoutTZ);
                                    //   },
                                    //   label: "SCLK",
                                    //   parse: (string: string) => new Date(string),
                                    // },
                                    ticks: {
                                        getTicks: lmstTicks,
                                        tickLabelWidth: 110,
                                    },
                                },
                            }];
                    }
                    else {
                        return [2 /*return*/, {}];
                    }
            }
        });
    });
}

export { getPlugin, lmstTicks };
