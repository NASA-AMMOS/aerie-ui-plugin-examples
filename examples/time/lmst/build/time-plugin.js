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

/**
 * @name toDate
 * @category Common Helpers
 * @summary Convert the given argument to an instance of Date.
 *
 * @description
 * Convert the given argument to an instance of Date.
 *
 * If the argument is an instance of Date, the function returns its clone.
 *
 * If the argument is a number, it is treated as a timestamp.
 *
 * If the argument is none of the above, the function returns Invalid Date.
 *
 * **Note**: *all* Date arguments passed to any *date-fns* function is processed by `toDate`.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param argument - The value to convert
 *
 * @returns The parsed date in the local time zone
 *
 * @example
 * // Clone the date:
 * const result = toDate(new Date(2014, 1, 11, 11, 30, 30))
 * //=> Tue Feb 11 2014 11:30:30
 *
 * @example
 * // Convert the timestamp to date:
 * const result = toDate(1392098430000)
 * //=> Tue Feb 11 2014 11:30:30
 */
function toDate(argument) {
  const argStr = Object.prototype.toString.call(argument);

  // Clone the date
  if (
    argument instanceof Date ||
    (typeof argument === "object" && argStr === "[object Date]")
  ) {
    // Prevent the date to lose the milliseconds when passed to new Date() in IE10
    return new argument.constructor(+argument);
  } else if (
    typeof argument === "number" ||
    argStr === "[object Number]" ||
    typeof argument === "string" ||
    argStr === "[object String]"
  ) {
    // TODO: Can we get rid of as?
    return new Date(argument);
  } else {
    // TODO: Can we get rid of as?
    return new Date(NaN);
  }
}

/**
 * @name constructFrom
 * @category Generic Helpers
 * @summary Constructs a date using the reference date and the value
 *
 * @description
 * The function constructs a new date using the constructor from the reference
 * date and the given value. It helps to build generic functions that accept
 * date extensions.
 *
 * It defaults to `Date` if the passed reference date is a number or a string.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The reference date to take constructor from
 * @param value - The value to create the date
 *
 * @returns Date initialized using the given date and value
 *
 * @example
 * import { constructFrom } from 'date-fns'
 *
 * // A function that clones a date preserving the original type
 * function cloneDate<DateType extends Date(date: DateType): DateType {
 *   return constructFrom(
 *     date, // Use contrustor from the given date
 *     date.getTime() // Use the date value to create a new date
 *   )
 * }
 */
function constructFrom(date, value) {
  if (date instanceof Date) {
    return new date.constructor(value);
  } else {
    return new Date(value);
  }
}

/**
 * @module constants
 * @summary Useful constants
 * @description
 * Collection of useful date constants.
 *
 * The constants could be imported from `date-fns/constants`:
 *
 * ```ts
 * import { maxTime, minTime } from "./constants/date-fns/constants";
 *
 * function isAllowedTime(time) {
 *   return time <= maxTime && time >= minTime;
 * }
 * ```
 */


/**
 * @constant
 * @name millisecondsInWeek
 * @summary Milliseconds in 1 week.
 */
const millisecondsInWeek = 604800000;

/**
 * @constant
 * @name millisecondsInDay
 * @summary Milliseconds in 1 day.
 */
const millisecondsInDay = 86400000;

let defaultOptions = {};

function getDefaultOptions() {
  return defaultOptions;
}

/**
 * The {@link startOfWeek} function options.
 */

/**
 * @name startOfWeek
 * @category Week Helpers
 * @summary Return the start of a week for the given date.
 *
 * @description
 * Return the start of a week for the given date.
 * The result will be in the local timezone.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 * @param options - An object with options
 *
 * @returns The start of a week
 *
 * @example
 * // The start of a week for 2 September 2014 11:55:00:
 * const result = startOfWeek(new Date(2014, 8, 2, 11, 55, 0))
 * //=> Sun Aug 31 2014 00:00:00
 *
 * @example
 * // If the week starts on Monday, the start of the week for 2 September 2014 11:55:00:
 * const result = startOfWeek(new Date(2014, 8, 2, 11, 55, 0), { weekStartsOn: 1 })
 * //=> Mon Sep 01 2014 00:00:00
 */
function startOfWeek(date, options) {
  const defaultOptions = getDefaultOptions();
  const weekStartsOn =
    options?.weekStartsOn ??
    options?.locale?.options?.weekStartsOn ??
    defaultOptions.weekStartsOn ??
    defaultOptions.locale?.options?.weekStartsOn ??
    0;

  const _date = toDate(date);
  const day = _date.getDay();
  const diff = (day < weekStartsOn ? 7 : 0) + day - weekStartsOn;

  _date.setDate(_date.getDate() - diff);
  _date.setHours(0, 0, 0, 0);
  return _date;
}

/**
 * @name startOfISOWeek
 * @category ISO Week Helpers
 * @summary Return the start of an ISO week for the given date.
 *
 * @description
 * Return the start of an ISO week for the given date.
 * The result will be in the local timezone.
 *
 * ISO week-numbering year: http://en.wikipedia.org/wiki/ISO_week_date
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 *
 * @returns The start of an ISO week
 *
 * @example
 * // The start of an ISO week for 2 September 2014 11:55:00:
 * const result = startOfISOWeek(new Date(2014, 8, 2, 11, 55, 0))
 * //=> Mon Sep 01 2014 00:00:00
 */
function startOfISOWeek(date) {
  return startOfWeek(date, { weekStartsOn: 1 });
}

/**
 * @name getISOWeekYear
 * @category ISO Week-Numbering Year Helpers
 * @summary Get the ISO week-numbering year of the given date.
 *
 * @description
 * Get the ISO week-numbering year of the given date,
 * which always starts 3 days before the year's first Thursday.
 *
 * ISO week-numbering year: http://en.wikipedia.org/wiki/ISO_week_date
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The given date
 *
 * @returns The ISO week-numbering year
 *
 * @example
 * // Which ISO-week numbering year is 2 January 2005?
 * const result = getISOWeekYear(new Date(2005, 0, 2))
 * //=> 2004
 */
function getISOWeekYear(date) {
  const _date = toDate(date);
  const year = _date.getFullYear();

  const fourthOfJanuaryOfNextYear = constructFrom(date, 0);
  fourthOfJanuaryOfNextYear.setFullYear(year + 1, 0, 4);
  fourthOfJanuaryOfNextYear.setHours(0, 0, 0, 0);
  const startOfNextYear = startOfISOWeek(fourthOfJanuaryOfNextYear);

  const fourthOfJanuaryOfThisYear = constructFrom(date, 0);
  fourthOfJanuaryOfThisYear.setFullYear(year, 0, 4);
  fourthOfJanuaryOfThisYear.setHours(0, 0, 0, 0);
  const startOfThisYear = startOfISOWeek(fourthOfJanuaryOfThisYear);

  if (_date.getTime() >= startOfNextYear.getTime()) {
    return year + 1;
  } else if (_date.getTime() >= startOfThisYear.getTime()) {
    return year;
  } else {
    return year - 1;
  }
}

/**
 * @name startOfDay
 * @category Day Helpers
 * @summary Return the start of a day for the given date.
 *
 * @description
 * Return the start of a day for the given date.
 * The result will be in the local timezone.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 *
 * @returns The start of a day
 *
 * @example
 * // The start of a day for 2 September 2014 11:55:00:
 * const result = startOfDay(new Date(2014, 8, 2, 11, 55, 0))
 * //=> Tue Sep 02 2014 00:00:00
 */
function startOfDay(date) {
  const _date = toDate(date);
  _date.setHours(0, 0, 0, 0);
  return _date;
}

/**
 * Google Chrome as of 67.0.3396.87 introduced timezones with offset that includes seconds.
 * They usually appear for dates that denote time before the timezones were introduced
 * (e.g. for 'Europe/Prague' timezone the offset is GMT+00:57:44 before 1 October 1891
 * and GMT+01:00:00 after that date)
 *
 * Date#getTimezoneOffset returns the offset in minutes and would return 57 for the example above,
 * which would lead to incorrect calculations.
 *
 * This function returns the timezone offset in milliseconds that takes seconds in account.
 */
function getTimezoneOffsetInMilliseconds(date) {
  const _date = toDate(date);
  const utcDate = new Date(
    Date.UTC(
      _date.getFullYear(),
      _date.getMonth(),
      _date.getDate(),
      _date.getHours(),
      _date.getMinutes(),
      _date.getSeconds(),
      _date.getMilliseconds(),
    ),
  );
  utcDate.setUTCFullYear(_date.getFullYear());
  return +date - +utcDate;
}

/**
 * @name differenceInCalendarDays
 * @category Day Helpers
 * @summary Get the number of calendar days between the given dates.
 *
 * @description
 * Get the number of calendar days between the given dates. This means that the times are removed
 * from the dates and then the difference in days is calculated.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param dateLeft - The later date
 * @param dateRight - The earlier date
 *
 * @returns The number of calendar days
 *
 * @example
 * // How many calendar days are between
 * // 2 July 2011 23:00:00 and 2 July 2012 00:00:00?
 * const result = differenceInCalendarDays(
 *   new Date(2012, 6, 2, 0, 0),
 *   new Date(2011, 6, 2, 23, 0)
 * )
 * //=> 366
 * // How many calendar days are between
 * // 2 July 2011 23:59:00 and 3 July 2011 00:01:00?
 * const result = differenceInCalendarDays(
 *   new Date(2011, 6, 3, 0, 1),
 *   new Date(2011, 6, 2, 23, 59)
 * )
 * //=> 1
 */
function differenceInCalendarDays(dateLeft, dateRight) {
  const startOfDayLeft = startOfDay(dateLeft);
  const startOfDayRight = startOfDay(dateRight);

  const timestampLeft =
    +startOfDayLeft - getTimezoneOffsetInMilliseconds(startOfDayLeft);
  const timestampRight =
    +startOfDayRight - getTimezoneOffsetInMilliseconds(startOfDayRight);

  // Round the number of days to the nearest integer because the number of
  // milliseconds in a day is not constant (e.g. it's different in the week of
  // the daylight saving time clock shift).
  return Math.round((timestampLeft - timestampRight) / millisecondsInDay);
}

/**
 * @name startOfISOWeekYear
 * @category ISO Week-Numbering Year Helpers
 * @summary Return the start of an ISO week-numbering year for the given date.
 *
 * @description
 * Return the start of an ISO week-numbering year,
 * which always starts 3 days before the year's first Thursday.
 * The result will be in the local timezone.
 *
 * ISO week-numbering year: http://en.wikipedia.org/wiki/ISO_week_date
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 *
 * @returns The start of an ISO week-numbering year
 *
 * @example
 * // The start of an ISO week-numbering year for 2 July 2005:
 * const result = startOfISOWeekYear(new Date(2005, 6, 2))
 * //=> Mon Jan 03 2005 00:00:00
 */
function startOfISOWeekYear(date) {
  const year = getISOWeekYear(date);
  const fourthOfJanuary = constructFrom(date, 0);
  fourthOfJanuary.setFullYear(year, 0, 4);
  fourthOfJanuary.setHours(0, 0, 0, 0);
  return startOfISOWeek(fourthOfJanuary);
}

/**
 * @name isDate
 * @category Common Helpers
 * @summary Is the given value a date?
 *
 * @description
 * Returns true if the given value is an instance of Date. The function works for dates transferred across iframes.
 *
 * @param value - The value to check
 *
 * @returns True if the given value is a date
 *
 * @example
 * // For a valid date:
 * const result = isDate(new Date())
 * //=> true
 *
 * @example
 * // For an invalid date:
 * const result = isDate(new Date(NaN))
 * //=> true
 *
 * @example
 * // For some value:
 * const result = isDate('2014-02-31')
 * //=> false
 *
 * @example
 * // For an object:
 * const result = isDate({})
 * //=> false
 */
function isDate(value) {
  return (
    value instanceof Date ||
    (typeof value === "object" &&
      Object.prototype.toString.call(value) === "[object Date]")
  );
}

/**
 * @name isValid
 * @category Common Helpers
 * @summary Is the given date valid?
 *
 * @description
 * Returns false if argument is Invalid Date and true otherwise.
 * Argument is converted to Date using `toDate`. See [toDate](https://date-fns.org/docs/toDate)
 * Invalid Date is a Date, whose time value is NaN.
 *
 * Time value of Date: http://es5.github.io/#x15.9.1.1
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The date to check
 *
 * @returns The date is valid
 *
 * @example
 * // For the valid date:
 * const result = isValid(new Date(2014, 1, 31))
 * //=> true
 *
 * @example
 * // For the value, convertable into a date:
 * const result = isValid(1393804800000)
 * //=> true
 *
 * @example
 * // For the invalid date:
 * const result = isValid(new Date(''))
 * //=> false
 */
function isValid(date) {
  if (!isDate(date) && typeof date !== "number") {
    return false;
  }
  const _date = toDate(date);
  return !isNaN(Number(_date));
}

/**
 * @name differenceInDays
 * @category Day Helpers
 * @summary Get the number of full days between the given dates.
 *
 * @description
 * Get the number of full day periods between two dates. Fractional days are
 * truncated towards zero.
 *
 * One "full day" is the distance between a local time in one day to the same
 * local time on the next or previous day. A full day can sometimes be less than
 * or more than 24 hours if a daylight savings change happens between two dates.
 *
 * To ignore DST and only measure exact 24-hour periods, use this instead:
 * `Math.trunc(differenceInHours(dateLeft, dateRight)/24)|0`.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param dateLeft - The later date
 * @param dateRight - The earlier date
 *
 * @returns The number of full days according to the local timezone
 *
 * @example
 * // How many full days are between
 * // 2 July 2011 23:00:00 and 2 July 2012 00:00:00?
 * const result = differenceInDays(
 *   new Date(2012, 6, 2, 0, 0),
 *   new Date(2011, 6, 2, 23, 0)
 * )
 * //=> 365
 *
 * @example
 * // How many full days are between
 * // 2 July 2011 23:59:00 and 3 July 2011 00:01:00?
 * const result = differenceInDays(
 *   new Date(2011, 6, 3, 0, 1),
 *   new Date(2011, 6, 2, 23, 59)
 * )
 * //=> 0
 *
 * @example
 * // How many full days are between
 * // 1 March 2020 0:00 and 1 June 2020 0:00 ?
 * // Note: because local time is used, the
 * // result will always be 92 days, even in
 * // time zones where DST starts and the
 * // period has only 92*24-1 hours.
 * const result = differenceInDays(
 *   new Date(2020, 5, 1),
 *   new Date(2020, 2, 1)
 * )
 * //=> 92
 */
function differenceInDays(dateLeft, dateRight) {
  const _dateLeft = toDate(dateLeft);
  const _dateRight = toDate(dateRight);

  const sign = compareLocalAsc(_dateLeft, _dateRight);
  const difference = Math.abs(differenceInCalendarDays(_dateLeft, _dateRight));

  _dateLeft.setDate(_dateLeft.getDate() - sign * difference);

  // Math.abs(diff in full days - diff in calendar days) === 1 if last calendar day is not full
  // If so, result must be decreased by 1 in absolute value
  const isLastDayNotFull = Number(
    compareLocalAsc(_dateLeft, _dateRight) === -sign,
  );
  const result = sign * (difference - isLastDayNotFull);
  // Prevent negative zero
  return result === 0 ? 0 : result;
}

// Like `compareAsc` but uses local time not UTC, which is needed
// for accurate equality comparisons of UTC timestamps that end up
// having the same representation in local time, e.g. one hour before
// DST ends vs. the instant that DST ends.
function compareLocalAsc(dateLeft, dateRight) {
  const diff =
    dateLeft.getFullYear() - dateRight.getFullYear() ||
    dateLeft.getMonth() - dateRight.getMonth() ||
    dateLeft.getDate() - dateRight.getDate() ||
    dateLeft.getHours() - dateRight.getHours() ||
    dateLeft.getMinutes() - dateRight.getMinutes() ||
    dateLeft.getSeconds() - dateRight.getSeconds() ||
    dateLeft.getMilliseconds() - dateRight.getMilliseconds();

  if (diff < 0) {
    return -1;
  } else if (diff > 0) {
    return 1;
    // Return 0 if diff is 0; return NaN if diff is NaN
  } else {
    return diff;
  }
}

/**
 * @name startOfYear
 * @category Year Helpers
 * @summary Return the start of a year for the given date.
 *
 * @description
 * Return the start of a year for the given date.
 * The result will be in the local timezone.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 *
 * @returns The start of a year
 *
 * @example
 * // The start of a year for 2 September 2014 11:55:00:
 * const result = startOfYear(new Date(2014, 8, 2, 11, 55, 00))
 * //=> Wed Jan 01 2014 00:00:00
 */
function startOfYear(date) {
  const cleanDate = toDate(date);
  const _date = constructFrom(date, 0);
  _date.setFullYear(cleanDate.getFullYear(), 0, 1);
  _date.setHours(0, 0, 0, 0);
  return _date;
}

const formatDistanceLocale = {
  lessThanXSeconds: {
    one: "less than a second",
    other: "less than {{count}} seconds",
  },

  xSeconds: {
    one: "1 second",
    other: "{{count}} seconds",
  },

  halfAMinute: "half a minute",

  lessThanXMinutes: {
    one: "less than a minute",
    other: "less than {{count}} minutes",
  },

  xMinutes: {
    one: "1 minute",
    other: "{{count}} minutes",
  },

  aboutXHours: {
    one: "about 1 hour",
    other: "about {{count}} hours",
  },

  xHours: {
    one: "1 hour",
    other: "{{count}} hours",
  },

  xDays: {
    one: "1 day",
    other: "{{count}} days",
  },

  aboutXWeeks: {
    one: "about 1 week",
    other: "about {{count}} weeks",
  },

  xWeeks: {
    one: "1 week",
    other: "{{count}} weeks",
  },

  aboutXMonths: {
    one: "about 1 month",
    other: "about {{count}} months",
  },

  xMonths: {
    one: "1 month",
    other: "{{count}} months",
  },

  aboutXYears: {
    one: "about 1 year",
    other: "about {{count}} years",
  },

  xYears: {
    one: "1 year",
    other: "{{count}} years",
  },

  overXYears: {
    one: "over 1 year",
    other: "over {{count}} years",
  },

  almostXYears: {
    one: "almost 1 year",
    other: "almost {{count}} years",
  },
};

const formatDistance = (token, count, options) => {
  let result;

  const tokenValue = formatDistanceLocale[token];
  if (typeof tokenValue === "string") {
    result = tokenValue;
  } else if (count === 1) {
    result = tokenValue.one;
  } else {
    result = tokenValue.other.replace("{{count}}", count.toString());
  }

  if (options?.addSuffix) {
    if (options.comparison && options.comparison > 0) {
      return "in " + result;
    } else {
      return result + " ago";
    }
  }

  return result;
};

function buildFormatLongFn(args) {
  return (options = {}) => {
    // TODO: Remove String()
    const width = options.width ? String(options.width) : args.defaultWidth;
    const format = args.formats[width] || args.formats[args.defaultWidth];
    return format;
  };
}

const dateFormats = {
  full: "EEEE, MMMM do, y",
  long: "MMMM do, y",
  medium: "MMM d, y",
  short: "MM/dd/yyyy",
};

const timeFormats = {
  full: "h:mm:ss a zzzz",
  long: "h:mm:ss a z",
  medium: "h:mm:ss a",
  short: "h:mm a",
};

const dateTimeFormats = {
  full: "{{date}} 'at' {{time}}",
  long: "{{date}} 'at' {{time}}",
  medium: "{{date}}, {{time}}",
  short: "{{date}}, {{time}}",
};

const formatLong = {
  date: buildFormatLongFn({
    formats: dateFormats,
    defaultWidth: "full",
  }),

  time: buildFormatLongFn({
    formats: timeFormats,
    defaultWidth: "full",
  }),

  dateTime: buildFormatLongFn({
    formats: dateTimeFormats,
    defaultWidth: "full",
  }),
};

const formatRelativeLocale = {
  lastWeek: "'last' eeee 'at' p",
  yesterday: "'yesterday at' p",
  today: "'today at' p",
  tomorrow: "'tomorrow at' p",
  nextWeek: "eeee 'at' p",
  other: "P",
};

const formatRelative = (token, _date, _baseDate, _options) =>
  formatRelativeLocale[token];

/* eslint-disable no-unused-vars */

/**
 * The localize function argument callback which allows to convert raw value to
 * the actual type.
 *
 * @param value - The value to convert
 *
 * @returns The converted value
 */

/**
 * The map of localized values for each width.
 */

/**
 * The index type of the locale unit value. It types conversion of units of
 * values that don't start at 0 (i.e. quarters).
 */

/**
 * Converts the unit value to the tuple of values.
 */

/**
 * The tuple of localized era values. The first element represents BC,
 * the second element represents AD.
 */

/**
 * The tuple of localized quarter values. The first element represents Q1.
 */

/**
 * The tuple of localized day values. The first element represents Sunday.
 */

/**
 * The tuple of localized month values. The first element represents January.
 */

function buildLocalizeFn(args) {
  return (value, options) => {
    const context = options?.context ? String(options.context) : "standalone";

    let valuesArray;
    if (context === "formatting" && args.formattingValues) {
      const defaultWidth = args.defaultFormattingWidth || args.defaultWidth;
      const width = options?.width ? String(options.width) : defaultWidth;

      valuesArray =
        args.formattingValues[width] || args.formattingValues[defaultWidth];
    } else {
      const defaultWidth = args.defaultWidth;
      const width = options?.width ? String(options.width) : args.defaultWidth;

      valuesArray = args.values[width] || args.values[defaultWidth];
    }
    const index = args.argumentCallback ? args.argumentCallback(value) : value;

    // @ts-expect-error - For some reason TypeScript just don't want to match it, no matter how hard we try. I challenge you to try to remove it!
    return valuesArray[index];
  };
}

const eraValues = {
  narrow: ["B", "A"],
  abbreviated: ["BC", "AD"],
  wide: ["Before Christ", "Anno Domini"],
};

const quarterValues = {
  narrow: ["1", "2", "3", "4"],
  abbreviated: ["Q1", "Q2", "Q3", "Q4"],
  wide: ["1st quarter", "2nd quarter", "3rd quarter", "4th quarter"],
};

// Note: in English, the names of days of the week and months are capitalized.
// If you are making a new locale based on this one, check if the same is true for the language you're working on.
// Generally, formatted dates should look like they are in the middle of a sentence,
// e.g. in Spanish language the weekdays and months should be in the lowercase.
const monthValues = {
  narrow: ["J", "F", "M", "A", "M", "J", "J", "A", "S", "O", "N", "D"],
  abbreviated: [
    "Jan",
    "Feb",
    "Mar",
    "Apr",
    "May",
    "Jun",
    "Jul",
    "Aug",
    "Sep",
    "Oct",
    "Nov",
    "Dec",
  ],

  wide: [
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
  ],
};

const dayValues = {
  narrow: ["S", "M", "T", "W", "T", "F", "S"],
  short: ["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"],
  abbreviated: ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"],
  wide: [
    "Sunday",
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
  ],
};

const dayPeriodValues = {
  narrow: {
    am: "a",
    pm: "p",
    midnight: "mi",
    noon: "n",
    morning: "morning",
    afternoon: "afternoon",
    evening: "evening",
    night: "night",
  },
  abbreviated: {
    am: "AM",
    pm: "PM",
    midnight: "midnight",
    noon: "noon",
    morning: "morning",
    afternoon: "afternoon",
    evening: "evening",
    night: "night",
  },
  wide: {
    am: "a.m.",
    pm: "p.m.",
    midnight: "midnight",
    noon: "noon",
    morning: "morning",
    afternoon: "afternoon",
    evening: "evening",
    night: "night",
  },
};

const formattingDayPeriodValues = {
  narrow: {
    am: "a",
    pm: "p",
    midnight: "mi",
    noon: "n",
    morning: "in the morning",
    afternoon: "in the afternoon",
    evening: "in the evening",
    night: "at night",
  },
  abbreviated: {
    am: "AM",
    pm: "PM",
    midnight: "midnight",
    noon: "noon",
    morning: "in the morning",
    afternoon: "in the afternoon",
    evening: "in the evening",
    night: "at night",
  },
  wide: {
    am: "a.m.",
    pm: "p.m.",
    midnight: "midnight",
    noon: "noon",
    morning: "in the morning",
    afternoon: "in the afternoon",
    evening: "in the evening",
    night: "at night",
  },
};

const ordinalNumber = (dirtyNumber, _options) => {
  const number = Number(dirtyNumber);

  // If ordinal numbers depend on context, for example,
  // if they are different for different grammatical genders,
  // use `options.unit`.
  //
  // `unit` can be 'year', 'quarter', 'month', 'week', 'date', 'dayOfYear',
  // 'day', 'hour', 'minute', 'second'.

  const rem100 = number % 100;
  if (rem100 > 20 || rem100 < 10) {
    switch (rem100 % 10) {
      case 1:
        return number + "st";
      case 2:
        return number + "nd";
      case 3:
        return number + "rd";
    }
  }
  return number + "th";
};

const localize = {
  ordinalNumber,

  era: buildLocalizeFn({
    values: eraValues,
    defaultWidth: "wide",
  }),

  quarter: buildLocalizeFn({
    values: quarterValues,
    defaultWidth: "wide",
    argumentCallback: (quarter) => quarter - 1,
  }),

  month: buildLocalizeFn({
    values: monthValues,
    defaultWidth: "wide",
  }),

  day: buildLocalizeFn({
    values: dayValues,
    defaultWidth: "wide",
  }),

  dayPeriod: buildLocalizeFn({
    values: dayPeriodValues,
    defaultWidth: "wide",
    formattingValues: formattingDayPeriodValues,
    defaultFormattingWidth: "wide",
  }),
};

function buildMatchFn(args) {
  return (string, options = {}) => {
    const width = options.width;

    const matchPattern =
      (width && args.matchPatterns[width]) ||
      args.matchPatterns[args.defaultMatchWidth];
    const matchResult = string.match(matchPattern);

    if (!matchResult) {
      return null;
    }
    const matchedString = matchResult[0];

    const parsePatterns =
      (width && args.parsePatterns[width]) ||
      args.parsePatterns[args.defaultParseWidth];

    const key = Array.isArray(parsePatterns)
      ? findIndex(parsePatterns, (pattern) => pattern.test(matchedString))
      : // eslint-disable-next-line @typescript-eslint/no-explicit-any -- I challange you to fix the type
        findKey(parsePatterns, (pattern) => pattern.test(matchedString));

    let value;

    value = args.valueCallback ? args.valueCallback(key) : key;
    value = options.valueCallback
      ? // eslint-disable-next-line @typescript-eslint/no-explicit-any -- I challange you to fix the type
        options.valueCallback(value)
      : value;

    const rest = string.slice(matchedString.length);

    return { value, rest };
  };
}

function findKey(object, predicate) {
  for (const key in object) {
    if (
      Object.prototype.hasOwnProperty.call(object, key) &&
      predicate(object[key])
    ) {
      return key;
    }
  }
  return undefined;
}

function findIndex(array, predicate) {
  for (let key = 0; key < array.length; key++) {
    if (predicate(array[key])) {
      return key;
    }
  }
  return undefined;
}

function buildMatchPatternFn(args) {
  return (string, options = {}) => {
    const matchResult = string.match(args.matchPattern);
    if (!matchResult) return null;
    const matchedString = matchResult[0];

    const parseResult = string.match(args.parsePattern);
    if (!parseResult) return null;
    let value = args.valueCallback
      ? args.valueCallback(parseResult[0])
      : parseResult[0];

    // eslint-disable-next-line @typescript-eslint/no-explicit-any -- I challange you to fix the type
    value = options.valueCallback ? options.valueCallback(value) : value;

    const rest = string.slice(matchedString.length);

    return { value, rest };
  };
}

const matchOrdinalNumberPattern = /^(\d+)(th|st|nd|rd)?/i;
const parseOrdinalNumberPattern = /\d+/i;

const matchEraPatterns = {
  narrow: /^(b|a)/i,
  abbreviated: /^(b\.?\s?c\.?|b\.?\s?c\.?\s?e\.?|a\.?\s?d\.?|c\.?\s?e\.?)/i,
  wide: /^(before christ|before common era|anno domini|common era)/i,
};
const parseEraPatterns = {
  any: [/^b/i, /^(a|c)/i],
};

const matchQuarterPatterns = {
  narrow: /^[1234]/i,
  abbreviated: /^q[1234]/i,
  wide: /^[1234](th|st|nd|rd)? quarter/i,
};
const parseQuarterPatterns = {
  any: [/1/i, /2/i, /3/i, /4/i],
};

const matchMonthPatterns = {
  narrow: /^[jfmasond]/i,
  abbreviated: /^(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)/i,
  wide: /^(january|february|march|april|may|june|july|august|september|october|november|december)/i,
};
const parseMonthPatterns = {
  narrow: [
    /^j/i,
    /^f/i,
    /^m/i,
    /^a/i,
    /^m/i,
    /^j/i,
    /^j/i,
    /^a/i,
    /^s/i,
    /^o/i,
    /^n/i,
    /^d/i,
  ],

  any: [
    /^ja/i,
    /^f/i,
    /^mar/i,
    /^ap/i,
    /^may/i,
    /^jun/i,
    /^jul/i,
    /^au/i,
    /^s/i,
    /^o/i,
    /^n/i,
    /^d/i,
  ],
};

const matchDayPatterns = {
  narrow: /^[smtwf]/i,
  short: /^(su|mo|tu|we|th|fr|sa)/i,
  abbreviated: /^(sun|mon|tue|wed|thu|fri|sat)/i,
  wide: /^(sunday|monday|tuesday|wednesday|thursday|friday|saturday)/i,
};
const parseDayPatterns = {
  narrow: [/^s/i, /^m/i, /^t/i, /^w/i, /^t/i, /^f/i, /^s/i],
  any: [/^su/i, /^m/i, /^tu/i, /^w/i, /^th/i, /^f/i, /^sa/i],
};

const matchDayPeriodPatterns = {
  narrow: /^(a|p|mi|n|(in the|at) (morning|afternoon|evening|night))/i,
  any: /^([ap]\.?\s?m\.?|midnight|noon|(in the|at) (morning|afternoon|evening|night))/i,
};
const parseDayPeriodPatterns = {
  any: {
    am: /^a/i,
    pm: /^p/i,
    midnight: /^mi/i,
    noon: /^no/i,
    morning: /morning/i,
    afternoon: /afternoon/i,
    evening: /evening/i,
    night: /night/i,
  },
};

const match = {
  ordinalNumber: buildMatchPatternFn({
    matchPattern: matchOrdinalNumberPattern,
    parsePattern: parseOrdinalNumberPattern,
    valueCallback: (value) => parseInt(value, 10),
  }),

  era: buildMatchFn({
    matchPatterns: matchEraPatterns,
    defaultMatchWidth: "wide",
    parsePatterns: parseEraPatterns,
    defaultParseWidth: "any",
  }),

  quarter: buildMatchFn({
    matchPatterns: matchQuarterPatterns,
    defaultMatchWidth: "wide",
    parsePatterns: parseQuarterPatterns,
    defaultParseWidth: "any",
    valueCallback: (index) => index + 1,
  }),

  month: buildMatchFn({
    matchPatterns: matchMonthPatterns,
    defaultMatchWidth: "wide",
    parsePatterns: parseMonthPatterns,
    defaultParseWidth: "any",
  }),

  day: buildMatchFn({
    matchPatterns: matchDayPatterns,
    defaultMatchWidth: "wide",
    parsePatterns: parseDayPatterns,
    defaultParseWidth: "any",
  }),

  dayPeriod: buildMatchFn({
    matchPatterns: matchDayPeriodPatterns,
    defaultMatchWidth: "any",
    parsePatterns: parseDayPeriodPatterns,
    defaultParseWidth: "any",
  }),
};

/**
 * @category Locales
 * @summary English locale (United States).
 * @language English
 * @iso-639-2 eng
 * @author Sasha Koss [@kossnocorp](https://github.com/kossnocorp)
 * @author Lesha Koss [@leshakoss](https://github.com/leshakoss)
 */
const enUS = {
  code: "en-US",
  formatDistance: formatDistance,
  formatLong: formatLong,
  formatRelative: formatRelative,
  localize: localize,
  match: match,
  options: {
    weekStartsOn: 0 /* Sunday */,
    firstWeekContainsDate: 1,
  },
};

/**
 * @name getDayOfYear
 * @category Day Helpers
 * @summary Get the day of the year of the given date.
 *
 * @description
 * Get the day of the year of the given date.
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The given date
 *
 * @returns The day of year
 *
 * @example
 * // Which day of the year is 2 July 2014?
 * const result = getDayOfYear(new Date(2014, 6, 2))
 * //=> 183
 */
function getDayOfYear(date) {
  const _date = toDate(date);
  const diff = differenceInCalendarDays(_date, startOfYear(_date));
  const dayOfYear = diff + 1;
  return dayOfYear;
}

/**
 * @name getISOWeek
 * @category ISO Week Helpers
 * @summary Get the ISO week of the given date.
 *
 * @description
 * Get the ISO week of the given date.
 *
 * ISO week-numbering year: http://en.wikipedia.org/wiki/ISO_week_date
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The given date
 *
 * @returns The ISO week
 *
 * @example
 * // Which week of the ISO-week numbering year is 2 January 2005?
 * const result = getISOWeek(new Date(2005, 0, 2))
 * //=> 53
 */
function getISOWeek(date) {
  const _date = toDate(date);
  const diff = +startOfISOWeek(_date) - +startOfISOWeekYear(_date);

  // Round the number of weeks to the nearest integer because the number of
  // milliseconds in a week is not constant (e.g. it's different in the week of
  // the daylight saving time clock shift).
  return Math.round(diff / millisecondsInWeek) + 1;
}

/**
 * The {@link getWeekYear} function options.
 */

/**
 * @name getWeekYear
 * @category Week-Numbering Year Helpers
 * @summary Get the local week-numbering year of the given date.
 *
 * @description
 * Get the local week-numbering year of the given date.
 * The exact calculation depends on the values of
 * `options.weekStartsOn` (which is the index of the first day of the week)
 * and `options.firstWeekContainsDate` (which is the day of January, which is always in
 * the first week of the week-numbering year)
 *
 * Week numbering: https://en.wikipedia.org/wiki/Week#The_ISO_week_date_system
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The given date
 * @param options - An object with options.
 *
 * @returns The local week-numbering year
 *
 * @example
 * // Which week numbering year is 26 December 2004 with the default settings?
 * const result = getWeekYear(new Date(2004, 11, 26))
 * //=> 2005
 *
 * @example
 * // Which week numbering year is 26 December 2004 if week starts on Saturday?
 * const result = getWeekYear(new Date(2004, 11, 26), { weekStartsOn: 6 })
 * //=> 2004
 *
 * @example
 * // Which week numbering year is 26 December 2004 if the first week contains 4 January?
 * const result = getWeekYear(new Date(2004, 11, 26), { firstWeekContainsDate: 4 })
 * //=> 2004
 */
function getWeekYear(date, options) {
  const _date = toDate(date);
  const year = _date.getFullYear();

  const defaultOptions = getDefaultOptions();
  const firstWeekContainsDate =
    options?.firstWeekContainsDate ??
    options?.locale?.options?.firstWeekContainsDate ??
    defaultOptions.firstWeekContainsDate ??
    defaultOptions.locale?.options?.firstWeekContainsDate ??
    1;

  const firstWeekOfNextYear = constructFrom(date, 0);
  firstWeekOfNextYear.setFullYear(year + 1, 0, firstWeekContainsDate);
  firstWeekOfNextYear.setHours(0, 0, 0, 0);
  const startOfNextYear = startOfWeek(firstWeekOfNextYear, options);

  const firstWeekOfThisYear = constructFrom(date, 0);
  firstWeekOfThisYear.setFullYear(year, 0, firstWeekContainsDate);
  firstWeekOfThisYear.setHours(0, 0, 0, 0);
  const startOfThisYear = startOfWeek(firstWeekOfThisYear, options);

  if (_date.getTime() >= startOfNextYear.getTime()) {
    return year + 1;
  } else if (_date.getTime() >= startOfThisYear.getTime()) {
    return year;
  } else {
    return year - 1;
  }
}

/**
 * The {@link startOfWeekYear} function options.
 */

/**
 * @name startOfWeekYear
 * @category Week-Numbering Year Helpers
 * @summary Return the start of a local week-numbering year for the given date.
 *
 * @description
 * Return the start of a local week-numbering year.
 * The exact calculation depends on the values of
 * `options.weekStartsOn` (which is the index of the first day of the week)
 * and `options.firstWeekContainsDate` (which is the day of January, which is always in
 * the first week of the week-numbering year)
 *
 * Week numbering: https://en.wikipedia.org/wiki/Week#The_ISO_week_date_system
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 * @param options - An object with options
 *
 * @returns The start of a week-numbering year
 *
 * @example
 * // The start of an a week-numbering year for 2 July 2005 with default settings:
 * const result = startOfWeekYear(new Date(2005, 6, 2))
 * //=> Sun Dec 26 2004 00:00:00
 *
 * @example
 * // The start of a week-numbering year for 2 July 2005
 * // if Monday is the first day of week
 * // and 4 January is always in the first week of the year:
 * const result = startOfWeekYear(new Date(2005, 6, 2), {
 *   weekStartsOn: 1,
 *   firstWeekContainsDate: 4
 * })
 * //=> Mon Jan 03 2005 00:00:00
 */
function startOfWeekYear(date, options) {
  const defaultOptions = getDefaultOptions();
  const firstWeekContainsDate =
    options?.firstWeekContainsDate ??
    options?.locale?.options?.firstWeekContainsDate ??
    defaultOptions.firstWeekContainsDate ??
    defaultOptions.locale?.options?.firstWeekContainsDate ??
    1;

  const year = getWeekYear(date, options);
  const firstWeek = constructFrom(date, 0);
  firstWeek.setFullYear(year, 0, firstWeekContainsDate);
  firstWeek.setHours(0, 0, 0, 0);
  const _date = startOfWeek(firstWeek, options);
  return _date;
}

/**
 * The {@link getWeek} function options.
 */

/**
 * @name getWeek
 * @category Week Helpers
 * @summary Get the local week index of the given date.
 *
 * @description
 * Get the local week index of the given date.
 * The exact calculation depends on the values of
 * `options.weekStartsOn` (which is the index of the first day of the week)
 * and `options.firstWeekContainsDate` (which is the day of January, which is always in
 * the first week of the week-numbering year)
 *
 * Week numbering: https://en.wikipedia.org/wiki/Week#The_ISO_week_date_system
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The given date
 * @param options - An object with options
 *
 * @returns The week
 *
 * @example
 * // Which week of the local week numbering year is 2 January 2005 with default options?
 * const result = getWeek(new Date(2005, 0, 2))
 * //=> 2
 *
 * @example
 * // Which week of the local week numbering year is 2 January 2005,
 * // if Monday is the first day of the week,
 * // and the first week of the year always contains 4 January?
 * const result = getWeek(new Date(2005, 0, 2), {
 *   weekStartsOn: 1,
 *   firstWeekContainsDate: 4
 * })
 * //=> 53
 */

function getWeek(date, options) {
  const _date = toDate(date);
  const diff = +startOfWeek(_date, options) - +startOfWeekYear(_date, options);

  // Round the number of weeks to the nearest integer because the number of
  // milliseconds in a week is not constant (e.g. it's different in the week of
  // the daylight saving time clock shift).
  return Math.round(diff / millisecondsInWeek) + 1;
}

function addLeadingZeros(number, targetLength) {
  const sign = number < 0 ? "-" : "";
  const output = Math.abs(number).toString().padStart(targetLength, "0");
  return sign + output;
}

/*
 * |     | Unit                           |     | Unit                           |
 * |-----|--------------------------------|-----|--------------------------------|
 * |  a  | AM, PM                         |  A* |                                |
 * |  d  | Day of month                   |  D  |                                |
 * |  h  | Hour [1-12]                    |  H  | Hour [0-23]                    |
 * |  m  | Minute                         |  M  | Month                          |
 * |  s  | Second                         |  S  | Fraction of second             |
 * |  y  | Year (abs)                     |  Y  |                                |
 *
 * Letters marked by * are not implemented but reserved by Unicode standard.
 */

const lightFormatters = {
  // Year
  y(date, token) {
    // From http://www.unicode.org/reports/tr35/tr35-31/tr35-dates.html#Date_Format_tokens
    // | Year     |     y | yy |   yyy |  yyyy | yyyyy |
    // |----------|-------|----|-------|-------|-------|
    // | AD 1     |     1 | 01 |   001 |  0001 | 00001 |
    // | AD 12    |    12 | 12 |   012 |  0012 | 00012 |
    // | AD 123   |   123 | 23 |   123 |  0123 | 00123 |
    // | AD 1234  |  1234 | 34 |  1234 |  1234 | 01234 |
    // | AD 12345 | 12345 | 45 | 12345 | 12345 | 12345 |

    const signedYear = date.getFullYear();
    // Returns 1 for 1 BC (which is year 0 in JavaScript)
    const year = signedYear > 0 ? signedYear : 1 - signedYear;
    return addLeadingZeros(token === "yy" ? year % 100 : year, token.length);
  },

  // Month
  M(date, token) {
    const month = date.getMonth();
    return token === "M" ? String(month + 1) : addLeadingZeros(month + 1, 2);
  },

  // Day of the month
  d(date, token) {
    return addLeadingZeros(date.getDate(), token.length);
  },

  // AM or PM
  a(date, token) {
    const dayPeriodEnumValue = date.getHours() / 12 >= 1 ? "pm" : "am";

    switch (token) {
      case "a":
      case "aa":
        return dayPeriodEnumValue.toUpperCase();
      case "aaa":
        return dayPeriodEnumValue;
      case "aaaaa":
        return dayPeriodEnumValue[0];
      case "aaaa":
      default:
        return dayPeriodEnumValue === "am" ? "a.m." : "p.m.";
    }
  },

  // Hour [1-12]
  h(date, token) {
    return addLeadingZeros(date.getHours() % 12 || 12, token.length);
  },

  // Hour [0-23]
  H(date, token) {
    return addLeadingZeros(date.getHours(), token.length);
  },

  // Minute
  m(date, token) {
    return addLeadingZeros(date.getMinutes(), token.length);
  },

  // Second
  s(date, token) {
    return addLeadingZeros(date.getSeconds(), token.length);
  },

  // Fraction of second
  S(date, token) {
    const numberOfDigits = token.length;
    const milliseconds = date.getMilliseconds();
    const fractionalSeconds = Math.trunc(
      milliseconds * Math.pow(10, numberOfDigits - 3),
    );
    return addLeadingZeros(fractionalSeconds, token.length);
  },
};

const dayPeriodEnum = {
  am: "am",
  pm: "pm",
  midnight: "midnight",
  noon: "noon",
  morning: "morning",
  afternoon: "afternoon",
  evening: "evening",
  night: "night",
};

/*
 * |     | Unit                           |     | Unit                           |
 * |-----|--------------------------------|-----|--------------------------------|
 * |  a  | AM, PM                         |  A* | Milliseconds in day            |
 * |  b  | AM, PM, noon, midnight         |  B  | Flexible day period            |
 * |  c  | Stand-alone local day of week  |  C* | Localized hour w/ day period   |
 * |  d  | Day of month                   |  D  | Day of year                    |
 * |  e  | Local day of week              |  E  | Day of week                    |
 * |  f  |                                |  F* | Day of week in month           |
 * |  g* | Modified Julian day            |  G  | Era                            |
 * |  h  | Hour [1-12]                    |  H  | Hour [0-23]                    |
 * |  i! | ISO day of week                |  I! | ISO week of year               |
 * |  j* | Localized hour w/ day period   |  J* | Localized hour w/o day period  |
 * |  k  | Hour [1-24]                    |  K  | Hour [0-11]                    |
 * |  l* | (deprecated)                   |  L  | Stand-alone month              |
 * |  m  | Minute                         |  M  | Month                          |
 * |  n  |                                |  N  |                                |
 * |  o! | Ordinal number modifier        |  O  | Timezone (GMT)                 |
 * |  p! | Long localized time            |  P! | Long localized date            |
 * |  q  | Stand-alone quarter            |  Q  | Quarter                        |
 * |  r* | Related Gregorian year         |  R! | ISO week-numbering year        |
 * |  s  | Second                         |  S  | Fraction of second             |
 * |  t! | Seconds timestamp              |  T! | Milliseconds timestamp         |
 * |  u  | Extended year                  |  U* | Cyclic year                    |
 * |  v* | Timezone (generic non-locat.)  |  V* | Timezone (location)            |
 * |  w  | Local week of year             |  W* | Week of month                  |
 * |  x  | Timezone (ISO-8601 w/o Z)      |  X  | Timezone (ISO-8601)            |
 * |  y  | Year (abs)                     |  Y  | Local week-numbering year      |
 * |  z  | Timezone (specific non-locat.) |  Z* | Timezone (aliases)             |
 *
 * Letters marked by * are not implemented but reserved by Unicode standard.
 *
 * Letters marked by ! are non-standard, but implemented by date-fns:
 * - `o` modifies the previous token to turn it into an ordinal (see `format` docs)
 * - `i` is ISO day of week. For `i` and `ii` is returns numeric ISO week days,
 *   i.e. 7 for Sunday, 1 for Monday, etc.
 * - `I` is ISO week of year, as opposed to `w` which is local week of year.
 * - `R` is ISO week-numbering year, as opposed to `Y` which is local week-numbering year.
 *   `R` is supposed to be used in conjunction with `I` and `i`
 *   for universal ISO week-numbering date, whereas
 *   `Y` is supposed to be used in conjunction with `w` and `e`
 *   for week-numbering date specific to the locale.
 * - `P` is long localized date format
 * - `p` is long localized time format
 */

const formatters = {
  // Era
  G: function (date, token, localize) {
    const era = date.getFullYear() > 0 ? 1 : 0;
    switch (token) {
      // AD, BC
      case "G":
      case "GG":
      case "GGG":
        return localize.era(era, { width: "abbreviated" });
      // A, B
      case "GGGGG":
        return localize.era(era, { width: "narrow" });
      // Anno Domini, Before Christ
      case "GGGG":
      default:
        return localize.era(era, { width: "wide" });
    }
  },

  // Year
  y: function (date, token, localize) {
    // Ordinal number
    if (token === "yo") {
      const signedYear = date.getFullYear();
      // Returns 1 for 1 BC (which is year 0 in JavaScript)
      const year = signedYear > 0 ? signedYear : 1 - signedYear;
      return localize.ordinalNumber(year, { unit: "year" });
    }

    return lightFormatters.y(date, token);
  },

  // Local week-numbering year
  Y: function (date, token, localize, options) {
    const signedWeekYear = getWeekYear(date, options);
    // Returns 1 for 1 BC (which is year 0 in JavaScript)
    const weekYear = signedWeekYear > 0 ? signedWeekYear : 1 - signedWeekYear;

    // Two digit year
    if (token === "YY") {
      const twoDigitYear = weekYear % 100;
      return addLeadingZeros(twoDigitYear, 2);
    }

    // Ordinal number
    if (token === "Yo") {
      return localize.ordinalNumber(weekYear, { unit: "year" });
    }

    // Padding
    return addLeadingZeros(weekYear, token.length);
  },

  // ISO week-numbering year
  R: function (date, token) {
    const isoWeekYear = getISOWeekYear(date);

    // Padding
    return addLeadingZeros(isoWeekYear, token.length);
  },

  // Extended year. This is a single number designating the year of this calendar system.
  // The main difference between `y` and `u` localizers are B.C. years:
  // | Year | `y` | `u` |
  // |------|-----|-----|
  // | AC 1 |   1 |   1 |
  // | BC 1 |   1 |   0 |
  // | BC 2 |   2 |  -1 |
  // Also `yy` always returns the last two digits of a year,
  // while `uu` pads single digit years to 2 characters and returns other years unchanged.
  u: function (date, token) {
    const year = date.getFullYear();
    return addLeadingZeros(year, token.length);
  },

  // Quarter
  Q: function (date, token, localize) {
    const quarter = Math.ceil((date.getMonth() + 1) / 3);
    switch (token) {
      // 1, 2, 3, 4
      case "Q":
        return String(quarter);
      // 01, 02, 03, 04
      case "QQ":
        return addLeadingZeros(quarter, 2);
      // 1st, 2nd, 3rd, 4th
      case "Qo":
        return localize.ordinalNumber(quarter, { unit: "quarter" });
      // Q1, Q2, Q3, Q4
      case "QQQ":
        return localize.quarter(quarter, {
          width: "abbreviated",
          context: "formatting",
        });
      // 1, 2, 3, 4 (narrow quarter; could be not numerical)
      case "QQQQQ":
        return localize.quarter(quarter, {
          width: "narrow",
          context: "formatting",
        });
      // 1st quarter, 2nd quarter, ...
      case "QQQQ":
      default:
        return localize.quarter(quarter, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // Stand-alone quarter
  q: function (date, token, localize) {
    const quarter = Math.ceil((date.getMonth() + 1) / 3);
    switch (token) {
      // 1, 2, 3, 4
      case "q":
        return String(quarter);
      // 01, 02, 03, 04
      case "qq":
        return addLeadingZeros(quarter, 2);
      // 1st, 2nd, 3rd, 4th
      case "qo":
        return localize.ordinalNumber(quarter, { unit: "quarter" });
      // Q1, Q2, Q3, Q4
      case "qqq":
        return localize.quarter(quarter, {
          width: "abbreviated",
          context: "standalone",
        });
      // 1, 2, 3, 4 (narrow quarter; could be not numerical)
      case "qqqqq":
        return localize.quarter(quarter, {
          width: "narrow",
          context: "standalone",
        });
      // 1st quarter, 2nd quarter, ...
      case "qqqq":
      default:
        return localize.quarter(quarter, {
          width: "wide",
          context: "standalone",
        });
    }
  },

  // Month
  M: function (date, token, localize) {
    const month = date.getMonth();
    switch (token) {
      case "M":
      case "MM":
        return lightFormatters.M(date, token);
      // 1st, 2nd, ..., 12th
      case "Mo":
        return localize.ordinalNumber(month + 1, { unit: "month" });
      // Jan, Feb, ..., Dec
      case "MMM":
        return localize.month(month, {
          width: "abbreviated",
          context: "formatting",
        });
      // J, F, ..., D
      case "MMMMM":
        return localize.month(month, {
          width: "narrow",
          context: "formatting",
        });
      // January, February, ..., December
      case "MMMM":
      default:
        return localize.month(month, { width: "wide", context: "formatting" });
    }
  },

  // Stand-alone month
  L: function (date, token, localize) {
    const month = date.getMonth();
    switch (token) {
      // 1, 2, ..., 12
      case "L":
        return String(month + 1);
      // 01, 02, ..., 12
      case "LL":
        return addLeadingZeros(month + 1, 2);
      // 1st, 2nd, ..., 12th
      case "Lo":
        return localize.ordinalNumber(month + 1, { unit: "month" });
      // Jan, Feb, ..., Dec
      case "LLL":
        return localize.month(month, {
          width: "abbreviated",
          context: "standalone",
        });
      // J, F, ..., D
      case "LLLLL":
        return localize.month(month, {
          width: "narrow",
          context: "standalone",
        });
      // January, February, ..., December
      case "LLLL":
      default:
        return localize.month(month, { width: "wide", context: "standalone" });
    }
  },

  // Local week of year
  w: function (date, token, localize, options) {
    const week = getWeek(date, options);

    if (token === "wo") {
      return localize.ordinalNumber(week, { unit: "week" });
    }

    return addLeadingZeros(week, token.length);
  },

  // ISO week of year
  I: function (date, token, localize) {
    const isoWeek = getISOWeek(date);

    if (token === "Io") {
      return localize.ordinalNumber(isoWeek, { unit: "week" });
    }

    return addLeadingZeros(isoWeek, token.length);
  },

  // Day of the month
  d: function (date, token, localize) {
    if (token === "do") {
      return localize.ordinalNumber(date.getDate(), { unit: "date" });
    }

    return lightFormatters.d(date, token);
  },

  // Day of year
  D: function (date, token, localize) {
    const dayOfYear = getDayOfYear(date);

    if (token === "Do") {
      return localize.ordinalNumber(dayOfYear, { unit: "dayOfYear" });
    }

    return addLeadingZeros(dayOfYear, token.length);
  },

  // Day of week
  E: function (date, token, localize) {
    const dayOfWeek = date.getDay();
    switch (token) {
      // Tue
      case "E":
      case "EE":
      case "EEE":
        return localize.day(dayOfWeek, {
          width: "abbreviated",
          context: "formatting",
        });
      // T
      case "EEEEE":
        return localize.day(dayOfWeek, {
          width: "narrow",
          context: "formatting",
        });
      // Tu
      case "EEEEEE":
        return localize.day(dayOfWeek, {
          width: "short",
          context: "formatting",
        });
      // Tuesday
      case "EEEE":
      default:
        return localize.day(dayOfWeek, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // Local day of week
  e: function (date, token, localize, options) {
    const dayOfWeek = date.getDay();
    const localDayOfWeek = (dayOfWeek - options.weekStartsOn + 8) % 7 || 7;
    switch (token) {
      // Numerical value (Nth day of week with current locale or weekStartsOn)
      case "e":
        return String(localDayOfWeek);
      // Padded numerical value
      case "ee":
        return addLeadingZeros(localDayOfWeek, 2);
      // 1st, 2nd, ..., 7th
      case "eo":
        return localize.ordinalNumber(localDayOfWeek, { unit: "day" });
      case "eee":
        return localize.day(dayOfWeek, {
          width: "abbreviated",
          context: "formatting",
        });
      // T
      case "eeeee":
        return localize.day(dayOfWeek, {
          width: "narrow",
          context: "formatting",
        });
      // Tu
      case "eeeeee":
        return localize.day(dayOfWeek, {
          width: "short",
          context: "formatting",
        });
      // Tuesday
      case "eeee":
      default:
        return localize.day(dayOfWeek, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // Stand-alone local day of week
  c: function (date, token, localize, options) {
    const dayOfWeek = date.getDay();
    const localDayOfWeek = (dayOfWeek - options.weekStartsOn + 8) % 7 || 7;
    switch (token) {
      // Numerical value (same as in `e`)
      case "c":
        return String(localDayOfWeek);
      // Padded numerical value
      case "cc":
        return addLeadingZeros(localDayOfWeek, token.length);
      // 1st, 2nd, ..., 7th
      case "co":
        return localize.ordinalNumber(localDayOfWeek, { unit: "day" });
      case "ccc":
        return localize.day(dayOfWeek, {
          width: "abbreviated",
          context: "standalone",
        });
      // T
      case "ccccc":
        return localize.day(dayOfWeek, {
          width: "narrow",
          context: "standalone",
        });
      // Tu
      case "cccccc":
        return localize.day(dayOfWeek, {
          width: "short",
          context: "standalone",
        });
      // Tuesday
      case "cccc":
      default:
        return localize.day(dayOfWeek, {
          width: "wide",
          context: "standalone",
        });
    }
  },

  // ISO day of week
  i: function (date, token, localize) {
    const dayOfWeek = date.getDay();
    const isoDayOfWeek = dayOfWeek === 0 ? 7 : dayOfWeek;
    switch (token) {
      // 2
      case "i":
        return String(isoDayOfWeek);
      // 02
      case "ii":
        return addLeadingZeros(isoDayOfWeek, token.length);
      // 2nd
      case "io":
        return localize.ordinalNumber(isoDayOfWeek, { unit: "day" });
      // Tue
      case "iii":
        return localize.day(dayOfWeek, {
          width: "abbreviated",
          context: "formatting",
        });
      // T
      case "iiiii":
        return localize.day(dayOfWeek, {
          width: "narrow",
          context: "formatting",
        });
      // Tu
      case "iiiiii":
        return localize.day(dayOfWeek, {
          width: "short",
          context: "formatting",
        });
      // Tuesday
      case "iiii":
      default:
        return localize.day(dayOfWeek, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // AM or PM
  a: function (date, token, localize) {
    const hours = date.getHours();
    const dayPeriodEnumValue = hours / 12 >= 1 ? "pm" : "am";

    switch (token) {
      case "a":
      case "aa":
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "abbreviated",
          context: "formatting",
        });
      case "aaa":
        return localize
          .dayPeriod(dayPeriodEnumValue, {
            width: "abbreviated",
            context: "formatting",
          })
          .toLowerCase();
      case "aaaaa":
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "narrow",
          context: "formatting",
        });
      case "aaaa":
      default:
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // AM, PM, midnight, noon
  b: function (date, token, localize) {
    const hours = date.getHours();
    let dayPeriodEnumValue;
    if (hours === 12) {
      dayPeriodEnumValue = dayPeriodEnum.noon;
    } else if (hours === 0) {
      dayPeriodEnumValue = dayPeriodEnum.midnight;
    } else {
      dayPeriodEnumValue = hours / 12 >= 1 ? "pm" : "am";
    }

    switch (token) {
      case "b":
      case "bb":
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "abbreviated",
          context: "formatting",
        });
      case "bbb":
        return localize
          .dayPeriod(dayPeriodEnumValue, {
            width: "abbreviated",
            context: "formatting",
          })
          .toLowerCase();
      case "bbbbb":
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "narrow",
          context: "formatting",
        });
      case "bbbb":
      default:
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // in the morning, in the afternoon, in the evening, at night
  B: function (date, token, localize) {
    const hours = date.getHours();
    let dayPeriodEnumValue;
    if (hours >= 17) {
      dayPeriodEnumValue = dayPeriodEnum.evening;
    } else if (hours >= 12) {
      dayPeriodEnumValue = dayPeriodEnum.afternoon;
    } else if (hours >= 4) {
      dayPeriodEnumValue = dayPeriodEnum.morning;
    } else {
      dayPeriodEnumValue = dayPeriodEnum.night;
    }

    switch (token) {
      case "B":
      case "BB":
      case "BBB":
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "abbreviated",
          context: "formatting",
        });
      case "BBBBB":
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "narrow",
          context: "formatting",
        });
      case "BBBB":
      default:
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: "wide",
          context: "formatting",
        });
    }
  },

  // Hour [1-12]
  h: function (date, token, localize) {
    if (token === "ho") {
      let hours = date.getHours() % 12;
      if (hours === 0) hours = 12;
      return localize.ordinalNumber(hours, { unit: "hour" });
    }

    return lightFormatters.h(date, token);
  },

  // Hour [0-23]
  H: function (date, token, localize) {
    if (token === "Ho") {
      return localize.ordinalNumber(date.getHours(), { unit: "hour" });
    }

    return lightFormatters.H(date, token);
  },

  // Hour [0-11]
  K: function (date, token, localize) {
    const hours = date.getHours() % 12;

    if (token === "Ko") {
      return localize.ordinalNumber(hours, { unit: "hour" });
    }

    return addLeadingZeros(hours, token.length);
  },

  // Hour [1-24]
  k: function (date, token, localize) {
    let hours = date.getHours();
    if (hours === 0) hours = 24;

    if (token === "ko") {
      return localize.ordinalNumber(hours, { unit: "hour" });
    }

    return addLeadingZeros(hours, token.length);
  },

  // Minute
  m: function (date, token, localize) {
    if (token === "mo") {
      return localize.ordinalNumber(date.getMinutes(), { unit: "minute" });
    }

    return lightFormatters.m(date, token);
  },

  // Second
  s: function (date, token, localize) {
    if (token === "so") {
      return localize.ordinalNumber(date.getSeconds(), { unit: "second" });
    }

    return lightFormatters.s(date, token);
  },

  // Fraction of second
  S: function (date, token) {
    return lightFormatters.S(date, token);
  },

  // Timezone (ISO-8601. If offset is 0, output is always `'Z'`)
  X: function (date, token, _localize) {
    const timezoneOffset = date.getTimezoneOffset();

    if (timezoneOffset === 0) {
      return "Z";
    }

    switch (token) {
      // Hours and optional minutes
      case "X":
        return formatTimezoneWithOptionalMinutes(timezoneOffset);

      // Hours, minutes and optional seconds without `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `XX`
      case "XXXX":
      case "XX": // Hours and minutes without `:` delimiter
        return formatTimezone(timezoneOffset);

      // Hours, minutes and optional seconds with `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `XXX`
      case "XXXXX":
      case "XXX": // Hours and minutes with `:` delimiter
      default:
        return formatTimezone(timezoneOffset, ":");
    }
  },

  // Timezone (ISO-8601. If offset is 0, output is `'+00:00'` or equivalent)
  x: function (date, token, _localize) {
    const timezoneOffset = date.getTimezoneOffset();

    switch (token) {
      // Hours and optional minutes
      case "x":
        return formatTimezoneWithOptionalMinutes(timezoneOffset);

      // Hours, minutes and optional seconds without `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `xx`
      case "xxxx":
      case "xx": // Hours and minutes without `:` delimiter
        return formatTimezone(timezoneOffset);

      // Hours, minutes and optional seconds with `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `xxx`
      case "xxxxx":
      case "xxx": // Hours and minutes with `:` delimiter
      default:
        return formatTimezone(timezoneOffset, ":");
    }
  },

  // Timezone (GMT)
  O: function (date, token, _localize) {
    const timezoneOffset = date.getTimezoneOffset();

    switch (token) {
      // Short
      case "O":
      case "OO":
      case "OOO":
        return "GMT" + formatTimezoneShort(timezoneOffset, ":");
      // Long
      case "OOOO":
      default:
        return "GMT" + formatTimezone(timezoneOffset, ":");
    }
  },

  // Timezone (specific non-location)
  z: function (date, token, _localize) {
    const timezoneOffset = date.getTimezoneOffset();

    switch (token) {
      // Short
      case "z":
      case "zz":
      case "zzz":
        return "GMT" + formatTimezoneShort(timezoneOffset, ":");
      // Long
      case "zzzz":
      default:
        return "GMT" + formatTimezone(timezoneOffset, ":");
    }
  },

  // Seconds timestamp
  t: function (date, token, _localize) {
    const timestamp = Math.trunc(date.getTime() / 1000);
    return addLeadingZeros(timestamp, token.length);
  },

  // Milliseconds timestamp
  T: function (date, token, _localize) {
    const timestamp = date.getTime();
    return addLeadingZeros(timestamp, token.length);
  },
};

function formatTimezoneShort(offset, delimiter = "") {
  const sign = offset > 0 ? "-" : "+";
  const absOffset = Math.abs(offset);
  const hours = Math.trunc(absOffset / 60);
  const minutes = absOffset % 60;
  if (minutes === 0) {
    return sign + String(hours);
  }
  return sign + String(hours) + delimiter + addLeadingZeros(minutes, 2);
}

function formatTimezoneWithOptionalMinutes(offset, delimiter) {
  if (offset % 60 === 0) {
    const sign = offset > 0 ? "-" : "+";
    return sign + addLeadingZeros(Math.abs(offset) / 60, 2);
  }
  return formatTimezone(offset, delimiter);
}

function formatTimezone(offset, delimiter = "") {
  const sign = offset > 0 ? "-" : "+";
  const absOffset = Math.abs(offset);
  const hours = addLeadingZeros(Math.trunc(absOffset / 60), 2);
  const minutes = addLeadingZeros(absOffset % 60, 2);
  return sign + hours + delimiter + minutes;
}

const dateLongFormatter = (pattern, formatLong) => {
  switch (pattern) {
    case "P":
      return formatLong.date({ width: "short" });
    case "PP":
      return formatLong.date({ width: "medium" });
    case "PPP":
      return formatLong.date({ width: "long" });
    case "PPPP":
    default:
      return formatLong.date({ width: "full" });
  }
};

const timeLongFormatter = (pattern, formatLong) => {
  switch (pattern) {
    case "p":
      return formatLong.time({ width: "short" });
    case "pp":
      return formatLong.time({ width: "medium" });
    case "ppp":
      return formatLong.time({ width: "long" });
    case "pppp":
    default:
      return formatLong.time({ width: "full" });
  }
};

const dateTimeLongFormatter = (pattern, formatLong) => {
  const matchResult = pattern.match(/(P+)(p+)?/) || [];
  const datePattern = matchResult[1];
  const timePattern = matchResult[2];

  if (!timePattern) {
    return dateLongFormatter(pattern, formatLong);
  }

  let dateTimeFormat;

  switch (datePattern) {
    case "P":
      dateTimeFormat = formatLong.dateTime({ width: "short" });
      break;
    case "PP":
      dateTimeFormat = formatLong.dateTime({ width: "medium" });
      break;
    case "PPP":
      dateTimeFormat = formatLong.dateTime({ width: "long" });
      break;
    case "PPPP":
    default:
      dateTimeFormat = formatLong.dateTime({ width: "full" });
      break;
  }

  return dateTimeFormat
    .replace("{{date}}", dateLongFormatter(datePattern, formatLong))
    .replace("{{time}}", timeLongFormatter(timePattern, formatLong));
};

const longFormatters = {
  p: timeLongFormatter,
  P: dateTimeLongFormatter,
};

const dayOfYearTokenRE = /^D+$/;
const weekYearTokenRE = /^Y+$/;

const throwTokens = ["D", "DD", "YY", "YYYY"];

function isProtectedDayOfYearToken(token) {
  return dayOfYearTokenRE.test(token);
}

function isProtectedWeekYearToken(token) {
  return weekYearTokenRE.test(token);
}

function warnOrThrowProtectedError(token, format, input) {
  const _message = message(token, format, input);
  console.warn(_message);
  if (throwTokens.includes(token)) throw new RangeError(_message);
}

function message(token, format, input) {
  const subject = token[0] === "Y" ? "years" : "days of the month";
  return `Use \`${token.toLowerCase()}\` instead of \`${token}\` (in \`${format}\`) for formatting ${subject} to the input \`${input}\`; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md`;
}

// This RegExp consists of three parts separated by `|`:
// - [yYQqMLwIdDecihHKkms]o matches any available ordinal number token
//   (one of the certain letters followed by `o`)
// - (\w)\1* matches any sequences of the same letter
// - '' matches two quote characters in a row
// - '(''|[^'])+('|$) matches anything surrounded by two quote characters ('),
//   except a single quote symbol, which ends the sequence.
//   Two quote characters do not end the sequence.
//   If there is no matching single quote
//   then the sequence will continue until the end of the string.
// - . matches any single character unmatched by previous parts of the RegExps
const formattingTokensRegExp =
  /[yYQqMLwIdDecihHKkms]o|(\w)\1*|''|'(''|[^'])+('|$)|./g;

// This RegExp catches symbols escaped by quotes, and also
// sequences of symbols P, p, and the combinations like `PPPPPPPppppp`
const longFormattingTokensRegExp = /P+p+|P+|p+|''|'(''|[^'])+('|$)|./g;

const escapedStringRegExp = /^'([^]*?)'?$/;
const doubleQuoteRegExp = /''/g;
const unescapedLatinCharacterRegExp = /[a-zA-Z]/;

/**
 * The {@link format} function options.
 */

/**
 * @name format
 * @alias formatDate
 * @category Common Helpers
 * @summary Format the date.
 *
 * @description
 * Return the formatted date string in the given format. The result may vary by locale.
 *
 * > ⚠️ Please note that the `format` tokens differ from Moment.js and other libraries.
 * > See: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 *
 * The characters wrapped between two single quotes characters (') are escaped.
 * Two single quotes in a row, whether inside or outside a quoted sequence, represent a 'real' single quote.
 * (see the last example)
 *
 * Format of the string is based on Unicode Technical Standard #35:
 * https://www.unicode.org/reports/tr35/tr35-dates.html#Date_Field_Symbol_Table
 * with a few additions (see note 7 below the table).
 *
 * Accepted patterns:
 * | Unit                            | Pattern | Result examples                   | Notes |
 * |---------------------------------|---------|-----------------------------------|-------|
 * | Era                             | G..GGG  | AD, BC                            |       |
 * |                                 | GGGG    | Anno Domini, Before Christ        | 2     |
 * |                                 | GGGGG   | A, B                              |       |
 * | Calendar year                   | y       | 44, 1, 1900, 2017                 | 5     |
 * |                                 | yo      | 44th, 1st, 0th, 17th              | 5,7   |
 * |                                 | yy      | 44, 01, 00, 17                    | 5     |
 * |                                 | yyy     | 044, 001, 1900, 2017              | 5     |
 * |                                 | yyyy    | 0044, 0001, 1900, 2017            | 5     |
 * |                                 | yyyyy   | ...                               | 3,5   |
 * | Local week-numbering year       | Y       | 44, 1, 1900, 2017                 | 5     |
 * |                                 | Yo      | 44th, 1st, 1900th, 2017th         | 5,7   |
 * |                                 | YY      | 44, 01, 00, 17                    | 5,8   |
 * |                                 | YYY     | 044, 001, 1900, 2017              | 5     |
 * |                                 | YYYY    | 0044, 0001, 1900, 2017            | 5,8   |
 * |                                 | YYYYY   | ...                               | 3,5   |
 * | ISO week-numbering year         | R       | -43, 0, 1, 1900, 2017             | 5,7   |
 * |                                 | RR      | -43, 00, 01, 1900, 2017           | 5,7   |
 * |                                 | RRR     | -043, 000, 001, 1900, 2017        | 5,7   |
 * |                                 | RRRR    | -0043, 0000, 0001, 1900, 2017     | 5,7   |
 * |                                 | RRRRR   | ...                               | 3,5,7 |
 * | Extended year                   | u       | -43, 0, 1, 1900, 2017             | 5     |
 * |                                 | uu      | -43, 01, 1900, 2017               | 5     |
 * |                                 | uuu     | -043, 001, 1900, 2017             | 5     |
 * |                                 | uuuu    | -0043, 0001, 1900, 2017           | 5     |
 * |                                 | uuuuu   | ...                               | 3,5   |
 * | Quarter (formatting)            | Q       | 1, 2, 3, 4                        |       |
 * |                                 | Qo      | 1st, 2nd, 3rd, 4th                | 7     |
 * |                                 | QQ      | 01, 02, 03, 04                    |       |
 * |                                 | QQQ     | Q1, Q2, Q3, Q4                    |       |
 * |                                 | QQQQ    | 1st quarter, 2nd quarter, ...     | 2     |
 * |                                 | QQQQQ   | 1, 2, 3, 4                        | 4     |
 * | Quarter (stand-alone)           | q       | 1, 2, 3, 4                        |       |
 * |                                 | qo      | 1st, 2nd, 3rd, 4th                | 7     |
 * |                                 | qq      | 01, 02, 03, 04                    |       |
 * |                                 | qqq     | Q1, Q2, Q3, Q4                    |       |
 * |                                 | qqqq    | 1st quarter, 2nd quarter, ...     | 2     |
 * |                                 | qqqqq   | 1, 2, 3, 4                        | 4     |
 * | Month (formatting)              | M       | 1, 2, ..., 12                     |       |
 * |                                 | Mo      | 1st, 2nd, ..., 12th               | 7     |
 * |                                 | MM      | 01, 02, ..., 12                   |       |
 * |                                 | MMM     | Jan, Feb, ..., Dec                |       |
 * |                                 | MMMM    | January, February, ..., December  | 2     |
 * |                                 | MMMMM   | J, F, ..., D                      |       |
 * | Month (stand-alone)             | L       | 1, 2, ..., 12                     |       |
 * |                                 | Lo      | 1st, 2nd, ..., 12th               | 7     |
 * |                                 | LL      | 01, 02, ..., 12                   |       |
 * |                                 | LLL     | Jan, Feb, ..., Dec                |       |
 * |                                 | LLLL    | January, February, ..., December  | 2     |
 * |                                 | LLLLL   | J, F, ..., D                      |       |
 * | Local week of year              | w       | 1, 2, ..., 53                     |       |
 * |                                 | wo      | 1st, 2nd, ..., 53th               | 7     |
 * |                                 | ww      | 01, 02, ..., 53                   |       |
 * | ISO week of year                | I       | 1, 2, ..., 53                     | 7     |
 * |                                 | Io      | 1st, 2nd, ..., 53th               | 7     |
 * |                                 | II      | 01, 02, ..., 53                   | 7     |
 * | Day of month                    | d       | 1, 2, ..., 31                     |       |
 * |                                 | do      | 1st, 2nd, ..., 31st               | 7     |
 * |                                 | dd      | 01, 02, ..., 31                   |       |
 * | Day of year                     | D       | 1, 2, ..., 365, 366               | 9     |
 * |                                 | Do      | 1st, 2nd, ..., 365th, 366th       | 7     |
 * |                                 | DD      | 01, 02, ..., 365, 366             | 9     |
 * |                                 | DDD     | 001, 002, ..., 365, 366           |       |
 * |                                 | DDDD    | ...                               | 3     |
 * | Day of week (formatting)        | E..EEE  | Mon, Tue, Wed, ..., Sun           |       |
 * |                                 | EEEE    | Monday, Tuesday, ..., Sunday      | 2     |
 * |                                 | EEEEE   | M, T, W, T, F, S, S               |       |
 * |                                 | EEEEEE  | Mo, Tu, We, Th, Fr, Sa, Su        |       |
 * | ISO day of week (formatting)    | i       | 1, 2, 3, ..., 7                   | 7     |
 * |                                 | io      | 1st, 2nd, ..., 7th                | 7     |
 * |                                 | ii      | 01, 02, ..., 07                   | 7     |
 * |                                 | iii     | Mon, Tue, Wed, ..., Sun           | 7     |
 * |                                 | iiii    | Monday, Tuesday, ..., Sunday      | 2,7   |
 * |                                 | iiiii   | M, T, W, T, F, S, S               | 7     |
 * |                                 | iiiiii  | Mo, Tu, We, Th, Fr, Sa, Su        | 7     |
 * | Local day of week (formatting)  | e       | 2, 3, 4, ..., 1                   |       |
 * |                                 | eo      | 2nd, 3rd, ..., 1st                | 7     |
 * |                                 | ee      | 02, 03, ..., 01                   |       |
 * |                                 | eee     | Mon, Tue, Wed, ..., Sun           |       |
 * |                                 | eeee    | Monday, Tuesday, ..., Sunday      | 2     |
 * |                                 | eeeee   | M, T, W, T, F, S, S               |       |
 * |                                 | eeeeee  | Mo, Tu, We, Th, Fr, Sa, Su        |       |
 * | Local day of week (stand-alone) | c       | 2, 3, 4, ..., 1                   |       |
 * |                                 | co      | 2nd, 3rd, ..., 1st                | 7     |
 * |                                 | cc      | 02, 03, ..., 01                   |       |
 * |                                 | ccc     | Mon, Tue, Wed, ..., Sun           |       |
 * |                                 | cccc    | Monday, Tuesday, ..., Sunday      | 2     |
 * |                                 | ccccc   | M, T, W, T, F, S, S               |       |
 * |                                 | cccccc  | Mo, Tu, We, Th, Fr, Sa, Su        |       |
 * | AM, PM                          | a..aa   | AM, PM                            |       |
 * |                                 | aaa     | am, pm                            |       |
 * |                                 | aaaa    | a.m., p.m.                        | 2     |
 * |                                 | aaaaa   | a, p                              |       |
 * | AM, PM, noon, midnight          | b..bb   | AM, PM, noon, midnight            |       |
 * |                                 | bbb     | am, pm, noon, midnight            |       |
 * |                                 | bbbb    | a.m., p.m., noon, midnight        | 2     |
 * |                                 | bbbbb   | a, p, n, mi                       |       |
 * | Flexible day period             | B..BBB  | at night, in the morning, ...     |       |
 * |                                 | BBBB    | at night, in the morning, ...     | 2     |
 * |                                 | BBBBB   | at night, in the morning, ...     |       |
 * | Hour [1-12]                     | h       | 1, 2, ..., 11, 12                 |       |
 * |                                 | ho      | 1st, 2nd, ..., 11th, 12th         | 7     |
 * |                                 | hh      | 01, 02, ..., 11, 12               |       |
 * | Hour [0-23]                     | H       | 0, 1, 2, ..., 23                  |       |
 * |                                 | Ho      | 0th, 1st, 2nd, ..., 23rd          | 7     |
 * |                                 | HH      | 00, 01, 02, ..., 23               |       |
 * | Hour [0-11]                     | K       | 1, 2, ..., 11, 0                  |       |
 * |                                 | Ko      | 1st, 2nd, ..., 11th, 0th          | 7     |
 * |                                 | KK      | 01, 02, ..., 11, 00               |       |
 * | Hour [1-24]                     | k       | 24, 1, 2, ..., 23                 |       |
 * |                                 | ko      | 24th, 1st, 2nd, ..., 23rd         | 7     |
 * |                                 | kk      | 24, 01, 02, ..., 23               |       |
 * | Minute                          | m       | 0, 1, ..., 59                     |       |
 * |                                 | mo      | 0th, 1st, ..., 59th               | 7     |
 * |                                 | mm      | 00, 01, ..., 59                   |       |
 * | Second                          | s       | 0, 1, ..., 59                     |       |
 * |                                 | so      | 0th, 1st, ..., 59th               | 7     |
 * |                                 | ss      | 00, 01, ..., 59                   |       |
 * | Fraction of second              | S       | 0, 1, ..., 9                      |       |
 * |                                 | SS      | 00, 01, ..., 99                   |       |
 * |                                 | SSS     | 000, 001, ..., 999                |       |
 * |                                 | SSSS    | ...                               | 3     |
 * | Timezone (ISO-8601 w/ Z)        | X       | -08, +0530, Z                     |       |
 * |                                 | XX      | -0800, +0530, Z                   |       |
 * |                                 | XXX     | -08:00, +05:30, Z                 |       |
 * |                                 | XXXX    | -0800, +0530, Z, +123456          | 2     |
 * |                                 | XXXXX   | -08:00, +05:30, Z, +12:34:56      |       |
 * | Timezone (ISO-8601 w/o Z)       | x       | -08, +0530, +00                   |       |
 * |                                 | xx      | -0800, +0530, +0000               |       |
 * |                                 | xxx     | -08:00, +05:30, +00:00            | 2     |
 * |                                 | xxxx    | -0800, +0530, +0000, +123456      |       |
 * |                                 | xxxxx   | -08:00, +05:30, +00:00, +12:34:56 |       |
 * | Timezone (GMT)                  | O...OOO | GMT-8, GMT+5:30, GMT+0            |       |
 * |                                 | OOOO    | GMT-08:00, GMT+05:30, GMT+00:00   | 2     |
 * | Timezone (specific non-locat.)  | z...zzz | GMT-8, GMT+5:30, GMT+0            | 6     |
 * |                                 | zzzz    | GMT-08:00, GMT+05:30, GMT+00:00   | 2,6   |
 * | Seconds timestamp               | t       | 512969520                         | 7     |
 * |                                 | tt      | ...                               | 3,7   |
 * | Milliseconds timestamp          | T       | 512969520900                      | 7     |
 * |                                 | TT      | ...                               | 3,7   |
 * | Long localized date             | P       | 04/29/1453                        | 7     |
 * |                                 | PP      | Apr 29, 1453                      | 7     |
 * |                                 | PPP     | April 29th, 1453                  | 7     |
 * |                                 | PPPP    | Friday, April 29th, 1453          | 2,7   |
 * | Long localized time             | p       | 12:00 AM                          | 7     |
 * |                                 | pp      | 12:00:00 AM                       | 7     |
 * |                                 | ppp     | 12:00:00 AM GMT+2                 | 7     |
 * |                                 | pppp    | 12:00:00 AM GMT+02:00             | 2,7   |
 * | Combination of date and time    | Pp      | 04/29/1453, 12:00 AM              | 7     |
 * |                                 | PPpp    | Apr 29, 1453, 12:00:00 AM         | 7     |
 * |                                 | PPPppp  | April 29th, 1453 at ...           | 7     |
 * |                                 | PPPPpppp| Friday, April 29th, 1453 at ...   | 2,7   |
 * Notes:
 * 1. "Formatting" units (e.g. formatting quarter) in the default en-US locale
 *    are the same as "stand-alone" units, but are different in some languages.
 *    "Formatting" units are declined according to the rules of the language
 *    in the context of a date. "Stand-alone" units are always nominative singular:
 *
 *    `format(new Date(2017, 10, 6), 'do LLLL', {locale: cs}) //=> '6. listopad'`
 *
 *    `format(new Date(2017, 10, 6), 'do MMMM', {locale: cs}) //=> '6. listopadu'`
 *
 * 2. Any sequence of the identical letters is a pattern, unless it is escaped by
 *    the single quote characters (see below).
 *    If the sequence is longer than listed in table (e.g. `EEEEEEEEEEE`)
 *    the output will be the same as default pattern for this unit, usually
 *    the longest one (in case of ISO weekdays, `EEEE`). Default patterns for units
 *    are marked with "2" in the last column of the table.
 *
 *    `format(new Date(2017, 10, 6), 'MMM') //=> 'Nov'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMM') //=> 'November'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMMM') //=> 'N'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMMMM') //=> 'November'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMMMMM') //=> 'November'`
 *
 * 3. Some patterns could be unlimited length (such as `yyyyyyyy`).
 *    The output will be padded with zeros to match the length of the pattern.
 *
 *    `format(new Date(2017, 10, 6), 'yyyyyyyy') //=> '00002017'`
 *
 * 4. `QQQQQ` and `qqqqq` could be not strictly numerical in some locales.
 *    These tokens represent the shortest form of the quarter.
 *
 * 5. The main difference between `y` and `u` patterns are B.C. years:
 *
 *    | Year | `y` | `u` |
 *    |------|-----|-----|
 *    | AC 1 |   1 |   1 |
 *    | BC 1 |   1 |   0 |
 *    | BC 2 |   2 |  -1 |
 *
 *    Also `yy` always returns the last two digits of a year,
 *    while `uu` pads single digit years to 2 characters and returns other years unchanged:
 *
 *    | Year | `yy` | `uu` |
 *    |------|------|------|
 *    | 1    |   01 |   01 |
 *    | 14   |   14 |   14 |
 *    | 376  |   76 |  376 |
 *    | 1453 |   53 | 1453 |
 *
 *    The same difference is true for local and ISO week-numbering years (`Y` and `R`),
 *    except local week-numbering years are dependent on `options.weekStartsOn`
 *    and `options.firstWeekContainsDate` (compare [getISOWeekYear](https://date-fns.org/docs/getISOWeekYear)
 *    and [getWeekYear](https://date-fns.org/docs/getWeekYear)).
 *
 * 6. Specific non-location timezones are currently unavailable in `date-fns`,
 *    so right now these tokens fall back to GMT timezones.
 *
 * 7. These patterns are not in the Unicode Technical Standard #35:
 *    - `i`: ISO day of week
 *    - `I`: ISO week of year
 *    - `R`: ISO week-numbering year
 *    - `t`: seconds timestamp
 *    - `T`: milliseconds timestamp
 *    - `o`: ordinal number modifier
 *    - `P`: long localized date
 *    - `p`: long localized time
 *
 * 8. `YY` and `YYYY` tokens represent week-numbering years but they are often confused with years.
 *    You should enable `options.useAdditionalWeekYearTokens` to use them. See: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 *
 * 9. `D` and `DD` tokens represent days of the year but they are often confused with days of the month.
 *    You should enable `options.useAdditionalDayOfYearTokens` to use them. See: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 *
 * @typeParam DateType - The `Date` type, the function operates on. Gets inferred from passed arguments. Allows to use extensions like [`UTCDate`](https://github.com/date-fns/utc).
 *
 * @param date - The original date
 * @param format - The string of tokens
 * @param options - An object with options
 *
 * @returns The formatted date string
 *
 * @throws `date` must not be Invalid Date
 * @throws `options.locale` must contain `localize` property
 * @throws `options.locale` must contain `formatLong` property
 * @throws use `yyyy` instead of `YYYY` for formatting years using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws use `yy` instead of `YY` for formatting years using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws use `d` instead of `D` for formatting days of the month using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws use `dd` instead of `DD` for formatting days of the month using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws format string contains an unescaped latin alphabet character
 *
 * @example
 * // Represent 11 February 2014 in middle-endian format:
 * const result = format(new Date(2014, 1, 11), 'MM/dd/yyyy')
 * //=> '02/11/2014'
 *
 * @example
 * // Represent 2 July 2014 in Esperanto:
 * import { eoLocale } from 'date-fns/locale/eo'
 * const result = format(new Date(2014, 6, 2), "do 'de' MMMM yyyy", {
 *   locale: eoLocale
 * })
 * //=> '2-a de julio 2014'
 *
 * @example
 * // Escape string by single quote characters:
 * const result = format(new Date(2014, 6, 2, 15), "h 'o''clock'")
 * //=> "3 o'clock"
 */
function format(date, formatStr, options) {
  const defaultOptions = getDefaultOptions();
  const locale = defaultOptions.locale ?? enUS;

  const firstWeekContainsDate =
    defaultOptions.firstWeekContainsDate ??
    defaultOptions.locale?.options?.firstWeekContainsDate ??
    1;

  const weekStartsOn =
    defaultOptions.weekStartsOn ??
    defaultOptions.locale?.options?.weekStartsOn ??
    0;

  const originalDate = toDate(date);

  if (!isValid(originalDate)) {
    throw new RangeError("Invalid time value");
  }

  let parts = formatStr
    .match(longFormattingTokensRegExp)
    .map((substring) => {
      const firstCharacter = substring[0];
      if (firstCharacter === "p" || firstCharacter === "P") {
        const longFormatter = longFormatters[firstCharacter];
        return longFormatter(substring, locale.formatLong);
      }
      return substring;
    })
    .join("")
    .match(formattingTokensRegExp)
    .map((substring) => {
      // Replace two single quote characters with one single quote character
      if (substring === "''") {
        return { isToken: false, value: "'" };
      }

      const firstCharacter = substring[0];
      if (firstCharacter === "'") {
        return { isToken: false, value: cleanEscapedString(substring) };
      }

      if (formatters[firstCharacter]) {
        return { isToken: true, value: substring };
      }

      if (firstCharacter.match(unescapedLatinCharacterRegExp)) {
        throw new RangeError(
          "Format string contains an unescaped latin alphabet character `" +
            firstCharacter +
            "`",
        );
      }

      return { isToken: false, value: substring };
    });

  // invoke localize preprocessor (only for french locales at the moment)
  if (locale.localize.preprocessor) {
    parts = locale.localize.preprocessor(originalDate, parts);
  }

  const formatterOptions = {
    firstWeekContainsDate,
    weekStartsOn,
    locale,
  };

  return parts
    .map((part) => {
      if (!part.isToken) return part.value;

      const token = part.value;

      if (
        (isProtectedWeekYearToken(token)) ||
        (isProtectedDayOfYearToken(token))
      ) {
        warnOrThrowProtectedError(token, formatStr, String(date));
      }

      const formatter = formatters[token[0]];
      return formatter(originalDate, token, locale.localize, formatterOptions);
    })
    .join("");
}

function cleanEscapedString(input) {
  const matched = input.match(escapedStringRegExp);

  if (!matched) {
    return input;
  }

  return matched[1].replace(doubleQuoteRegExp, "'");
}

var SPACECRAFT_ID = 168; // Perseverence Rover Spacecraft ID
var LMST_SPACECRAFT_ID = parseInt("-".concat(SPACECRAFT_ID, "900 "), 10);
var SPICE_LMST_RE = /^\d\/(\d+):(\d{2}):(\d{2}):(\d{2}):(\d+)?$/;
var DISPLAY_LMST_RE = /^(Sol-)?(\d+)M(\d{2}):(\d{2}):(\d{2})(.(\d*))?$/;
var LMST_FORMAT_STRING = "DDDDDMHH:MM:SS";
var spiceInstance = undefined;
// Mars seconds since Sol-0
function msss0(lmst) {
    try {
        var sols = +lmst.split("M")[0];
        var hours = +lmst.split("M")[1].split(":")[0];
        var minutes = +lmst.split("M")[1].split(":")[1];
        var seconds = +lmst.split("M")[1].split(":")[2];
        var sss0 = sols * 86400 + hours * 3600 + minutes * 60 + seconds;
        return sss0;
    }
    catch (err) {
        console.log("LMST Plugin Error: msss0:", lmst, err);
        return NaN;
    }
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
function ephemerisToSCLK(et) {
    var sclkStr = spiceInstance.sce2s(-SPACECRAFT_ID, et);
    // sclkStr = "1/0436236010-12059"
    var split = sclkStr.substring(2).split("-");
    var sclk = parseInt(split[0], 10) + parseInt(split[1], 10) / Math.pow(2, 16);
    return sclk.toFixed();
}
function ephemerisToUTC(et) {
    // Do not use more than 6 digits of precision since javascript date parsing will
    // not correctly interpret more precise numbers correctly since ISO-8601 spec is vague
    // This is not documented within JS Date parsing but can be seen by examining the output of
    // the following two statements:
    // new Date('2024 JUN 03 15:05:28.000001' + "Z").toISOString() -> '2024-06-03T15:05:28.000Z'
    // new Date('2024 JUN 03 15:05:28.0000010000000' + "Z").toISOString() -> '2024-06-03T15:05:28.010Z'
    // Notice the difference in the fractional seconds.
    // Semi-related post https://stackoverflow.com/a/50570660
    return new Date(spiceInstance.et2utc(et, "ISOC", 6) + "Z");
}
function lmstToUTC(lmst) {
    if (spiceInstance) {
        try {
            var et = lmstToEphemeris(lmst);
            return ephemerisToUTC(et);
        }
        catch (error) {
            console.log("LMST Plugin Error: lmstToUTC:", error);
        }
    }
    return new Date();
}
function utcStringToLMST(utc) {
    if (spiceInstance) {
        try {
            var et = spiceInstance.str2et(utc);
            return ephemerisToLMST(et);
        }
        catch (error) {
            console.error("LMST Plugin Error: utcStringToLMST:", utc, error);
            return "Invalid";
        }
    }
    return "Invalid";
}
function utcStringToSCLK(utc) {
    if (spiceInstance) {
        try {
            var et = spiceInstance.str2et(utc);
            return ephemerisToSCLK(et);
        }
        catch (error) {
            console.error(error);
            return "Invalid";
        }
    }
    return "Invalid";
}
function lmstTicks(start, stop, tickCount) {
    var lmstStart = utcStringToLMST(start.toISOString().slice(0, -1));
    var lmstEnd = utcStringToLMST(stop.toISOString().slice(0, -1));
    if (!lmstStart || !lmstEnd) {
        return [];
    }
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
                    // Set error action on spice to report instead of abort which exits
                    spiceInstance.erract("SET", "REPORT");
                    // Log stderr and stdour and reset spice if failed
                    // TODO not seeing stdErr, spice/timecraft may not be reporting these errors to stderr under "REPORT"
                    // mode so our try/catch exceptions may not be getting called. Need to sort out best way of handling
                    // errors from spice/timecraft and figure out if it is plugin or aerie UI that needs to know if a
                    // particular function failed.
                    // Currently if parsing fails, say on a sol out of range, an invalid date will be returned
                    spiceInstance.onStdErr = function (err) {
                        console.error(err);
                        if (spiceInstance.failed()) {
                            spiceInstance.reset();
                        }
                    };
                    spiceInstance.onStdOut = function (err) {
                        console.log(err);
                        if (spiceInstance.failed()) {
                            spiceInstance.reset();
                        }
                    };
                    console.log("Spice initialized", spiceInstance);
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
var LMST_TIME = "HH:mm:ss";
// 3613M04:04:13.84606
var lmstPattern = /(\d+)M(\d{2}):(\d{2})(?::(\d{2})(\.\d+)?)/;
var ROUNDING_MS = 500;
// This function doesn't use surface epoch or mars seconds since it is purely for rounding times
function roundLMST(s) {
    var m = s.match(lmstPattern);
    if (m) {
        var year = 2020;
        var monthIndex = 0;
        var dayOfMonth = 1;
        var sol = parseInt(m[1], 10);
        var hours = parseInt(m[2], 10);
        var minutes = parseInt(m[3], 10);
        var seconds = parseInt(m[4], 10);
        var ms = m[5] ? ROUNDING_MS + 1000 * parseFloat(m[5]) : 0;
        var t0 = new Date(year, monthIndex, dayOfMonth);
        var d = new Date(year, monthIndex, dayOfMonth, hours, minutes, seconds, ms);
        return "".concat(sol + differenceInDays(d, t0), "M").concat(format(d, LMST_TIME));
    }
    return s;
}
function formatPrimaryTime(date) {
    var dateWithoutTZ = date.toISOString().slice(0, -1);
    return roundLMST(utcStringToLMST(dateWithoutTZ));
}
function formatTickLMST(date, viewDurationMs, tickCount) {
    return formatPrimaryTime(date);
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
                                    enableDatePicker: false,
                                    getDefaultPlanEndDate: function (start) {
                                        // Format to LMST, add a sol, parse back to Date
                                        var lmst = formatPrimaryTime(start);
                                        var sols = +lmst.split("M")[0];
                                        return lmstToUTC("".concat(sols + 1, "M").concat(lmst.split("M")[1]));
                                    },
                                    primary: {
                                        format: formatPrimaryTime,
                                        formatShort: formatPrimaryTime,
                                        formatString: LMST_FORMAT_STRING,
                                        formatTick: formatTickLMST,
                                        label: "LMST",
                                        parse: lmstToUTC,
                                        validate: validateLMSTString,
                                    },
                                    additional: [
                                        {
                                            format: function (date) {
                                                var dateWithoutTZ = date.toISOString().slice(0, -1);
                                                return utcStringToSCLK(dateWithoutTZ);
                                            },
                                            label: "SCLK",
                                        },
                                        {
                                            format: function (date) { return date.toISOString().slice(0, -5); },
                                            label: "UTC",
                                        },
                                    ],
                                    ticks: {
                                        getTicks: lmstTicks,
                                        maxLabelWidth: 110,
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

export { getPlugin, lmstTicks, roundLMST };
