# Lunar Time Plugin Example (Moonfall-class missions)

An Aerie UI time plugin for short-duration multi-spacecraft lunar surface missions (e.g., Moonfall, CADRE, CLPS landers).

Unlike the sibling [lmst/](../lmst/) plugin which is Perseverance-specific and uses Mars LMST as the primary time, this plugin uses **UTC** as the primary time and exposes per-spacecraft SCLK readouts alongside it. That choice reflects how real lunar surface missions actually plan: Apollo aside, every modern lunar mission (Surveyor, Chandrayaan-3, all CLPS landers, Artemis II, CADRE's MEXEC architecture, ISS OSTPV) uses **UTC as the planning timeline axis** with Mission Elapsed Time and per-vehicle SCLK alongside.

There is no operational "Lunar LMST" because one lunar mean solar day is ~29.5 Earth days — a 14-day surface mission only sweeps half a lunar "morning," making LMST a poor cadence clock.

## What's shown in the UI

| Slot | Format | Required? |
|---|---|---|
| **Primary** | UTC (ISO-8601) | Always |
| Additional | MET (Mission Elapsed Time) — `T±D:HH:MM:SS` | Only if `landingEpochUtc` is set |
| Additional | `${name} SCLK` — one row per spacecraft with a loaded kernel | Per spacecraft |

Sun elevation, Local Solar Time, and hours-since-sunrise are intentionally omitted — they are not times, and within a single lunar day they don't move usefully. If desired, those belong in a separate visualization plugin, not the time plugin.

### Accepted input formats for the primary field

Both NASA-ops conventions are accepted interchangeably:

| Form | Example | Notes |
|---|---|---|
| **DOY** (day-of-year) | `2026-073T18:30:00` | Aerie UI's native default; canonical for mission ops. |
| **UTC** (calendar) | `2026-03-14T18:30:00` | Convenient for paste-from-anywhere; widely used outside ops. |

`format()` emits DOY (so timeline labels match Aerie's defaults). `parse()` and `validate()` accept either. The field hint reads `YYYY-DDDTHH:mm:ss (DOY) or YYYY-MM-DDTHH:mm:ss (UTC)` and the validation error mirrors that.

This dual-format acceptance also works around [plandev-ui#1657](https://github.com/NASA-AMMOS/plandev-ui/issues/1657) (imported-plan default times bypass `formatDate`) and aligns with the planned "input via additional formats" work in [plandev-ui#1379](https://github.com/NASA-AMMOS/plandev-ui/issues/1379).

## Runtime configuration (not baked into the bundle)

The plugin fetches `/resources/lunar-time-config.json` at init time so that ops can update the spacecraft roster, SCLK kernels, and touchdown epoch on the deployed Aerie UI host **without rebuilding** the plugin. This matters because:

- Many spacecraft don't have NAIF SPICE IDs or SCLK kernels during formulation.
- Touchdown UTC isn't known until close to landing, and is replaced post-landing.
- The same bundled plugin needs to serve formulation, pre-flight tactical, and post-landing tactical phases.

### Schema

```ts
type SpacecraftConfig = {
  name: string;            // display label, e.g. "M1"
  spiceId?: number;        // NAIF SCLK ID (negative); when absent, no SCLK row is rendered
  sclkKernel?: string;     // URL to .tsc; required iff spiceId is set
};

type LunarTimeConfig = {
  landingEpochUtc?: string;          // ISO-8601 (no trailing Z); when absent, MET row hidden
  defaultPlanDurationDays?: number;  // default 14 (single lunar daylight window)
  lskKernel?: string;                // default "/resources/kernels/naif0012.tls"
  spacecraft: SpacecraftConfig[];    // may be empty during early formulation
};
```

### Formulation-phase config (no kernels, no touchdown)

```json
{
  "spacecraft": [
    { "name": "M1" },
    { "name": "M2" },
    { "name": "M3" },
    { "name": "M4" }
  ]
}
```

Result: UTC primary only. No SPICE init (the WASM blob isn't even fetched). MET row hidden.

### Tactical config (epoch + kernels)

```json
{
  "landingEpochUtc": "2027-03-14T18:42:00",
  "defaultPlanDurationDays": 14,
  "spacecraft": [
    { "name": "M1", "spiceId": -901, "sclkKernel": "/resources/kernels/moonfall_m1.tsc" },
    { "name": "M2", "spiceId": -902, "sclkKernel": "/resources/kernels/moonfall_m2.tsc" },
    { "name": "M3", "spiceId": -903, "sclkKernel": "/resources/kernels/moonfall_m3.tsc" },
    { "name": "M4", "spiceId": -904, "sclkKernel": "/resources/kernels/moonfall_m4.tsc" }
  ]
}
```

Result: UTC primary + MET (countdown pre-landing as `T-…`, elapsed post-landing as `T+…`) + four SCLK rows.

### Fallback behavior

- Missing/invalid `lunar-time-config.json` → warning logged, UTC-only plugin returned.
- Individual SCLK kernel that fails to load → only that vehicle's row is dropped; other SCLKs, MET, and UTC keep working.
- Invalid `landingEpochUtc` → warning logged, MET row hidden.

## Running the example with real CLPS lander kernels

Four public CLPS-lander SCLK kernels are archived in the NAIF PDS4 archive — enough to exercise the multi-SCLK path against real kernels. The included [lunar-time-config.example.json](lunar-time-config.example.json) is wired up for these:

| File | Spacecraft | NAIF ID |
|---|---|---|
| `clps_to2ab_apm1_v02.tsc` | Astrobotic Peregrine | -244 |
| `clps_to2im_im1_v01.tsc` | Intuitive Machines IM-1 Odysseus | -370011 |
| `clps_to19d_bgm1_v01.tsc` | Firefly Blue Ghost M1 | -2711 |
| `clps_prime1_im2_v01.tsc` | Intuitive Machines IM-2 Athena | -370021 |

To run end-to-end:

1. `npm install`
2. `npm run build`
3. Download kernels into `build/resources/kernels/`:
   - LSK: <https://naif.jpl.nasa.gov/pub/naif/generic_kernels/lsk/naif0012.tls>
   - The four SCLKs above from <https://naif.jpl.nasa.gov/pub/naif/pds/pds4/clps/clps_spice/spice_kernels/sclk/>
4. Copy `lunar-time-config.example.json` to `build/resources/lunar-time-config.json`.
5. Serve `build/` from any static file server and point Aerie UI at the resulting `time-plugin.js`.

The example's `landingEpochUtc` is set to IM-2's actual touchdown (2025-03-02T08:34 UTC). Each SCLK row should produce a finite numeric value near that instant.

> **Heads-up on kernel coverage:** each public CLPS SCLK kernel only covers its real flight window:
> - Peregrine: Jan 2024
> - IM-1 Odysseus: Feb 2024
> - Blue Ghost M1: Feb–Mar 2025
> - IM-2 Athena: Feb–Mar 2025
>
> None overlap. If your plan timeline falls outside a kernel's window, that SCLK column will render blank for those ticks — the plugin returns `null` and logs a one-time `warn` per spacecraft instead of spamming SPICE tracebacks. To see live values for a given lander, set the plan start/end into its window. **Real Moonfall kernels won't have this issue** because all spacecraft share a deployment window.

> **Note on `spiceId` values:** these IDs are extracted from each kernel's `SCLK01_TIME_SYSTEM_<N>` parameter. If `sce2s` fails for a kernel, try the base spacecraft ID (e.g. `-370` instead of `-370011`) — some CLPS SCLKs use partition IDs.

## Implementation notes

- Built on [TimeCraftJS](https://github.com/NASA-AMMOS/timecraftjs), the same SPICE-in-JS library used by the sibling LMST example.
- Only LSK + N SCLK kernels are loaded. No PCK/FK/SPK is required because the plugin computes no geometry.
- SPICE init is skipped entirely when no spacecraft has a kernel — formulation deployments don't pay the WASM-fetch cost.
- The SPICE error handlers (`erract`, `onStdErr`, `onStdOut`, `reset()`) mirror the LMST plugin's pattern.
- No custom tick generator — UTC ticks are well-handled by Aerie UI's defaults.
- Native date picker is **enabled** (the LMST plugin disables it because LMST strings aren't pickable; UTC strings are).
