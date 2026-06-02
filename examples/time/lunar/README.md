# Lunar Time Plugin Example

An Aerie UI time plugin for lunar mission planning that exposes **UTC** as primary plus **PDT** and **LMST** as secondary readouts.

Unlike the sibling [lmst/](../lmst/) plugin which is Perseverance-specific and uses Mars LMST as the primary time, this plugin uses **UTC** as the primary time. That choice reflects how real lunar surface missions actually plan: Apollo aside, every modern lunar mission (Surveyor, Chandrayaan-3, all CLPS landers, Artemis II, CADRE's MEXEC architecture, ISS OSTPV) uses **UTC as the planning timeline axis**.

One lunar mean solar day is ~29.5 Earth days, so a 14-day surface mission only sweeps half a lunar "morning" — LMST is a poor *scheduling* clock. The **LMST** readout this plugin provides is computed locally (no SPICE) by dividing elapsed UTC seconds by the mean lunar synodic day and scaling into 24 "lunar hours" against a hardcoded anchor. Useful as a phase-within-the-lunar-day indicator; not a high-fidelity solar clock.

## What's shown in the UI

| Slot | Format | Notes |
|---|---|---|
| **Primary** | UTC, `YYYY-DDDTHH:mm:ss` (DOY) | Accepts both DOY and calendar UTC on input |
| Additional | PDT, `YYYY-MM-DD HH:MM:SS` | Pacific time (Los Angeles), via `Intl.DateTimeFormat` |
| Additional | LMST, `DDDDDL HH:MM:SS` | Lunar Local Mean Solar Time, anchored to a hardcoded `LMST_LOCAL_MIDNIGHT_UTC`, 24 lunar-hours per ~29.53 Earth days |

No SPICE, no kernels, no runtime config — everything is computed in plain JavaScript.

### Accepted input formats for the primary field

Both conventions are accepted interchangeably:

| Form | Example | Notes |
|---|---|---|
| **DOY** (day-of-year) | `2026-073T18:30:00` | Aerie UI's native default; canonical for mission ops. |
| **UTC** (calendar) | `2026-03-14T18:30:00` | Convenient for paste-from-anywhere; widely used outside ops. |

`format()` emits DOY (so timeline labels match Aerie's defaults). `parse()` and `validate()` accept either. This dual-format acceptance works around [plandev-ui#1657](https://github.com/NASA-AMMOS/plandev-ui/issues/1657) (imported-plan default times bypass `formatDate`) and aligns with the planned "input via additional formats" work in [plandev-ui#1379](https://github.com/NASA-AMMOS/plandev-ui/issues/1379).

## LMST anchor

`LMST_LOCAL_MIDNIGHT_UTC` in [time-plugin.ts](time-plugin.ts) is the UTC instant that corresponds to local mean midnight at the reference landing site. At that instant LMST reads `00000L00:00:00`; half a lunar sol later (~14.77 Earth days) it reads `00000L12:00:00`. Pre-anchor dates render as `-0001L23:…` style.

Hardcoded for now. When the plugin becomes per-spacecraft, this moves into a per-spacecraft config entry.

The math is uniform (constant lunar synodic day = 29.530589 days), so it's strictly **mean** local solar time. The true apparent sun position drifts from this by up to ~±30 LMST minutes peak over a sol due to lunar orbital eccentricity (e≈0.055, 3× Earth's). Fine for phase-of-day indication; not a precision solar clock.

## Building

```bash
npm install
npm run build
```

Outputs a single `build/time-plugin.js`. No WASM, no kernels, no fetched config.

To preview locally, serve `build/` from any static server and open `index.html`:

```bash
cd build && python3 -m http.server 8080
```

## Implementation notes

- **No SPICE.** Earlier iterations used TimeCraftJS for per-spacecraft SCLK readouts against real CLPS lander kernels; that was scoped down to UTC/PDT/LMST while the plugin's structure firms up.
- **PDT label is approximate.** `Intl.DateTimeFormat` with `timeZone: "America/Los_Angeles"` produces the correct local time year-round, automatically switching for DST — the row label stays `PDT` even during standard-time months.
- **No custom tick generator.** UTC ticks are well-handled by Aerie UI's defaults.
- **Native date picker enabled.** UTC strings work with the native picker; the LMST example disables it because LMST strings don't.
