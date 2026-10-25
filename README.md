# OcilotX Chess Engines

Source repository for the local engines used by OcilotX Chess.

| File | Host menu name | Upstream engine identity |
| --- | --- | --- |
| `engines/Nova.lua` | OcilotX Nova | Zyrqon Nova 2.0.3-frame-safe; display name changed |
| `engines/Lith.lua` | Lith | Auralith Sovereign |
| `engines/Null.lua` | Null | FABLE |
| `engines/Muse.lua` | Muse | Aether Prime |

The **OcilotX** baseline entry uses the game's GarboChess module. It is not another downloadable file from API_URLS and is not included here.

These are algorithms that run locally, not online AI endpoints. This import preserves the upstream algorithms. OcilotX branding does not change source authorship; provenance and original hashes are in `SOURCES.json`. No new license is asserted for the upstream files.

## Stable interface

Each file returns an engine table:

```lua
local move, score, reaction = engine:GetBestMoveFromFEN(fen, seconds)
-- move: UCI string, e.g. e2e4 or a7a8q; nil if there is no legal move
-- preserve the engine's existing score convention and optional third result
engine:SetStyle("Balanced") -- where supported
```

The host default is **OcilotX Nova, 2.5 seconds**. Preserve existing optional methods and arguments. Engines have mutable search state: serialize calls to the same instance.

Current host styles: `Balanced`, `Aggressive`, `Calm`, `Defensive`, `Tactical`, `Trickery`, `Positional`, `Endgame`, `Alien Gambit`, `Willy Alien`. These are preferences, not a guarantee of strength. New styles require corresponding host and dashboard integration.

## Ask Claude to improve the engines

Give Claude this repository and **[PROMPT_CLAUDE.md](PROMPT_CLAUDE.md)**. If it cannot read GitHub, attach the four Lua files and the prompt.

## Offline validation

With LuaJIT installed, from this repository root:

```text
luajit tests/engine_smoke.lua
```

The smoke harness checks 20 returned moves against a separate legal-move implementation and known perft values for engines that expose Perft. It is not an Elo or win-rate measurement.

## Loading engines

This repository is public. `API_URLS.lua` contains the raw source addresses; no API key or GitHub token is needed.

The OcilotX host downloads an engine on first use in each script session, validates the returned interface, then caches it for that session. A failed or timed-out download falls back to the bundled version. Reload the host to use a newer engine from `main`. Review and test engine changes before merging them into `main`.

The source is public and readable by anyone. Keep credentials and personal settings out of the repository. If you make it private again, unauthenticated downloads will fail and the host will use its bundled fallback.
