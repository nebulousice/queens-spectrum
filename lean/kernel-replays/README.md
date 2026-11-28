# Queens spectrum: kernel replay of the Lean files (lean4checker / leanchecker)

*2026-11-27, Formaliser (stage 7). Human approval to download lean4checker: 2026-11-27. Nothing else was downloaded (Mathlib and the toolchain were already in `lean/.lake` and `~/.elan`). Local user paths are redacted as `<user>`, the hostname as `<host>`.*

## Verdict

| Check | Result |
| --- | --- |
| Standalone [leanprover/lean4checker](https://github.com/leanprover/lean4checker), built with toolchain v4.37.0-rc1 | **cannot be built** (API drift, below). Task 1 as specified stops here. |
| `leanchecker` shipped in the v4.37.0-rc1 toolchain (the upstreamed lean4checker), replay of every `Pipeline.QueensSpectrum.*` module from its imports | **PASS** (12 of 12 modules, exit 0) |
| same tool, `--fresh` replay of `Pipeline.QueensSpectrum.Main` (every constant, Lean core and Mathlib included, re-added to an empty environment) | **PASS** (exit 0, 8 min 25 s) |

## 1. The standalone lean4checker repository

- Cloned 2026-11-27 into the session scratchpad (never inside this repo). `origin/master` is `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` (2026-03-25), whose only change over the last release tag is a README deprecation notice: *lean4checker has been merged into Lean and ships as `leanchecker` with every toolchain from v4.28.0*.
- The newest tag is `v4.29.0-rc8` = `90151c4d12922510ff90802118953adb6edcfe1d` (2026-03-25). There is no tag or branch for v4.30 or later (newest remote branch: `bump_to_v4.29.0-rc8`). So `v4.29.0-rc8` is the nearest version to our toolchain v4.37.0-rc1; its source is identical to `master` apart from `README.md`.
- Build: `lean-toolchain` overridden locally (scratchpad only) from `v4.29.0-rc8` to `v4.37.0-rc1`, then `lake build lean4checker`. It fails in `Lean4Checker/Replay.lean:65`: the tool calls `Kernel.Environment.addDeclCore env 0 d (cancelTk? := none)`, but in v4.37.0-rc1 `addDeclCore` takes two numeric limits, `(maxHeartbeats : USize) (maxRecDepth : USize)`, before the declaration (`src/lean/Lean/Environment.lean:337` of the toolchain). Full log: [`standalone_build.log`](standalone_build.log).
- Building it with its own toolchain v4.29.0-rc8 is not an option: that toolchain is not installed (it would be a further download, not approved), and a v4.29 binary cannot read `.olean` files written by v4.37.0-rc1.
- The tool was not patched: a hand-patched checker would not be the official tool.

## 2. The toolchain's own `leanchecker` (supplementary)

The deprecation notice of the repository points to `leanchecker`, which ships in the toolchain already used to build the proof; running it needed no download. Its source (`src/lean/LeanChecker.lean` of the toolchain, copyright Kim Morrison and Sebastian Ullrich) has the same `replayFromImports` / `replayFromFresh` logic as the standalone tool, with `Kernel.Environment.replay` in place of the tool's own `Replay.lean`.

- Toolchain: `Lean (version 4.37.0-rc1, x86_64-w64-windows-gnu, commit 0b77e12952ad39077d80d8bd6b66d601f225c321, Release)`.
- sha256: `leanchecker.exe` `a8f1b1e960078d4a494cb6bb7a5dac5408a20edef8138e3b2dd13ca4bc0940dd`; `lean.exe` `a2a725e1239d5a7f955d911ce811858e08b376296a22a67ded6dd327134c17ae`; `src/lean/LeanChecker.lean` `9c4b1e34256f40b0f85a3a69aa21c8ebe797d46945805e073ded7576db51e25b`.
- Mathlib: `8ec7bd8e5f837ab7e335374928e18341c4e9f385` (as pinned in `lean/lake-manifest.json`), the existing `lean/.lake` build.
- Machine: AMD Ryzen 9 270 (16 logical CPUs), 31.3 GB RAM, Windows 11. Peak memory of the parallel replay about 9 GB.

Runs, from `lean/` (the `.olean` files are those of `bash scripts/lean_check.sh QueensSpectrum`, PASS, same day):

| Log | Command | Modules | Wall time | Result |
| --- | --- | --- | --- | --- |
| [`replay_pre.log`](replay_pre.log) | `lake env leanchecker -v Pipeline.QueensSpectrum` | the 11 QS-1 modules, before `Eigenspace.lean` existed | 6 min 6 s | exit 0 |
| [`replay_all.log`](replay_all.log) | same, after adding `Eigenspace.lean` (QS-2) | all 12 modules, `Main` and `Eigenspace` included | 5 min 27 s | exit 0 |
| [`replay_fresh_main.log`](replay_fresh_main.log) | `lake env leanchecker -v --fresh Pipeline.QueensSpectrum.Main` | `Main` and its whole import closure, from an empty environment | 8 min 25 s | exit 0 |

`leanchecker` prints nothing on success other than the `-v` progress lines, and exits non-zero with "leanchecker found a problem in …" on a kernel rejection. A module name is matched as a prefix, so `Pipeline.QueensSpectrum` covers every module of the target.

What this does and does not show: the Lean kernel re-accepts every declaration stored in the `.olean` files, so the build did not depend on any environment manipulation by tactics or metaprograms. It is not an independent kernel (it is Lean's own kernel). The external kernels bundled with this toolchain (`lean4lean`, `nanoda_bin`, `leanchecker-paranoid`) were not run.

## Reproduce

```
cd lean
lake env leanchecker -v Pipeline.QueensSpectrum
lake env leanchecker -v --fresh Pipeline.QueensSpectrum.Main
```
