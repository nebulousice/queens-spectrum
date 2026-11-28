# Reproducing the checks

This guide has three parts.

1. **The Lean check** (the formal proof of the whole Theorem and of Corollary 13). This is the strongest check in this repository. Part 1b reruns the kernel replays of the compiled proofs and the exact check of the Corollary 13 statement.
2. **The computer checks** in Python (exact arithmetic for finitely many $n$). They are corroboration only.
3. **LaTeX** (the paper, version 3).

The written proof in [`PROOF.md`](PROOF.md) uses neither of them.

## Part 1. The Lean check

### Versions

| Item | Version |
| --- | --- |
| Lean | 4.37.0-rc1 (`leanprover/lean4:v4.37.0-rc1`, file [`lean/lean-toolchain`](lean/lean-toolchain)) |
| Lake | 5.0.0-src+0b77e12 (ships with that Lean) |
| Mathlib | commit `8ec7bd8e5f837ab7e335374928e18341c4e9f385`, pinned with all its dependencies in [`lean/lake-manifest.json`](lean/lake-manifest.json) |
| elan (toolchain manager) | 4.4.0 was used; any recent elan works |
| Shell | bash (Git Bash on Windows 11 for the archived runs) |

[`lean/lakefile.toml`](lean/lakefile.toml) names Mathlib's `master` branch, but Lake builds the exact commit recorded in `lake-manifest.json`. Do not run `lake update`, which would move Mathlib to a newer commit.

[`lean/Pipeline.lean`](lean/Pipeline.lean) is the root file of the library. In the project where the formalization was written, the same root file also imports other, unrelated work; in this repository it imports only `Pipeline.QueensSpectrum.Main` (which imports `Eigenspace.lean`). The 12 files in [`lean/Pipeline/QueensSpectrum/`](lean/Pipeline/QueensSpectrum/), `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are byte-identical copies of the checked files.

### Commands

Install elan from https://github.com/leanprover/elan (it installs the Lean version named in `lean-toolchain` automatically). Then, from the root of this repository:

```
cd lean
lake exe cache get        # download Mathlib's prebuilt files for the pinned commit (several GB; network)
cd ..
bash scripts/lean_check.sh QueensSpectrum
```

[`scripts/lean_check.sh`](scripts/lean_check.sh) is the check script used for the archived runs, unchanged. It does three things, and prints `PASS` only if all three succeed:

1. `lake build` in `lean/`, with no `error:` in the output;
2. a scan of `lean/Pipeline/QueensSpectrum/*.lean` for `sorry` and `admit` (it must find nothing);
3. `lake env lean lean/Pipeline/QueensSpectrum/Main.lean`, which runs the `#print axioms` lines at the end of `Main.lean`; every reported axiom must be `propext`, `Classical.choice` or `Quot.sound`.

The script writes `build.log` and `axioms.log` into `lean/Pipeline/QueensSpectrum/`. The archived copies are kept separately in [`lean/logs/`](lean/logs/), so a rerun does not overwrite them.

`native_decide` is not scanned for by the script, but it is absent from the files (`grep -rn native_decide lean/Pipeline/QueensSpectrum` finds nothing), and it would show up in the axiom report as `Lean.ofReduceBool`.

### Expected output

The build prints warnings that the Mathlib files it imports are designed for Lean's module system; these are notices, not errors. The output then ends with:

```
Build completed successfully (… jobs).
== sorry / admit scan
== axioms
'QueensSpectrum.queensGraph_sanity' depends on axioms: [propext]
'QueensSpectrum.lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.lemma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.ker_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.finrank_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_mult_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_mult_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_alg_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_hasEigenvalue' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_alg_mult_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_eigenspace' depends on axioms: [propext, Classical.choice, Quot.sound]
'QueensSpectrum.queens_eigenspace_real' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS lean_check QueensSpectrum (Lean (version 4.37.0-rc1, x86_64-w64-windows-gnu, commit 0b77e12952ad39077d80d8bd6b66d601f225c321, Release))
```

On another platform the text inside the final parentheses names that platform (for example `x86_64-unknown-linux-gnu`). The job count depends on the Lake setup. The standalone run of this repository's files reported 6689 jobs, but that run predates `Eigenspace.lean` (see "Archived runs"); with it, one more module is built. In the project where the files were written, which also builds other work, the latest run reported 7057. The axiom lines must match exactly: compare your `lean/Pipeline/QueensSpectrum/axioms.log` with [`lean/logs/axioms.log`](lean/logs/axioms.log), ignoring line endings.

### Archived runs

| File | What it is |
| --- | --- |
| [`lean/logs/axioms.log`](lean/logs/axioms.log) | The axiom report written by `lean_check.sh` in the project where the formalization was written (2026-11-27), after `Eigenspace.lean` was added: 13 lines, including `queens_eigenspace` and `queens_eigenspace_real`. Its first 11 lines are identical to the earlier report, which an AI referee's fresh-checkout run reproduced byte for byte |
| [`lean/logs/lean_check_standalone.log`](lean/logs/lean_check_standalone.log) | Full console output of `bash scripts/lean_check.sh QueensSpectrum` run on a copy of the files of this repository as of paper version 2, that is, the 11 files before `Eigenspace.lean` was added (2026-11-27). Its last line, `exit=0 seconds=97`, was added by the shell wrapper that ran the script |
| [`lean/logs/axioms_standalone.log`](lean/logs/axioms_standalone.log) | The axiom report of that standalone run (11 lines, without the two Corollary 13 theorems); identical to the first 11 lines of `axioms.log` |

The standalone run has not been repeated with `Eigenspace.lean`. The 12 Lean files here are byte-identical to the files that passed `lean_check` in the working project (which wrote `axioms.log`), and the root file here imports `Main.lean`, which imports `Eigenspace.lean`.

The full `build.log` (about 0.9 MB of import notices and linter warnings) is not archived here; the standalone console log contains its last 20 lines.

### Runtime

- With Mathlib's prebuilt files already present, the standalone run took **97 s** wall-clock on one Windows 11 machine (the 11 files of this formalization take 4–13 s each to build). The Mathlib files were taken from a local copy of the same pinned packages, not downloaded.
- `lake exe cache get` downloads several GB; its time depends on the network and was not measured.
- Building Mathlib from source instead of downloading it takes hours and is not needed.

## Part 1b. Kernel replays and the Corollary 13 statement check

These reruns need a completed build from Part 1 (the `.olean` files in `lean/.lake`). Every tool ships with the Lean toolchain v4.37.0-rc1 that elan installs; nothing else is downloaded. [`LEAN.md`](LEAN.md) explains what the replays show and their limit; the full records are [`lean/kernel-replays/README.md`](lean/kernel-replays/README.md) and [`lean/kernel-replays/independent/README.md`](lean/kernel-replays/independent/README.md). The archived runs were made on 2026-11-27 on one Windows 11 machine (16 logical CPUs, 31.3 GB RAM).

### Versions

| Tool | Version | sha256 of the Windows binary used |
| --- | --- | --- |
| Lean toolchain | 4.37.0-rc1, commit `0b77e12952ad39077d80d8bd6b66d601f225c321` | `lean.exe` `a2a725e1239d5a7f955d911ce811858e08b376296a22a67ded6dd327134c17ae` |
| `leanchecker` | ships with that toolchain | `a8f1b1e960078d4a494cb6bb7a5dac5408a20edef8138e3b2dd13ca4bc0940dd` |
| `leanchecker-paranoid` | ships with that toolchain | `47123ab78b5af09179896eb0a7ac48d918fd1fc513248db7fd31f3e6482c88a7` |
| `leanexport` | lean4export 3.1.0 | `91cda59d8ed7f7528ca25784a29db2f461dc173645b3aeb0ec2b5b1c90eb82c1` |
| `nanoda_bin` | 0.4.31 | `f50fea903a8b44bb6f713fa973d10933194fe4873f085e780df5b470117d7c00` |
| `lean4lean` | embeds Lean githash `c155094f54eab345cca3da867dbd888a34fbf0d2` | `f2f9afc661d0ffd993cf0b0e276421952c2d1b8058deb57632939d566dff4391` |
| `con-ron` | ships with that toolchain | `c0f9e399992ca088ca06080f811f440f3be44e637e008f87766ebd83f170e0eb` |
| `con-leche` | ships with that toolchain | `9f86dcccba6b6a7ab1e70dd218e8468b9c760a4f113ad8f5ffcc2a0af0a14745` |
| Python (helper scripts) | 3.12.10, standard library only | |

On another platform the binaries differ and the hashes will not match.

### Replay by Lean's own kernel

From `lean/`:

```
lake env leanchecker -v Pipeline.QueensSpectrum
lake env leanchecker -v --fresh Pipeline.QueensSpectrum.Main
lake env leanchecker-paranoid -v Pipeline.QueensSpectrum
lake env leanchecker-paranoid -v --fresh Pipeline.QueensSpectrum.Main
```

Expected: exit code 0 for each. With `-v` the tool prints one `replaying …` line per module (12 lines for `Pipeline.QueensSpectrum`, which matches every module whose name starts with it) and nothing else; on a kernel rejection it prints `leanchecker found a problem in …` and exits non-zero. Archived wall times: 5 min 27 s and 8 min 25 s ([`replay_all.log`](lean/kernel-replays/replay_all.log), [`replay_fresh_main.log`](lean/kernel-replays/replay_fresh_main.log)); 5 min 7 s and 8 min 34 s for the paranoid build ([`paranoid_replay.log`](lean/kernel-replays/independent/logs/paranoid_replay.log), [`paranoid_fresh.log`](lean/kernel-replays/independent/logs/paranoid_fresh.log)). Peak memory of the parallel replay was about 9 GB.

### Independent kernels on an export

First write the export of the nine main theorems and their closure (from `lean/`; about 162 MB, 2 min 44 s; not archived because of its size):

```
lake env leanexport Pipeline.QueensSpectrum.Main -- \
  QueensSpectrum.queensGraph_sanity QueensSpectrum.queens_mult QueensSpectrum.queens_alg_mult \
  QueensSpectrum.queens_hasEigenvalue QueensSpectrum.queens_mult_real QueensSpectrum.queens_mult_rat \
  QueensSpectrum.queens_alg_mult_real QueensSpectrum.queens_eigenspace QueensSpectrum.queens_eigenspace_real \
  > queens.ndjson
```

The archived export had sha256 `c138f9d6e386c2069adc6b849bdb1c7eb6b8f5901aa9b3e14edf35beeb13ddbe` and 24689 declaration records (counted by [`keys.py`](lean/kernel-replays/independent/scripts/keys.py)). Then, with the toolchain's `bin` folder on the `PATH` (or `lake env` in front of each command):

```
nanoda_bin nanoda_config.json
lean4lean --import queens.ndjson
leanchecker-paranoid --from-export queens.ndjson
con-ron --verified --jobs=8 queens.ndjson
con-leche --verified --jobs=8 queens.ndjson
```

Before running `nanoda_bin`, copy [`nanoda_config.json`](lean/kernel-replays/independent/scripts/nanoda_config.json) and set `export_file_path` to your `queens.ndjson` and `pp_output_path` to a file in an existing folder (the archived config shows redacted paths). It permits exactly the axioms `propext`, `Classical.choice` and `Quot.sound` and stops with an error on any other.

| Command | Expected output | Exit | Archived time |
| --- | --- | --- | --- |
| `nanoda_bin nanoda_config.json` | `Checked 25995 declarations with no errors` | 0 | 3.8 s |
| `lean4lean --import queens.ndjson` | `checked 24686 declarations` | 0 | 39.5 s |
| `leanchecker-paranoid --from-export queens.ndjson` | `Lean default kernel accepts the solution` | 0 | 31.7 s |
| `con-ron --verified --jobs=8 queens.ndjson` | `con-ron: accepted 24689 declarations (--verified)` | 0 | 5.1 s |
| `con-leche --verified --jobs=8 queens.ndjson` | `con-leche: accepted 24689 declarations (--verified)`, after three `stats` lines | 0 | 8.0 s |

The archived outputs are in [`lean/kernel-replays/independent/logs/`](lean/kernel-replays/independent/logs/). The declaration counts differ because the checkers count constructors, recursors and quotient constants differently.

**Negative control.** Make a tampered copy in which the proof of `queens_eigenspace_real` is replaced by another theorem's proof, then run the five commands above on `tampered.ndjson` (for `nanoda_bin`, point `export_file_path` at it):

```
python -I -B lean/kernel-replays/independent/scripts/tamper.py queens.ndjson tampered.ndjson QueensSpectrum.queens_eigenspace_real
```

Expected: every checker rejects it. Archived: `nanoda_bin` exit 101 (assertion failure); `lean4lean`, `leanchecker-paranoid`, `con-ron` and `con-leche` exit 1 with a type mismatch at `queens_eigenspace_real` (the `*_tampered.log` files).

**Limit.** These kernels check the exporter's rendering of the compiled files, not the `.olean` files themselves; only Lean's own kernel replays those. The `lean4lean` binary in the toolchain cannot read v4.37.0-rc1 `.olean` files (`incompatible header`, [`lean4lean_olean.log`](lean/kernel-replays/independent/logs/lean4lean_olean.log)), and `con-ron` and `con-leche` decline them (format version 4; they read version 2).

**The standalone lean4checker.** The repository [leanprover/lean4checker](https://github.com/leanprover/lean4checker) is deprecated and does not build for v4.37.0-rc1 (its newest tag is `v4.29.0-rc8`; the build fails in `Lean4Checker/Replay.lean` on a changed signature of `addDeclCore`). The failed build is in [`standalone_build.log`](lean/kernel-replays/standalone_build.log). It is not needed: `leanchecker` above is its upstreamed successor.

### Exact check of the Corollary 13 statement

Pure Python (standard library only). The second script imports the first, so run both from their folder:

```
cd lean/kernel-replays/independent/cor13_statement_check
python -I -B cor13_check.py 4 10
python -I -B src_vectors_check.py
```

Expected last lines `COR13 CHECK: ALL PASS` and `SOURCE VECTORS CHECK: ALL PASS`, exit code 0. Each output should equal the archived [`cor13_check.log`](lean/kernel-replays/independent/cor13_statement_check/cor13_check.log) and [`src_vectors_check.log`](lean/kernel-replays/independent/cor13_statement_check/src_vectors_check.log), ignoring line endings. Both were rerun from this folder on 2026-11-27 while this guide was updated: identical output, 2.5 s and 1.3 s. (`-B` stops Python from writing a `__pycache__` folder next to the scripts.)

## Part 2. The computer checks (Python)

**Read this first.** The checks below confirm the Theorem and the individual steps of its proof for finitely many $n$, in exact integer and rational arithmetic. They are corroboration, with status `numerical`. None of them has been archived as a certificate (an independent second implementation rerun from a clean copy, with archived output); there is no `cert/` folder. For the Theorem they are superseded by the Lean proof of Part 1.

### Environment used for the archived runs

| Item | Version |
| --- | --- |
| OS | Windows 11 Home 10.0.26200 |
| Python | 3.12.10 |
| python-flint | 0.7.1 (used by `p2_verify.py` subcommands `sectors`, `fullflint`, `adjacency`) |
| sympy | 1.14.0 (used only by `p2_proofcheck.py symbolic`) |

`prover_check.py` is pure Python (integers and `fractions.Fraction`); it imports no third-party library. `p2_verify.py fraction` and `p2_verify.py lemmas` are also pure Python. All archived runs date from 2026-11-27. [`scripts/logs/versions.txt`](scripts/logs/versions.txt) is the version record written with the replay runs.

Install the two libraries with:

```
python -m pip install python-flint==0.7.1 sympy==1.14.0
```

### Commands

Run every command from the folder [`scripts/`](scripts/). Each command writes one log; the archived copy is in [`scripts/logs/`](scripts/logs/). To keep the archived logs intact, write new output somewhere else (for example `new/`) and compare.

| # | Command (from `scripts/`) | Archived output | Expected last line | Runtime |
| --- | --- | --- | --- | --- |
| 1 | `python prover_check.py small` | `logs/small_4_5.log` | `   null(M - nI) = 3: ok; eigenvectors on the board: ok` | 3.6 s (rerun) |
| 2 | `python prover_check.py 4 40` | `logs/replay_4_40.log` | `PROVER REPLAY: ALL PASS` | 381 s (archived); 469 s (a referee's rerun) |
| 3 | `python p2_verify.py fullflint 4 40` | `logs/fullflint_4_40.log` | `FULL GRAM (flint): ALL PASS` | 31.2 s (rerun) |
| 4 | `python p2_verify.py fraction 4 16` | `logs/fraction_4_16.log` | `FRACTION/INT IMPLEMENTATION: ALL PASS` | 3.6 s (rerun) |
| 5 | `python p2_verify.py fraction 17 40` | `logs/fraction_17_40.log` | `FRACTION/INT IMPLEMENTATION: ALL PASS` | 60.6 s (sum of per-$n$ times in the log) |
| 6 | `python p2_verify.py sectors 4 40` | `logs/sectors_flint_4_40.log` | `SECTORS (flint): ALL PASS` | 3.1 s (rerun) |
| 7 | `python p2_verify.py sectors 41 150` | `logs/sectors_flint_41_150.log` | `SECTORS (flint): ALL PASS` | 53.4 s (sum of per-$n$ times in the log) |
| 8 | `python p2_verify.py adjacency 4 12` | `logs/adjacency_4_12.log` | `ADJACENCY: ALL PASS` | 3.2 s (rerun) |
| 9 | `python p2_verify.py lemmas 4 40` | `logs/verify_lemmas_4_40.log` | `LEMMA CHECKS: ALL PASS` | 17.3 s (rerun) |
| 10 | `python p2_proofcheck.py sectors 4 40` | `logs/proofcheck_sectors_4_40.log` | `SECTOR FORMULAS FROM BOARD: ALL PASS` | 102.9 s (sum of per-$n$ times in the log) |
| 11 | `python p2_proofcheck.py a1 4 40` | `logs/proofcheck_a1_4_40.log` | `A1 LEMMA STEPS: ALL PASS` | 16.1 s (rerun) |
| 12 | `python p2_proofcheck.py e 4 40` | `logs/proofcheck_e_4_40.log` | `E LEMMA STEPS: ALL PASS` | 12.3 s (rerun) |
| 13 | `python p2_proofcheck.py b2 4 40` | `logs/proofcheck_b2_4_40.log` | `B2 LEMMA STEPS: ALL PASS` | 9.2 s (rerun) |
| 14 | `python p2_proofcheck.py g 1 80` | `logs/proofcheck_g_1_80.log` | `G_q PIVOT FORMULA q=1..80: ALL PASS` | 39.2 s (rerun) |
| 15 | `python p2_proofcheck.py symbolic` | `logs/proofcheck_symbolic.log` | `pivot k + gamma_k = k*(-k + q + 1)/(-k + q)` | 20.6 s (rerun) |

"Rerun" times are wall-clock times measured on 2026-11-27 while this guide was written, on the same Windows 11 machine, which was also running other jobs. Runs 2–14 exit with code 0 on success and 1 on any failure, and print `FAIL` or `FAILURE` where a check fails; a successful run ends with the last line shown. Runs 1 and 15 only print values; compare them with the archived logs.

### What each run shows

| # | What it checks | Range |
| --- | --- | --- |
| 1 | The $n=4$ and $n=5$ cases of §9 of the proof, printed in full | $n=4,5$ |
| 2 | Every identity of the proof, rebuilt from the board; $\dim\ker(M-nI)$ by rank modulo $2^{31}-1$ (upper bound on the nullity) plus explicit kernel vectors (lower bound) | $4\le n\le40$; Lemma 1 for $n\le24$; Corollary 13 for $n\le16$; Lemma G for $q\le60$ |
| 3 | Nullity of $M-nI$ on the full $(6n-2)\times(6n-2)$ matrix, FLINT exact integer rank | $4\le n\le40$ |
| 4, 5 | The same nullity by pure-Python fraction-free (Bareiss) elimination (the second implementation; it shares with run 3 only the routine that builds $M$ from the board) | $4\le n\le40$ |
| 6, 7 | Nullity of $M-nI$ on each sector, from the sector formulas, with FLINT: $A_1$ 0, $B_1$ $\lceil n/2\rceil-1$, $B_2$ $[n\text{ odd}]$, $E$ 0 | $4\le n\le150$ (one implementation above 40) |
| 8 | Nullity of $\mathbf A-(n-4)I$ on the $n^2\times n^2$ adjacency matrix, and the explicit eigenvectors of Corollary 13 | $4\le n\le12$ |
| 9 | Alternative steps for the $B_2$ sector (Appendix A of the proof) and a reduced system for the $A_1$ sector | $4\le n\le40$ |
| 10–13 | The sector formulas and the steps of Lemmas 7, 9 and 12, from the board, by a script written independently of runs 1–9 | $4\le n\le40$ |
| 14 | The pivots in the proof of Lemma G | $1\le q\le80$ |
| 15 | The reduced determinants $-\frac32$ and $5n^2$ of the remark after Lemma 9 (sympy) | symbolic |

Note on runs 4–7: their PASS lines also require that three sector determinants agree with closed-form expressions written into `p2_verify.py`. Those expressions are not proved and are not used anywhere in the proof; they are an extra consistency check only.

### Comparing with the archived output

The logs contain per-$n$ timings such as `(0.4s)`. Four archived logs (`fraction_4_16.log`, `fraction_17_40.log`, `sectors_flint_4_40.log`, `sectors_flint_41_150.log`) also start with a UTF-8 byte-order mark, and on the Windows machine most logs have CRLF line endings. The archived logs are kept exactly as written, so the comparison removes the timings, a leading byte-order mark and carriage returns from both sides; everything else should match exactly. In a POSIX shell with GNU sed (Git Bash, Linux; on macOS use `gsed`):

```
mkdir -p new
norm() { sed -E -e '1s/^\xEF\xBB\xBF//' -e 's/\r$//' -e 's/ \([0-9.]+s\)//' "$1"; }
python p2_verify.py fraction 4 16 > new/fraction_4_16.log
diff <(norm new/fraction_4_16.log) <(norm logs/fraction_4_16.log) && echo SAME
```

Change the command and the two file names for the other runs.

In Windows PowerShell 5.1, `>` may write UTF-16 or add a byte-order mark; compare with `Compare-Object` on `Get-Content` output (after removing the timings) rather than byte by byte.

**Reproduction on 2026-11-27.** While writing this guide, runs 1, 3, 4, 6, 8, 9 and 11–15 were rerun from fresh copies of the three scripts. Each exited with code 0, and each output was identical to the archived log apart from the timings. Runs 2, 5, 7 and 10 were not rerun then, to keep load off a shared machine. Run 2 was rerun independently by both referees of review round 1, with output identical to the archive apart from timings.

## Integrity

SHA-256 of the Lean files and the Lean check, computed on 2026-11-27 after normalizing line endings to LF (paths relative to the root of this repository):

```
f9a187cdfe09af10b4c5ff4495cf502557e7ff5d70ca6b72cb0cbe71a768c8ee  lean/Pipeline/QueensSpectrum/AlgMult.lean
a9f8d805c61a2db7446296e3dc50c7d907d37be70fe8a08522c704e465f03b61  lean/Pipeline/QueensSpectrum/Count.lean
019d5b9d37a8da8c2b2b625860439f5d354fabe700e674b9c0481fd8e51615a8  lean/Pipeline/QueensSpectrum/Defs.lean
496cd4649ea45a3f79cffaa5ad928c7dead84c591b4b9ae77996aea6fb3149b8  lean/Pipeline/QueensSpectrum/Eigenspace.lean
8089b2b927cd4d6d091628167800cdfc612db2fdcc6704530d579486c150ff8d  lean/Pipeline/QueensSpectrum/Kernel.lean
5568d5326a4beca3577f9d8565b6653ee9525868843df26af3f477181c75c98a  lean/Pipeline/QueensSpectrum/Main.lean
4ee4754e491f0019fd76c76cb215aecffb75621ae9609235f3332095e40c747a  lean/Pipeline/QueensSpectrum/Reduction.lean
7e41d587a3daf98703f71162f6c548adf17473b347e965a3923ca61c7403e19f  lean/Pipeline/QueensSpectrum/SectorA1.lean
0b93fdeec614fd593b2fb87a2729559e1885f4c985331a5aebf0b1d218d74a06  lean/Pipeline/QueensSpectrum/SectorB2.lean
431b2e35c079dd30ba2a62f6dbc27bd99565d9c797eb7d0839b91306bea86ca8  lean/Pipeline/QueensSpectrum/SectorE.lean
d62f95047fac835a40432eebf293e3f5db08f4a70ef5f4832a149c885986a95c  lean/Pipeline/QueensSpectrum/Seq.lean
7dae61ec39938e67766209577e8d1e8aecb37fd7b008f438044d617737197c23  lean/Pipeline/QueensSpectrum/Symmetry.lean
0879f4704d7b2f87dcdd4b691a8b4d7171308377cb6704824f3f8696884822cf  lean/Pipeline.lean
f11739c25d1640e2b3fda8a98af6d64e97d7b2b1c99840535587a9079b3afee7  lean/lean-toolchain
9bcb7a2358388c512f7dee02f176d3ab62786b67e451e9aefaf3983a2f4c0986  lean/lakefile.toml
2d4de66c9b38d7ba993501e58b3515d865010b7a22f78fae22fc2d4f13d8596a  lean/lake-manifest.json
5ea44ab15d5a8f4841e353d45a429a3c0e4f7eb59d58dcef8954cc740ff029f6  lean/logs/axioms.log
db77b9c8fc69b1dab24df214c68f8b68cc7f454b91cf4ab2b47283bb30e7c66f  lean/logs/axioms_standalone.log
db063f67b6ec4fc8a5622724b934d0638e21fc0f2534e85274ab4d6bf522cbd2  lean/logs/lean_check_standalone.log
fbf8a005932b2b4464910656ca7ae47b276a557c437ab40dec2efffaac6eff9d  scripts/lean_check.sh
```

The hashes of `Eigenspace.lean`, `Main.lean` and `axioms.log` were updated on 2026-11-27, after paper version 2, when Corollary 13 was formalized; the other lines are unchanged. Before normalization, `Eigenspace.lean` has CRLF line endings and sha256 `d00ed63a16ff3b3f53312d9ff6acbfedaeda3824785a8893d984d32be0d6e7c3`, the value recorded by the AI referee who checked its statement; `Main.lean` has LF line endings, so its two hashes agree.

SHA-256 of the kernel-replay records in [`lean/kernel-replays/`](lean/kernel-replays/), computed on 2026-11-27 after normalizing line endings to LF (paths relative to that folder):

```
93143d091ff133252a510753dd906252caeab34ba455e1a7594cd95b899fb990  README.md
ae957b1ee755fa8c1ed9ac1c1341a65854152944adf4aa8d4a3adc4f803af8e6  replay_all.log
a3529e0bb213b5cf8585d7d74ace12f0fcde0bf7686824e80995775a8720bcdf  replay_fresh_main.log
bc47c40fb44366ac3d62a5aced196388f325bf24daed808e053ee45f59721aa0  replay_pre.log
b22b24adabacf55b0e4f89cc208630815a8e7c6cefae1cf90df7ba97cac5a15c  standalone_build.log
a9344bfb185fc82aae14443374e78f0f506c275d972eef1b8275cb98cfb92e8e  independent/README.md
5d874031ffe558701d6f011f99c634ecaa294975e0356329bc9725265942903c  independent/cor13_statement_check/cor13_check.log
56b8999996b387ea8b2df6b369696be227982f6103afae0f859f183812f6894e  independent/cor13_statement_check/cor13_check.py
7039b54c83226e56f099c4586d032b490f4cece81f550fb23d74b73a500fd5c1  independent/cor13_statement_check/src_vectors_check.log
6b19724bfa9096f629f442112cb3e10996c8b32f0f5c4d7652bd61f93c677ed3  independent/cor13_statement_check/src_vectors_check.py
67fde07ee70ebf046ffaa9585e5d37d634a93b4d5d5f60f0bebadc1738cd3038  independent/logs/con-leche_olean.log
a4cdcc20f9f6fb2e68f4e8ee73c4d0772927c535ad57409f3e3e46d084020c1b  independent/logs/con-leche_queens.log
eff88e8acbd68a0533a1941d583a06d322f6be5c3342b9294555ece0c851ac53  independent/logs/con-leche_tampered.log
ba1bf9a557b5f9b4dfff778e60ea258352cfef1ffb7bd09bb8440a2030ce9874  independent/logs/con-ron_olean.log
0204f89cbb1c1f5a991c46ad44e51bf36ecf50d773b751f07cca8eab8c224f93  independent/logs/con-ron_queens.log
ffa58a1b56d99b2f1e5446605352e36b17ca5c0f55af094021138a4ea76486d1  independent/logs/con-ron_tampered.log
bc888dbf5e6f8bdaf7109e2f94f3bd42390603f3f8fc38bc94a1326fdf3400f8  independent/logs/export.err
19025a80b4e1eec09683a47fbf5d004d03861c092ba7c59014611e705260f376  independent/logs/lean4lean_import.log
c64ca40429855a9b363e96fac2fa1809ec9961c17b1fa45fb45e7f5018d18385  independent/logs/lean4lean_import_compare.log
99116165a784d732b8583b54b299b6967156a37b1a186d281569e0aa92444039  independent/logs/lean4lean_import_tampered.log
809ff010e60e264cde97f23d7531242bf9c3cb0c4a1f3784b84ea0497f1c235a  independent/logs/lean4lean_olean.log
dddb6bb48374466b5648e48e016697b4e4a731ea17f55b70140d9571838d7ce9  independent/logs/nanoda.log
4aad43515195f33a48a42946c82dd8c9d6fa361bbe28cb331c4b14bd0fff274c  independent/logs/nanoda_pp.txt
3294d46d9322604b7773c425abf1d8e099b53f3128a5658d5d2ee8ef70f308c2  independent/logs/nanoda_tampered.log
f6eb011d06921a762faf07619c6fc80609eaee6f3a6006b991e98e67c9b145f3  independent/logs/paranoid_export.log
006bfbf2a9a5f7a8f65651214b4f79a436712fe56b64daf74aaf161fbf32bc7d  independent/logs/paranoid_export_tampered.log
e435a5caaf19d0d76c8470a3154ac1ca7b8928775f1f96aab025a442bfb03b26  independent/logs/paranoid_fresh.log
66445d004f355fbfbbc7c7461cfa4e13da47cf3df42a041ef6e2ed79a676aef6  independent/logs/paranoid_replay.log
edec2191137373d939e8c5de48116e528b83c1d9544a4c69824d841659898bd9  independent/scripts/keys.py
a33ca7bec83d7d601b2cbced2fcd4090c6775366de40308cf3b04e7c73217d85  independent/scripts/nanoda_config.json
d73f727a95925c16a2ffe323eb0dbecbe3d9cfabed88acbc502e3814c5244c73  independent/scripts/tamper.py
```

SHA-256 of the Python files in [`scripts/`](scripts/), computed on 2026-11-27 after normalizing line endings to LF (the form git stores; these are unchanged copies of the working files; paths relative to `scripts/`):

```
fe3c45ce3ed5b932fdff031ed5a6e52be22b13f9a8a4a72fdbf069b7d10a3708  prover_check.py
ddaf58cf06d225f487cd6a055b2085800789daf159ebb7da46479e730605cc0c  p2_verify.py
9e25ddcb70a07f1435321eec0f856a91e23dfcfa79aa3f37ef3d2cfb28948fe4  p2_proofcheck.py
c48264e1a881e5accdc15f1ba0ac2b943d17bbd61869e549a319497c93ef3ddc  logs/small_4_5.log
4d00f66e1cb10b030d982385dc0449ba57e8644647ffcfe8a7ae820746109972  logs/replay_4_40.log
900dedc48f789bf679b826171aad1521c809b341faa89d8a27ab20099a801620  logs/versions.txt
654251151e465ebcbf4e6013c8e830fd462099c9380d09d844fe14ca8eda1373  logs/fullflint_4_40.log
f98143d123ccef28262e3185b33552cc106b7f644f3b3f46e24ce591a5d41c80  logs/fraction_4_16.log
fa6c8903cf368be7b6802b322f8d02b3b0f1da29547e611b0e5c9171d6cf14a9  logs/fraction_17_40.log
520aeb7dae36d985f5d476724ff1629581e85beea6464b7af3dfae7d06396af1  logs/sectors_flint_4_40.log
3f143d5cf8cea632d38cff1035084f0e9bbba71312261ce486d1dfd0cd3193a2  logs/sectors_flint_41_150.log
195e839ef887f9339b78af3b7fcf8a48c7958f52a5e0fa01106cd5b9ed961af7  logs/adjacency_4_12.log
f0b6f28d39bc2925214a8add7540b6f3fbd57a98d3f1c0566c8227490dda0153  logs/verify_lemmas_4_40.log
3444c8bce1b5876b0582e8a02e747060b0311d1e0e0d421d12d09d43ccdd18d1  logs/proofcheck_sectors_4_40.log
24a4e40c9557786233486887ba64b456eeb69156c2c29db4b52a0f0b9b128c47  logs/proofcheck_a1_4_40.log
341741ac7a6a3401154f9717d4db3720b5327168df7428ed694f39ab50ec2c31  logs/proofcheck_e_4_40.log
4a1d7e22d81c06b6ce0292f71510ff824fa556e198b61125bdf19d643ee4affa  logs/proofcheck_b2_4_40.log
aea29274cdafbbc532e8fcd256ab07d36a0b53ada91fe5bfe85d283248749611  logs/proofcheck_g_1_80.log
e06f138b908afc7540188a5c9221feaeef1b3a2710556e50bb74c2a78f8a3c5f  logs/proofcheck_symbolic.log
```

On the Windows machine most of these files have CRLF line endings, which give different hashes for the same content (for example `efa75878…` for `logs/small_4_5.log` and `e644eadd…` for `logs/replay_4_40.log`). Normalize line endings before comparing.

**One script differs from the version that wrote its log.** `logs/replay_4_40.log` and `logs/small_4_5.log` were written by an earlier version of `prover_check.py`. After review round 1, one comment line in it was corrected (it now names Lemma 8 instead of step (A.5)). No code changed: a round-2 referee confirmed that the two versions have identical Python syntax trees. The `small` replay was rerun after the change and is identical to the archive, and referees reran the full replay up to $n=26$ with the new version, identical to the archive apart from timings.

The script names (`p2_verify.py`, `p2_proofcheck.py`, `prover_check.py`) are kept from the working repository so that they match the archived logs. Some docstrings refer to internal working notes that are not part of this repository; the mathematics they check is all in [`PROOF.md`](PROOF.md).

## Part 3. LaTeX

[`paper.pdf`](paper.pdf) (version 3, 26 pages) was compiled from [`paper.tex`](paper.tex) on 2026-11-27 with Tectonic: no errors, no undefined references or citations, and no overfull boxes in the final pass (a few underfull boxes from page breaking remain). Command:

```
tectonic -X compile paper.tex
```

With TeX Live or MiKTeX, `latexmk -pdf paper.tex` also builds it.

It needs only the standard `amsart` class and the packages `fontenc` (T1), `lmodern`, `amssymb`, `amsthm`, `booktabs`, `array` and `hyperref`.
