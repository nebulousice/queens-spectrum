# Queens spectrum: replay by independent kernels

*2026-11-27, Checker (Lean statement review of QS-2 at commit 60cb49b). Nothing was downloaded: every tool below ships in the toolchain already installed (`~/.elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin`). Local user paths are redacted as `<user>`, the hostname as `<host>`, the session scratchpad as `<scratchpad>`.*

## Verdict

| Checker | What it is | Input | Result |
| --- | --- | --- | --- |
| `nanoda_bin` 0.4.31 | independent kernel, Rust (ammkrn/nanoda_lib) | lean4export file of the closure of the 9 main theorems | **PASS** (25 995 declarations, exit 0, 3.8 s); tampered control **rejected** (exit 101) |
| `lean4lean` | independent kernel written in Lean (digama0/lean4lean) | the same export file, via `--import` | **PASS** (24 686 declarations, exit 0, 40 s); tampered control **rejected** (exit 1) |
| `lean4lean` | same | `.olean` files directly | **not run**: the binary reads only `.olean` files of a different Lean build (`incompatible header`, below) |
| `leanchecker-paranoid` | Lean's own kernel, a separate checking build (not an independent kernel) | every `Pipeline.QueensSpectrum.*` module, replayed from its imports | **PASS** (12 of 12 modules, exit 0, 5 min 7 s) |
| `leanchecker-paranoid` | same | `--fresh Pipeline.QueensSpectrum.Main` (whole closure from an empty environment) | **PASS** (exit 0, 8 min 34 s) |
| `leanchecker-paranoid` | same | the export file (`--from-export`) | **PASS** (exit 0, 32 s); tampered control **rejected** (exit 1) |
| `con-ron`, `con-leche` (extra, not requested) | two further kernels shipped in the toolchain | the export file | **PASS** (24 689 declarations each, `--verified`, exit 0); tampered control **rejected** by both (exit 1). `.olean` mode **declined** (reads `.olean` format version 2 only; ours is version 4) |

What this shows: the 9 headline theorems of `Main.lean` and `Eigenspace.lean` (`queensGraph_sanity`, `queens_mult`, `queens_alg_mult`, `queens_hasEigenvalue`, `queens_mult_real`, `queens_mult_rat`, `queens_alg_mult_real`, `queens_eigenspace`, `queens_eigenspace_real`), together with every declaration they depend on (Lean core, Batteries and Mathlib included), are accepted by two kernels that do not share code with Lean's C++ kernel (nanoda, lean4lean) and by two more (con-ron, con-leche). The only axioms in the exported closure are `propext`, `Classical.choice` and `Quot.sound`; nanoda was run with exactly those three permitted and `unpermitted_axiom_hard_error: true`.

What it does not show: the export file is produced by `leanexport` (lean4export 3.1.0, a Lean program that reads the `.olean` files), so the independent kernels check the exporter's rendering of the environment, not the `.olean` files themselves. The kernel-side pretty print by nanoda ([`logs/nanoda_pp.txt`](logs/nanoda_pp.txt)) shows that the exported types of `queens_eigenspace`, `queens_eigenspace_real`, `queens_mult` and the definitions `queensGraph`, `Attack` are the ones in the source files. The `.olean` files themselves were replayed only by the Lean kernel (`leanchecker`, earlier; `leanchecker-paranoid`, here).

## 1. Tools

Toolchain: `Lean (version 4.37.0-rc1, x86_64-w64-windows-gnu, commit 0b77e12952ad39077d80d8bd6b66d601f225c321, Release)`. Mathlib `8ec7bd8e5f837ab7e335374928e18341c4e9f385` (`lean/lake-manifest.json`), the existing `lean/.lake` build. `lake build --no-build Pipeline.QueensSpectrum.Main` reported "All targets up-to-date" before the runs, and the files `lean/Pipeline/QueensSpectrum/*.lean` in the working tree are identical to commit 60cb49b.

| Binary | sha256 | size (bytes) | version / how identified |
| --- | --- | --- | --- |
| `nanoda_bin.exe` | `f50fea903a8b44bb6f713fa973d10933194fe4873f085e780df5b470117d7c00` | 1 146 880 | `--help` prints `nanoda_bin 0.4.31`; takes one argument, a JSON config file |
| `lean4lean.exe` | `f2f9afc661d0ffd993cf0b0e276421952c2d1b8058deb57632939d566dff4391` | 33 063 936 | embeds Lean githash `c155094f54eab345cca3da867dbd888a34fbf0d2` (not the toolchain's `0b77e129…`); flags `-v`, `--fresh`, `--compare`, `--import FILE`; embeds lean4export's `Export.Parse`, so `--import` reads a lean4export file |
| `leanchecker-paranoid.exe` | `47123ab78b5af09179896eb0a7ac48d918fd1fc513248db7fd31f3e6482c88a7` | 14 715 392 | embeds githash `0b77e129…`; same CLI as `leanchecker` (`-v`, `--fresh`, `--from-export`, `--silent`). The toolchain ships no separate source or documentation for it; from the name and the shared CLI it is the `leanchecker` driver linked against a separately built kernel with extra internal checks. It is Lean's kernel, not an independent one. |
| `leanexport.exe` | `91cda59d8ed7f7528ca25784a29db2f461dc173645b3aeb0ec2b5b1c90eb82c1` | 241 664 | prints lean4export 3.1.0, Lean 4.37.0-rc1, githash `0b77e129…` |
| `con-ron.exe` | `c0f9e399992ca088ca06080f811f440f3be44e637e008f87766ebd83f170e0eb` | 2 994 176 | `--help` |
| `con-leche.exe` | `9f86dcccba6b6a7ab1e70dd218e8468b9c760a4f113ad8f5ffcc2a0af0a14745` | 121 297 408 | `--help` |
| `leanchecker.exe` (reference) | `a8f1b1e960078d4a494cb6bb7a5dac5408a20edef8138e3b2dd13ca4bc0940dd` | 57 856 | as in `../README.md` |

Machine: the same Windows 11 machine as `../README.md` (16 logical CPUs, 31.3 GB RAM). Python 3.12.10 for the helper scripts.

## 2. The export file

```
cd lean
lake env leanexport Pipeline.QueensSpectrum.Main -- \
  QueensSpectrum.queensGraph_sanity QueensSpectrum.queens_mult QueensSpectrum.queens_alg_mult \
  QueensSpectrum.queens_hasEigenvalue QueensSpectrum.queens_mult_real QueensSpectrum.queens_mult_rat \
  QueensSpectrum.queens_alg_mult_real QueensSpectrum.queens_eigenspace QueensSpectrum.queens_eigenspace_real \
  > queens.ndjson
```

- Wall time 2 min 44 s, exit 0, empty stderr ([`logs/export.err`](logs/export.err) holds only the `time` output).
- `queens.ndjson`: 162 367 960 bytes, 3 060 773 lines, sha256 `c138f9d6e386c2069adc6b849bdb1c7eb6b8f5901aa9b3e14edf35beeb13ddbe`. Not archived (size); it is regenerated by the command above.
- Contents (counted by [`scripts/keys.py`](scripts/keys.py)): 17 865 theorems, 6 203 definitions, 612 inductive blocks, 2 opaques, 4 quotient constants, 3 axioms (`propext`, `Classical.choice`, `Quot.sound`) = 24 689 declaration records. lean4lean counts 24 686 (the four quotient constants are added as one); nanoda counts 25 995 (constructors and recursors separately). All 9 target theorems are present.
- Restricting to the closure of the 9 theorems is the "restrict to given declarations" option: lemmas of the `Pipeline.QueensSpectrum.*` files that no headline theorem uses are not in the export, and they carry no claim.

## 3. Runs

| Log | Command (from `lean/`, or from the folder of the export file) | Wall time | Exit | Output |
| --- | --- | --- | --- | --- |
| [`logs/nanoda.log`](logs/nanoda.log) | `nanoda_bin.exe nanoda_config.json` ([config](scripts/nanoda_config.json): 8 threads, 1 GiB stack, Nat and String extensions on, the 3 axioms permitted, hard error on any other) | 3.8 s | 0 | `Checked 25995 declarations with no errors` |
| [`logs/nanoda_pp.txt`](logs/nanoda_pp.txt) | same run, `pp_declars` | | | kernel-side print of `queensGraph`, `Attack`, `queens_eigenspace`, `queens_eigenspace_real`, `queens_mult`, and the 3 axioms |
| [`logs/lean4lean_import.log`](logs/lean4lean_import.log) | `lean4lean.exe --import queens.ndjson` | 39.5 s | 0 | `checked 24686 declarations` |
| [`logs/lean4lean_import_compare.log`](logs/lean4lean_import_compare.log) | `lean4lean.exe --import --compare queens.ndjson` | 39.1 s | 0 | `checked 24686 declarations` |
| [`logs/lean4lean_olean.log`](logs/lean4lean_olean.log) | `lake env lean4lean -v Pipeline.QueensSpectrum.Defs` | 1 min 8 s | 1 | `failed to read file '…\Defs.olean', incompatible header`: the binary was built against Lean githash `c155094f…`, so it cannot read v4.37.0-rc1 `.olean` files. Run with no arguments it fails the same way on the toolchain's own `Std` files. Not a kernel rejection. |
| [`logs/paranoid_replay.log`](logs/paranoid_replay.log) | `lake env leanchecker-paranoid -v Pipeline.QueensSpectrum` | 5 min 7 s | 0 | `replaying …` for all 12 modules, no problem reported |
| [`logs/paranoid_fresh.log`](logs/paranoid_fresh.log) | `lake env leanchecker-paranoid -v --fresh Pipeline.QueensSpectrum.Main` | 8 min 34 s | 0 | `replaying Pipeline.QueensSpectrum.Main with --fresh`, no problem reported |
| [`logs/paranoid_export.log`](logs/paranoid_export.log) | `leanchecker-paranoid.exe --from-export queens.ndjson` | 31.7 s | 0 | `Lean default kernel accepts the solution` (the driver's fixed message) |
| [`logs/con-ron_queens.log`](logs/con-ron_queens.log) | `con-ron.exe --verified --jobs=8 queens.ndjson` | 5.1 s | 0 | `accepted 24689 declarations (--verified)` |
| [`logs/con-leche_queens.log`](logs/con-leche_queens.log) | `con-leche.exe --verified --jobs=8 queens.ndjson` | 8.0 s | 0 | `accepted 24689 declarations (--verified)` |
| [`logs/con-ron_olean.log`](logs/con-ron_olean.log), [`logs/con-leche_olean.log`](logs/con-leche_olean.log) | `--olean --search-path=… --constant=… Pipeline.QueensSpectrum.Main` | 0.1 s | 2 | declined: `.olean format version 4 (this reader reads version 2)` |

The export and the export-file checkers ran while one of the two `leanchecker-paranoid` runs was in progress (8 worker threads each, to share the 16 CPUs); this affects timing only.

## 4. Negative control (the checkers do reject a bad proof)

[`scripts/tamper.py`](scripts/tamper.py) copies the export and replaces the proof term (`value`) of `QueensSpectrum.queens_eigenspace_real` by the proof term of the previous universe-monomorphic theorem in the file (`QueensSpectrum.N_vecB2._proof_1_37`), leaving its type unchanged (`tampered.ndjson`, sha256 `9eab5c2678543bc01fafb41c126da10b2df5c4aa3d4a64535c762865b441ac99`, not archived).

| Log | Checker | Exit | Message |
| --- | --- | --- | --- |
| [`logs/nanoda_tampered.log`](logs/nanoda_tampered.log) | nanoda_bin | 101 | panic `assertion failed: self.def_eq(u, v)` in `tc.rs` (rejection by assertion) |
| [`logs/lean4lean_import_tampered.log`](logs/lean4lean_import_tampered.log) | lean4lean `--import` | 1 | `at QueensSpectrum.queens_eigenspace_real: (kernel) declaration type mismatch` |
| [`logs/paranoid_export_tampered.log`](logs/paranoid_export_tampered.log) | leanchecker-paranoid `--from-export` | 1 | `declaration type mismatch, 'QueensSpectrum.queens_eigenspace_real'` |
| [`logs/con-ron_tampered.log`](logs/con-ron_tampered.log) | con-ron | 1 | `rejected: type mismatch in theorem [at theorem QueensSpectrum.queens_eigenspace_real …]` |
| [`logs/con-leche_tampered.log`](logs/con-leche_tampered.log) | con-leche | 1 | `invalid: type mismatch in theorem QueensSpectrum.queens_eigenspace_real` |

(A first tamper attempt borrowed the proof of a universe-polymorphic theorem; nanoda then panicked on an undefined universe parameter. The archived control is the second, cleaner one.)

## 5. Also archived here

[`cor13_statement_check/`](cor13_statement_check/): the Checker's exact rational check that the Lean family of `queens_eigenspace` equals `ker(A − (n−4)I)` for 4 ≤ n ≤ 10, and that the source eigenvectors (Yⁿ, Zⁿ of arXiv:2012.01992; F_{n,ℓ}, E_{n,n−4} of arXiv:2301.08106, as transcribed in `PROOF.md` §8) span the same space. See `../../reviews/checker-lean-cor13-60cb49b.md`.

## Reproduce

```
cd lean
lake env leanchecker-paranoid -v Pipeline.QueensSpectrum
lake env leanchecker-paranoid -v --fresh Pipeline.QueensSpectrum.Main
lake env leanexport Pipeline.QueensSpectrum.Main -- <the 9 names of §2> > queens.ndjson
nanoda_bin nanoda_config.json        # edit export_file_path / pp_output_path first; pp_output_path must exist
lean4lean --import queens.ndjson
leanchecker-paranoid --from-export queens.ndjson
con-ron --verified queens.ndjson
con-leche --verified queens.ndjson
python -I <repo>/targets/queens-spectrum/lean4checker/independent/scripts/tamper.py queens.ndjson tampered.ndjson QueensSpectrum.queens_eigenspace_real
python -I <repo>/targets/queens-spectrum/lean4checker/independent/scripts/keys.py queens.ndjson QueensSpectrum.queens_eigenspace
cd <repo>/targets/queens-spectrum/lean4checker/independent/cor13_statement_check
python -I cor13_check.py 4 10       # expected last line: COR13 CHECK: ALL PASS
python -I src_vectors_check.py      # expected last line: SOURCE VECTORS CHECK: ALL PASS
```
