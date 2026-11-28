# Lean 4 + Mathlib: what is formalized

## Summary

**The whole Theorem is formalized, for every $n\ge4$** (2026-11-27). Lean 4 checks a complete proof, from the definition of the $n$-Queens graph, that the eigenvalue $n-4$ has multiplicity exactly $(n-2)/2$ for even $n$ and $(n+1)/2$ for odd $n$. It proves this for both meanings of "multiplicity" (dimension of the eigenspace, and order as a root of the characteristic polynomial), over every linearly ordered field, so in particular over $\mathbb R$ and $\mathbb Q$.

**Corollary 13, the explicit eigenspace, is also formalized** (2026-11-27; included in version 3 of the paper). Lean proves both inclusions: for every $n\ge4$, a function on the squares lies in the eigenspace of $n-4$ exactly when it has the form given in Corollary 13.

**The compiled proofs were replayed by several kernels** (2026-11-27; also in version 3 of the paper): by Lean's own checker on all modules, and by independent kernels on an exported copy of the main theorems. See [Kernel replays](#kernel-replays) below, with its limit.

| Item | Value |
| --- | --- |
| Files | [`lean/Pipeline/QueensSpectrum/`](lean/Pipeline/QueensSpectrum/): 12 files, 2,283 lines (11 files, 2,157 lines for the Theorem; [`Eigenspace.lean`](lean/Pipeline/QueensSpectrum/Eigenspace.lean), 123 lines, for Corollary 13; `Main.lean` gained one import line and two `#print axioms` lines) |
| Lean | 4.37.0-rc1 ([`lean/lean-toolchain`](lean/lean-toolchain)) |
| Mathlib | commit `8ec7bd8e5f837ab7e335374928e18341c4e9f385`, pinned in [`lean/lake-manifest.json`](lean/lake-manifest.json) |
| Check | `bash scripts/lean_check.sh QueensSpectrum`: PASS |
| Build | 0 errors |
| Unproved steps | none: no `sorry`, `admit` or `native_decide` in the files |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only ([`lean/logs/axioms.log`](lean/logs/axioms.log)) |
| Independent checks | the check passed in two separate runs on 2026-11-27, both before and after `Eigenspace.lean` was added; an AI referee (Claude Opus) rebuilt the files of the Theorem from a fresh checkout (PASS, byte-identical axiom output) and confirmed that the Lean statement matches the source; a second check by the same model confirmed the statement of Corollary 13 |
| Kernel replays | `leanchecker` and `leanchecker-paranoid` (Lean's kernel) on all 12 modules and, with `--fresh`, on the whole closure of `Main.lean`: PASS; `nanoda_bin` 0.4.31, `lean4lean`, `con-ron`, `con-leche` on a lean4export file of the closure of the nine main theorems: PASS; tampered export rejected by all five export checkers ([`lean/kernel-replays/`](lean/kernel-replays/)) |

Exact commands, runtimes and the expected output are in [`REPRODUCE.md`](REPRODUCE.md).

## The statement

The definition of the graph is in [`Defs.lean`](lean/Pipeline/QueensSpectrum/Defs.lean). Squares are `Fin n × Fin n`, that is, pairs $(i,j)$ with $0\le i,j\le n-1$. These four lines are the whole definition:

```lean
def Attack (n : ℕ) (x y : Fin n × Fin n) : Prop :=                    -- line 27
  x.1 = y.1 ∨ x.2 = y.2 ∨ ((x.1 : ℤ) - x.2 = (y.1 : ℤ) - y.2) ∨
    ((x.1 : ℤ) + x.2 = (y.1 : ℤ) + y.2)
  Adj x y := x ≠ y ∧ Attack n x y                                       -- line 34, in queensGraph
```

In words: two distinct squares are adjacent when they share a row, a column, a diagonal or an antidiagonal. The differences and sums are taken in the integers, so nothing wraps around modulo $n$. The source indexes squares from 1 and Lean from 0; shifting the indices is a graph isomorphism.

The main theorems are in [`Main.lean`](lean/Pipeline/QueensSpectrum/Main.lean). Here `A = (queensGraph n).adjMatrix K` is Mathlib's adjacency matrix (entry 1 for adjacent squares, 0 otherwise).

| Theorem | File, line | Statement, for every linearly ordered field `K` and every `n ≥ 4` |
| --- | --- | --- |
| `queens_mult` | `Main`, 49 | `finrank K (End.eigenspace (toLin' A) ((n:K) - 4)) = if Even n then (n - 2) / 2 else (n + 1) / 2`, that is, the dimension of the kernel of $\mathbf A-(n-4)I$ |
| `queens_alg_mult` | `Main`, 58 | the same value for `A.charpoly.rootMultiplicity ((n:K) - 4)`, the multiplicity of $n-4$ as a root of the characteristic polynomial |
| `queens_hasEigenvalue` | `Main`, 66 | $n-4$ is an eigenvalue of $\mathbf A$ |
| `queens_mult_real`, `queens_mult_rat` | `Main`, 76, 82 | `queens_mult` for `K = ℝ` and `K = ℚ` |
| `queens_alg_mult_real` | `Main`, 88 | `queens_alg_mult` for `K = ℝ` |
| `queensGraph_sanity` | `Main`, 41 | a kernel-checked sanity test of the definition on the 4 × 4 board |
| `queens_eigenspace` | `Eigenspace`, 74 | **Corollary 13**: `x` lies in the eigenspace of $n-4$ if and only if $`x(i,j)=r_i-r_j+\gamma([i=j]-[i+j=n-1])`$ for some palindromic `r` and some `γ` with `γ = 0` for even `n` (statement below) |
| `queens_eigenspace_real` | `Eigenspace`, 116 | `queens_eigenspace` for `K = ℝ`, the identical statement |


The right-hand side is a natural number with truncating division. For $n\ge4$ the division is exact, so it equals $(n-2)/2$ or $(n+1)/2$. The eigenvalue `(n:K) - 4` is computed in the field, so there is no truncation there.

**This is the Theorem of the paper, not a weaker statement.** Over $\mathbb R$ it says exactly what the second sentence of Conjecture 1 of [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) says (part (b) in our labelling; the source does not number its parts). The extra generality (any ordered field, both multiplicities) only adds strength.

### The statement of Corollary 13

```lean
theorem queens_eigenspace (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (hn : 4 ≤ n) (x : Fin n × Fin n → K) :
    x ∈ End.eigenspace (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4) ↔
      ∃ r : Fin n → K, (∀ i, r i.rev = r i) ∧ ∃ γ : K, (Even n → γ = 0) ∧
        ∀ i j : Fin n, x (i, j) = r i - r j +
          γ * ((if i = j then 1 else 0) - (if (i : ℕ) + (j : ℕ) = n - 1 then 1 else 0))
```

In words: `i.rev` is $n-1-i$, so `r i.rev = r i` says that $r$ is palindromic. The sum $i+j$ is taken in the natural numbers, so nothing wraps around, and $n-1$ is not truncated because $n\ge4$. The only hypothesis is $n\ge4$. The proof computes the image under the incidence matrix $N$ of the kernel of $M-nI$, which the proof of the Theorem already identifies exactly (`ker_char`, `vecB1_mem`, `vecB2_mem`).

The statement was checked against Corollary 13 by an AI referee (Claude Opus) on 2026-11-27, clause by clause, with verdict "statement confirmed" and 0 issues. The referee also ran its own exact rational check for $4\le n\le10$ ([`cor13_check.py`](lean/kernel-replays/independent/cor13_statement_check/cor13_check.py), [log](lean/kernel-replays/independent/cor13_statement_check/cor13_check.log)): the Lean family lies in the kernel of $\mathbf A-(n-4)I$ and spans it, its dimension is $(n-2)/2$ or $(n+1)/2$, and both side conditions are needed (for even $n$ the $\gamma$-term alone is not an eigenvector, and a non-palindromic $r$ gives a vector outside the eigenspace). A second script ([`src_vectors_check.py`](lean/kernel-replays/independent/cor13_statement_check/src_vectors_check.py), [log](lean/kernel-replays/independent/cor13_statement_check/src_vectors_check.log)) builds the eigenvectors printed by Cardoso, Costa and Duarte ($Y^n$, $Z^n$ of arXiv:2012.01992; $`F_{n,\ell}`$, $`E_{n,n-4}`$ of arXiv:2301.08106, as transcribed from automated renderings) and checks that they span the same space, for $4\le n\le10$.

Note on labels: the module docstring of `Main.lean` says "Conjecture 1(b)". That is our labelling of the second sentence of Conjecture 1, as explained above. The docstrings also contain bookkeeping labels and paths of the working repository where the files were written ("ledger QS-1", "QS-2", `targets/queens-spectrum/PROOF.md`); `PROOF.md` in this repository is the same proof. The Lean files are kept byte-identical to the checked versions, so the docstrings are not edited here.

## What you have to trust

1. The Lean kernel, which checks every proof.
2. The four lines of definition above.
3. Mathlib's standard notions used in the statements: `SimpleGraph.adjMatrix`, `Matrix.toLin'`, `Module.End.eigenspace`, `Module.finrank`, `Matrix.charpoly`, `Polynomial.rootMultiplicity`, `Even`, `Fin.rev` (for Corollary 13), and the classes `Field`, `LinearOrder` and `IsStrictOrderedRing`.
4. The three standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Everything else in the 12 files (the lines, the incidence matrix, the symmetries, the sectors) is used only inside the proof. An error there could make the proof fail to check; it could not make a false statement pass.

The statement was checked against the source by an AI referee (Claude Opus) on 2026-11-27. Besides reading the definitions, the referee compared the Lean adjacency with an independently written queen-move rule: a kernel `decide` proof of agreement on all 256 pairs for $n=4$; `#eval` agreement for every $n\le8$; the edge count $n(n-1)(5n-1)/3$ of the source for $n\le8$; and, for $n=4,5,6$, the Lean adjacency matrices against matrices from an independent exact Python script, entry by entry.

## How the Lean proof maps to the written proof

Lemma numbers are those of [`PROOF.md`](PROOF.md) and [`paper.pdf`](paper.pdf); they agree. The Lean comments use the lettering of an earlier text for the parts of Lemma 4: Lean's 4(a), 4(b), 4(c) are parts (b), (c), (a) here.

| Written proof | Lean (file: name) |
| --- | --- |
| Lines, incidence matrix $N$, $M=N^{T}N$, formula for $Nv$ | `Defs`: `Line`, `N`, `M`, `N_mulVec` |
| Lemma 1 ($NN^{T}=\mathbf A+4I$) | `Defs`: `lemma1` |
| Lemma 2 (reduction to $\ker(M-nI)$) | `Reduction`: `finrank_eigenspace_mul_comm`, `lemma2` |
| Lemma 3 (the symmetries $t,h,z$) | `Symmetry`: `lt_invol`, `lh_invol`, `lz_invol`, `lt_lh`, `lh_lt_lh`, `lh_lz`, `lt_lz`, `M_mulVec_comp` |
| Lemma 4(a)–(c) (sectors, $W=0$, decomposition, invariance) | `Symmetry`: `T_coords`, `H_coords`, `Z_coords`; `Kernel`: `W_zero`, `decomp`, projectors `Vp`, `Vm`, `Pp`, `Qq` |
| Lemma 5 and Remark 4.5 of `PROOF.md` (Remark 1 in the paper): action of $M$ on the sectors | `Defs`: `M_mulVec_row`, `M_mulVec_diag`; `SectorE`: `row_expand`, `diag_expand`; `Symmetry`: `ker_eqs` |
| Lemma 6 (sector $B_1$) | `Kernel`: `B1_form`, `vecB1_mem`; `Count`: `finrank_P0` |
| Lemma 7 (sector $E$) | `SectorE`: `sectorE_pure`; `Kernel`: `E_zero` |
| Lemmas 8–9 (sector $A_1$) | `SectorA1`: `sectorA1_pure`; `Seq`: `TT_step`; `Kernel`: `A1_zero` |
| Lemma 10 (weighted means) | `SectorB2`: `weighted_means` |
| Lemmas 11–12 (sector $B_2$) | `SectorB2`: `sectorB2_pure`; `Kernel`: `B2_form`, `dcirc_eq`, `vecB2_mem` |
| Proof of the Theorem (the count) | `Kernel`: `ker_char`; `Count`: `range_PsiE`, `range_PsiO`, `finrank_E`; `Main`: `queens_mult` |
| Algebraic = geometric multiplicity for symmetric matrices | `AlgMult` |
| Corollary 13 (the eigenspace on the board) | `Eigenspace`: `N_vecB1`, `N_vecB2`, `mem_eigenspace_adj_iff`, `queens_eigenspace`, `queens_eigenspace_real` |

## Where the Lean route differs from the written proof

Each item is a different route to the same conclusion, never a weaker statement. All of them sit inside the formalized proof.

1. **Lemma 4(d)** (adding kernel dimensions over the five sectors) is not formalized as stated. Instead `ker_char` shows that every vector in $\ker(M-nI)$ is $(r,-r,0,0)+\gamma(0,0,d^{\circ},-d^{\circ})$ with $r$ palindromic, $\sum_i r_i=0$, and $\gamma=0$ for even $n$; `vecB1_mem` and `vecB2_mem` give the converse. The dimension is then that of the domain of an injective linear parametrization (`Count.lean`). The number is the same as in §8 of the proof.
2. **Lemma 8 (window identity)** is replaced by an equivalent consequence: $U_k=T_{n-1-k}+T_{k-1}$ satisfies $U_{k+2}=U_k$, from $T_{m+2}=T_m+2d_{m+2}$ and $d_{n-k}=d_k$. The small linear systems of Lemma 9 are solved with explicit linear combinations; the determinants $-3$ and $-10n$ are not computed as such.
3. **Lemma 10** assumes a rank function that strictly decreases along $\alpha$ away from $j_0$, instead of "the $\alpha$-chain reaches $j_0$". For the index maps of Lemma 12 the two hypotheses are equivalent.
4. **Lemma 7**, last step: from $k d_k=\rho_k=\rho_{n-k}=(n-k)d_{n-k}=-(n-k)d_k$ it follows that $n d_k=0$. This replaces the positivity of a bracket in the written proof.
5. **Lemma 11**: only the direction used is formalized (the equations Eq imply the equations $F$).
6. **The sector dimensions** in Lemma 4(a), and the check after Lemma 4, are not formalized. The proof does not need them.

## What is not formalized

- **Appendix A** (second proof of Lemma 12). Not used by the Theorem.
- **Credit and literature statements.** They are about published papers, which Lean cannot check.
- **The finite computer checks** in [`scripts/`](scripts/). For the Theorem they are superseded by the general Lean proof; they remain independent checks of the definitions.
- **Parts (a) and (c) of Conjecture 1** (its first and third sentences). Not addressed; they remain open.

Corollary 13 was in this list in version 2 of the paper. It is now formalized (above), as version 3 of the paper states; the description of the eigenspace remains credited to Cardoso, Costa and Duarte.

## Kernel replays

A Lean build checks each proof with Lean's kernel as the file is compiled. A kernel replay checks the compiled proofs again, afterwards, from the stored files. This guards against a fault in the build process, for example a tactic or metaprogram that changed the environment in a way the kernel did not see. All runs were on 2026-11-27, on the same Windows 11 machine, with the toolchain Lean 4.37.0-rc1 (commit `0b77e12952ad39077d80d8bd6b66d601f225c321`) and the pinned Mathlib. Every tool below ships with that toolchain. Full records, with tool hashes, commands, wall times and logs: [`lean/kernel-replays/README.md`](lean/kernel-replays/README.md) and [`lean/kernel-replays/independent/README.md`](lean/kernel-replays/independent/README.md).

| Checker | Kernel | Input | Result |
| --- | --- | --- | --- |
| `leanchecker` | Lean's own | every `Pipeline.QueensSpectrum.*` module (12 of 12), replayed from its imports | PASS, exit 0, 5 min 27 s |
| `leanchecker --fresh` | Lean's own | `Main.lean` and its whole import closure (Lean core and Mathlib included), re-added to an empty environment | PASS, exit 0, 8 min 25 s |
| `leanchecker-paranoid` | Lean's own, a separate checking build | all 12 modules; and `--fresh` on `Main.lean` | PASS (5 min 7 s); PASS (8 min 34 s) |
| `nanoda_bin` 0.4.31 | independent (Rust) | lean4export file of the closure of the nine main theorems | PASS, `Checked 25995 declarations with no errors`, 3.8 s |
| `lean4lean` | independent (written in Lean) | the same export file | PASS, `checked 24686 declarations`, 40 s |
| `leanchecker-paranoid --from-export` | Lean's own | the same export file | PASS, 32 s |
| `con-ron`, `con-leche` | two further kernels shipped with the toolchain | the same export file | PASS, `accepted 24689 declarations (--verified)` each |

The nine main theorems are `queensGraph_sanity`, `queens_mult`, `queens_alg_mult`, `queens_hasEigenvalue`, `queens_mult_real`, `queens_mult_rat`, `queens_alg_mult_real`, `queens_eigenspace` and `queens_eigenspace_real`. Their closure contains every declaration they use, including those from Lean core, Batteries and Mathlib; its only axioms are `propext`, `Classical.choice` and `Quot.sound`, and `nanoda_bin` was run with exactly those three permitted. The three declaration counts differ only in how the checkers count constructors, recursors and quotient constants.

**Negative control.** In a copy of the export, the proof of `queens_eigenspace_real` was replaced by the proof of another theorem, with the stated type unchanged. All five export checkers rejected it (`nanoda_bin` by an assertion failure, the other four with a type mismatch at `queens_eigenspace_real`). So the PASS lines are not vacuous.

**Limits.**

- The independent kernels check the exporter's rendering of the compiled files, not the compiled `.olean` files themselves. The exporter (lean4export 3.1.0) is trusted for that rendering. The kernel-side print by `nanoda_bin` ([`nanoda_pp.txt`](lean/kernel-replays/independent/logs/nanoda_pp.txt)) shows that the exported statements of `queens_eigenspace`, `queens_eigenspace_real`, `queens_mult` and the definitions `queensGraph`, `Attack` are those of the source files.
- Only Lean's own kernel (`leanchecker`, `leanchecker-paranoid`) replayed the `.olean` files directly. The `lean4lean` binary in the toolchain was built for a different Lean version and cannot read them; `con-ron` and `con-leche` read only an older `.olean` format.
- The standalone [lean4checker](https://github.com/leanprover/lean4checker) repository is deprecated (it has been merged into Lean as `leanchecker`) and does not build for Lean v4.37.0-rc1, because of a change in Lean's internal interface. It was not patched. [`standalone_build.log`](lean/kernel-replays/standalone_build.log) has the failed build.

**Paths in the copied records.** The files in [`lean/kernel-replays/`](lean/kernel-replays/) are unchanged copies from the working repository where the replays were run. There, this folder is `targets/queens-spectrum/lean4checker/`, so a path such as `<repo>/targets/queens-spectrum/lean4checker/independent/scripts/tamper.py` means `lean/kernel-replays/independent/scripts/tamper.py` here. The referee report they mention (`../../reviews/checker-lean-cor13-60cb49b.md`) is not included; [`REVIEWS.md`](REVIEWS.md) summarizes it. `<user>`, `<host>` and `<scratchpad>` stand for redacted local paths ([`REDACTIONS.md`](REDACTIONS.md)).

## Status words

A statement is `formalized` only when `lake build` passes with no `sorry` and only the standard axioms. The Theorem has that status, in addition to `proved` (the written proof passed our review rule). Corollary 13 has status `formalized`.
