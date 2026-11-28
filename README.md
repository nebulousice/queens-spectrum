# The exact multiplicity of the eigenvalue $n-4$ of the $n$-Queens graph

> **In one line:** for every $`n\ge4`$, the eigenvalue $n-4$ of the $n$-Queens graph has multiplicity exactly $(n-2)/2$ when $n$ is even and $(n+1)/2$ when $n$ is odd. Cardoso, Costa and Duarte proved that these numbers are lower bounds and conjectured equality. This repository gives a short pen-and-paper proof of the matching upper bound, and a formal proof of the whole theorem in Lean 4 with Mathlib. Two other parts of their conjecture remain open.

**Formalized in Lean 4 + Mathlib** (full theorem and the explicit eigenspace, all n ≥ 4). **Expert verification required.** Verified so far with: Lean 4 + Mathlib (the whole Theorem, and Corollary 13, the explicit eigenspace); kernel replays of the compiled Lean proofs, by Lean's own checker (all 12 modules, also from an empty environment) and by independent kernels (nanoda, lean4lean, con-ron, con-leche) on an exported copy of the main theorems; three rounds of AI review of the written proof (Claude Opus, Claude Fable, Claude Sonnet; passed round 3); AI checks of both Lean statements against the source (Claude Opus; both confirmed); exact computation for 4 ≤ n ≤ 40; outside cross-checks by ChatGPT and Gemini (both passed).

> **Paper version.** [`paper.pdf`](paper.pdf) is version 3 of the paper (2026-11-27). It includes the Lean formalization of Corollary 13 and the kernel replays, and corrects several citations and bibliographic details of version 2. The mathematical argument is unchanged. All versions: [doi:10.5281/zenodo.24596852](https://doi.org/10.5281/zenodo.24596852).

## Summary

**Theorem.** Let $`n\ge4`$, and let $`\mathbf A`$ be the adjacency matrix of the $n$-Queens graph $`\mathcal Q(n)`$. Then $n-4$ is an eigenvalue of $`\mathbf A`$, and its multiplicity is exactly

```math
\frac{n-2}{2}\quad\text{if } n \text{ is even},\qquad\qquad \frac{n+1}{2}\quad\text{if } n \text{ is odd}.
```

This is the second sentence of Conjecture 1 (part (b) in our labelling; the source does not number the parts) of D. M. Cardoso, I. S. Costa and R. Duarte, *Integer eigenvalues of the n-Queens graph*, Discrete Math. 347(9) (2024) 114065 ([arXiv:2301.08106](https://arxiv.org/abs/2301.08106), [doi:10.1016/j.disc.2024.114065](https://doi.org/10.1016/j.disc.2024.114065)).

**Priority and credit.**

- The conjecture is due to Cardoso, Costa and Duarte ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992), Conjecture 3; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106), Conjecture 1).
- The lower bounds on the multiplicity, and explicit eigenvectors, are theirs. They first appeared in [arXiv:2012.01992](https://arxiv.org/abs/2012.01992) (2020-12-03; abstract and Theorem 3.10) and were restated in [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) (Theorem 4.1 and Corollary 4.2).
- The explicit description of the eigenspace that our proof also yields is theirs in full: their eigenvectors span it.
- They report that their computations confirm the whole conjecture for $`n\le100`$.
- **The exact value, equivalently the upper bound (the Theorem), is conjectured but not proved in their papers** ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992) Conj. 3; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) Conj. 1; [arXiv:2508.01088](https://arxiv.org/abs/2508.01088) Conj. 4.1); whether a proof of it, or the method used here, appears elsewhere has not been checked beyond our literature search of 2026-11-27. **This repository proves it.**
- A literature search on 2026-11-27 found no earlier proof or claim of this upper bound in the sources checked. Some sources could not be checked that day. This is a dated search result, not a priority claim. [`LITERATURE_CHECK.md`](LITERATURE_CHECK.md) has the details.
- **Parts (a) and (c) of their Conjecture 1 (its first and third sentences) stay open:** that no other integer is an eigenvalue, and that the other listed integers are simple eigenvalues. This repository does not settle the conjecture.

**Method.**

1. *Lines.* Every square of the board lies on exactly four lines: its row, its column, its diagonal and its antidiagonal. Two distinct squares are adjacent exactly when they share a line. So $`\mathbf A = NN^{T}-4I`$, where $N$ is the square–line incidence matrix.
2. *Reduction.* Hence the multiplicity of $n-4$ in $`\mathbf A`$ equals the dimension of the kernel of $M-nI$. Here $`M=N^{T}N`$ is the $`(6n-2)\times(6n-2)`$ matrix whose entries are the sizes of intersections of lines.
3. *Symmetry.* Three symmetries of the board (transpose, left–right flip, half-turn) split the space of functions on lines into five subspaces that $M$ preserves. Two of them behave identically. No representation theory is needed.
4. *Four small systems.* On each subspace, $M-nI$ has an explicit form, and its kernel is computed by hand. It has dimension $`\lceil n/2\rceil-1`$ on one subspace, $1$ (odd $n$) or $0$ (even $n$) on another, and $0$ on the remaining three. The hardest case uses a discrete maximum principle for weighted means.
5. *Count.* Adding up gives $(n-2)/2$ for even $n$ and $(n+1)/2$ for odd $n$.

**Side facts** (all part of the proof, none claimed as new).

- The kernel of $M-nI$ on each of the five subspaces is found exactly (step 4).
- The eigenspace consists of the functions $`x(i,j)=r_i-r_j+\gamma\bigl([i=j]-[i+j=n-1]\bigr)`$, with $r$ palindromic and $`\gamma=0`$ for even $n$. This description is due to Cardoso, Costa and Duarte. It is formalized in Lean (`queens_eigenspace`).
- An alternative proof of one step uses an explicit elimination showing that a certain matrix $`G_q`$ is positive semidefinite of rank $q$ ([`PROOF.md`](PROOF.md), Appendix A).

**Verification.**

- *Proof:* complete, by hand, for all $`n\ge4`$. No step uses a computer. Status: `proved` (passed our review rule; the referees are AI models, see below).
- *Lean 4 + Mathlib:* the whole Theorem is `formalized`, for every $`n\ge4`$, and over every linearly ordered field (so over $`\mathbb R`$ and $`\mathbb Q`$). Lean proves both readings of "multiplicity": the dimension of the kernel of $`\mathbf A-(n-4)I`$ (`queens_mult`) and the order of $n-4$ as a root of the characteristic polynomial (`queens_alg_mult`). The files are in [`lean/`](lean/) (12 files, 2,283 lines; main theorems in [`Main.lean`](lean/Pipeline/QueensSpectrum/Main.lean), Corollary 13 in [`Eigenspace.lean`](lean/Pipeline/QueensSpectrum/Eigenspace.lean)).
  - `bash scripts/lean_check.sh QueensSpectrum` passes: Lean 4.37.0-rc1 with Mathlib as pinned in [`lean/lake-manifest.json`](lean/lake-manifest.json); 0 build errors; no `sorry`, `admit` or `native_decide`; the axioms are `propext`, `Classical.choice` and `Quot.sound` only ([`lean/logs/axioms.log`](lean/logs/axioms.log)).
  - It passed in two separate runs on 2026-11-27. An AI referee (Claude Opus) rebuilt it from a fresh checkout, with the same result, and confirmed that the Lean statement matches the source conjecture.
  - *Trust base:* the Lean kernel; the four lines of Lean that define the graph (`Attack` and the adjacency rule of `queensGraph` in [`Defs.lean`](lean/Pipeline/QueensSpectrum/Defs.lean), lines 27–29 and 34); and Mathlib's standard notions (adjacency matrix, eigenspace, dimension, characteristic polynomial, root multiplicity). Everything else is checked.
  - The Lean proof follows the written proof, with a few local differences (for example, it counts the kernel directly instead of adding sector dimensions). [`LEAN.md`](LEAN.md) lists them, and what is not formalized: Appendix A (a second proof of one lemma, not used by the Theorem).
- *Corollary 13 in Lean (2026-11-27):* the explicit eigenspace is `formalized` as `queens_eigenspace` (any linearly ordered field) and `queens_eigenspace_real`, in [`Eigenspace.lean`](lean/Pipeline/QueensSpectrum/Eigenspace.lean). For every $`n\ge4`$, a function $x$ on the squares lies in the eigenspace of $n-4$ if and only if it has the form $`x(i,j)=r_i-r_j+\gamma\bigl([i=j]-[i+j=n-1]\bigr)`$ with $r$ palindromic and $`\gamma=0`$ for even $n$. Both inclusions are proved.
  - `lean_check` passes with these files; the axioms of both theorems are `propext`, `Classical.choice` and `Quot.sound` only ([`lean/logs/axioms.log`](lean/logs/axioms.log)).
  - An AI referee (Claude Opus) confirmed the Lean statement clause by clause against Corollary 13. It also checked it in exact rational arithmetic for $`4\le n\le10`$: the Lean family spans exactly the kernel of $`\mathbf A-(n-4)I`$, dropping either side condition makes the statement false, and the eigenvectors printed by Cardoso, Costa and Duarte span the same space ([`lean/kernel-replays/independent/cor13_statement_check/`](lean/kernel-replays/independent/cor13_statement_check/)).
- *Kernel replays (2026-11-27):* the compiled Lean proofs were checked again by proof-checking kernels, separately from the build. Details and logs: [`lean/kernel-replays/`](lean/kernel-replays/).
  - Lean's own checker `leanchecker`, shipped with Lean 4.37.0-rc1, and its separately built variant `leanchecker-paranoid` replayed every declaration of all 12 modules: PASS. With `--fresh` they also re-added the whole import closure of `Main.lean` (Lean core and Mathlib included) to an empty environment: PASS. Both use Lean's own kernel.
  - Two kernels written independently of Lean's kernel, `nanoda_bin` 0.4.31 (25995 declarations) and `lean4lean` (24686 declarations), and two further kernels shipped with the toolchain, `con-ron` and `con-leche`, checked an export of the nine main theorems and everything they depend on (made with lean4export 3.1.0): all PASS. A copy of the export with one proof replaced by a wrong one was rejected by all five export checkers.
  - *Limit:* the independent kernels check the exporter's rendering of the compiled files, not the compiled files themselves; only Lean's own kernel replayed those directly. The standalone lean4checker repository is deprecated and does not build for Lean v4.37.0-rc1.
- *Credit check:* the theorem numbers and eigenvector definitions of Cardoso, Costa and Duarte were checked against the PDFs of their papers on 2026-11-27, and the identification of their eigenvectors with ours by exact computation for small $n$.
- *Computer checks (corroboration only, exact arithmetic):*
  - the Theorem for $`4\le n\le40`$, with two rank algorithms;
  - the Theorem for $`41\le n\le150`$, with one implementation;
  - the adjacency matrix directly for $`4\le n\le12`$;
  - a replay of every identity in the proof for $`4\le n\le40`$.

  None of these is archived as a certificate (an independent second implementation rerun from a clean copy, with archived output). For the Theorem they are superseded by the Lean proof. See [`REPRODUCE.md`](REPRODUCE.md).
- *Reviews (2026-11-27):* the proof passed our review rule in round 3 (three AI referees on three Claude models). No referee has found a mathematical error.
  - Round 1: Referee 1 (Claude Opus, line-by-line check) raised 3 minor issues, all fixed; Referee 2 (Claude Fable, adversarial check) accepted with 0 issues.
  - Round 2, on the fixed version: Referee 3 (Claude Sonnet, fresh) accepted with 0 issues; Referee 1 raised 1 cosmetic issue (a stale status sentence); Referee 2 raised 2 minor issues (credit the lower bound first to arXiv:2012.01992, and the same stale sentence). Not yet a pass.
  - Round 3, on the version with the round-2 fixes: Referee 1 (Claude Opus) and Referee 3 (Claude Sonnet) accepted with 0 issues; Referee 2 (Claude Fable) raised 2 minor wording points in the credit remarks (what the papers of Cardoso, Costa and Duarte say about the upper bound, and a linear relation among the vectors of their printed set $Y^n$), now fixed, with no mathematical change. Two of three clean and no major issue: a pass under our rule. See [`REVIEWS.md`](REVIEWS.md).
  - Lean statement check: Claude Opus confirmed that the Lean definition and both multiplicities match the source, with no mismatch found.
  - Lean statement check of Corollary 13: Claude Opus confirmed the statement of `queens_eigenspace`, accepting with 0 issues (details above and in [`REVIEWS.md`](REVIEWS.md)).
- *Outside cross-checks:* ChatGPT and Gemini, each in a fresh chat with a referee prompt, checked the first version of the paper. They found no mathematical error and reported minor formatting issues only.

**How it was made.** The literature review, the search for a method, the proof, the computer checks and the review were each done by AI models (Claude, from Anthropic) in separate sessions, directed by the owner of this repository. After the review, the Theorem was formalized in Lean 4 with Mathlib, again by a Claude model, and the Lean statement was checked against the source by a separate AI referee. Later the same day, Corollary 13 was formalized in the same way, its Lean statement was checked by an AI referee, and the compiled Lean proofs were replayed by several proof-checking kernels. All computation (Python and Lean) ran on one Windows 11 machine. The process is summarised in the research log below.

## Where to start

| If you want… | Read |
| --- | --- |
| The proof (self-contained, every step labelled) | [`PROOF.md`](PROOF.md) |
| The paper | [`paper.pdf`](paper.pdf) (version 3), compiled with Tectonic from [`paper.tex`](paper.tex) (amsart) |
| To rerun the computer checks | [`REPRODUCE.md`](REPRODUCE.md), then the scripts in [`scripts/`](scripts/) |
| Prior work and the priority search | [`LITERATURE_CHECK.md`](LITERATURE_CHECK.md) |
| The review history | [`REVIEWS.md`](REVIEWS.md) |
| What is formalized in Lean, and what you have to trust | [`LEAN.md`](LEAN.md), then the files in [`lean/`](lean/) |

---

## Research log

### Setup

The **$n$-Queens graph** $`\mathcal Q(n)`$ has the $n^2$ squares of an $`n\times n`$ board as vertices. Two distinct squares are adjacent when a chess queen on one attacks the other: same row, same column, or same diagonal in either direction. Its **adjacency matrix** $`\mathbf A`$ has entry 1 for adjacent squares and 0 otherwise. It is real and symmetric, so the **multiplicity** of an eigenvalue $`\lambda`$ (as a root of the characteristic polynomial) equals the dimension of the kernel of $`\mathbf A-\lambda I`$.

For $`n\ge4`$, Cardoso, Costa and Duarte consider the set of integers

```math
L(n)=\{-4,\ n-4\}\ \ (n \text{ even}),\qquad L(n)=\Bigl\{-4,-3,\dots,\tfrac{n-11}{2}\Bigr\}\cup\Bigl\{\tfrac{n-5}{2},\dots,n-5,\ n-4\Bigr\}\ \ (n \text{ odd}).
```

They proved that every element of $L(n)$ other than $-4$ is an eigenvalue ([arXiv:2301.08106](https://arxiv.org/abs/2301.08106), Sections 3–4), that $-4$ is the least eigenvalue and has multiplicity exactly $(n-3)^2$ ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992), Theorems 3.6 and 3.8; [arXiv:2201.01224](https://arxiv.org/abs/2201.01224)), and that $n-4$ has multiplicity at least $(n-2)/2$ or $(n+1)/2$ ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992), Theorem 3.10; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106), Corollary 4.2). Their Conjecture 1 has three sentences, which the source does not number. In our words, with our labels (a)–(c) for its three sentences in order:

- (a) the integer eigenvalues of $`\mathbf A`$ are exactly the elements of $L(n)$;
- (b) the eigenvalue $n-4$ has multiplicity $(n-2)/2$ for even $n$ and $(n+1)/2$ for odd $n$;
- (c) the elements of $L(n)$ other than $-4$ and $n-4$ are simple eigenvalues.

This repository proves (b), the second sentence. Parts (a) and (c) remain open.

### Notation

Squares are $(i,j)$ with $`0\le i,j\le n-1`$. The **lines** are the rows $`R_i`$, the columns $`C_j`$, the diagonals $`D_k=\lbrace(i,j): i-j=k\rbrace`$ and the antidiagonals $`A_s=\lbrace(i,j): i+j-(n-1)=s\rbrace`$; there are $6n-2$ of them. $N$ is the square–line incidence matrix and $`M=N^{T}N`$, so the entry of $M$ for two lines is the number of squares they share. A vector on lines is written $v=(r,c,d,a)$ (values on rows, columns, diagonals, antidiagonals). Then

```math
(Nv)(i,j)=r_i+c_j+d_{i-j}+a_{i+j-(n-1)}.
```

A vector $`r\in\mathbb R^n`$ is **palindromic** if $`r_{n-1-i}=r_i`$ for all $i$. The three symmetries are

```math
t(r,c,d,a)=(c,r,d^{-},a),\qquad h(r,c,d,a)=(r,c^{\leftarrow},a,d),\qquad z(r,c,d,a)=(r^{\leftarrow},c^{\leftarrow},d^{-},a^{-}),
```

where $`r^{\leftarrow}_i=r_{n-1-i}`$ and $`d^{-}_k=d_{-k}`$. The five subspaces ("sectors") are the joint eigenspaces $`A_1`$ ($t=h=1$), $`B_1`$ ($t=-1$, $h=1$), $`B_2`$ ($t=1$, $h=-1$), $E$ ($z=-1$, $h=1$) and $E'$ ($z=-1$, $h=-1$). [`PROOF.md`](PROOF.md) §1 and §3 define everything in full.

### Results along the way

Status words: `formalized` = checked by Lean 4 with Mathlib (build passes, no `sorry`, standard axioms only); `proved` = complete written argument that passed our review rule (AI referees); `numerical` = finite check by computer in exact arithmetic, never used as a proof step; `open` = nothing above applies.

| # | Statement | Status | Evidence |
| --- | --- | --- | --- |
| 1 | Two distinct squares share at most one line; $`\mathbf A=NN^{T}-4I`$ | proved | [`PROOF.md`](PROOF.md) Lemma 1 |
| 2 | Multiplicity of $n-4$ in $`\mathbf A`$ equals $`\dim\ker(M-nI)`$ | proved | Lemma 2 |
| 3 | $t,h,z$ commute with $M$; the five sectors decompose the line space, and $E$, $E'$ contribute equally | proved | Lemmas 3–5 |
| 4 | Sector $`B_1`$: kernel of $M-nI$ has dimension $`\lceil n/2\rceil-1`$ | proved | Lemma 6 |
| 5 | Sector $E$: kernel of $M-nI$ is zero | proved | Lemma 7 |
| 6 | Sector $`A_1`$: kernel of $M-nI$ is zero | proved | Lemmas 8–9 |
| 7 | Sector $`B_2`$: kernel of $M-nI$ has dimension 1 ($n$ odd) or 0 ($n$ even) | proved | Lemmas 10–12; second proof in Appendix A |
| 8 | **The Theorem:** multiplicity of $n-4$ is exactly $(n-2)/2$ or $(n+1)/2$, all $`n\ge4`$ (pen-and-paper proof complete, no computational step; round 1: one referee minor, 3 issues fixed, one accept; round 2: one accept, two minor on wording and citation; round 3: two accepts, one minor on wording, a pass. Lean: whole Theorem for all $`n\ge4`$, geometric and algebraic multiplicity, over any linearly ordered field including $`\mathbb R`$ and $`\mathbb Q`$; `lean_check` PASS; Lean statement confirmed against the source by an AI referee; kernel replays PASS: Lean's own checker on all modules, also from an empty environment, and four other kernels on an exported copy, two of them independent of Lean's kernel) | formalized; proved | [`PROOF.md`](PROOF.md) §8; [`lean/Pipeline/QueensSpectrum/Main.lean`](lean/Pipeline/QueensSpectrum/Main.lean) (`queens_mult`, `queens_alg_mult`); [`LEAN.md`](LEAN.md) |
| 9 | Explicit eigenspace of $n-4$ (not new: the eigenvectors are those of Cardoso, Costa and Duarte, first in arXiv:2012.01992; with the Theorem they span the eigenspace). Lean: both inclusions, all $`n\ge4`$, over any linearly ordered field; `lean_check` PASS; Lean statement confirmed by an AI referee, with an exact check for $`4\le n\le10`$ that includes the source eigenvectors | formalized | [`PROOF.md`](PROOF.md) Corollary 13 and the remark after it; [`lean/Pipeline/QueensSpectrum/Eigenspace.lean`](lean/Pipeline/QueensSpectrum/Eigenspace.lean) (`queens_eigenspace`, `queens_eigenspace_real`); [`LEAN.md`](LEAN.md) |
| 10 | The Theorem for $`4\le n\le40`$, by exact rank of $M-nI$ | numerical (exact arithmetic, two implementations) | [`scripts/logs/fullflint_4_40.log`](scripts/logs/fullflint_4_40.log), [`fraction_4_16.log`](scripts/logs/fraction_4_16.log), [`fraction_17_40.log`](scripts/logs/fraction_17_40.log) |
| 11 | The Theorem for $`41\le n\le150`$, by exact rank on the sectors | numerical | [`scripts/logs/sectors_flint_41_150.log`](scripts/logs/sectors_flint_41_150.log) |
| 12 | Nullity of $`\mathbf A-(n-4)I`$ on the $`n^2\times n^2`$ matrix, $`4\le n\le12`$ | numerical | [`scripts/logs/adjacency_4_12.log`](scripts/logs/adjacency_4_12.log) |
| 13 | Every identity of the proof replayed exactly, $`4\le n\le40`$ | numerical | [`scripts/logs/replay_4_40.log`](scripts/logs/replay_4_40.log) |
| 14 | Part (a) of Conjecture 1, its first sentence (no other integer eigenvalue) | open | — |
| 15 | Part (c) of Conjecture 1, its third sentence (the other listed integers are simple) | open | — |

Rows 1–7 are proof steps of row 8. The Lean proof of row 8 checks each of them, some by a different route; a few parts that the proof does not need (the sector dimensions in Lemma 4, one direction of Lemma 11) are not formalized. [`LEAN.md`](LEAN.md) lists the differences.

### Timeline (all 2026-11-27)

1. Priority check of the conjecture: open, no claim or active work found.
2. Literature and methods review; five attack routes written down, each with a decisive first test.
3. Exploration: the symmetry reduction, and hand proofs for each sector, found and checked in exact arithmetic for $`n\le40`$.
4. The full proof written ([`PROOF.md`](PROOF.md)).
5. Second priority check before any claim, including the published journal text and Costa's thesis: the upper bound is still open in every source checked.
6. Review round 1 by two AI referees; three minor issues fixed, no mathematical step changed.
7. Review round 2 by three AI referees: one accept; two minor issues on wording and citation (credit the lower bound first to the 2020 paper).
8. Review round 3 by three AI referees: two accepts with 0 issues, one minor (two wording points in the credit remarks); the review rule passed. The two wording points were then fixed.
9. Version 1 of the paper and of this write-up, with the round-3 wording fixes.
10. A third literature search (16:12–16:34 UTC, no proof or claim found); the source statements checked against the PDFs; all archived computer runs reproduced from a clean copy; out-of-date statements in the write-up corrected.
11. Outside cross-checks: ChatGPT and Gemini, in fresh chats, each checked the first version of the paper; they found no mathematical error and reported minor formatting issues only.
12. Lean 4 formalization of the whole Theorem for all $`n\ge4`$; `lean_check` PASS, then an independent rerun PASS.
13. Lean statement check by an AI referee (Claude Opus): the definition of the graph and both multiplicities match the source; fresh-checkout build PASS.
14. Version 2 of the paper, with the Lean files and their check output.
15. Corollary 13 (the explicit eigenspace) formalized in Lean; `lean_check` PASS, then an independent rerun PASS.
16. Kernel replays: Lean's own checker `leanchecker` on all 12 modules, also from an empty environment, PASS; then an AI referee (Claude Opus) confirmed the Lean statement of Corollary 13 (exact check for $`4\le n\le10`$, including the source eigenvectors) and ran the independent kernels on an exported copy of the main theorems, all PASS, with a tampered copy rejected by every export checker.
17. Version 3 of the paper: Corollary 13 formalized, the kernel replays, and corrected citations and bibliographic details; the mathematical argument is unchanged.

## Files

| Path | Contents |
| --- | --- |
| [`PROOF.md`](PROOF.md) | The complete proof, every step labelled with its status |
| [`paper.tex`](paper.tex), [`paper.pdf`](paper.pdf) | The same proof as an amsart paper (version 3), with sections on computer and formal verification; the PDF is compiled with Tectonic |
| [`LITERATURE_CHECK.md`](LITERATURE_CHECK.md) | Priority timeline, sources searched, comparison with prior work |
| [`REVIEWS.md`](REVIEWS.md) | Review history and current review status |
| [`LEAN.md`](LEAN.md) | What is formalized in Lean (the whole Theorem), the trust base, where the Lean route differs, what is not formalized |
| [`lean/`](lean/) | The Lean 4 project: the 12 files of the formalization, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and the check output in [`lean/logs/`](lean/logs/) |
| [`lean/kernel-replays/`](lean/kernel-replays/) | Kernel replays of the compiled Lean proofs (`leanchecker`, `leanchecker-paranoid`, and the independent kernels on an exported copy), with logs, helper scripts, the negative control, and the exact check of the Corollary 13 statement |
| [`scripts/lean_check.sh`](scripts/lean_check.sh) | The Lean check: build, `sorry`/`admit` scan, axiom report |
| [`REDACTIONS.md`](REDACTIONS.md) | What was checked for local paths and personal data before publishing the logs |
| [`REPRODUCE.md`](REPRODUCE.md) | Exact commands, versions, runtimes, expected output |
| [`scripts/prover_check.py`](scripts/prover_check.py) | Exact replay of every identity in the proof (pure Python) |
| [`scripts/p2_verify.py`](scripts/p2_verify.py) | Exact ranks: full matrix (two algorithms), sectors, adjacency matrix |
| [`scripts/p2_proofcheck.py`](scripts/p2_proofcheck.py) | Step-by-step checks from the board, written independently of the other scripts |
| [`scripts/logs/`](scripts/logs/) | Archived outputs of every run cited, and the tool versions |

## Credits

- Mathematics and code: Claude models (Anthropic), directed by the owner of this repository.
- Thanks to Domingos M. Cardoso, Inês Serôdio Costa and Rui Duarte for the conjecture, the lower bounds and the eigenvectors.
