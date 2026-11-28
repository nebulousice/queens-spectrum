# Review history

## Current status (2026-11-27)

- **Proof status: `proved`.** It passed our review rule in round 3 (2026-11-27).
- **No referee has found a mathematical error** in three rounds (eight referee reports in all).
- **Round 1** (two referees): one minor (3 issues, all fixed), one accept (0 issues). Not a pass, because the rule needs both clean.
- **Round 2** (three referees, on the fixed version): one accept (0 issues); two minor (wording and citation only). Not a pass: only 1 of 3 referees was clean, and the rule needs 2.
- **Round 3** (three referees, on the version with the round-2 fixes): two accept (0 issues); one minor (two wording points in the credit remarks, no mathematical change). A pass: 2 of 3 referees clean, and no major issue. The two wording points were then fixed (wording only; that fix was not itself refereed).
- **Lean 4 + Mathlib** (2026-11-27): the whole Theorem is `formalized`, for every $n\ge4$, geometric and algebraic multiplicity, over any linearly ordered field. `lean_check` PASS in two separate runs; an AI referee (Claude Opus) confirmed the Lean statement against the source and rebuilt it from a fresh checkout (PASS). See "Lean formalization and statement check" below and [`LEAN.md`](LEAN.md).
- **Corollary 13 in Lean** (2026-11-27, after paper version 2): the explicit eigenspace is `formalized` (`queens_eigenspace`, `queens_eigenspace_real`). An AI referee (Claude Opus) confirmed its Lean statement, accepting with 0 issues, with an exact check for $n=4,\dots,10$ that includes the eigenvectors printed by Cardoso, Costa and Duarte. The same referee ran the independent-kernel replays (all PASS). See "Lean statement check of Corollary 13 and kernel replays" below.
- **Outside cross-checks** (2026-11-27): ChatGPT and Gemini, each in a fresh chat, both reported a pass on the first version of the paper, with minor formatting issues only (summary by the owner of this repository; full replies not yet archived).
- **Formalized in Lean 4 + Mathlib** (full theorem and the explicit eigenspace, all n ≥ 4). **Expert verification required.** Verified so far with: Lean 4 + Mathlib (the whole Theorem, and Corollary 13); kernel replays of the compiled Lean proofs by Lean's own checker and by independent kernels on an exported copy (all PASS); three rounds of AI review of the written proof (Claude Opus, Claude Fable, Claude Sonnet; passed round 3); AI checks of both Lean statements against the source (Claude Opus; both confirmed); exact computation for 4 ≤ n ≤ 40; outside cross-checks by ChatGPT and Gemini (both passed).

**Review rule.** In round 1, two referees on different models review the same version, blind to each other and to the working notes. The proof passes if both accept with zero issues. Otherwise every issue is fixed or rebutted, and three referees (the first two plus a fresh one on a third model) review the fixed version. It then passes if at least two of the three accept with zero issues and no referee has an unresolved major issue. Otherwise the cycle repeats.

All referees of the three review rounds are AI models (Claude, from Anthropic). They reviewed the proof file of the working repository, not this write-up. This write-up presents the same argument with internal labels removed, and with the parts of one lemma (Lemma 4) put in an order where no part refers forward; no mathematical step differs. It reflects the round-2 points (the citation of arXiv:2012.01992 first, and neutral credit wording) and the two round-3 wording fixes. The write-up itself has not been refereed.

## Round 1 (reviewed version: commit `ec45639`)

The package reviewed was the full proof file, the replay script `prover_check.py` and its archived outputs. Both referees worked from a clean extraction of that commit.

### Referee 1: line-by-line check (Claude Opus) — minor

No mathematical error found.

What was checked:

- The statement against the source (arXiv HTML of 2301.08106v2): same range $n\ge4$, same multiplicities, same graph (both diagonal directions), and "multiplicity" as algebraic multiplicity, which equals the geometric one for a symmetric matrix. The source's printed characteristic polynomials $q_2$ and $q_3$ (from 2012.01992) were reproduced exactly from an independently built adjacency matrix.
- Every lemma line by line, including both appendix proofs: all 12 table entries of Lemma 3, the projectors of Lemma 4, every index range in Lemmas 5–12, the determinants $-3$, $-10n$ and $5n^2$, and the hand checks for $n=4,5$.
- Own exact computations, written from scratch (python 3.12.10, python-flint 0.7.1, sympy 1.14.0):
  - nullity of $\mathbf A-(n-4)I$ for $4\le n\le18$; root multiplicity in the factored characteristic polynomial for $4\le n\le10$; $NN^T=\mathbf A+4I$ for $n\le14$;
  - the eigenspace of Corollary 13 and the eigenvectors of arXiv:2301.08106 span the same space, $4\le n\le16$;
  - $\dim\ker(M-nI)$ from line intersections, $4\le n\le100$;
  - the sector relations, dimensions and per-sector kernels, $4\le n\le30$, built from board permutations rather than from the file's formulas;
  - Lemma 8 and the $B_2$ system, $4\le n\le120$; Lemma G, $1\le q\le80$.
- The replay script rerun: output identical to the archive apart from timings, ending `PROVER REPLAY: ALL PASS` (469 s on that host, against 381 s archived).

| # | Issue (all minor) | Fix |
| --- | --- | --- |
| 1 | The finite-range check $4\le n\le40$ was labelled `certified`, but no certificate had been archived and the project ledger did not record it as certified | Relabelled `numerical (exact arithmetic, two implementations)`; `certified` is no longer used as a status anywhere in the proof file |
| 2 | Credit: the proof file said that the odd-$n$ eigenvector of arXiv:2301.08106 had not been compared with ours, which left room to read the explicit eigenspace as new. The referee showed that their $E_{n,n-4}$ is $\frac{n+1}{2}\bigl([i=j]-[i+j=n-1]\bigr)$ in our indexing, so their eigenvectors span the whole eigenspace | The eigenspace description is credited to Cardoso, Costa and Duarte in full |
| 3 | A comment in the replay script named the wrong step (it said (A.5) where the code checks Lemma 8), and one sentence of the proof file was stale | Comment corrected (comment-only change; the short replay was rerun and is byte-identical); stale sentence updated |

### Referee 2: adversarial check (Claude Fable) — accept, 0 issues

The referee assumed the proof was wrong and tried to break every lemma.

- The statement against the source PDF of 2301.08106v2 and 2012.01992v1, and the journal record.
- Conventions, by reproducing first values with an independently written adjacency matrix (queen moves by ray casting): the multiplicity of $-4$ is $(n-3)^2$, and the integer eigenvalues are exactly the authors' list, for $4\le n\le13$.
- Every lemma recomputed by hand, including the boundary cases (lines with one square, $k=0$ and $k=n-1$, $n=4$ and $n=5$).
- Attacks: whether the sector sum is direct and complete; whether unlisted components could be nonzero; every hypothesis of every lemma against its use (Lemma 8 fails without its symmetry hypothesis, which (A.1) supplies; Lemma 10 tested on 4000 random systems, including $\lambda=1$ and $\beta(j)=j$); hidden dependence on $n$ modulo 4; circularity.
- Own exact computations: per-sector kernels for $2\le n\le110$ and eight values of $n$ up to 301; the nullity of $\mathbf A-(n-4)I$ for $4\le n\le30$ and $41\le n\le44$, with the eigenspace of Corollary 13; algebraic against geometric multiplicity for $3\le n\le12$; Lemma G for $q\le70$.
- The replay script rerun: identical output apart from timings.

### Fix after round 1 (commit `a5b272f`)

3 issues fixed, 0 rebutted, 0 open. No mathematical step changed. The only code change was the comment in the replay script.

## Round 2 (reviewed version: commit `a5b272f`)

### Referee 3: fresh referee on a third model (Claude Sonnet) — accept, 0 issues

- Statement and conventions against the arXiv HTML of 2301.08106v2.
- Own exact computations: nullity of $\mathbf A-(n-4)I$ for $4\le n\le11$; sectors, operators and per-sector kernels rebuilt from the definitions for $4\le n\le20$; formulas (4.1)–(4.4) on random sector vectors and Corollary 13 on random palindromic $r$, $4\le n\le24$; the determinants $-10n$ and $5n^2$ symbolically; Lemmas 8 and 11 on random vectors, $4\le n\le40$; the kernel vector of Lemma 12 for odd $n\le39$.
- Every lemma checked by hand; replay rerun for $4\le n\le13$; the archived replay parsed (37 PASS lines; per-line times sum to 380.8 s).
- No circular dependence found; Cardoso, Costa and Duarte's lower-bound theorem is not used by the proof.
- Non-blocking observations: remove references to review files and working notes from the write-up; give every remark a status word; avoid wording that reads as a novelty statement; confirm the definitions of the source's eigenvectors against the PDF. This write-up follows the first three; the fourth is still open.

### Referee 1 (Claude Opus) — minor, 1 issue (cosmetic)

- Confirmed all three round-1 fixes, and that no mathematical text changed between the two versions.
- New exact computations written from scratch: nullity of $\mathbf A-(n-4)I$ for $4\le n\le14$ (and root multiplicity for $n\le10$); $\dim\ker(M-nI)$ for $4\le n\le60$; sectors for $4\le n\le24$; formulas (4.0a)–(4.4) on random vectors for $4\le n\le20$; Lemmas 8 and 11 and the $B_2$ system for $4\le n\le100$; Lemma G for $q\le60$; the determinants. Replay rerun for $4\le n\le26$: identical to the archive.
- Issue: a sentence in §0 of the proof file still said that no review had run, which contradicted the file's header. The conclusion (nothing is labelled `proved`) was still right. Suggested wording: "The review rule has not yet passed". (This write-up does not contain that sentence.)

### Referee 2 (Claude Fable) — minor, 2 issues (credit and wording)

- Re-derived every step by hand and attacked it again with new exact computations: the Theorem on the adjacency matrix for $2\le n\le26$ and two-sided bounds for $n=33,36,45,46$; $\dim\ker(M-nI)$ for every $4\le n\le152$ and $n=200,201,250,251$; reduced systems for 124 values of $n$ up to 301; Lemma 10 on 3000 random systems (and the hypothesis $\lambda_j>0$ shown to be needed). Nothing broke.
- Checked that the fix changed no mathematical line (the replay script's syntax tree is unchanged, so the archived replay logs remain valid).

| # | Issue (both minor) | How this write-up handles it |
| --- | --- | --- |
| 1 | The lower bound and the explicit eigenvectors were credited only to arXiv:2301.08106 (2023). The same authors had already proved both in arXiv:2012.01992 (v1, 2020-12-03; abstract and Theorem 3.10, with eigenvector sets $Y^n$ and $Z^n$, which are exactly the two generators of Corollary 13) | arXiv:2012.01992 is cited first everywhere, with arXiv:2301.08106 as the restatement; "their paper" became "their papers" |
| 2 | The same stale §0 sentence as Referee 1's issue | Not present in this write-up |

The referee also asked that the theorem number 3.10 and the definitions of $Y^n$, $Z^n$, $F_{n,\ell}$ and $E_{n,n-4}$ be confirmed against the PDFs; they were read through automated page readers. In round 3, two referees read these items in the text layer of the PDFs and confirmed them (see Round 3); the final pre-release check (2026-11-27) confirmed them again against the PDF text layer. The rendered pages have not been viewed.

## Round 3 (reviewed version: commit `471a533`)

All three referees worked from a clean extraction of that commit and confirmed that the fix after round 2 changed no mathematical line.

### Referee 1: line-by-line check (Claude Opus) — accept, 0 issues

- Confirmed both round-2 fixes, and re-checked every lemma by hand.
- New exact computations written from scratch: the nullity of $\mathbf A-(n-4)I$ for $4\le n\le16$ (and the root multiplicity for $n\le10$); $\dim\ker(M-nI)$ for $4\le n\le80$; the symmetries and sectors for $4\le n\le30$; formulas (4.0a)–(4.4) on random vectors for $4\le n\le24$; Lemmas 8 and 11 and the $B_2$ system for $4\le n\le100$; Lemma G for $q\le60$; the determinants symbolically. Replay rerun for $4\le n\le22$: identical to the archive.

### Referee 3: fresh referee on a third model (Claude Sonnet) — accept, 0 issues

- Read the statement and the credit items in the text layer of the PDFs of arXiv:2301.08106v2, arXiv:2012.01992v1 and arXiv:2508.01088v1.
- Every lemma re-derived by hand; own exact computations: the nullity of $\mathbf A-(n-4)I$ for $4\le n\le24$; $\dim\ker(M-nI)$ for $4\le n\le60$; per-sector kernels for $4\le n\le16$; the hypotheses of Lemma 10 in every use for $4\le n\le80$; the sets $Y^n$, $Z^n$ of arXiv:2012.01992 against Corollary 13 for $4\le n\le18$; Lemma G for $q\le60$. Replay rerun for $4\le n\le18$: identical to the archive.

### Referee 2: adversarial check (Claude Fable) — minor, 2 issues (wording)

- Re-derived every step by hand a third time and attacked it with new exact code, including the Theorem on the adjacency matrix for $2\le n\le17$, two-sided bounds up to $n=304$, and the reduced systems for $4\le n\le70$. Nothing broke. Confirmed the credit items against the text layer of the PDFs.

| # | Issue (both minor) | Fix |
| --- | --- | --- |
| 1 | The upper bound was called "the part not stated in their papers". Their papers do state it, as a conjecture (arXiv:2012.01992 Conj. 3; arXiv:2301.08106 Conj. 1; arXiv:2508.01088 Conj. 4.1); what they do not contain is a proof | Everywhere replaced by: the exact value, equivalently the upper bound, is conjectured but not proved in their papers; whether a proof of it, or the method used here, appears elsewhere has not been checked beyond the priority search of 2026-11-27 |
| 2 | The remark on the known eigenvectors said that the sets of arXiv:2012.01992 are linearly independent, so that their number is a lower bound. As printed, $Y^n$ has $\lceil n/2\rceil$ vectors with one linear relation (rank $\lceil n/2\rceil-1$, checked for $2\le n\le17$); the source's own proof uses one vector fewer. The count claim holds for arXiv:2301.08106 Theorem 4.1 | The remark now says that the proof there uses $\lceil n/2\rceil-1$ vectors of $Y^n$, together with $Z^n$ for odd $n$, as linearly independent eigenvectors, so the number of linearly independent ones is the lower bound |

### Outcome

Two of three referees accepted with zero issues, and no referee raised a major issue: the proof passed our review rule. The two wording points were fixed afterwards; no mathematical step changed.

## Lean formalization and statement check (2026-11-27)

After the review rule passed, the whole Theorem was formalized in Lean 4 (4.37.0-rc1) with Mathlib, by a Claude model. Details are in [`LEAN.md`](LEAN.md); the files are in [`lean/`](lean/).

- **Lean check.** `bash scripts/lean_check.sh QueensSpectrum` passed: 0 build errors, no `sorry` or `admit` (and no `native_decide`), axioms `propext`, `Classical.choice` and `Quot.sound` only. It was run by the formalizing session and then rerun independently, both on 2026-11-27.
- **Statement check by an AI referee (Claude Opus). Verdict: statement confirmed, no mismatch.** The referee checked the Lean statement only; Lean's kernel checks the proof.
  - The graph definition matches the source (arXiv:2301.08106v2 §1 and arXiv:2012.01992v1 §2): distinct squares, same row, column, diagonal or antidiagonal, no wrap-around. The 0-based indexing is a graph isomorphism of the source's 1-based one.
  - The eigenvalue is the field element $n-4$; `queens_mult` is the dimension of $\ker(\mathbf A-(n-4)I)$ and `queens_alg_mult` the root multiplicity in the characteristic polynomial, so both readings of "multiplicity" are covered. The natural-number formula is exact for $n\ge4$. The only hypothesis is $n\ge4$. Over $\mathbb R$ the statement is the source's; other ordered fields only add strength.
  - Independent tests: an exact Python check of the multiplicity and of the source's edge count $n(n-1)(5n-1)/3$ for $4\le n\le12$; a kernel `decide` proof that the Lean adjacency agrees with an independently written queen-move rule on all 256 pairs for $n=4$; `#eval` agreement for $n\le8$ and the edge count for $n\le8$; the Lean adjacency matrices for $n=4,5,6$ equal to the Python ones entry by entry.
  - Fresh-checkout build in a separate worktree: PASS, with an axiom report byte-identical to the archived one.
  - Three non-blocking notes: a stale sentence in the formalization notes (since fixed in the working repository); the label "Conjecture 1(b)" in the docstring of `Main.lean` is our labelling of the second sentence of Conjecture 1, which the source does not number (this write-up now says so wherever the label appears; the Lean files are kept byte-identical and are not edited); and the check script does not scan for `native_decide` (absent here, and it would appear in the axiom report).

## Lean statement check of Corollary 13 and kernel replays (2026-11-27)

This took place after version 2 of the paper. Corollary 13 (the explicit eigenspace of $n-4$) was formalized in [`Eigenspace.lean`](lean/Pipeline/QueensSpectrum/Eigenspace.lean) by a Claude model; `lean_check` passed, and an independent rerun passed. Details are in [`LEAN.md`](LEAN.md).

- **Statement check by an AI referee (Claude Opus), on the version at commit `60cb49b`. Verdict: statement confirmed; overall accept, 0 issues.** The referee checked the Lean statement only; Lean's kernel checks the proof.
  - Clause by clause against Corollary 13: the only hypothesis is $n\ge4$; the graph and the adjacency matrix are those already confirmed for the Theorem; the statement is an "if and only if", so both inclusions are covered; "palindromic" is `r i.rev = r i`; $\gamma$ is free for odd $n$ and $0$ for even $n$; the indicator of $i+j=n-1$ is computed in the natural numbers, with no wrap-around or truncation. The general field version only adds strength; the version over $\mathbb R$ is verbatim. The axioms are `propext`, `Classical.choice` and `Quot.sound` only.
  - Independent exact test ([`cor13_check.py`](lean/kernel-replays/independent/cor13_statement_check/cor13_check.py), pure Python with exact fractions, written by the referee): for $4\le n\le10$ the Lean family lies in the kernel of $\mathbf A-(n-4)I$ and spans it, with dimension $(n-2)/2$ or $(n+1)/2$. Both side conditions are needed: for even $n$ the $\gamma$-term alone is not an eigenvector, and a non-palindromic $r$ gives a vector outside the eigenspace. Output `COR13 CHECK: ALL PASS`.
  - The source eigenvectors ([`src_vectors_check.py`](lean/kernel-replays/independent/cor13_statement_check/src_vectors_check.py)): the sets $Y^n$, $Z^n$ of arXiv:2012.01992 and $`F_{n,\ell}`$, $`E_{n,n-4}`$ of arXiv:2301.08106, built as transcribed from automated renderings of those papers, are eigenvectors for $n-4$, lie in the span of the Corollary 13 family, and have the same rank as it, for $4\le n\le10$. Output `SOURCE VECTORS CHECK: ALL PASS`. The referee read the renderings, not the PDFs.
- **Independent-kernel replays, by the same referee.** `nanoda_bin` 0.4.31 (25995 declarations) and `lean4lean` (24686 declarations), two kernels written independently of Lean's, and two further kernels shipped with the toolchain, `con-ron` and `con-leche`, accepted a lean4export file of the nine main theorems and everything they depend on. `leanchecker-paranoid`, a separate build of Lean's kernel, replayed all 12 modules, the whole closure of `Main.lean` from an empty environment, and the export file: PASS. A tampered export, with the proof of `queens_eigenspace_real` replaced by another theorem's proof, was rejected by all five export checkers. Before this, Lean's own `leanchecker` had replayed all 12 modules, also from an empty environment: PASS.
  - Limit, stated by the referee: the independent kernels check the exporter's rendering of the compiled files, not the compiled files themselves; only Lean's own kernel replayed those. The standalone lean4checker repository is deprecated and does not build for Lean v4.37.0-rc1.
  - Records: [`lean/kernel-replays/`](lean/kernel-replays/) and [`LEAN.md`](LEAN.md), section "Kernel replays".
- **Not checked by this referee:** the proof of `queens_eigenspace` line by line (the kernels check it); the credit transcriptions against the rendered PDFs; whether the exporter renders the compiled files faithfully; and what exactly distinguishes `leanchecker-paranoid` from `leanchecker` (the toolchain ships no documentation for it).

## Outside cross-checks (2026-11-27)

ChatGPT and Gemini were each given the first version of the paper (`paper.pdf` as first published) in a fresh chat, with a referee prompt asking for a line-by-line check of every lemma, the statement against the source, the credit, and the appendix, with a verdict per item. Neither saw the other's answer. As summarized by the owner of this repository, **both reported a pass, with minor formatting issues only.** The full replies and the prompt are not yet archived in this repository.

## What an expert referee should look at first

- The reduction (Lemmas 1–2) and the sector decomposition (Lemmas 3–5) are routine; the substance is in Lemmas 7, 9 and 12.
- Lemma 12 uses a maximum-principle argument (Lemma 10) whose hypotheses depend on careful index ranges. All referees checked them, and Appendix A gives an independent second proof.
- The Theorem and Corollary 13 are formalized; an expert check is most useful for the trust base (the four-line definition of the graph in `lean/Pipeline/QueensSpectrum/Defs.lean`, against the source), for the credit statements, and for the exposition.
- The credit for the lower bound and the eigenspace rests on reading arXiv:2012.01992 (§3, Theorem 3.10) and arXiv:2301.08106 (§3–4) through automated renderings and, in round 3, the text layer of the PDFs; please confirm against the rendered PDFs.
