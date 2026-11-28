# Literature and priority check

- **Dates:** three searches, all on 2026-11-27. The first ran before any work on the problem. The second ran before any claim, after the proof was written; its last checks of the three most active AI research repositories ran at 14:31 UTC. The third ran in the final pre-release check, from 16:12 to 16:34 UTC, and repeated the full checklist.
- **Question:** has anyone already proved that the eigenvalue $n-4$ of the $n$-Queens graph has multiplicity exactly $(n-2)/2$ ($n$ even) and $(n+1)/2$ ($n$ odd)? Equivalently, since the lower bounds are known: has anyone proved the matching upper bound?
- **Answer, as of 2026-11-27:** no proof, disproof or claim was found in any source checked. Some sources could not be checked (listed below). This is a dated search result, not a priority claim.

## The problem and its source

The statement is the multiplicity sentence of Conjecture 1 in D. M. Cardoso, I. S. Costa, R. Duarte, *Integer eigenvalues of the n-Queens graph*, [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) §5, published in Discrete Math. 347(9) (2024) 114065, [doi:10.1016/j.disc.2024.114065](https://doi.org/10.1016/j.disc.2024.114065). The published text (read from the University of Aveiro open-access deposit, [hdl:10773/46604](http://hdl.handle.net/10773/46604)) states Conjecture 1 with the same wording as arXiv v2. The same conjecture appears in I. S. Costa's PhD thesis (§4.8) and as Conjecture 4.1 of [arXiv:2508.01088](https://arxiv.org/abs/2508.01088).

Conjecture 1 has three sentences, which the source does not number; we label them (a), (b), (c) in order: (a) the integer eigenvalues are exactly an explicit list; (b) the multiplicity of $n-4$; (c) simplicity of the other listed integers except $-4$. **Only (b) is proved in this repository. Parts (a) and (c) remain open.**

## Timeline

| Date | Event | Source |
| --- | --- | --- |
| 2020-12-03 | Cardoso, Costa and Duarte state the full conjecture (Conjecture 3) and report that their computations confirm it for $n\le100$. They prove that $-4$ is the least eigenvalue, with multiplicity $(n-3)^2$ (Theorem 3.8), and that $n-4$ has multiplicity **at least** $(n-2)/2$ or $(n+1)/2$, with explicit linearly independent eigenvectors (abstract and Theorem 3.10, stated for $n\ge3$; eigenvector sets $Y^n$ and $Z^n$). | [arXiv:2012.01992](https://arxiv.org/abs/2012.01992), *Spectral properties of the n-Queens' graphs* (one version, no journal reference) |
| 2022-01-04 | The same authors publish sharp bounds on the least eigenvalue from edge clique partitions, covering the eigenvalue $-4$ of the Queens graph. | [arXiv:2201.01224](https://arxiv.org/abs/2201.01224); J. Algebraic Combin. 58 (2023) 263–277 |
| 2023-01-19, 2023-05-10 | arXiv v1 and v2: every listed integer is an eigenvalue (the inclusion "⊇"); the lower bound for $n-4$ is restated with eigenvectors $F_{n,\ell}$ and $E_{n,n-4}$ (Theorem 4.1, Corollary 4.2, stated for $n\ge3$); the remaining content is stated as Conjecture 1. | [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) |
| 2024-03-27 | Costa's PhD thesis is defended. Its conclusions name the exact multiplicities and the absence of other integer eigenvalues as the main open problems, which the author could not prove and lists as future work. | [hdl:10773/41899](http://hdl.handle.net/10773/41899) |
| 2024-05-20 | The 2023 paper appears in Discrete Mathematics (received 2023-12-30, accepted 2024-04-25). Its §5 calls the exact characterization of the integer eigenvalues an open problem. No erratum or addendum was found. | [doi:10.1016/j.disc.2024.114065](https://doi.org/10.1016/j.disc.2024.114065) |
| 2025-08-01 | The authors decompose the Queens graph into edge-disjoint pieces (including an integral graph), bound eigenvalues with Weyl's inequalities, and restate the conjecture as open (Conjecture 4.1). | [arXiv:2508.01088](https://arxiv.org/abs/2508.01088), *A family of regular integral graphs and its application to the n-Queens' graph* |
| 2026-04-04 | The only citing paper not by the authors: the spectrum of the toroidal 3D queen graph, a different graph (a Cayley graph solved by Fourier characters). It cites 2012.01992 for context only. | [arXiv:2604.03842](https://arxiv.org/abs/2604.03842) |
| 2026-11-27 | Our three searches (the last ending at 16:34 UTC): no proof or claim of the upper bound found. | this file |
| 2026-11-27 | Our proof of the upper bound written ([`PROOF.md`](PROOF.md)); three review rounds, the review rule passing in round 3 ([`REVIEWS.md`](REVIEWS.md)). | this repository |

## Sources searched (2026-11-27)

| Source | What was searched | Finding |
| --- | --- | --- |
| Primary sources | All arXiv versions of 2012.01992, 2301.08106 and 2508.01088; the published journal PDF of 2301.08106; Costa's thesis PDF (§4.7–4.8, §6.3.4, conclusions) | All state the exact multiplicity of $n-4$ as conjectural and prove only the lower bounds (first in 2012.01992) |
| arXiv | Author searches (Cardoso, Duarte, Costa/Serôdio); title and abstract searches for "queens graph", "queen graph", "n-queens eigenvalue", "simplicial rook"; new and recent listings of math.CO, math.SP, math.RA | No spectral work on the $n$-Queens graph after 2508.01088, other than the toroidal 3D paper above. The 2026 queens-graph papers found are about colouring, representation number, covering, independence, NP-completeness and domination |
| Citations | OpenAlex and Semantic Scholar citers of 2012.01992, 2301.08106 (and its journal DOI), 2508.01088 and 2201.01224; OpenCitations for the journal DOI | Every citer is by the same authors, except 2604.03842, which treats a different graph |
| Simplicial rook graphs | Martin–Wagner, *On the spectra of simplicial rook graphs* ([arXiv:1209.3493](https://arxiv.org/abs/1209.3493)); Brouwer–Cioabă–Haemers–Vermette, *Notes on simplicial rook graphs* ([arXiv:1408.5615](https://arxiv.org/abs/1408.5615)); their citers | These papers study the spectra of another family of integral graphs. Neither they nor their citers mention the $n$-Queens graph. They are not used in our proof |
| AI research repositories and sites | Full issue, pull-request and branch dumps of `1337isnot1337/solved-conjectures` and `PerAlexandersson/RealRooted`; `the-omega-institute/trureturing` (issues, pull requests, full trees); MathDB entries 348918, 369610 and 357273 (0 solutions, no progress recorded); Hexagon, Prove2Me, Crab Research, eulersolve; several other public AI-mathematics repositories; Zenodo | No item on the spectrum of the $n$-Queens graph |
| General | Web search; GitHub code and issue search; OEIS; Open Problem Garden; `google-deepmind/formal-conjectures`; MathOverflow and Math StackExchange | No proof, disproof or claim. One search-engine summary said that 2508.01088 proves the exact multiplicity; the PDF states it only as Conjecture 4.1. Search summaries are not evidence |

### Not completed on 2026-11-27

These gaps were the same in all three searches, except that Prove2Me's search was unavailable in the third.

- UnsolvedMath (rate-limited on every attempt, including three attempts in the third search; only a catalog snapshot dated 2026-09-22 was checked, and it has no entry on the Queens-graph spectrum).
- Google Scholar "cited by" (blocked).
- A repository called "Principia" (none identified).
- Prove2Me's search for `Cardoso` in the third search ("Search unavailable").
- The full theorem list of `prove2me/formalpedia`, and the parts of two large AI-mathematics repositories beyond the API's tree truncation (only their index files were searched).

**Re-run in the third search (16:12–16:34 UTC), and to be re-run before any further release:** the two GitHub issue dumps and the trureturing search; the arXiv author searches and the abstract search for "queens eigenvalues"; the MathDB progress fields; the Zenodo phrase searches (one prolific author of AI-assisted preprints was posting daily); and a retry of UnsolvedMath.

## Comparison with prior work

| | Cardoso, Costa and Duarte | This repository |
| --- | --- | --- |
| What is proved about $n-4$ | Multiplicity **at least** $(n-2)/2$ or $(n+1)/2$ | Multiplicity **exactly** $(n-2)/2$ or $(n+1)/2$ (the upper bound is conjectured but not proved in their papers) |
| How | Explicit eigenvectors: the sets $Y^n$ and, for odd $n$, $Z^n$ (2020; as printed, the set $Y^n$ has $\lceil n/2\rceil$ vectors with one linear relation, and the proof uses $\lceil n/2\rceil-1$ of them, together with $Z^n$ for odd $n$, as linearly independent eigenvectors), restated as $F_{n,\ell}$ and $E_{n,n-4}$ (2023) | The dimension of the eigenspace is computed exactly, via the line Gram matrix and five symmetry sectors |
| Shared ingredient | Edge clique partitions by lines (used for the eigenvalue $-4$) | The same partition gives $\mathbf A=NN^{T}-4I$, the starting point |
| Eigenspace | Their eigenvectors | The same space (our proof rederives it; the description is theirs) |
| Other tools | Equitable partitions; a decomposition into an integral graph plus cliques and bicliques, with Weyl's inequalities | Three explicit involutions; elementary elimination; a discrete maximum principle for weighted means |
| Computer | Computations for $n\le100$ (method not stated) | None in the proof; exact-arithmetic checks for small $n$ as corroboration |

**Conclusion.**

- The conjecture, the lower bounds and the eigenvectors are due to Cardoso, Costa and Duarte, first in arXiv:2012.01992 (2020) and again in arXiv:2301.08106 (2023).
- The exact value, equivalently the upper bound (the Theorem), is conjectured but not proved in their papers ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992) Conj. 3; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) Conj. 1; [arXiv:2508.01088](https://arxiv.org/abs/2508.01088) Conj. 4.1); whether a proof of it, or the method used here, appears elsewhere has not been checked beyond the priority search of 2026-11-27. In that search it was not found in any source checked, and the authors' 2025 paper and Costa's 2024 thesis still list it as open.
- The identification of their eigenvectors ($Y^n$, $Z^n$, $F_{n,\ell}$, $E_{n,n-4}$) with ours, and the theorem number 3.10 of arXiv:2012.01992, were read from automated renderings (ar5iv and arXiv HTML). Our referees confirmed the identification by exact computation. It was then confirmed against the PDF text layer (final gate, 2026-11-27); the rendered PDF pages have not been viewed.
