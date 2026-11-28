# Proof: the exact multiplicity of the eigenvalue $n-4$ of the $n$-Queens graph

*Written 2026-11-27. The proof below passed our review rule in round 3 (three AI referees on three Claude models; in round 3 two accepted with zero issues and the third raised two minor wording points, now fixed), so its steps are labelled `proved`. The referees read the proof file of the working repository; this file is a re-presentation of that refereed text: the parts of Lemma 4 are reordered (parts (a), (b), (c) here are parts (c), (a), (b) there), the auxiliary subspace $W$ is named in the list of subspaces before Lemma 4, and §0 and §10–§13 are rewritten. There is no mathematical change. **Formalized in Lean 4 + Mathlib** (full theorem, all n ≥ 4). Expert verification still welcome. Verified so far with: Lean 4 + Mathlib (whole theorem); three rounds of AI review (Claude Opus, Claude Fable, Claude Sonnet; passed round 3); exact computation for 4 ≤ n ≤ 40; outside cross-checks by ChatGPT and Gemini (both passed). The conjecture, the lower bounds and the eigenvectors are due to Cardoso, Costa and Duarte; §12 states the credit.*

## 0. What is proved, and the status words used

**What is proved.** For every $n\ge4$, the eigenvalue $n-4$ of the adjacency matrix of the $n$-Queens graph has multiplicity exactly $\frac{n-2}{2}$ ($n$ even) or $\frac{n+1}{2}$ ($n$ odd) (Theorem, §1). This is the multiplicity sentence of Conjecture 1 of Cardoso, Costa and Duarte ([arXiv:2301.08106](https://arxiv.org/abs/2301.08106), §5). They had already proved that these numbers are lower bounds, with explicit eigenvectors ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992), Theorem 3.10; restated in [arXiv:2301.08106](https://arxiv.org/abs/2301.08106), Theorem 4.1 and Corollary 4.2). The exact value, equivalently the upper bound (the Theorem), is conjectured but not proved in their papers ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992) Conj. 3; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) Conj. 1; [arXiv:2508.01088](https://arxiv.org/abs/2508.01088) Conj. 4.1); whether a proof of it, or the method used here, appears elsewhere has not been checked beyond the priority search of 2026-11-27.

**What is not proved.** Conjecture 1 has two further parts: (a) no integer outside their list is an eigenvalue; (c) the other listed integers are simple eigenvalues. (The source does not number the three sentences of Conjecture 1; the labels (a), (b), (c) are ours, in order, so the Theorem is part (b), its second sentence.) Both stay `open`. This file does not settle Conjecture 1.

**Status words.**

- `formalized`: checked by Lean 4 with Mathlib (`lake build` passes, no `sorry`, standard axioms only). The Theorem has this status: see [`LEAN.md`](LEAN.md). The Lean proof follows this file, with a few local differences of route listed there.
- `proved`: a complete argument written in this file that passed our review rule (AI referees; see [`REVIEWS.md`](REVIEWS.md)). It does not replace expert verification.
- `proposed`: written but not yet through the final check; used here only for Corollary 13, whose description is credited to Cardoso, Costa and Duarte, and its credit remark. The source transcriptions behind it were confirmed against the PDF text layer (final gate, 2026-11-27); the label stays until its review status is updated.
- `numerical`: a finite check by computer, for the stated range of $n$, in exact integer or rational arithmetic (never floating point). A `numerical` item is never used as a step of the proof.
- `open`: nothing above applies.
- The word `certified` (a computation reproduced by two independent implementations and archived as a certificate) is not used in this file, because no certificate has been archived yet.

Every lemma, remark, corollary and appendix item carries its status word in its heading, and §10 lists them all. Sub-steps inside a proof carry the status of their lemma.

**No step of the proof depends on a computation.** The scripts in [`scripts/`](scripts/) are corroboration for finitely many $n$ (§11).

## 1. Statement, conventions, notation

**Source.** D. M. Cardoso, I. S. Costa, R. Duarte: Conjecture 3 of [arXiv:2012.01992](https://arxiv.org/abs/2012.01992) §3; current form Conjecture 1 of [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) §5, published as Discrete Math. 347(9) (2024) 114065, [doi:10.1016/j.disc.2024.114065](https://doi.org/10.1016/j.disc.2024.114065); restated as Conjecture 4.1 of [arXiv:2508.01088](https://arxiv.org/abs/2508.01088). The sentence of Conjecture 1 proved here says, in our words: when $n$ is even the eigenvalue $n-4$ has multiplicity $\frac{n-2}{2}$, and when $n$ is odd it has multiplicity $\frac{n+1}{2}$. Conjecture 1 also says (a) that the integers in an explicit list (displayed in [`README.md`](README.md)) are the only integer eigenvalues, and (c) that the listed integers other than $-4$ and $n-4$ are simple eigenvalues. Parts (a) and (c) are not treated here.

**Theorem (status: proved).** Let $n\ge4$ be an integer and let $\mathbf A$ be the adjacency matrix of the $n$-Queens graph $\mathcal Q(n)$. Then $n-4$ is an eigenvalue of $\mathbf A$, and its multiplicity is exactly

```math
\frac{n-2}{2}\quad\text{if } n \text{ is even},\qquad\qquad \frac{n+1}{2}\quad\text{if } n \text{ is odd}.
```

**Conventions.** Throughout, $n\ge4$ is an integer and $[P]$ is 1 if the statement $P$ holds and 0 otherwise.

- *Board and graph.* The vertices of $\mathcal Q(n)$ are the $n^2$ squares $(i,j)$, $0\le i,j\le n-1$. Two **distinct** squares $(i,j)$ and $(i',j')$ are adjacent when $i=i'$ (same row), or $j=j'$ (same column), or $i-j=i'-j'$ (same diagonal), or $i+j=i'+j'$ (same antidiagonal). These are the squares a chess queen on $(i,j)$ attacks. $\mathbf A$ is the $n^2\times n^2$ adjacency matrix: $\mathbf A_{x,x'}=1$ if $x$ and $x'$ are adjacent and 0 otherwise. It is real symmetric, so the multiplicity of an eigenvalue $\lambda$ (as a root of the characteristic polynomial) equals $\dim\ker(\mathbf A-\lambda I)$; this is the meaning of "multiplicity" everywhere below. (Cardoso, Costa and Duarte index squares from 1; shifting indices is a graph isomorphism and changes nothing.)
- *Lines.* There are four families of lines: rows $R_i$ and columns $C_j$ ($0\le i,j\le n-1$), diagonals $D_k$ and antidiagonals $A_s$ ($\lvert k\rvert,\lvert s\rvert\le n-1$):

```math
R_i=\{(i,j):0\le j\le n-1\},\quad C_j=\{(i,j):0\le i\le n-1\},\quad D_k=\{(i,j):i-j=k\},\quad A_s=\{(i,j):i+j-(n-1)=s\}.
```

  There are $n+n+(2n-1)+(2n-1)=6n-2$ lines, all nonempty. The square $(i,j)$ lies on exactly four lines, one of each family: $R_i$, $C_j$, $D_{i-j}$ and $A_{i+j-(n-1)}$. (The letter $A$ with an integer subscript is always an antidiagonal; the adjacency matrix is the bold $\mathbf A$.)
- *Line space.* $V=\mathbb R^{6n-2}$ is the space of real functions on the set of lines. A vector is written $v=(r,c,d,a)$ with $r=(r_i)_{0\le i\le n-1}$ its values on the rows, $c=(c_j)_{0\le j\le n-1}$ on the columns, $d=(d_k)_{\lvert k\rvert\le n-1}$ on the diagonals and $a=(a_s)_{\lvert s\rvert\le n-1}$ on the antidiagonals.
- *Incidence and Gram matrices.* $N$ is the $n^2\times(6n-2)$ matrix with $N_{x,L}=[x\in L]$ for a square $x$ and a line $L$ (the *incidence matrix*), and $M=N^{T}N$ (the *Gram matrix of the lines*), so that $M_{L,L'}=\lvert L\cap L'\rvert$. Explicitly, for $v=(r,c,d,a)$:

```math
(Nv)(i,j)=r_i+c_j+d_{i-j}+a_{i+j-(n-1)},\qquad\qquad (Mv)_L=\sum_{x\in L}(Nv)(x).\qquad\text{(1.1)}
```

- *Reversals.* For $r\in\mathbb R^n$ put $r^{\leftarrow}_i=r_{n-1-i}$; for $d=(d_k)_{\lvert k\rvert\le n-1}$ put $d^{-}_k=d_{-k}$. Call $r$ *palindromic* if $r^{\leftarrow}=r$ and *antipalindromic* if $r^{\leftarrow}=-r$; call $d$ *even* if $d^{-}=d$ and *odd* if $d^{-}=-d$ (then $d_0=0$).
- *Sums.* For $r\in\mathbb R^n$: $\rho_k=\sum_{i=k}^{n-1}r_i$ for $0\le k\le n-1$, $\rho_n=0$, and $R=\rho_0=\sum_i r_i$; note $r_i=\rho_i-\rho_{i+1}$. For $m\ge0$ let $S(m)=\lbrace -m,-m+2,\dots,m-2,m\rbrace$ ($m+1$ integers, a set symmetric under $s\mapsto-s$). For real numbers $d_0,\dots,d_{n-1}$:

```math
T_m=\sum_{s\in S(m)}d_{\lvert s\rvert}\quad(0\le m\le n-1),\qquad T_{-1}=0,\qquad D=\sum_{k=0}^{n-1}d_k .\qquad\text{(1.2)}
```

  So $T_m=d_0+2(d_2+d_4+\dots+d_m)$ for even $m$ and $T_m=2(d_1+d_3+\dots+d_m)$ for odd $m$. Without a subscript, $R$ and $D$ denote these sums; with a subscript, $R_i$ and $D_k$ denote lines.

**Plan of the proof.** §2 turns the question into a question about the $(6n-2)\times(6n-2)$ matrix $M$: the multiplicity of $n-4$ in $\mathbf A$ equals $\dim\ker(M-nI)$. §3 splits the line space into five pieces ("sectors") that $M$ preserves, using three explicit symmetries of the board. §4 writes down $M$ on each sector. §5–§7 compute the kernel of $M-nI$ on each sector by elementary linear algebra. §8 adds up the dimensions.

## 2. Reduction to the Gram matrix of the lines

**Lemma 1 (status: proved).** Two distinct squares lie on at most one common line, and they are adjacent in $\mathcal Q(n)$ if and only if they lie on a common line. Hence $NN^{T}=\mathbf A+4I$.

*Proof.* $(NN^{T})_{x,x'}$ is the number of lines containing both $x$ and $x'$. For $x=x'$ it is 4 (§1). Let $x=(i,j)\ne x'=(i',j')$. Since each square is on exactly one line of each family, the number of common lines is the number of true statements among

```math
\text{(a) } i=i',\qquad \text{(b) } j=j',\qquad \text{(c) } i-j=i'-j',\qquad \text{(d) } i+j=i'+j'.
```

By definition $x$ and $x'$ are adjacent exactly when at least one of (a)–(d) holds. Any two of them force $x=x'$: (a),(b) directly; (a),(c) give $j=j'$; (a),(d) give $j=j'$; (b),(c) give $i=i'$; (b),(d) give $i=i'$; (c),(d) give $2i=2i'$ by addition, hence $i=i'$ and then $j=j'$. So for $x\ne x'$ at most one holds, and $(NN^{T})_{x,x'}=[x\text{ adjacent to }x']=\mathbf A_{x,x'}$. $\square$

**Lemma 2 (status: proved).** For every real $\mu\ne0$, the map $v\mapsto Nv$ is a linear bijection from $\ker(M-\mu I)$ onto $\ker(NN^{T}-\mu I)$. Consequently, for every $n\ge4$,

```math
\text{multiplicity of } n-4 \text{ in } \mathbf A \quad=\quad \dim\ker(M-nI),
```

and $N$ maps $\ker(M-nI)$ bijectively onto the eigenspace $\ker(\mathbf A-(n-4)I)$.

*Proof.* If $Mv=\mu v$ then $NN^{T}(Nv)=N(Mv)=\mu Nv$, so $N$ maps $\ker(M-\mu I)$ into $\ker(NN^{T}-\mu I)$. It is injective there: if $Mv=\mu v$ and $Nv=0$ then $\mu v=N^{T}Nv=0$, so $v=0$ because $\mu\ne0$. Hence $\dim\ker(M-\mu I)\le\dim\ker(NN^{T}-\mu I)$. By the same argument with the roles of $N$ and $N^{T}$ exchanged, $N^{T}$ maps $\ker(NN^{T}-\mu I)$ injectively into $\ker(M-\mu I)$, which gives the reverse inequality. So the two dimensions are equal and the injective map $N$ is a bijection. By Lemma 1, $\ker(\mathbf A-(n-4)I)=\ker(NN^{T}-nI)$, and $\mu=n\ne0$. $\square$

## 3. Three symmetry operators and the five sectors

No representation theory is used: the decomposition below is obtained from three explicit involutions (linear maps whose square is the identity). The names $A_1$, $B_1$, $B_2$, $E$, $E'$ of the five sectors are only labels.

Define linear maps $t,h,z:V\to V$ by

```math
t(r,c,d,a)=(c,\ r,\ d^{-},\ a),\qquad h(r,c,d,a)=(r,\ c^{\leftarrow},\ a,\ d),\qquad z(r,c,d,a)=(r^{\leftarrow},\ c^{\leftarrow},\ d^{-},\ a^{-}).\qquad\text{(3.0)}
```

**Lemma 3 (status: proved).**
(a) $t^2=h^2=z^2=I$, $tz=zt$, $hz=zh$, $th=z ht$, and $(th)^2=z$.
(b) Each of $t,h,z$ commutes with $M$.

*Proof.* (a) Each of the reversals $r\mapsto r^{\leftarrow}$, $d\mapsto d^{-}$ is an involution, and so is a swap; hence $t^2=h^2=z^2=I$. For $v=(r,c,d,a)$, substituting in (3.0):

```math
\begin{aligned}
tzv&=t(r^{\leftarrow},c^{\leftarrow},d^{-},a^{-})=(c^{\leftarrow},r^{\leftarrow},d,a^{-}), & ztv&=z(c,r,d^{-},a)=(c^{\leftarrow},r^{\leftarrow},d,a^{-}),\\
hzv&=h(r^{\leftarrow},c^{\leftarrow},d^{-},a^{-})=(r^{\leftarrow},c,a^{-},d^{-}), & zhv&=z(r,c^{\leftarrow},a,d)=(r^{\leftarrow},c,a^{-},d^{-}),\\
thv&=t(r,c^{\leftarrow},a,d)=(c^{\leftarrow},r,a^{-},d), & z(htv)&=z(c,r^{\leftarrow},a,d^{-})=(c^{\leftarrow},r,a^{-},d).
\end{aligned}
```

So $tz=zt$, $hz=zh$ and $th=z ht$. Finally $(th)^2=(z ht)(th)=z h(tt)h=z hh=z$.

(b) Consider the three bijections of the board $\tau(i,j)=(j,i)$ (transpose), $\eta(i,j)=(i,n-1-j)$ (left–right flip) and $\zeta(i,j)=(n-1-i,n-1-j)$ (half-turn). Each is an involution and maps lines onto lines, as in the table below. Each entry $\sigma(L)\subseteq L'$ is checked by substituting into the defining equation of the line; for instance $(i,j)\in D_k$ means $i-j=k$, which is $i+(n-1-j)-(n-1)=k$, i.e. $\eta(i,j)\in A_k$. The inclusions are equalities: the table also gives $\sigma(L')\subseteq L$ (for example $\eta(A_k)\subseteq D_k$), so $L'=\sigma(\sigma(L'))\subseteq\sigma(L)$.

| | $R_i$ | $C_j$ | $D_k$ | $A_s$ |
| --- | --- | --- | --- | --- |
| $\tau$ maps it onto | $C_i$ | $R_j$ | $D_{-k}$ | $A_s$ |
| $\eta$ maps it onto | $R_i$ | $C_{n-1-j}$ | $A_k$ | $D_s$ |
| $\zeta$ maps it onto | $R_{n-1-i}$ | $C_{n-1-j}$ | $D_{-k}$ | $A_{-s}$ |

Let $\sigma$ be one of $\tau,\eta,\zeta$. It permutes the set of lines, and $\sigma^{-1}=\sigma$. Define $\hat\sigma :V\to V$ by $(\hat\sigma v)_L=v_{\sigma(L)}$. Since $\sigma$ is a bijection of the board, $\lvert\sigma(L)\cap\sigma(L')\rvert=\lvert L\cap L'\rvert$ for all lines $L,L'$, and therefore, substituting $L'=\sigma(L'')$,

```math
(M\hat\sigma v)_L=\sum_{L'}\lvert L\cap L'\rvert v_{\sigma(L')}=\sum_{L''}\lvert L\cap\sigma(L'')\rvert v_{L''}=\sum_{L''}\lvert\sigma(L)\cap L''\rvert v_{L''}=(Mv)_{\sigma(L)}=(\hat\sigma Mv)_L .
```

(The third equality applies $\sigma$ to both sets and uses $\sigma\sigma=\mathrm{id}$.) So $\hat\sigma $ commutes with $M$. Reading the table: $(\hat\tau v)_{R_i}=v_{C_i}=c_i$, $(\hat\tau v)_{C_j}=r_j$, $(\hat\tau v)_{D_k}=d_{-k}$, $(\hat\tau v)_{A_s}=a_s$, so $\hat\tau =t$; $(\hat\eta v)_{R_i}=r_i$, $(\hat\eta v)_{C_j}=c_{n-1-j}$, $(\hat\eta v)_{D_k}=a_k$, $(\hat\eta v)_{A_s}=d_s$, so $\hat\eta =h$; and $(\hat\zeta v)_{R_i}=r_{n-1-i}$, $(\hat\zeta v)_{C_j}=c_{n-1-j}$, $(\hat\zeta v)_{D_k}=d_{-k}$, $(\hat\zeta v)_{A_s}=a_{-s}$, so $\hat\zeta =z$. $\square$

Define six subspaces of $V$:

```math
\begin{aligned}
V_{A1}&=\{v: tv=v,\ hv=v\}, & V_{B1}&=\{v: tv=-v,\ hv=v\}, & V_{B2}&=\{v: tv=v,\ hv=-v\},\\
W&=\{v: tv=-v,\ hv=-v\}, & V_{E}&=\{v: zv=-v,\ hv=v\}, & V_{E'}&=\{v: zv=-v,\ hv=-v\}.
\end{aligned}
```

**Lemma 4 (status: proved).**
(a) $W=0$, and explicitly:

```math
\begin{aligned}
V_{A1}&=\{(r,\ r,\ d,\ d): r \text{ palindromic},\ d \text{ even}\}, &\dim&=\lceil n/2\rceil+n, &&(3.1)\\
V_{B1}&=\{(r,\ -r,\ 0,\ 0): r \text{ palindromic}\}, &\dim&=\lceil n/2\rceil, &&(3.2)\\
V_{B2}&=\{(0,\ 0,\ d,\ -d): d \text{ even}\}, &\dim&=n, &&(3.3)\\
V_{E}&=\{(r,\ 0,\ d,\ d): r \text{ antipalindromic},\ d \text{ odd}\}, &\dim&=\lfloor n/2\rfloor+n-1. &&(3.4)
\end{aligned}
```

(b) $V=V_{A1}\oplus V_{B1}\oplus V_{B2}\oplus V_{E}\oplus V_{E'}$.
(c) Each of the five subspaces in (b) is $M$-invariant, and $t$ restricts to a linear bijection $V_E\to V_{E'}$ that commutes with $M$.
(d) For every real $\mu$,

```math
\dim\ker(M-\mu I)=\dim\ker\bigl((M-\mu I)\vert_{V_{A1}}\bigr)+\dim\ker\bigl((M-\mu I)\vert_{V_{B1}}\bigr)+\dim\ker\bigl((M-\mu I)\vert_{V_{B2}}\bigr)+2\dim\ker\bigl((M-\mu I)\vert_{V_{E}}\bigr).
```

*Proof.* Part (a) uses only (3.0). Part (b) uses Lemma 3(a) and part (a). Part (c) uses Lemma 3. Part (d) uses parts (b) and (c).

(a) Write $v=(r,c,d,a)$. From (3.0):

- $tv=v$ means $c=r$ and $d$ even. $tv=-v$ means $c=-r$, $d$ odd and $a=0$.
- $hv=v$ means $c$ palindromic and $a=d$. $hv=-v$ means $r=0$, $c$ antipalindromic and $a=-d$.
- $zv=-v$ means $r,c$ antipalindromic and $d,a$ odd.

Combining: for $V_{A1}$ we get $c=r$ palindromic and $a=d$ even, which is (3.1). For $V_{B1}$: $c=-r$ palindromic, $a=0$, and $d=a=0$, which is (3.2). For $V_{B2}$: $r=0$, $c=r=0$, $d$ even and $a=-d$, which is (3.3). For $W$: $r=0$, $c=-r=0$, $a=0$ and $d=-a=0$, so $W=0$. For $V_E$: $c$ is both palindromic and antipalindromic, so $c=0$; $r$ is antipalindromic; $a=d$ is odd; this is (3.4). The dimensions follow by counting free coordinates: a palindromic $r$ has $\lceil n/2\rceil$ free entries, an antipalindromic one $\lfloor n/2\rfloor$, an even $d$ has $n$ (namely $d_0,\dots,d_{n-1}$), an odd $d$ has $n-1$ (namely $d_1,\dots,d_{n-1}$).

(b) Put $V_{\pm}=\ker(z\mp I)$. Since $z^2=I$, every $v$ is $\frac12(v+zv)+\frac12(v-zv)$ with the first term in $V_+$ and the second in $V_-$, and $V_+\cap V_-=0$; so $V=V_+\oplus V_-$. Since $t$ and $h$ commute with $z$ (Lemma 3(a)), they map $V_+$ into $V_+$ and $V_-$ into $V_-$.

*The part $V_+$.* For $v\in V_+$ we have $htv\in V_+$, hence $thv=z(htv)=htv$ by Lemma 3(a). So $t$ and $h$ restrict to commuting involutions of $V_+$. For signs $\varepsilon,\delta\in\lbrace +1,-1\rbrace$ put $\pi_{\varepsilon\delta}=\frac14(I+\varepsilon t)(I+\delta h)$ on $V_+$. Then $\sum_{\varepsilon,\delta}\pi_{\varepsilon\delta}=\frac14(2I)(2I)=I$, and, because $t$ and $h$ commute on $V_+$ and $t(I+\varepsilon t)=\varepsilon(I+\varepsilon t)$, $h(I+\delta h)=\delta(I+\delta h)$, every vector $w=\pi_{\varepsilon\delta}v$ with $v\in V_+$ satisfies $tw=\varepsilon w$ and $hw=\delta w$. Conversely, if $w\in V_+$ with $tw=\varepsilon' w$ and $hw=\delta' w$ then $\pi_{\varepsilon\delta}w=\frac14(1+\varepsilon\varepsilon')(1+\delta\delta')w$, which is $w$ if $(\varepsilon,\delta)=(\varepsilon',\delta')$ and $0$ otherwise. Hence $V_+$ is the direct sum of the four spaces $\lbrace v\in V_+:tv=\varepsilon v,\ hv=\delta v\rbrace$: the first statement shows that they span $V_+$, and applying $\pi_{\varepsilon\delta}$ to a vanishing sum of vectors, one from each space, shows that each summand is zero. Moreover any $v\in V$ with $tv=\varepsilon v$ and $hv=\delta v$ lies in $V_+$, because $zv=(th)^2v=(\varepsilon\delta)^2v=v$ (Lemma 3(a)). So the four spaces are $V_{A1}$ ($\varepsilon=\delta=1$), $V_{B1}$ ($\varepsilon=-1,\delta=1$), $V_{B2}$ ($\varepsilon=1,\delta=-1$) and $W$ ($\varepsilon=\delta=-1$). By part (a), $W=0$. Hence $V_+=V_{A1}\oplus V_{B1}\oplus V_{B2}$.

*The part $V_-$.* $h$ is an involution of $V_-$, so, as for $z$ above, $V_-=\lbrace v\in V_-:hv=v\rbrace\oplus\lbrace v\in V_-:hv=-v\rbrace=V_E\oplus V_{E'}$. This proves (b).

(c) If $g\in\lbrace t,h,z\rbrace$ and $gv=\varepsilon v$ then $g(Mv)=M(gv)=\varepsilon Mv$ by Lemma 3(b). So each of the five subspaces, being defined by such conditions, is $M$-invariant. Let $v\in V_E$. Then $z(tv)=t(zv)=-tv$. Multiplying $th=z ht$ on the left by $z$ gives $ht=z th$, so $h(tv)=z t(hv)=z(tv)=-tv$. Hence $tv\in V_{E'}$. In the same way, for $v\in V_{E'}$: $z(tv)=-tv$ and $h(tv)=z t(hv)=-z(tv)=tv$, so $tv\in V_E$. Since $t^2=I$, $t:V_E\to V_{E'}$ is a bijection with inverse $t$, and it commutes with $M$.

(d) Let $V=\bigoplus_i W_i$ with $MW_i\subseteq W_i$, and $v=\sum_i w_i$ with $w_i\in W_i$. Then $(M-\mu I)v=\sum_i(M-\mu I)w_i$ with $(M-\mu I)w_i\in W_i$, so $(M-\mu I)v=0$ if and only if $(M-\mu I)w_i=0$ for all $i$. Hence $\ker(M-\mu I)=\bigoplus_i\ker((M-\mu I)\vert_{W_i})$. Apply this to the decomposition (b), whose summands are $M$-invariant by (c). By (c), $t$ maps $\ker((M-\mu I)\vert_{V_E})$ bijectively onto $\ker((M-\mu I)\vert_{V_{E'}})$, so these two have the same dimension. $\square$

*Check (not needed for the proof; status: proved).* The dimensions in (a), with $V_E$ counted twice, add up to $2\lceil n/2\rceil+2\lfloor n/2\rfloor+4n-2=6n-2=\dim V$.

## 4. The action of $M$ on the sectors

**Lemma 5 (status: proved).** For $v=(r,c,d,a)\in V$, $0\le i\le n-1$ and $0\le k\le n-1$:

```math
(Mv)_{R_i}=n r_i+\sum_{j=0}^{n-1}c_j+\sum_{k'=i-n+1}^{i}d_{k'}+\sum_{s=i-n+1}^{i}a_s ,\qquad\text{(4.0a)}
```

```math
(Mv)_{D_k}=(n-k) d_k+\sum_{i'=k}^{n-1}r_{i'}+\sum_{j=0}^{n-1-k}c_j+\sum_{s\in S(n-1-k)}a_s .\qquad\text{(4.0b)}
```

Consequently, with the notation (1.2):

```math
\begin{aligned}
v=(r,r,d,d)\in V_{A1}:&\quad (Mv)_{R_i}=n r_i+R+2\sum_{k'=i-n+1}^{i}d_{\lvert k'\rvert},\qquad (Mv)_{D_k}=(n-k) d_k+2\rho_k+T_{n-1-k}; &&(4.1)\\
v=(r,-r,0,0)\in V_{B1}:&\quad (Mv)_{R_i}=n r_i-R; &&(4.2)\\
v=(0,0,d,-d)\in V_{B2}:&\quad (Mv)_{D_k}=(n-k) d_k-T_{n-1-k}; &&(4.3)\\
v=(r,0,d,d)\in V_{E}:&\quad (Mv)_{R_i}=n r_i+2\sum_{k'=i-n+1}^{i}d_{k'},\qquad (Mv)_{D_k}=(n-k) d_k+\rho_k\quad(1\le k\le n-1). &&(4.4)
\end{aligned}
```

*Proof.* By (1.1), $(Mv)_L=\sum_{(i,j)\in L}\bigl(r_i+c_j+d_{i-j}+a_{i+j-(n-1)}\bigr)$.

For $L=R_i$ the squares are $(i,j)$, $0\le j\le n-1$. As $j$ runs through $0,\dots,n-1$, the index $i-j$ runs once through $i-n+1,\dots,i$ and the index $i+j-(n-1)$ runs once through $i-n+1,\dots,i$. This is (4.0a).

For $L=D_k$ with $0\le k\le n-1$ the squares are $(i',i'-k)$, $k\le i'\le n-1$ (there are $n-k$ of them). The row index $i'$ runs through $k,\dots,n-1$; the column index $i'-k$ runs through $0,\dots,n-1-k$; the antidiagonal index is $i'+(i'-k)-(n-1)=-(n-1-k)+2(i'-k)$, which runs once through $S(n-1-k)$ as $i'-k$ runs through $0,\dots,n-1-k$. This is (4.0b).

(4.1): here $c=r$, so $\sum_jc_j=R$; $a=d$ is even, so the two sums in (4.0a) are both $\sum_{k'=i-n+1}^{i}d_{\lvert k'\rvert}$; in (4.0b), $\sum_{j=0}^{n-1-k}c_j=\sum_{j=0}^{n-1-k}r_{n-1-j}=\sum_{i'=k}^{n-1}r_{i'}=\rho_k$ because $r$ is palindromic, and $\sum_{s\in S(n-1-k)}a_s=\sum_{s\in S(n-1-k)}d_{\lvert s\rvert}=T_{n-1-k}$.
(4.2): $c=-r$ and $d=a=0$ in (4.0a).
(4.3): $r=c=0$ and $a_s=-d_{\lvert s\rvert}$ in (4.0b).
(4.4): $c=0$ and $a=d$ in (4.0a); in (4.0b), $\sum_{s\in S(n-1-k)}a_s=\sum_{s\in S(n-1-k)}d_s=0$ because $S(n-1-k)$ is symmetric under $s\mapsto-s$ and $d$ is odd. $\square$

**Remark 4.5 (which components decide; status: proved).** Let $V_S$ be one of the four sectors (3.1)–(3.4) and $v\in V_S$. By Lemma 4(c), $(M-nI)v\in V_S$. By (3.1)–(3.4), a vector of $V_{A1}$ is determined by its components on $R_i$ ($0\le i\le n-1$) and $D_k$ ($0\le k\le n-1$); a vector of $V_{B1}$ by its components on the $R_i$; a vector of $V_{B2}$ by its components on $D_k$ ($0\le k\le n-1$); a vector of $V_E$ by its components on $R_i$ ($0\le i\le n-1$) and $D_k$ ($1\le k\le n-1$). So $(M-nI)v=0$ if and only if those components of $(M-nI)v$ vanish. Lemma 5 gives exactly those components.

## 5. The sectors $B_1$ and $E$ at $\mu=n$

**Lemma 6 (sector $B_1$; status: proved).** $\ker\bigl((M-nI)\vert_{V_{B1}}\bigr)=\lbrace (r,-r,0,0): r \text{ palindromic},\ \sum_i r_i=0\rbrace$, and its dimension is $\lceil n/2\rceil-1$.

*Proof.* Let $v=(r,-r,0,0)\in V_{B1}$. By (4.2), the $R_i$-component of $(M-nI)v$ is $-R$ for every $i$. By Remark 4.5, $(M-nI)v=0$ if and only if $R=0$. The linear form $r\mapsto R$ on the $\lceil n/2\rceil$-dimensional space of palindromic vectors is not zero (it takes the value $n$ at $r=(1,\dots,1)$), so its kernel has dimension $\lceil n/2\rceil-1$. $\square$

**Lemma 7 (sector $E$; status: proved).** $\ker\bigl((M-nI)\vert_{V_{E}}\bigr)=0$.

*Proof.* Let $v=(r,0,d,d)\in V_E$ ($r$ antipalindromic, $d$ odd) with $(M-nI)v=0$. By (4.4) and Remark 4.5 this means

```math
(\mathrm{row}_i)\quad 2\sum_{k'=i-n+1}^{i}d_{k'}=0\quad(0\le i\le n-1),\qquad\qquad(\mathrm{diag}_k)\quad -k d_k+\rho_k=0\quad(1\le k\le n-1).
```

*(E1)* For $1\le i\le n-1$, subtracting $(\mathrm{row}_{i-1})$ from $(\mathrm{row}_i)$: the window of summation moves from $[i-n,i-1]$ to $[i-n+1,i]$, so the difference is $2(d_i-d_{i-n})=2(d_i+d_{n-i})$, using that $d$ is odd and $1\le n-i\le n-1$. Hence $d_i+d_{n-i}=0$ for $1\le i\le n-1$.

*(E2)* Since $r$ is antipalindromic, $\rho_0=\sum_ir_i=0$, and for $0\le k\le n$: $\rho_{n-k}=\sum_{i\ge n-k}r_i=-\sum_{i\ge n-k}r_{n-1-i}=-\sum_{j=0}^{k-1}r_j=-(\rho_0-\rho_k)=\rho_k$.

*(E3)* By $(\mathrm{diag}_k)$, $d_k=\rho_k/k$ for $1\le k\le n-1$. Insert this and (E2) into (E1): for $1\le k\le n-1$,

```math
0=d_k+d_{n-k}=\frac{\rho_k}{k}+\frac{\rho_{n-k}}{n-k}=\rho_k\Bigl(\frac1k+\frac1{n-k}\Bigr),
```

and the bracket is positive, so $\rho_k=0$ for $1\le k\le n-1$. Together with $\rho_0=0$ and $\rho_n=0$: $r_i=\rho_i-\rho_{i+1}=0$ for all $i$, and $d_k=\rho_k/k=0$ for $1\le k\le n-1$. So $v=0$. $\square$

## 6. The sector $A_1$ at $\mu=n$

**Lemma 8 (window identity; status: proved).** Let $d_0,\dots,d_{n-1}$ be real numbers with $d_{n-k}=d_k$ for $1\le k\le n-1$, and put $P_0=\sum_{0\le s\le n-1,\ s \text{ even}}d_s$ and $P_1=\sum_{0\le s\le n-1,\ s \text{ odd}}d_s$. Then for $0\le k\le n-1$:

```math
T_{n-1-k}+T_{k-1}=\begin{cases}D,& n \text{ odd};\\ 2P_1,& n \text{ even},\ k \text{ even};\\ 2P_0,& n \text{ even},\ k \text{ odd}.\end{cases}
```

*Proof.* Let $g:\mathbb Z\to\mathbb R$ be the $n$-periodic function with $g(s)=d_s$ for $0\le s\le n-1$. For $1\le s\le n-1$ we have $g(-s)=g(n-s)=d_{n-s}=d_s$ by the hypothesis. Hence $g(s)=d_{\lvert s\rvert}$ for all $\lvert s\rvert\le n-1$, and by (1.2), $T_m=\sum_{s\in S(m)}g(s)$ for $0\le m\le n-1$.

Fix $0\le k\le n-1$. The set $S(n-1-k)$ consists of the $n-k$ integers $k+1-n+2j$, $0\le j\le n-1-k$. If $k\ge1$, the set $S(k-1)$ consists of the $k$ integers $1-k+2i$, $0\le i\le k-1$; by periodicity $g(1-k+2i)=g(n+1-k+2i)$, and $n+1-k+2i=k+1-n+2j$ for $j=n-k+i$, which runs through $n-k,\dots,n-1$. Therefore (also for $k=0$, where $T_{-1}=0$ and $j$ already runs through $0,\dots,n-1$)

```math
T_{n-1-k}+T_{k-1}=\sum_{j=0}^{n-1}g(k+1-n+2j).
```

If $n$ is odd, $2$ is invertible modulo $n$, so $j\mapsto k+1-n+2j$ is a bijection of $\mathbb Z/n$, and the sum is $\sum_{s=0}^{n-1}g(s)=D$. If $n$ is even, the terms for $j$ and $j+n/2$ are equal, and for $0\le j\le n/2-1$ the residues of $k+1-n+2j$ modulo $n$ are pairwise distinct (the numbers $2j$ are distinct in $\lbrace 0,2,\dots,n-2\rbrace$) and all congruent to $k+1$ modulo 2; since exactly $n/2$ residues modulo $n$ have that parity, they are all of them. So the sum is $2\sum_{0\le s\le n-1,\ s\equiv k+1\ (\mathrm{mod}\ 2)}d_s$, which is $2P_1$ for even $k$ and $2P_0$ for odd $k$. $\square$

**Lemma 9 (sector $A_1$; status: proved).** $\ker\bigl((M-nI)\vert_{V_{A1}}\bigr)=0$.

*Proof.* Let $v=(r,r,d,d)\in V_{A1}$ ($r$ palindromic, $d$ even, coordinates $d_0,\dots,d_{n-1}$) with $(M-nI)v=0$. By (4.1) and Remark 4.5 this means

```math
(\mathrm{row}_i)\quad R+2\sum_{k'=i-n+1}^{i}d_{\lvert k'\rvert}=0\quad(0\le i\le n-1),\qquad(\mathrm{diag}_k)\quad -k d_k+2\rho_k+T_{n-1-k}=0\quad(0\le k\le n-1).
```

*(A.1)* For $1\le i\le n-1$, subtracting $(\mathrm{row}_{i-1})$ from $(\mathrm{row}_i)$ gives $2(d_{\lvert i\rvert}-d_{\lvert i-n\rvert})=2(d_i-d_{n-i})=0$. So $d_{n-k}=d_k$ for $1\le k\le n-1$, and Lemma 8 applies to $d_0,\dots,d_{n-1}$.

*(A.2)* $(\mathrm{row}_0)$ reads $R+2\sum_{k'=-(n-1)}^{0}d_{\lvert k'\rvert}=R+2D=0$.

*(A.3)* Since $r$ is palindromic, for $0\le k\le n$: $\rho_{n-k}=\sum_{i\ge n-k}r_i=\sum_{i\ge n-k}r_{n-1-i}=\sum_{j=0}^{k-1}r_j=R-\rho_k$.

*(A.4)* For $1\le k\le n-1$, add $(\mathrm{diag}_k)$ and $(\mathrm{diag}_{n-k})$ and use (A.1), (A.3):

```math
0=-k d_k-(n-k) d_{n-k}+2(\rho_k+\rho_{n-k})+T_{n-1-k}+T_{k-1}=-n d_k+2R+T_{n-1-k}+T_{k-1}.
```

*(A.5)* $(\mathrm{diag}_0)$ reads $2\rho_0+T_{n-1}=2R+T_{n-1}=0$.

*Case $n$ odd.* By Lemma 8, (A.4) becomes $n d_k=2R+D$ for $1\le k\le n-1$, and (A.5) becomes $2R+D=0$ (Lemma 8 with $k=0$). Hence $d_k=0$ for $1\le k\le n-1$, so $D=d_0$, and (A.2), (A.5) form the system

```math
\begin{pmatrix}1&2\\2&1\end{pmatrix}\begin{pmatrix}R\\D\end{pmatrix}=0,\qquad\det\begin{pmatrix}1&2\\2&1\end{pmatrix}=1\cdot1-2\cdot2=-3\ne0 .
```

So $R=D=0$, hence $d_0=0$ and $d=0$.

*Case $n$ even.* By Lemma 8, (A.4) becomes $n d_k=2R+2P_1$ for even $k$ and $n d_k=2R+2P_0$ for odd $k$ ($1\le k\le n-1$), and (A.5) becomes $2R+2P_1=0$. Hence:

- $d_k=0$ for every even $k$ with $2\le k\le n-2$; therefore $P_0=d_0$.
- All $d_k$ with $k$ odd are equal to one number $\beta$, where $n\beta=2R+2d_0$; there are $n/2$ odd indices in $[1,n-1]$, so $P_1=\frac n2\beta$ and $D=P_0+P_1=d_0+\frac n2\beta$.

So $(d_0,\beta,R)$ satisfies: $2d_0-n\beta+2R=0$ (the relation for odd $k$); $n\beta+2R=0$ (from (A.5)); $2d_0+n\beta+R=0$ (from (A.2)). Solving by hand: the second gives $R=-\frac n2\beta$; the first then gives $2d_0=n\beta-2R=2n\beta$; the third then gives $2n\beta+n\beta-\frac n2\beta=\frac52n\beta=0$. So $\beta=0$, $R=0$, $d_0=0$, and $d=0$. Equivalently, the coefficient matrix is nonsingular:

```math
\det\begin{pmatrix}2&-n&2\\0&n&2\\2&n&1\end{pmatrix}=2(n\cdot1-2\cdot n)-(-n)(0\cdot1-2\cdot2)+2(0\cdot n-n\cdot2)=-2n-4n-4n=-10n\ne0 .
```

*Conclusion, both cases.* We have $d=0$ and $R=0$. Then $(\mathrm{diag}_k)$ gives $2\rho_k=k d_k-T_{n-1-k}=0$ for $0\le k\le n-1$, and $\rho_n=0$, so $r_i=\rho_i-\rho_{i+1}=0$ for all $i$. Hence $v=0$. $\square$

*Remark (an equivalent normalization; not needed for the proof; status: proved).* The exact check `scripts/p2_proofcheck.py a1` replays this proof with slightly different final systems; their determinants can also be checked by hand. For $n$ odd: unknowns $(R,D)$, rows $(\frac12,1)$ and $(2,1)$, determinant $\frac12-2=-\frac32$. For $n$ even: before using $d_k=0$ for even $k\ge2$, call the common value of those $d_k$ $\alpha$ (so $P_0=d_0+(\frac n2-1)\alpha$); the four relations $n\alpha=2R+n\beta$, $n\beta=2R+2d_0+(n-2)\alpha$, $D+\frac R2=0$, $2R+n\beta=0$ have, in the unknowns $(d_0,\alpha,\beta,R)$, the matrix

```math
\begin{pmatrix}0&n&-n&-2\\-2&-(n-2)&n&-2\\1&\frac n2-1&\frac n2&\frac12\\0&0&n&2\end{pmatrix}.
```

Adding the fourth row to the first turns the first row into $(0,n,0,0)$; expanding along it, the determinant is $-n$ times the determinant of the matrix with rows $(-2,n,-2)$, $(1,\frac n2,\frac12)$, $(0,n,2)$, which is $-2(n-\frac n2)-n\cdot2+(-2)\cdot n=-5n$. So the determinant is $5n^2\ne0$.

## 7. The sector $B_2$ at $\mu=n$

**Lemma 10 (weighted means; status: proved).** Let $I$ be a finite set, $j_0\in I$, and $(e_j)_{j\in I}$ real numbers. Suppose that for every $j\in I$, $j\ne j_0$, there are $\alpha(j),\beta(j)\in I$ and a real number $\lambda_j$ with $0\lt \lambda_j\le1$ such that

```math
e_j=\lambda_j e_{\alpha(j)}+(1-\lambda_j) e_{\beta(j)},
```

and that for every $j\in I$ the sequence $j,\ \alpha(j),\ \alpha(\alpha(j)),\dots$ reaches $j_0$ after finitely many steps. Then $e_j=e_{j_0}$ for all $j\in I$.

*Proof.* Let $m=\max_{j\in I}e_j$ and $Z=\lbrace j\in I:e_j=m\rbrace$, a nonempty set. If $j\in Z$ and $j\ne j_0$, then $m=e_j=\lambda_je_{\alpha(j)}+(1-\lambda_j)e_{\beta(j)}\le\lambda_je_{\alpha(j)}+(1-\lambda_j)m$, so $\lambda_j(m-e_{\alpha(j)})\le0$; since $\lambda_j\gt 0$ and $e_{\alpha(j)}\le m$, this forces $e_{\alpha(j)}=m$, i.e. $\alpha(j)\in Z$. Take any $j\in Z$ and follow the sequence $j,\alpha(j),\alpha(\alpha(j)),\dots$: every term before $j_0$ is reached lies in $Z$ and is different from $j_0$, so its successor lies in $Z$; since the sequence reaches $j_0$, we get $j_0\in Z$, i.e. $e_{j_0}=m$. The numbers $(-e_j)_{j\in I}$ satisfy the same hypotheses, so $-e_{j_0}=\max_j(-e_j)$, i.e. $e_{j_0}=\min_je_j$. Hence $\max=\min$ and all $e_j$ are equal. $\square$

**Setup.** Let $v=(0,0,d,-d)\in V_{B2}$ with coordinates $d_0,\dots,d_{n-1}$. By (4.3) and Remark 4.5, $(M-nI)v=0$ if and only if

```math
\mathrm{Eq}(k):\qquad k d_k+T_{n-1-k}=0\qquad(0\le k\le n-1).\qquad\text{(7.1)}
```

Introduce $e_0=d_0$, $e_k=2d_k$ for $1\le k\le n-1$, and the conventions $e_n=e_{n+1}=0$. By the remark after (1.2) ($T_m=d_0+2(d_2+\dots+d_m)$ for even $m$, $T_m=2(d_1+d_3+\dots+d_m)$ for odd $m$), $T_m=\sum_{0\le j\le m,\ j\equiv m\ (\mathrm{mod}\ 2)}e_j$ for $0\le m\le n-1$, so

```math
\mathrm{Eq}(k)=\frac k2 e_k+\sum_{\substack{0\le j\le n-1-k\\ j\equiv n-1-k\ (\mathrm{mod}\ 2)}}e_j\qquad(0\le k\le n-1)\qquad\text{(7.2)}
```

(for $k=0$ the first term is $0=0\cdot d_0$; for $k\ge1$ it is $k d_k$). Define, for $0\le k\le n-1$,

```math
F_k=k e_k-(k+2) e_{k+2}+2 e_{n-1-k}.\qquad\text{(7.3)}
```

**Lemma 11 (status: proved).** With $\mathrm{Eq}(n)=\mathrm{Eq}(n+1)=0$ by convention, $F_k=2 \mathrm{Eq}(k)-2 \mathrm{Eq}(k+2)$ for $0\le k\le n-1$, and $\mathrm{Eq}(k)=\frac12\sum_{i\ge0,\ k+2i\le n-1}F_{k+2i}$. Hence the systems $\lbrace\mathrm{Eq}(k)=0,\ 0\le k\le n-1\rbrace$ and $\lbrace F_k=0,\ 0\le k\le n-1\rbrace$ have the same solutions.

*Proof.* For $0\le k\le n-3$: in (7.2) the sums for $\mathrm{Eq}(k)$ and $\mathrm{Eq}(k+2)$ run over the $j$ of one and the same parity up to $n-1-k$ and up to $n-3-k$ respectively, so they differ by the single term $e_{n-1-k}$; hence $2\mathrm{Eq}(k)-2\mathrm{Eq}(k+2)=k e_k-(k+2)e_{k+2}+2e_{n-1-k}=F_k$. For $k=n-2$: $\mathrm{Eq}(n-2)=\frac{n-2}2e_{n-2}+e_1$, and $F_{n-2}=(n-2)e_{n-2}-n e_n+2e_1=(n-2)e_{n-2}+2e_1$. For $k=n-1$: $\mathrm{Eq}(n-1)=\frac{n-1}2e_{n-1}+e_0$, and $F_{n-1}=(n-1)e_{n-1}-(n+1)e_{n+1}+2e_0=(n-1)e_{n-1}+2e_0$. The second formula follows by telescoping. $\square$

Two consequences of (7.3) are used below:

```math
F_0=0\iff e_2=e_{n-1};\qquad\qquad F_k=0\iff e_{k+2}=\frac{k}{k+2} e_k+\frac{2}{k+2} e_{n-1-k}\quad(1\le k\le n-3).\qquad\text{(7.4)}
```

**Lemma 12 (sector $B_2$; status: proved).**
(a) If $n$ is even, $\ker\bigl((M-nI)\vert_{V_{B2}}\bigr)=0$.
(b) If $n$ is odd, $\ker\bigl((M-nI)\vert_{V_{B2}}\bigr)$ has dimension 1; it is spanned by $(0,0,d^{\circ},-d^{\circ})$, where $d^{\circ}$ is the even vector with $d^{\circ}_0=n-1$, $d^{\circ}_k=-1$ for even $k$ with $2\le k\le n-1$, and $d^{\circ}_k=0$ for odd $k$.

*Proof.* By (7.1) and Lemma 11, $v\in\ker((M-nI)\vert_{V_{B2}})$ if and only if $F_k=0$ for $0\le k\le n-1$. Let $e$ be such a solution. The idea is to apply Lemma 10 to the relations (7.4), which express most $e_j$ as weighted means of two others.

(a) *$n$ even.* Apply Lemma 10 with $I=\lbrace 1,2,\dots,n-1\rbrace$ and $j_0=1$:

- for $j=2$: $e_2=e_{n-1}$ by (7.4) ($F_0=0$); take $\alpha(2)=\beta(2)=n-1$, $\lambda_2=1$;
- for $3\le j\le n-1$: (7.4) with $k=j-2\in[1,n-3]$ gives $e_j=\frac{j-2}{j}e_{j-2}+\frac2je_{n+1-j}$; take $\alpha(j)=j-2$, $\beta(j)=n+1-j\in[2,n-2]\subseteq I$, $\lambda_j=\frac{j-2}j\in(0,1)$.

The sequence $j,\alpha(j),\dots$ reaches 1: from an odd $j$ it descends $j,j-2,\dots,1$; from an even $j$ it descends $j,j-2,\dots,2$, then goes to $n-1$, which is odd because $n$ is even, and descends $n-1,n-3,\dots,1$. Hence $e_1=e_2=\dots=e_{n-1}=:c$. Now $F_{n-2}=(n-2)e_{n-2}+2e_1=nc$, so $c=0$; and $F_{n-1}=(n-1)e_{n-1}+2e_0=2e_0$, so $e_0=0$. Thus $e=0$, i.e. $d=0$ and $v=0$.

(b) *$n$ odd* (so $n\ge5$). Since $n-1-k\equiv k$ modulo 2, each $F_k$ involves only the $e_j$ with $j\equiv k$ modulo 2.

*Even indices.* Apply Lemma 10 with $I=\lbrace 2,4,\dots,n-1\rbrace$, $j_0=2$: for even $j$ with $4\le j\le n-1$, (7.4) with $k=j-2$ (even, $2\le k\le n-3$) gives $e_j=\frac{j-2}je_{j-2}+\frac2je_{n+1-j}$, where $n+1-j$ is even and lies in $[2,n-3]\subseteq I$; take $\alpha(j)=j-2$, $\beta(j)=n+1-j$, $\lambda_j=\frac{j-2}{j}\in(0,1)$. The sequence $j,j-2,\dots$ reaches 2. Hence $e_2=e_4=\dots=e_{n-1}=:c$. Then $F_{n-1}=(n-1)c+2e_0=0$ gives $e_0=-\frac{n-1}2c$.

*Odd indices.* Apply Lemma 10 with $I=\lbrace 3,5,\dots,n-2\rbrace$, $j_0=3$ (for $n=5$, $I=\lbrace 3\rbrace$ and there is nothing to do): for odd $j$ with $5\le j\le n-2$, (7.4) with $k=j-2$ (odd, $3\le k\le n-4$) gives $e_j=\frac{j-2}je_{j-2}+\frac2je_{n+1-j}$, where $n+1-j$ is odd and lies in $[3,n-4]\subseteq I$; take $\alpha(j)=j-2$, $\beta(j)=n+1-j$, $\lambda_j=\frac{j-2}j\in(0,1)$. The sequence $j,j-2,\dots$ reaches 3. Hence $e_3=e_5=\dots=e_{n-2}=:c'$. Then $F_{n-2}=(n-2)e_{n-2}+2e_1=(n-2)c'+2e_1=0$ gives $e_1=-\frac{n-2}2c'$, and (the indices $3$ and $n-2$ are in $I$)

```math
F_1=e_1-3e_3+2e_{n-2}=-\frac{n-2}{2}c'-3c'+2c'=-\frac n2 c' .
```

So $c'=0$, and $e_j=0$ for every odd $j$.

Therefore every solution is $e=-\frac c2(n-1,0,-2,0,-2,\dots,0,-2)$, that is, $d=-\frac c2d^{\circ}$. So the kernel has dimension at most 1. Conversely $d^{\circ}$ satisfies (7.1), by direct substitution: for odd $k$, $k d^{\circ}_k=0$ and $T_{n-1-k}=2(d^{\circ}_1+d^{\circ}_3+\dots+d^{\circ}_{n-1-k})=0$ ($n-1-k$ is odd); for $k=0$, $T_{n-1}=d^{\circ}_0+2(d^{\circ}_2+\dots+d^{\circ}_{n-1})=(n-1)-2\cdot\frac{n-1}2=0$; for even $k=2i\ge2$, $k d^{\circ}_k+T_{n-1-k}=-2i+(n-1)-2\bigl(\frac{n-1}2-i\bigr)=0$. Since $d^{\circ}\ne0$, the kernel has dimension exactly 1. $\square$

## 8. Proof of the Theorem, and the eigenspace

**Proof of the Theorem (status: proved).** Let $n\ge4$. By Lemma 2 the multiplicity of $n-4$ is $\dim\ker(M-nI)$. By Lemma 4(d) with $\mu=n$, and Lemmas 9, 6, 12 and 7 for the four terms:

```math
\dim\ker(M-nI)=\underbrace{0}_{A_1}+\underbrace{\lceil n/2\rceil-1}_{B_1}+\underbrace{[n \text{ odd}]}_{B_2}+2\cdot\underbrace{0}_{E}.
```

For $n$ even this is $\frac n2-1=\frac{n-2}2$. For $n$ odd this is $\frac{n+1}2-1+1=\frac{n+1}2$. Both numbers are at least 1 for $n\ge4$, so $n-4$ is an eigenvalue. $\square$

**Corollary 13 (the eigenspace; status: proposed; the description is due to Cardoso, Costa and Duarte, see the remark below).** For $n\ge4$ the eigenspace of $\mathbf A$ for the eigenvalue $n-4$ consists of the functions

```math
x(i,j)=r_i-r_j+\gamma \bigl([i=j]-[i+j=n-1]\bigr),
```

with $r\in\mathbb R^n$ palindromic and $\gamma\in\mathbb R$, where $\gamma=0$ if $n$ is even.

*Proof.* By Lemma 2 the eigenspace is $N\ker(M-nI)$. By the proof of Lemma 4(d), $\ker(M-nI)$ is the direct sum of the kernels of $M-nI$ on the five sectors; those on $V_{A1}$, $V_E$ and $V_{E'}$ are zero (Lemmas 9 and 7, and Lemma 4(c) for $V_{E'}$). So, by Lemmas 6 and 12, $\ker(M-nI)$ is spanned by the vectors $(r,-r,0,0)$ with $r$ palindromic and $\sum_ir_i=0$, together with $(0,0,d^{\circ},-d^{\circ})$ when $n$ is odd. By (1.1), $N(r,-r,0,0)(i,j)=r_i-r_j$; this expression does not change when a constant is added to $r$, so the restriction $\sum_ir_i=0$ can be dropped. For $n$ odd, $N(0,0,d^{\circ},-d^{\circ})(i,j)=d^{\circ}_{\lvert i-j\rvert}-d^{\circ}_{\lvert i+j-(n-1)\rvert}$. Here $i-j$ and $i+j-(n-1)$ have the same parity because $n-1$ is even. If both are odd, the value is $0-0=0$. If both are even: the value is $(n-1)-(-1)=n$ when $i=j$ and $i+j\ne n-1$; $(-1)-(n-1)=-n$ when $i\ne j$ and $i+j=n-1$; $0$ when both are zero or both nonzero. So $N(0,0,d^{\circ},-d^{\circ})=n\bigl([i=j]-[i+j=n-1]\bigr)$. $\square$

*Remark (relation to the known eigenvectors; credit; not a step of the proof).* Cardoso, Costa and Duarte proved that the multiplicity is **at least** the value in the Theorem, with explicit eigenvectors. They did so first in [arXiv:2012.01992](https://arxiv.org/abs/2012.01992) (v1, 2020-12-03; abstract and Theorem 3.10, stated for $n\ge3$). There the eigenvectors form two sets: $Y^n$, whose vectors are $C_i+C_{n+1-i}-R_i-R_{n+1-i}$ (indicators of two columns minus indicators of the same two rows, squares indexed from 1), and, for odd $n$, $Z^n$, the single vector $D_0-S_{n+1}$ (indicator of the main diagonal minus indicator of the antidiagonal). As printed, the set $Y^n$ has $\lceil n/2\rceil$ vectors with one linear relation, and the proof uses $\lceil n/2\rceil-1$ of them, together with $Z^n$ for odd $n$, as linearly independent eigenvectors. They restated the result in [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) (Theorem 4.1 and Corollary 4.2) with vectors $F_{n,\ell}$ and $E_{n,n-4}$.

In the notation above, the vectors of $Y^n$ and the $F_{n,\ell}$ ($1\le\ell\le\lceil n/2\rceil-1$; indicator of columns $\ell$ and $n+1-\ell$ minus indicator of rows $\ell$ and $n+1-\ell$) are $x(i,j)=r_i-r_j$ with $r=-[i\in\lbrace\ell-1,n-\ell\rbrace]$, a palindromic $r$. So the first summand of Corollary 13 is the span of these vectors. The vector of $Z^n$ is $[i=j]-[i+j=n-1]$ in our 0-indexed coordinates, the $\gamma$-term of Corollary 13. The vector $E_{n,n-4}=P_{n,n-4}+Q_{n,n-4}$ of the later paper (§3 there, $k=(\lambda+4)-\frac{n-1}2$ with $\lambda=n-4$, so $k=\frac{n+1}2$) has as its only nonzero entries $k$ on the main diagonal and $-k$ on the antidiagonal, so with indices from 1

```math
E_{n,n-4}=\tfrac{n+1}{2}\bigl([i=j]-[i+j=n+1]\bigr),
```

which in the 0-indexed coordinates of this file is $\frac{n+1}2\bigl([i=j]-[i+j=n-1]\bigr)$: again a nonzero multiple of the $\gamma$-term. Hence their eigenvectors span the whole space described in Corollary 13. They proved that these vectors are eigenvectors, so the number of linearly independent ones, $\frac{n-2}2$ resp. $\frac{n+1}2$, is a lower bound on the multiplicity; the Theorem above shows the multiplicity is no larger, so their eigenvectors span the eigenspace. **The whole description of the eigenspace in Corollary 13 is due to Cardoso, Costa and Duarte.** The exact value, equivalently the upper bound (the Theorem), is conjectured but not proved in their papers ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992) Conj. 3; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) Conj. 1; [arXiv:2508.01088](https://arxiv.org/abs/2508.01088) Conj. 4.1); whether a proof of it, or the method used here, appears elsewhere has not been checked beyond the priority search of 2026-11-27. The proof of Corollary 13 above derives the same eigenspace from the sector decomposition, without using their theorem; this gives no new credit.

The identification was made on 2026-11-27 from automated renderings of the two papers ([ar5iv of arXiv:2012.01992](https://ar5iv.labs.arxiv.org/html/2012.01992), [HTML of arXiv:2301.08106v2](https://arxiv.org/html/2301.08106v2)), not line by line against the PDFs; in particular the theorem number 3.10 is taken from the ar5iv rendering. Our referees confirmed the identification by exact computation (for the later paper's vectors: $4\le n\le16$ and $4\le n\le26$; status: numerical). It was then confirmed against the PDF text layer (final gate, 2026-11-27); the rendered PDF pages have not been viewed.

## 9. Smallest cases, checked by hand

Each lemma is checked here at its smallest $n$ (4 for the even case, 5 for the odd case). These hand checks are illustrations; the proof does not use them (status: proved). The same checks are replayed by `python scripts/prover_check.py small` (archived output [`scripts/logs/small_4_5.log`](scripts/logs/small_4_5.log); status of that replay: numerical).

**Dimensions (Lemma 4).** $n=4$: $6+2+4+2\cdot5=22=6\cdot4-2$. $n=5$: $8+3+5+2\cdot6=28=6\cdot5-2$.

**Lemma 6.** $n=4$: palindromic $r=(r_0,r_1,r_1,r_0)$ with $2r_0+2r_1=0$: dimension $1=\lceil4/2\rceil-1$. $n=5$: $r=(r_0,r_1,r_2,r_1,r_0)$ with $2r_0+2r_1+r_2=0$: dimension $2$.

**Lemma 7, $n=4$.** $r=(r_0,r_1,-r_1,-r_0)$: $\rho_0=0$, $\rho_1=-r_0$, $\rho_2=-r_0-r_1$, $\rho_3=-r_0=\rho_1$. (E3): $d_1=\rho_1$, $d_2=\rho_2/2$, $d_3=\rho_1/3$. (E1): $d_1+d_3=\frac43\rho_1=0$ and $2d_2=\rho_2=0$. So $r=0$, $d=0$.

**Lemma 9, $n=4$.** $r=(r_0,r_1,r_1,r_0)$, $R=2r_0+2r_1$. (A.1): the rows give $d_3=d_1=:\beta$. (A.5): $2R+T_3=2R+2(d_1+d_3)=2R+4\beta=0$. (A.4) with $k=2$: $4d_2=2R+T_1+T_1=2R+4\beta=0$, so $d_2=0$. (A.4) with $k=1$: $4\beta=2R+T_2+T_0=2R+2d_0+2d_2=2R+2d_0$, so with $R=-2\beta$: $d_0=4\beta$. (A.2): $R+2D=-2\beta+2(4\beta+2\beta)=10\beta=0$. This is $\frac52n\beta=0$ with $n=4$. So $d=0$, $R=0$; then $(\mathrm{diag}_3)$: $-3d_3+2\rho_3+T_0=2r_0=0$, and $r=0$.

**Lemma 9, $n=5$.** (A.1): $d_4=d_1$, $d_3=d_2$. (A.5): $2R+T_4=2R+d_0+2d_2+2d_4=2R+D$. (A.4): $5d_k=2R+D=0$ for $1\le k\le4$. So $D=d_0$, and $R+2d_0=0$, $2R+d_0=0$ give $R=d_0=0$.

**Lemma 12, $n=4$.** The system (7.3) is

```math
F_0=-2e_2+2e_3,\qquad F_1=e_1+2e_2-3e_3,\qquad F_2=2e_1+2e_2,\qquad F_3=2e_0+3e_3 .
```

$F_0=F_1=0$ give $e_2=e_3$ and $e_1=e_3$ (Lemma 10 with $I=\lbrace1,2,3\rbrace$); then $F_2=4e_3=0$ (this is $nc$) and $F_3$ gives $e_0=0$. Kernel $0$.

**Lemma 12, $n=5$.** The system (7.3) is

```math
F_0=-2e_2+2e_4,\qquad F_1=e_1-e_3,\qquad F_2=4e_2-4e_4,\qquad F_3=2e_1+3e_3,\qquad F_4=2e_0+4e_4 .
```

Even indices: $e_2=e_4=c$, $e_0=-2c$. Odd indices: $F_3$ gives $e_1=-\frac32e_3$, then $F_1=-\frac52e_3$ (this is $-\frac n2c'$), so $e_1=e_3=0$. Kernel: $e=-\frac c2(4,0,-2,0,-2)$, i.e. $d^{\circ}=(4,0,-1,0,-1)$. Dimension 1.

**Theorem.** $n=4$: $0+1+0+0=1=\frac{4-2}2$. $n=5$: $0+2+1+0=3=\frac{5+1}2$. Both agree with the nullity of $\mathbf A-(n-4)I$ computed directly on the $16\times16$ and $25\times25$ adjacency matrices ([`scripts/logs/adjacency_4_12.log`](scripts/logs/adjacency_4_12.log): 1 and 3; status: numerical).

## 10. Table of lemmas and steps

"Complete" means: a full argument is written in this file. Evidence paths are relative to this folder. The computer checks are exact (integers and rationals); they corroborate, they are not part of the proof.

| Step | Statement (short) | Status | Complete | Corroboration (not used by the proof) |
| --- | --- | --- | --- | --- |
| Lemma 1 | two squares share at most one line; $NN^T=\mathbf A+4I$ | proved | yes | `scripts/logs/replay_4_40.log`, column `reduction` ($4\le n\le24$) |
| Lemma 2 | multiplicity of $n-4$ equals $\dim\ker(M-nI)$ | proved | yes | — |
| Lemma 3 | relations among $t,h,z$; they commute with $M$ | proved | yes | `replay_4_40.log`, column `symmetry` ($4\le n\le40$) |
| Lemma 4 | explicit sectors, five-sector decomposition, kernel count formula | proved | yes | `replay_4_40.log`, column `symmetry`; `scripts/logs/proofcheck_sectors_4_40.log` |
| Lemma 5, Remark 4.5 | action of $M$ on the sectors, (4.0a)–(4.4) | proved | yes | `replay_4_40.log`, column `actions`; `proofcheck_sectors_4_40.log` |
| Lemma 6 | $B_1$: kernel dimension $\lceil n/2\rceil-1$ | proved | yes | `replay_4_40.log`, column `B1` |
| Lemma 7 | $E$: kernel $0$ | proved | yes | `replay_4_40.log`, column `E`; `scripts/logs/proofcheck_e_4_40.log` |
| Lemma 8 | window identity | proved | yes | `replay_4_40.log`, column `A` |
| Lemma 9 | $A_1$: kernel $0$ | proved | yes | `replay_4_40.log`, column `A`; `scripts/logs/proofcheck_a1_4_40.log` |
| Lemma 10 | weighted-means lemma | proved | yes | — |
| Lemma 11 | equivalence of the systems Eq and $F$ | proved | yes | `replay_4_40.log`, column `B` |
| Lemma 12 | $B_2$: kernel $0$ ($n$ even), dimension 1 ($n$ odd) | proved | yes | `replay_4_40.log`, column `B`; `scripts/logs/proofcheck_b2_4_40.log` |
| Theorem | multiplicity of $n-4$ is $\frac{n-2}2$ or $\frac{n+1}2$, all $n\ge4$ | formalized; proved | yes | Lean: [`lean/Pipeline/QueensSpectrum/Main.lean`](lean/Pipeline/QueensSpectrum/Main.lean) (`queens_mult`, `queens_alg_mult`), see [`LEAN.md`](LEAN.md); computer checks: §11 |
| Corollary 13 | explicit eigenspace (description due to Cardoso, Costa and Duarte) | proposed | yes | `replay_4_40.log`, column `eigvec` ($4\le n\le16$); `scripts/logs/adjacency_4_12.log` |
| Appendix A.1 | even $n$: explicit solution of a recurrence (alternative proof, not used) | proved | yes | `replay_4_40.log`, column `appx`; `proofcheck_b2_4_40.log` |
| Appendix A.2, Lemma G | odd $n$: block form; $G_q$ positive semidefinite of rank $q$ (alternative proof, not used) | proved | yes | `replay_4_40.log`, last lines ($1\le q\le60$); `scripts/logs/proofcheck_g_1_80.log` ($1\le q\le80$) |
| Theorem for $4\le n\le40$ | $\dim\ker(M-nI)$ by exact rank | numerical (exact arithmetic, two implementations); no certificate archived yet | n/a | `scripts/logs/fullflint_4_40.log`, `fraction_4_16.log`, `fraction_17_40.log`, `sectors_flint_4_40.log` |
| Theorem for $4\le n\le40$, third check | rank modulo a prime plus explicit kernel vectors | numerical | n/a | `replay_4_40.log`, column `total` |
| Theorem for $41\le n\le150$ | exact rank of the sector matrices, one implementation | numerical | n/a | `scripts/logs/sectors_flint_41_150.log` |
| Adjacency-level check, $4\le n\le12$ | nullity of $\mathbf A-(n-4)I$ on the $n^2\times n^2$ matrix | numerical | n/a | `scripts/logs/adjacency_4_12.log` |

No step is `heuristic` or `certified`, and no `numerical` row is used in the proof of the Theorem.

## 11. Computer checks (corroboration only)

**Nothing in the proof needs a computer:** there is no computational step, no numerical constant, no threshold and no tolerance. The checks below confirm the Theorem and its steps for finitely many $n$. All use exact integer or rational arithmetic. None has yet been archived as a certificate in our sense (an independent second implementation rerun from a clean copy, with its output archived). Exact commands, versions and runtimes are in [`REPRODUCE.md`](REPRODUCE.md).

1. **The Theorem for $4\le n\le40$, two rank algorithms.** For each $n$, the integer matrix $M-nI$ of size $6n-2$ is built square by square from the board (function `gram` in `scripts/p2_verify.py`, which uses no symmetry). Its rank over $\mathbb Q$ is computed twice: by FLINT's exact integer rank (`fmpz_mat.rank`, python-flint 0.7.1; `fullflint_4_40.log`) and by pure-Python fraction-free (Bareiss) elimination (`fraction_4_16.log`, `fraction_17_40.log`). Both give nullity $\frac{n-2}2$ ($n$ even) and $\frac{n+1}2$ ($n$ odd) for every $n$ in the range. The two runs share the routine that builds $M$; they differ in the rank algorithm.
2. **The Theorem by sectors.** The sector matrices are written from formulas (4.1)–(4.4) and their nullities at $\mu=n$ computed with FLINT: $A_1$: 0, $B_1$: $\lceil n/2\rceil-1$, $B_2$: $[n\text{ odd}]$, $E$: 0, for $4\le n\le40$ (`sectors_flint_4_40.log`) and $41\le n\le150$ (`sectors_flint_41_150.log`, one implementation only).
3. **A separate replay of every identity of this file**, `scripts/prover_check.py 4 40` (pure Python, no third-party library; `replay_4_40.log`, last line `PROVER REPLAY: ALL PASS`). It rebuilds everything from the board. For each $n$ it checks: Lemma 1 ($n\le24$); the table and relations of Lemma 3 and commutation with $M$ on every basis vector; the sector bases, their dimensions and that together they form a basis; formulas (4.1)–(4.4) on every sector basis vector; the identities (E1), (E2), (A.1)–(A.5) and Lemma 8 as identities of linear forms; the determinants $-3$, $-10n$, $5n^2$; formula (7.2) and Lemma 11; the conclusions of the three uses of Lemma 10 (exact null spaces of the subsystems); $F_{n-2}=nc$ and $F_1=-\frac n2c'$; the kernel vector $d^{\circ}$; $\dim\ker(M-nI)$ on the whole line space (rank modulo the prime $2^{31}-1$, which bounds the nullity from above, plus explicit kernel vectors, which bound it from below); Corollary 13 on the adjacency matrix ($n\le16$); Appendix A ($q\le60$).
4. **The adjacency matrix directly**, $4\le n\le12$: nullity of $\mathbf A-(n-4)I$ on the $n^2\times n^2$ matrix (FLINT exact rank), and the vectors of Corollary 13 lie in the kernel with full rank (`adjacency_4_12.log`).
5. **Step-by-step checks from the board**, $4\le n\le40$, by a third script, `scripts/p2_proofcheck.py`, written independently of the other two (pure Python; sympy 1.14.0 only for the symbolic determinants): the sector formulas (`proofcheck_sectors_4_40.log`); the steps of Lemma 9 (`proofcheck_a1_4_40.log`); the steps of Lemma 7 (`proofcheck_e_4_40.log`); the kernel of the $B_2$ sector and Appendix A (`proofcheck_b2_4_40.log`); the pivots of $G_q$ for $1\le q\le80$ (`proofcheck_g_1_80.log`); the reduced determinants $-\frac32$ and $5n^2$ of the remark after Lemma 9 (`proofcheck_symbolic.log`).

## 12. Sources and credit (no novelty claimed beyond what is stated here)

- **The conjecture** is due to D. M. Cardoso, I. S. Costa and R. Duarte: [arXiv:2012.01992](https://arxiv.org/abs/2012.01992) (Conjecture 3), [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) (Conjecture 1; Discrete Math. 347(9) (2024) 114065), [arXiv:2508.01088](https://arxiv.org/abs/2508.01088) (Conjecture 4.1). They report that their computations confirm the conjecture for $n\le100$ (method not stated). I. S. Costa's PhD thesis ([hdl:10773/41899](http://hdl.handle.net/10773/41899), Universidade de Aveiro, 2024) lists the conjecture as open.
- **The lower bound** "multiplicity at least $\frac{n-2}2$, resp. $\frac{n+1}2$", with explicit linearly independent eigenvectors, is due to the same authors. It first appeared in [arXiv:2012.01992](https://arxiv.org/abs/2012.01992) (v1, 2020-12-03; abstract and Theorem 3.10, eigenvector sets $Y^n$ and $Z^n$) and was restated in [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) (Theorem 4.1 and Corollary 4.2). **The explicit eigenspace (Corollary 13) is theirs in full** (remark after Corollary 13).
- **The least eigenvalue $-4$** and its multiplicity $(n-3)^2$ are theirs ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992), Theorem 3.8; [arXiv:2201.01224](https://arxiv.org/abs/2201.01224), J. Algebraic Combin. 58 (2023) 263–277). Lemma 1 (the partition of the edges into the cliques given by the lines, so $\mathbf A=NN^T-4I$) and Lemma 2 are standard facts about edge clique partitions and Gram matrices; they are proved here only to keep the file self-contained.
- **The exact value, equivalently the upper bound (the Theorem),** is conjectured but not proved in their papers ([arXiv:2012.01992](https://arxiv.org/abs/2012.01992) Conj. 3; [arXiv:2301.08106](https://arxiv.org/abs/2301.08106) Conj. 1; [arXiv:2508.01088](https://arxiv.org/abs/2508.01088) Conj. 4.1); whether a proof of it, or the method used here, appears elsewhere has not been checked beyond the priority search of 2026-11-27. That search ([`LITERATURE_CHECK.md`](LITERATURE_CHECK.md)) found no earlier proof or claim of this upper bound in the sources checked. Some sources could not be checked that day; they are listed there. This is a dated search result, not a priority claim.
- **Simplicial rook graphs** (Martin and Wagner, [arXiv:1209.3493](https://arxiv.org/abs/1209.3493); Brouwer, Cioabă, Haemers and Vermette, [arXiv:1408.5615](https://arxiv.org/abs/1408.5615)) were searched during the priority check; they are **not used** in this proof.

## 13. Limits of this file

- Part (a) of Conjecture 1 (no other integer eigenvalue) and part (c) (simplicity of the other listed integers) remain `open`. Conjecture 1 as a whole is **not** settled.
- Nothing is claimed for $n\le3$.
- The Lean formalization covers the Theorem (every $n\ge4$). It does not cover Corollary 13, Appendix A or the credit statements ([`LEAN.md`](LEAN.md)).
- Appendix A gives independent second proofs of Lemma 12. The Theorem does not depend on Appendix A.

## Appendix A. Alternative proofs of Lemma 12 (not used by the Theorem)

Notation as in §7: the system is $\mathrm{Eq}(k):\ k d_k+T_{n-1-k}=0$, $0\le k\le n-1$, and $e_0=d_0$, $e_k=2d_k$ ($k\ge1$).

### A.1 Even $n$: explicit solution of a recurrence (status: proved)

Let $n=2p$. Put $E_j=T_{2j}$ for $0\le j\le p-1$, and $Q_j=T_{2(p-1-j)+1}$ for $0\le j\le p-1$, $Q_p=0$. Since $T_0=d_0$, $T_1=2d_1$ and $T_m-T_{m-2}=2d_m$ for $2\le m\le n-1$, the numbers $(E_j)$, $(Q_j)$ determine $d$: $d_0=E_0$, $2d_{2i}=E_i-E_{i-1}$ ($1\le i\le p-1$), and $2d_{2i+1}=Q_{p-1-i}-Q_{p-i}$ ($0\le i\le p-1$; for $i=0$ this is $2d_1=T_1=Q_{p-1}-Q_p$). The equations become:

- $\mathrm{Eq}(0)$: $T_{2p-1}=Q_0=0$;
- $\mathrm{Eq}(2i)$, $1\le i\le p-1$: $2i d_{2i}+T_{2p-1-2i}=i(E_i-E_{i-1})+Q_i=0$, i.e. $E_i=E_{i-1}-\frac{Q_i}{i}$;
- $\mathrm{Eq}(2i+1)$, $0\le i\le p-1$, written with $j=p-1-i$: $(2i+1)d_{2i+1}+T_{2p-2-2i}=\frac{2p-1-2j}{2}(Q_j-Q_{j+1})+E_j=0$, i.e. $Q_{j+1}=Q_j+\frac{2E_j}{2p-1-2j}$ for $0\le j\le p-1$.

By induction on $j$, with $Q_0=0$: $E_j=E_0\frac{2p-1-2j}{2p-1}$ ($0\le j\le p-1$) and $Q_j=E_0\frac{2j}{2p-1}$ ($0\le j\le p$). Indeed, $Q_{j+1}=E_0\bigl(\frac{2j}{2p-1}+\frac{2}{2p-1}\bigr)$ and $E_{j+1}=E_0\bigl(\frac{2p-1-2j}{2p-1}-\frac{2}{2p-1}\bigr)$. The convention $Q_p=0$ then reads $E_0\frac{2p}{2p-1}=0$, so $E_0=0$, all $E_j$ and $Q_j$ vanish, and $d=0$. This is a second proof of Lemma 12(a). (In the variables of §7 the family found here is $e=\frac{E_0}{2p-1}(n-1,\ n-2,\ -2,\dots,-2)$, which satisfies every $F_k=0$ except $F_1$.)

### A.2 Odd $n$: block form and Lemma G (status: proved)

Let $n=2p+1$ ($p\ge2$). Put $u_l=e_{2l}$ ($0\le l\le p$) and $w_l=e_{2l+1}$ ($0\le l\le p-1$). By (7.2), for $0\le i\le p$ and $0\le i\le p-1$ respectively,

```math
\mathrm{Eq}(2i)=i u_i+\sum_{l=0}^{p-i}u_l=(G_pu)_i,\qquad \mathrm{Eq}(2i+1)=\frac{2i+1}{2} w_i+\sum_{l=0}^{p-1-i}w_l=\tfrac12\bigl((I+2G_{p-1})w\bigr)_i ,
```

where, for $q\ge0$, $G_q$ is the symmetric matrix of size $q+1$ with rows and columns indexed by $0,\dots,q$ and entries

```math
(G_q)_{ab}=a [a=b]+[a+b\le q].
```

**Lemma G (status: proved).** For $q\ge1$, $G_q$ is positive semidefinite of rank $q$; its kernel is spanned by $(q,-1,-1,\dots,-1)$.

*Proof.* We use the following fact. Let $X$ be a real symmetric matrix indexed by a finite set $J$, let $k\in J$ with $X_{kk}\ne0$, and let $X'$ be the matrix indexed by $J\setminus\lbrace k\rbrace$ with $X'_{ab}=X_{ab}-X_{ak}X_{kb}/X_{kk}$. Then $X$ is congruent to the block-diagonal matrix with blocks $X'$ and $(X_{kk})$ (subtract $X_{ak}/X_{kk}$ times row $k$ from row $a$, and the same for columns). Hence $\mathrm{rank} X=\mathrm{rank} X'+1$, and $X$ is positive semidefinite if and only if $X_{kk}\gt 0$ and $X'$ is positive semidefinite.

Let $m=\lfloor q/2\rfloor$. We eliminate the indices $q,q-1,\dots,1$ in this order and write $X^{(k)}$ for the matrix on $\lbrace0,\dots,k\rbrace$ obtained after eliminating $q,\dots,k+1$ (so $X^{(q)}=G_q$).

*Step 1: indices $q,\dots,m+1$.* Claim: for $m\le k\le q$ and $0\le a,b\le k$,

```math
X^{(k)}_{ab}=(G_q)_{ab}-\sum_{i=k+1}^{q}\frac{[a\le q-i] [b\le q-i]}{i}.
```

This holds for $k=q$. Suppose it holds for some $k\ge m+1$. For every $i\ge k+1$ we have $k+i\ge2m+3\gt q$, so $[k\le q-i]=0$ and row $k$ of $X^{(k)}$ equals row $k$ of $G_q$: $X^{(k)}_{kk}=k+[2k\le q]=k$ (as $2k\ge2m+2\gt q$) and $X^{(k)}_{ak}=[a\le q-k]$ for $a\lt k$. So the pivot is $k\gt 0$ and eliminating $k$ subtracts $[a\le q-k][b\le q-k]/k$, which gives the claim for $k-1$. For $k=m$ and $0\le a,b\le m$ we have $a+b\le2m\le q$, so $(G_q)_{ab}=a[a=b]+1$, and the claim reads

```math
X^{(m)}_{ab}=a [a=b]+c_{\max(a,b)},\qquad c_t=1-\sum_{i=m+1}^{q-t}\frac1i\quad(0\le t\le m),
```

where the sum is empty when $q-t\lt m+1$ (this happens only for $q=2m$, $t=m$).

*Step 2: indices $m,\dots,1$.* Put $\gamma_k=\frac{k}{q-k}$ for $0\le k\le m$ (note $q-k\ge q-m\ge1$). Claim: for $0\le k\le m$ and $0\le a,b\le k$,

```math
X^{(k)}_{ab}=a [a=b]+c_{\max(a,b)}-c_k+\gamma_k .
```

For $k=m$ this is Step 1 provided $c_m=\gamma_m$: if $q=2m$ then $c_m=1=\frac{m}{q-m}$; if $q=2m+1$ then $c_m=1-\frac1{m+1}=\frac m{m+1}=\frac{m}{q-m}$. Suppose the claim holds for some $k$ with $1\le k\le m$. Then $X^{(k)}_{kb}=\gamma_k$ for $b\lt k$ and the pivot is

```math
\pi_k=X^{(k)}_{kk}=k+\gamma_k=\frac{k(q+1-k)}{q-k}>0 .
```

Eliminating $k$ subtracts the constant $\gamma_k^2/\pi_k$ from every entry, so for $0\le a,b\le k-1$: $X^{(k-1)}_{ab}=a[a=b]+c_{\max(a,b)}-c_k+\gamma_k-\gamma_k^2/\pi_k$. Now $\gamma_k-\gamma_k^2/\pi_k=\gamma_k(\pi_k-\gamma_k)/\pi_k=k\gamma_k/\pi_k=\frac{k}{q+1-k}$, and $c_{k-1}-c_k=-\frac1{q+1-k}$ (the sum defining $c_{k-1}$ has the one extra term $i=q+1-k$, which is at least $m+1$ because $k\le m\le q-m$). Hence $-c_k+\frac k{q+1-k}=-c_{k-1}-\frac1{q+1-k}+\frac k{q+1-k}=-c_{k-1}+\frac{k-1}{q-(k-1)}=-c_{k-1}+\gamma_{k-1}$, which is the claim for $k-1$.

*Conclusion.* For $k=0$ the claim gives the $1\times1$ matrix $X^{(0)}=(c_0-c_0+\gamma_0)=(0)$. By the fact, applied $q$ times, $G_q$ is congruent to the diagonal matrix with entries $q,q-1,\dots,m+1,\pi_m,\dots,\pi_1,0$, of which the first $q$ are positive. So $G_q$ is positive semidefinite of rank $q$. Finally $\kappa=(q,-1,\dots,-1)$ is in the kernel: $(G_q\kappa)_0=q-q=0$, and for $1\le a\le q$, $(G_q\kappa)_a=-a+\bigl(q-(q-a)\bigr)=0$, since row $a$ of $([a+b\le q])$ has ones exactly in the columns $0,\dots,q-a$. $\square$

*Second proof of Lemma 12(b).* The system (7.1) is $G_pu=0$ together with $(I+2G_{p-1})w=0$. By Lemma G with $q=p\ge2$, $\ker G_p$ is spanned by $u=(p,-1,\dots,-1)$, i.e. $e_0=p$ and $e_{2l}=-1$ for $1\le l\le p$, i.e. $d_0=p$, $d_{2l}=-\frac12$, which is $\frac12d^{\circ}$ on the even indices. By Lemma G with $q=p-1\ge1$, $G_{p-1}$ is positive semidefinite, so $I+2G_{p-1}$ is positive definite and $w=0$. Hence the kernel of the system (7.1) has dimension exactly 1.
