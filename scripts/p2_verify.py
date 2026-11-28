#!/usr/bin/env python
"""p2_verify.py -- plan P2 (queens-spectrum): exact checks of the three nonsingularity lemmas at mu = n
and of the multiplicity theorem  mult_{Q(n)}(n-4) = (n-2)/2 (n even), (n+1)/2 (n odd).

Notation (BRIEF section 6): M = N^T N is the line Gram matrix (size 6n-2); A(Q(n)) = N N^T - 4I.
Sectors (coordinates as in BRIEF L2): A1 (r palindromic, c=r, d even, a=d), B1 (c=-r, r palindromic,
d=a=0), B2 (r=c=0, d even, a=-d), E (c=0, r antisymmetric, d odd, a=d).
T_m := sum_{|s|<=m, s = m mod 2} d_|s|.

Subcommands
  sectors NMIN NMAX   Implementation 1 (python-flint fmpz/fmpq): sector matrices written from the
                      formulas (own code), nullity of S - nI for A1, B1, B2, E; det(S - nI) for A1, E,
                      B2 (n even) against the closed forms of BRIEF L7; multiplicity
                      null(A1)+null(B1)+null(B2)+2 null(E) against the conjecture.
  fraction NMIN NMAX  Implementation 2 (pure Python, fractions.Fraction / int only): the same sector
                      determinants by Fraction Gaussian elimination, and the nullity of M - nI on the
                      FULL line Gram matrix built from the board (no symmetry reduction) by integer
                      fraction-free (Bareiss) elimination.
  fullflint NMIN NMAX nullity of M - nI on the full line Gram matrix with flint (fmpz_mat.rank).
  adjacency NMIN NMAX nullity of A(Q(n)) - (n-4)I on the n^2 x n^2 adjacency matrix (flint), and the
                      explicit eigenvectors: B1 x(i,j)=r_i-r_j (r palindromic, zero sum), B2 (n odd)
                      x(i,j) = [i=j] - [i+j=n-1].
  lemmas NMIN NMAX    exact (Fraction) checks of the proof steps:
                      (L-B2e) n=2p: shooting solution E_j=(2p-1-2j)/(2p-1), P_j=2j/(2p-1), P_p=2p/(2p-1),
                              and the residual of the corresponding d* is supported on the row k=1;
                      (L-G)   G_q = diag(0..q) + [i+j<=q] = L D L^T with D = (q, q-1, ..., m+1,
                              pi_m, ..., pi_1, 0), pi_k = k(q+1-k)/(q-k), m = floor(q/2); checked
                              for q = n (exact equality of L D L^T and G_q);
                      (L-B2o) n=2p+1: the B2 system at mu=n is G_p (+) (I + 2 G_{p-1}) in the
                              difference coordinates (matrix identity checked exactly);
                      (L-A1)  window identity T_{n-1-k}+T_{k-1} = sum of g over k+1-2n+2j... (as linear
                              forms) and the reduced square system of the A1 proof is nonsingular.
"""
import sys
import time
from fractions import Fraction as Fr
from math import factorial

# ---------------------------------------------------------------- sector matrices (lists of ints)


def T_form(n, m):
    """T_m as a dict {j: coeff} over d_j, j >= 0."""
    f = {}
    for s in range(-m, m + 1, 2):
        f[abs(s)] = f.get(abs(s), 0) + 1
    return f


def B2_rows(n, mu):
    """(B2 - mu I) in coordinates d_0..d_{n-1}:  (n-k-mu) d_k - T_{n-1-k}."""
    rows = []
    for k in range(n):
        row = [0] * n
        row[k] += n - k - mu
        for j, c in T_form(n, n - 1 - k).items():
            row[j] -= c
        rows.append(row)
    return rows


def A1_rows(n, mu):
    """(A1 - mu I): unknowns r_i (i in I, 2i >= n-1, r palindromic) then d_0..d_{n-1}."""
    I = [i for i in range(n) if 2 * i >= n - 1]
    nr = len(I)
    pos = {}
    for a, i in enumerate(I):
        pos[i] = a
        pos[n - 1 - i] = a
    dim = nr + n
    rows = []
    for i in I:   # row equation: n r_i + R + 2 sum_{k=i-n+1}^{i} d_|k|
        row = [0] * dim
        row[pos[i]] += n - mu
        for j in range(n):
            row[pos[j]] += 1
        for k in range(i - n + 1, i + 1):
            row[nr + abs(k)] += 2
        rows.append(row)
    for k in range(n):   # diagonal: (n-k) d_k + 2 sum_{i>=k} r_i + T_{n-1-k}
        row = [0] * dim
        row[nr + k] += n - k - mu
        for i in range(k, n):
            row[pos[i]] += 2
        for j, c in T_form(n, n - 1 - k).items():
            row[nr + j] += c
        rows.append(row)
    return rows


def E_rows(n, mu):
    """(E - mu I): unknowns r_i (2i > n-1, r antisymmetric) then d_1..d_{n-1} (d odd)."""
    I = [i for i in range(n) if 2 * i > n - 1]
    nr = len(I)
    dim = nr + n - 1

    def rcoef(i):   # r_i in terms of representatives: (index, sign) or None
        if 2 * i > n - 1:
            return (I.index(i), 1)
        if 2 * i < n - 1:
            return (I.index(n - 1 - i), -1)
        return None

    def dcoef(k):
        if k == 0:
            return None
        return (nr + abs(k) - 1, 1 if k > 0 else -1)
    rows = []
    for i in I:
        row = [0] * dim
        row[I.index(i)] += n - mu
        for k in range(i - n + 1, i + 1):
            c = dcoef(k)
            if c:
                row[c[0]] += 2 * c[1]
        rows.append(row)
    for k in range(1, n):
        row = [0] * dim
        row[nr + k - 1] += n - k - mu
        for i in range(k, n):
            c = rcoef(i)
            if c:
                row[c[0]] += c[1]
        rows.append(row)
    return rows


def B1_rows(n, mu):
    """(B1 - mu I) = (n - mu) I - J on palindromic r (coordinates r_i, 2i >= n-1)."""
    I = [i for i in range(n) if 2 * i >= n - 1]
    rows = []
    for i in I:
        row = [0] * len(I)
        row[I.index(i)] += n - mu
        for j in range(n):
            row[I.index(j) if 2 * j >= n - 1 else I.index(n - 1 - j)] -= 1
        rows.append(row)
    return rows


def closed_form(name, n):
    if name == "E":
        return (2 * n) ** ((n - 1) // 2) if n % 2 else -(2 ** (n // 2)) * n ** (n // 2 - 1)
    if name == "A1":
        return -3 * 2 ** (n - 1) * n ** ((n - 1) // 2) if n % 2 else 5 * 2 ** (n - 1) * n ** (n // 2)
    return -n * factorial(n - 2)


def expected_mult(n):
    return (n - 2) // 2 if n % 2 == 0 else (n + 1) // 2


# ---------------------------------------------------------------- full line Gram matrix from the board


def gram(n):
    """M = N^T N over the 6n-2 lines, built from the squares (no symmetry used)."""
    lines = []
    for i in range(n):
        lines.append([(i, j) for j in range(n)])
    for j in range(n):
        lines.append([(i, j) for i in range(n)])
    for k in range(-(n - 1), n):
        lines.append([(i, i - k) for i in range(n) if 0 <= i - k < n])
    for s in range(0, 2 * n - 1):
        lines.append([(i, s - i) for i in range(n) if 0 <= s - i < n])
    sets = [set(l) for l in lines]
    L = len(lines)
    return [[len(sets[a] & sets[b]) for b in range(L)] for a in range(L)]


def bareiss_rank(A):
    """Rank of an integer matrix by fraction-free elimination with row/column search (pure Python)."""
    A = [row[:] for row in A]
    m, ncol = len(A), len(A[0])
    rank, prev = 0, 1
    col = 0
    for col in range(ncol):
        piv = next((r for r in range(rank, m) if A[r][col] != 0), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        p = A[rank][col]
        for r in range(rank + 1, m):
            a = A[r][col]
            Ar, Ak = A[r], A[rank]
            A[r] = [(p * Ar[c] - a * Ak[c]) // prev if c > col else 0 for c in range(ncol)]
        prev = p
        rank += 1
        if rank == m:
            break
    return rank


def frac_det(rows):
    A = [[Fr(x) for x in r] for r in rows]
    nn = len(A)
    det = Fr(1)
    for c in range(nn):
        piv = next((r for r in range(c, nn) if A[r][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        p = A[c][c]
        det *= p
        for r in range(c + 1, nn):
            f = A[r][c] / p
            if f:
                A[r] = [A[r][j] - f * A[c][j] for j in range(nn)]
    return det


def frac_rank(rows):
    A = [[Fr(x) for x in r] for r in rows]
    m, ncol = len(A), len(A[0])
    rank = 0
    for c in range(ncol):
        piv = next((r for r in range(rank, m) if A[r][c] != 0), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        p = A[rank][c]
        for r in range(m):
            if r != rank and A[r][c] != 0:
                f = A[r][c] / p
                A[r] = [A[r][j] - f * A[rank][j] for j in range(ncol)]
        rank += 1
    return rank


# ---------------------------------------------------------------- subcommands


def cmd_sectors(nmin, nmax):
    from flint import fmpz_mat
    ok = True
    for n in range(nmin, nmax + 1):
        t0 = time.time()
        res = {}
        for name, f in (("A1", A1_rows), ("B1", B1_rows), ("B2", B2_rows), ("E", E_rows)):
            S = fmpz_mat(f(n, n))
            res[name] = (S.nrows() - S.rank(), int(S.det()))
        nullexp = {"A1": 0, "B1": (n + 1) // 2 - 1, "B2": n % 2, "E": 0}
        good_null = all(res[k][0] == nullexp[k] for k in nullexp)
        good_cf = res["A1"][1] == closed_form("A1", n) and res["E"][1] == closed_form("E", n) and \
            (n % 2 == 1 or res["B2"][1] == closed_form("B2", n))
        mult = res["A1"][0] + res["B1"][0] + res["B2"][0] + 2 * res["E"][0]
        good = good_null and good_cf and mult == expected_mult(n)
        ok = ok and good
        print(f"n={n}: nullity(S-nI) A1 {res['A1'][0]}, B1 {res['B1'][0]}, B2 {res['B2'][0]}, E {res['E'][0]};"
              f" mult(n-4) = {mult} (conj {expected_mult(n)}); closed forms {'ok' if good_cf else 'FAIL'};"
              f" {'PASS' if good else 'FAIL'} ({time.time() - t0:.1f}s)", flush=True)
    print("SECTORS (flint): ALL PASS" if ok else "SECTORS (flint): FAILURE")
    return 0 if ok else 1


def cmd_fraction(nmin, nmax):
    ok = True
    for n in range(nmin, nmax + 1):
        t0 = time.time()
        dA1 = frac_det(A1_rows(n, n))
        dE = frac_det(E_rows(n, n))
        dB2 = frac_det(B2_rows(n, n)) if n % 2 == 0 else None
        rB2 = frac_rank(B2_rows(n, n))
        good_cf = dA1 == closed_form("A1", n) and dE == closed_form("E", n) and \
            (dB2 is None or dB2 == closed_form("B2", n))
        good_b2 = (rB2 == n - (n % 2))
        M = gram(n)
        L = len(M)
        for a in range(L):
            M[a][a] -= n
        null_full = L - bareiss_rank(M)
        good = good_cf and good_b2 and null_full == expected_mult(n)
        ok = ok and good
        print(f"n={n}: Fraction det(S-nI) A1={dA1} E={dE} B2={dB2}; closed forms {'ok' if good_cf else 'FAIL'};"
              f" rank(B2-nI)={rB2}; full Gram nullity(M-nI)={null_full} (conj {expected_mult(n)});"
              f" {'PASS' if good else 'FAIL'} ({time.time() - t0:.1f}s)", flush=True)
    print("FRACTION/INT IMPLEMENTATION: ALL PASS" if ok else "FRACTION/INT IMPLEMENTATION: FAILURE")
    return 0 if ok else 1


def cmd_fullflint(nmin, nmax):
    from flint import fmpz_mat
    ok = True
    for n in range(nmin, nmax + 1):
        t0 = time.time()
        M = gram(n)
        for a in range(len(M)):
            M[a][a] -= n
        F = fmpz_mat(M)
        null = F.nrows() - F.rank()
        good = null == expected_mult(n)
        ok = ok and good
        print(f"n={n}: full Gram (flint) nullity(M-nI) = {null} (conj {expected_mult(n)}) "
              f"{'PASS' if good else 'FAIL'} ({time.time() - t0:.1f}s)", flush=True)
    print("FULL GRAM (flint): ALL PASS" if ok else "FULL GRAM (flint): FAILURE")
    return 0 if ok else 1


def cmd_adjacency(nmin, nmax):
    from flint import fmpz_mat
    ok = True
    for n in range(nmin, nmax + 1):
        sq = [(i, j) for i in range(n) for j in range(n)]
        idx = {s: a for a, s in enumerate(sq)}

        def adj(p, q):
            return p != q and (p[0] == q[0] or p[1] == q[1] or p[0] - p[1] == q[0] - q[1]
                               or p[0] + p[1] == q[0] + q[1])
        A = [[(1 if adj(p, q) else 0) - ((n - 4) if p == q else 0) for q in sq] for p in sq]
        F = fmpz_mat(A)
        null = F.nrows() - F.rank()
        # explicit eigenvectors
        vecs = []
        for l in range(1, (n + 1) // 2):         # B1: r = e_0 + e_{n-1} - e_l - e_{n-1-l} (palindromic, sum 0)
            r = [0] * n
            r[0] += 1
            r[n - 1] += 1
            r[l] -= 1
            r[n - 1 - l] -= 1
            if 2 * l == n - 1:
                r = [2 * x for x in r]
                r[l] = -2
            vecs.append([r[i] - r[j] for (i, j) in sq])
        if n % 2:
            vecs.append([(1 if i == j else 0) - (1 if i + j == n - 1 else 0) for (i, j) in sq])
        allok = True
        for v in vecs:
            w = (F * fmpz_mat([[x] for x in v]))
            allok = allok and all(w[a, 0] == 0 for a in range(len(sq))) and any(v)
        rk_vecs = fmpz_mat(vecs).rank() if vecs else 0
        good = null == expected_mult(n) and allok and rk_vecs == expected_mult(n)
        ok = ok and good
        print(f"n={n}: nullity(A - (n-4)I) on {n * n}x{n * n} = {null} (conj {expected_mult(n)}); explicit "
              f"eigenvectors in kernel: {allok}, their rank {rk_vecs}; {'PASS' if good else 'FAIL'}", flush=True)
    print("ADJACENCY: ALL PASS" if ok else "ADJACENCY: FAILURE")
    return 0 if ok else 1


def G_mat(q):
    return [[Fr((i if i == j else 0) + (1 if i + j <= q else 0)) for j in range(q + 1)] for i in range(q + 1)]


def ldl_check(q):
    """Exact symmetric elimination of G_q from the bottom index; compare pivots with the formula and
    check L D L^T == G_q exactly."""
    G = G_mat(q)
    N = q + 1
    S = [r[:] for r in G]
    order = list(range(q, -1, -1))
    Lcols = {}
    piv = {}
    for k in order:
        pk = S[k][k]
        piv[k] = pk
        col = [Fr(0)] * N
        if pk != 0:
            for i in range(N):
                col[i] = S[i][k] / pk
            for i in range(N):
                if S[i][k] == 0:
                    continue
                for j in range(N):
                    S[i][j] -= col[i] * pk * col[j] if False else S[i][k] * S[k][j] / pk if False else 0
            # do the Schur update properly
            rowk = [S[k][j] for j in range(N)]
            colk = [S[i][k] for i in range(N)]
            for i in range(N):
                if colk[i] == 0:
                    continue
                for j in range(N):
                    if rowk[j] != 0:
                        S[i][j] -= colk[i] * rowk[j] / pk
        else:
            col[k] = Fr(1)
        Lcols[k] = col
    m = q // 2
    formula = {}
    for k in range(q + 1):
        formula[k] = Fr(k) if 2 * k > q else Fr(k * (q + 1 - k), q - k)
    pivots_ok = all(piv[k] == formula[k] for k in range(q + 1))
    # reconstruct G = sum_k piv_k * col_k col_k^T  (col_k has entry 1 at k, entries S[i][k]/pk elsewhere)
    R = [[Fr(0)] * N for _ in range(N)]
    for k in order:
        if piv[k] == 0:
            continue
        c = Lcols[k]
        for i in range(N):
            if c[i]:
                for j in range(N):
                    if c[j]:
                        R[i][j] += piv[k] * c[i] * c[j]
    recon_ok = all(R[i][j] == G[i][j] for i in range(N) for j in range(N))
    return pivots_ok, recon_ok, [piv[k] for k in order], m


def cmd_lemmas(nmin, nmax):
    ok = True
    for n in range(nmin, nmax + 1):
        msgs = []
        # (L-B2e)
        if n % 2 == 0:
            p = n // 2
            E = [Fr(1)]
            P = [Fr(0)]
            for j in range(p):
                P.append(P[j] + 2 * E[j] / (2 * p - 1 - 2 * j))
                if j + 1 <= p - 1:
                    E.append(E[j] - P[j + 1] / (j + 1))
            fE = all(E[j] == Fr(2 * p - 1 - 2 * j, 2 * p - 1) for j in range(p))
            fP = all(P[j] == Fr(2 * j, 2 * p - 1) for j in range(p + 1))
            # build d* : T_{2i} = E_i, T_{2i+1} = O_i = P_{p-1-i}
            Ev = E
            Ov = [P[p - 1 - i] for i in range(p)]
            d = [Fr(0)] * n
            d[0] = Ev[0]
            for i in range(1, p):
                d[2 * i] = (Ev[i] - Ev[i - 1]) / 2
            d[1] = Ov[0] / 2
            for i in range(1, p):
                d[2 * i + 1] = (Ov[i] - Ov[i - 1]) / 2
            B = B2_rows(n, n)
            res = [sum(B[k][j] * d[j] for j in range(n)) for k in range(n)]
            supp = [k for k in range(n) if res[k] != 0]
            good = fE and fP and P[p] == Fr(2 * p, 2 * p - 1) and supp == [1]
            msgs.append(f"L-B2e {'ok' if good else 'FAIL'} (P_p={P[p]}, residual support {supp}, value {res[1]})")
            ok = ok and good
        else:
            p = (n - 1) // 2
            # (L-B2o): B2 - nI in difference coordinates equals -(G_p (+) (I + 2G_{p-1})) after scaling
            B = B2_rows(n, n)
            # change of variables d -> u: u_0 = d_0, u_l = 2 d_{2l} (l>=1), w_l = 2 d_{2l+1}
            # row k=2i:  -(i u_i + sum_{l<=p-i} u_l);  row k=2i+1: -( (2i+1) w_i + 2 sum_{l<=p-1-i} w_l )/2
            good = True
            for i in range(p + 1):
                row = B[2 * i]
                coeff_u = [Fr(row[0])] + [Fr(row[2 * l], 2) for l in range(1, p + 1)]
                target = [-(Fr(i) if l == i else 0) - (1 if l <= p - i else 0) for l in range(p + 1)]
                good = good and coeff_u == target and all(row[2 * l + 1] == 0 for l in range(p))
            for i in range(p):
                row = B[2 * i + 1]
                coeff_w = [Fr(row[2 * l + 1], 2) for l in range(p)]
                target = [Fr(-((2 * i + 1) if l == i else 0) - 2 * (1 if l <= p - 1 - i else 0), 2) for l in range(p)]
                good = good and coeff_w == target and all(row[2 * l] == 0 for l in range(p + 1))
            # explicit kernel vector d = (n-1) e_0 - sum_{even k >= 2} e_k
            dk = [0] * n
            dk[0] = n - 1
            for k in range(2, n, 2):
                dk[k] = -1
            kern = all(sum(B[k][j] * dk[j] for j in range(n)) == 0 for k in range(n))
            good = good and kern
            msgs.append(f"L-B2o {'ok' if good else 'FAIL'} (block form G_p (+) (I+2G_(p-1)); kernel vector ok: {kern})")
            ok = ok and good
        # (L-G) for q = n and q = n-1
        for q in (n - 1, n):
            pv, rc, pivs, m = ldl_check(q)
            good = pv and rc and all(x > 0 for x in pivs[:-1]) and pivs[-1] == 0
            ok = ok and good
            msgs.append(f"L-G q={q} {'ok' if good else 'FAIL'}")
        # (L-A1): window identity as linear forms on g (n-periodic even function)
        good = True
        for k in range(1, n):
            lhs = {}
            for m_, sgn in ((n - 1 - k, 1), (k - 1, 1)):
                for s in range(-m_, m_ + 1, 2):
                    key = s % n
                    lhs[key] = lhs.get(key, 0) + 1
            rhs = {}
            for j in range(n):
                s = k + 1 - 2 * n + 2 * j
                rhs[s % n] = rhs.get(s % n, 0) + 1
            good = good and lhs == rhs
        # T_{n-1} window
        lhsT = {}
        for s in range(-(n - 1), n, 2):
            lhsT[s % n] = lhsT.get(s % n, 0) + 1
        if n % 2:
            good = good and lhsT == {r: 1 for r in range(n)}
        else:
            good = good and lhsT == {r: 2 for r in range(1, n, 2)}
        # reduced system of the A1 proof: unknowns d_0..d_h (h = floor(n/2)), d_k = d_{n-k}
        h = n // 2

        def dfull(v):
            return [v[min(k, n - k)] if k > 0 else v[0] for k in range(n)]
        rows = []
        for b in range(h + 1):
            v = [0] * (h + 1)
            v[b] = 1
            d = dfull(v)
            R = -2 * sum(d)
            Tm = lambda m_: sum(d[abs(s)] for s in range(-m_, m_ + 1, 2))   # noqa: E731
            col = [n * d[k] - 2 * R - Tm(n - 1 - k) - Tm(k - 1) for k in range(1, h + 1)]
            col.append(2 * R + Tm(n - 1))
            rows.append(col)
        red = [[rows[b][e] for b in range(h + 1)] for e in range(h + 1)]
        dred = frac_det(red)
        good = good and dred != 0
        ok = ok and good
        msgs.append(f"L-A1 {'ok' if good else 'FAIL'} (det reduced system = {dred})")
        print(f"n={n}: " + "; ".join(msgs), flush=True)
    print("LEMMA CHECKS: ALL PASS" if ok else "LEMMA CHECKS: FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    a = sys.argv[1:]
    cmds = {"sectors": cmd_sectors, "fraction": cmd_fraction, "fullflint": cmd_fullflint,
            "adjacency": cmd_adjacency, "lemmas": cmd_lemmas}
    if len(a) == 3 and a[0] in cmds:
        sys.exit(cmds[a[0]](int(a[1]), int(a[2])))
    print(__doc__)
    sys.exit(2)
