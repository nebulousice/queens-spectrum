#!/usr/bin/env python
"""p2_proofcheck.py -- plan P2 (queens-spectrum), run 2026-11-27.

Exact (pure Python: int / fractions.Fraction, no flint, no sympy unless 'symbolic') replay of the
proof steps of the three nonsingularity lemmas at mu = n.  Everything is computed from the line Gram
matrix M = N^T N built from the board (own code, independent of p2_verify.py and ../../scripts).

Line coordinates: R_i, C_j (0<=i,j<n), D_k (k = i-j, |k|<=n-1), A_s (s = i+j-(n-1), |s|<=n-1).
A linear form on a sector is checked by evaluating it on every basis vector of that sector.

Subcommands
  sectors NMIN NMAX   (Gram) M maps each sector ansatz into itself and acts by the formulas of BRIEF L2
                      (A1, B1, B2, E): checked on every basis vector.  Also the involutions t, h, z
                      commute with M and the sector ansatzes are their joint eigenspaces (dimension count).
  a1 NMIN NMAX        A1 lemma steps S1..S6 (see LAB.md section 3) and the kernel of A1 - nI is 0.
  e NMIN NMAX         E lemma steps E1..E3 and the kernel of E - nI is 0.
  b2 NMIN NMAX        B2 lemma: even n shooting solution and residual 2p/(2p-1); odd n block form
                      G_p (+) (I + 2 G_{p-1}); kernel dimension (n odd: 1, n even: 0) from the board.
  g QMIN QMAX         G_q = diag(0..q) + [i+j<=q]: symmetric elimination from index q downwards has
                      pivots q, q-1, ..., m+1, then k(q+1-k)/(q-k) for k = m..1, then 0 (m = floor(q/2));
                      gamma_k = k/(q-k) (the max-matrix entry before eliminating k).
  symbolic            sympy: determinants of the final A1 reduced systems as polynomials in n.
"""
import sys
import time
from fractions import Fraction as Fr


# ------------------------------------------------------------------ board and Gram action
def line_index(n):
    idx = {}
    for i in range(n):
        idx[("R", i)] = len(idx)
    for j in range(n):
        idx[("C", j)] = len(idx)
    for k in range(-(n - 1), n):
        idx[("D", k)] = len(idx)
    for s in range(-(n - 1), n):
        idx[("A", s)] = len(idx)
    return idx


def lines_of_square(n, i, j):
    return [("R", i), ("C", j), ("D", i - j), ("A", i + j - (n - 1))]


def gram_apply(n, v):
    """(M v) for v a dict line -> value; M = N^T N computed square by square: (Mv)_L = sum over
    squares on L of (sum of v over the 4 lines through that square)."""
    out = {}
    for i in range(n):
        for j in range(n):
            ls = lines_of_square(n, i, j)
            s = sum(v.get(L, 0) for L in ls)
            for L in ls:
                out[L] = out.get(L, 0) + s
    return out


def minus_n(n, v, Mv):
    return {L: Mv.get(L, 0) - n * v.get(L, 0) for L in set(Mv) | set(v)}


# ------------------------------------------------------------------ sector ansatzes
def reps_pal(n):
    return [i for i in range(n) if 2 * i >= n - 1]


def reps_anti(n):
    return [i for i in range(n) if 2 * i > n - 1]


def A1_embed(n, r, d):
    """r: full length-n palindromic list, d: d_0..d_{n-1}."""
    v = {}
    for i in range(n):
        v[("R", i)] = r[i]
        v[("C", i)] = r[i]
    for k in range(-(n - 1), n):
        v[("D", k)] = d[abs(k)]
        v[("A", k)] = d[abs(k)]
    return v


def A1_basis(n):
    out = []
    for i in reps_pal(n):
        r = [0] * n
        r[i] = 1
        r[n - 1 - i] = 1
        out.append((r, [0] * n))
    for k in range(n):
        d = [0] * n
        d[k] = 1
        out.append(([0] * n, d))
    return out


def E_embed(n, r, d):
    """r: antisymmetric full list, d: d_0..d_{n-1} with d_0 = 0 (d odd)."""
    v = {}
    for i in range(n):
        v[("R", i)] = r[i]
        v[("C", i)] = 0
    for k in range(-(n - 1), n):
        val = d[abs(k)] * (1 if k > 0 else -1) if k != 0 else 0
        v[("D", k)] = val
        v[("A", k)] = val
    return v


def E_basis(n):
    out = []
    for i in reps_anti(n):
        r = [0] * n
        r[i] = 1
        r[n - 1 - i] = -1
        out.append((r, [0] * n))
    for k in range(1, n):
        d = [0] * n
        d[k] = 1
        out.append(([0] * n, d))
    return out


def B2_embed(n, d):
    v = {}
    for i in range(n):
        v[("R", i)] = 0
        v[("C", i)] = 0
    for k in range(-(n - 1), n):
        v[("D", k)] = d[abs(k)]
        v[("A", k)] = -d[abs(k)]
    return v


def B1_embed(n, r):
    v = {}
    for i in range(n):
        v[("R", i)] = r[i]
        v[("C", i)] = -r[i]
    for k in range(-(n - 1), n):
        v[("D", k)] = 0
        v[("A", k)] = 0
    return v


def T(n, d, m):
    """T_m = sum_{|s|<=m, s = m mod 2} d_|s|  (d indexed 0..n-1); T_{-1} = 0."""
    if m < 0:
        return 0
    return sum(d[abs(s)] for s in range(-m, m + 1, 2))


def rho(n, r, k):
    return sum(r[k:])


# ------------------------------------------------------------------ involutions
def act(n, g, v):
    """t: transpose, h: (i,j)->(i,n-1-j), z: (i,j)->(n-1-i,n-1-j); action on line functions:
    (g v)_{g L} = v_L."""
    out = {}
    for (typ, x), val in v.items():
        if g == "t":
            L = {"R": ("C", x), "C": ("R", x), "D": ("D", -x), "A": ("A", x)}[typ]
        elif g == "h":
            L = {"R": ("R", x), "C": ("C", n - 1 - x), "D": ("A", x), "A": ("D", x)}[typ]
        else:
            L = {"R": ("R", n - 1 - x), "C": ("C", n - 1 - x), "D": ("D", -x), "A": ("A", -x)}[typ]
        out[L] = val
    return out


# ------------------------------------------------------------------ subcommands
def cmd_sectors(nmin, nmax):
    ok = True
    for n in range(nmin, nmax + 1):
        t0 = time.time()
        good = True
        # A1
        for r, d in A1_basis(n):
            v = A1_embed(n, r, d)
            Mv = gram_apply(n, v)
            R = sum(r)
            rr = [Mv[("R", i)] for i in range(n)]
            dd = [Mv[("D", k)] for k in range(n)]
            good &= (Mv == A1_embed(n, rr, dd))      # image is again of A1 shape
            for i in range(n):
                good &= rr[i] == n * r[i] + R + 2 * sum(d[abs(k)] for k in range(i - n + 1, i + 1))
            for k in range(n):
                good &= dd[k] == (n - k) * d[k] + 2 * rho(n, r, k) + T(n, d, n - 1 - k)
            for g in "thz":     # commutation with M on this vector, and joint eigenvalue
                good &= gram_apply(n, act(n, g, v)) == act(n, g, Mv)
            good &= act(n, "t", v) == v and act(n, "h", v) == v
        okA1 = good
        # E
        for r, d in E_basis(n):
            v = E_embed(n, r, d)
            Mv = gram_apply(n, v)
            rr = [Mv[("R", i)] for i in range(n)]
            dd = [Mv[("D", k)] for k in range(n)]
            good &= dd[0] == 0 and (Mv == E_embed(n, rr, dd))
            dfull = {k: (d[abs(k)] * (1 if k > 0 else -1) if k else 0) for k in range(-(n - 1), n)}
            for i in range(n):
                good &= rr[i] == n * r[i] + 2 * sum(dfull[k] for k in range(i - n + 1, i + 1))
            for k in range(1, n):
                good &= dd[k] == (n - k) * d[k] + rho(n, r, k)
            zv = act(n, "z", v)
            good &= all(zv[L] == -v[L] for L in v) and act(n, "h", v) == v
        okE = good
        # B2
        for k0 in range(n):
            d = [0] * n
            d[k0] = 1
            v = B2_embed(n, d)
            Mv = gram_apply(n, v)
            dd = [Mv[("D", k)] for k in range(n)]
            good &= Mv == B2_embed(n, dd)
            for k in range(n):
                good &= dd[k] == (n - k) * d[k] - T(n, d, n - 1 - k)
            good &= act(n, "t", v) == v and all(act(n, "h", v)[L] == -v[L] for L in v)
        # B1
        for i0 in reps_pal(n):
            r = [0] * n
            r[i0] = 1
            r[n - 1 - i0] = 1
            v = B1_embed(n, r)
            Mv = gram_apply(n, v)
            rr = [Mv[("R", i)] for i in range(n)]
            good &= Mv == B1_embed(n, rr)
            good &= all(rr[i] == n * r[i] - sum(r) for i in range(n))
        dims = (len(reps_pal(n)) + n) + len(reps_pal(n)) + n + 2 * (len(reps_anti(n)) + n - 1)
        good &= dims == 6 * n - 2
        ok &= good
        print(f"n={n}: sector formulas A1 {'ok' if okA1 else 'FAIL'}, E {'ok' if okE else 'FAIL'}, "
              f"B2/B1 {'ok' if good else 'FAIL'}; dim A1+B1+B2+2E = {dims} (6n-2 = {6 * n - 2}) "
              f"({time.time() - t0:.1f}s)", flush=True)
    print("SECTOR FORMULAS FROM BOARD: ALL PASS" if ok else "SECTOR FORMULAS FROM BOARD: FAILURE")
    return 0 if ok else 1


def frac_kernel_dim(rows, ncols):
    A = [[Fr(x) for x in row] for row in rows]
    rank = 0
    for c in range(ncols):
        piv = next((r for r in range(rank, len(A)) if A[r][c] != 0), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        p = A[rank][c]
        for r in range(len(A)):
            if r != rank and A[r][c] != 0:
                f = A[r][c] / p
                A[r] = [A[r][j] - f * A[rank][j] for j in range(ncols)]
        rank += 1
    return ncols - rank


def cmd_a1(nmin, nmax):
    ok = True
    for n in range(nmin, nmax + 1):
        basis = A1_basis(n)
        forms_row = [[] for _ in range(n)]
        forms_diag = [[] for _ in range(n)]
        good = True
        for r, d in basis:
            v = A1_embed(n, r, d)
            W = minus_n(n, v, gram_apply(n, v))
            R = sum(r)
            D = sum(d)
            for i in range(n):
                forms_row[i].append(W[("R", i)])
            for k in range(n):
                forms_diag[k].append(W[("D", k)])
            # S1: row_i - row_{i-1} = 2 (d_i - d_{n-i});  S2: row_0 = R + 2 D
            for i in range(1, n):
                good &= W[("R", i)] - W[("R", i - 1)] == 2 * (d[i] - d[n - i])
            good &= W[("R", 0)] == R + 2 * D
            # S3: diag_k = -k d_k + 2 rho_k + T_{n-1-k};  S4: rho_{n-k} = R - rho_k
            for k in range(n):
                good &= W[("D", k)] == -k * d[k] + 2 * rho(n, r, k) + T(n, d, n - 1 - k)
            for k in range(1, n):
                good &= rho(n, r, n - k) == R - rho(n, r, k)
        s1to4 = good
        # S5: window identity on the subspace d_k = d_{n-k} (1<=k<=n-1): basis f_0 = e_0, f_k = e_k + e_{n-k}
        s5 = True
        for k0 in range(0, n // 2 + 1):
            d = [0] * n
            d[k0] = 1
            d[(n - k0) % n] = 1
            D = sum(d)
            P = [sum(d[s] for s in range(n) if s % 2 == e) for e in (0, 1)]
            for k in range(1, n):
                lhs = T(n, d, n - 1 - k) + T(n, d, k - 1)
                rhs = D if n % 2 else 2 * P[(k + 1) % 2]
                s5 &= lhs == rhs
            s5 &= T(n, d, n - 1) == (D if n % 2 else 2 * P[1])
        # S6: final reduced systems (n-dependent numbers), exact
        if n % 2:
            red = [[Fr(1, 2), 1], [2, 1]]                 # unknowns (R, D): row_0/2 and diag_0
            dred = red[0][0] * red[1][1] - red[0][1] * red[1][0]
        else:
            # unknowns (d0, alpha, beta, R)
            red = [[0, n, -n, -2],                         # n alpha = 2R + n beta
                   [-2, -(n - 2), n, -2],                  # n beta = 2R + 2 d0 + (n-2) alpha
                   [1, Fr(n, 2) - 1, Fr(n, 2), Fr(1, 2)],  # row_0 / 2: D + R/2 = 0
                   [0, 0, n, 2]]                           # diag_0: 2R + n beta = 0
            dred = det_frac(red)
        s6 = dred != 0
        # kernel of the full A1 system (rows for all i, diags for all k) on the A1 coordinates
        rows = forms_row + forms_diag
        kdim = frac_kernel_dim(rows, len(basis))
        good = s1to4 and s5 and s6 and kdim == 0
        ok &= good
        print(f"n={n}: S1-S4 {'ok' if s1to4 else 'FAIL'}; S5 window {'ok' if s5 else 'FAIL'}; "
              f"S6 reduced det = {dred}; kernel dim of (A1 - nI) from board = {kdim}; "
              f"{'PASS' if good else 'FAIL'}", flush=True)
    print("A1 LEMMA STEPS: ALL PASS" if ok else "A1 LEMMA STEPS: FAILURE")
    return 0 if ok else 1


def det_frac(m):
    A = [[Fr(x) for x in row] for row in m]
    N = len(A)
    det = Fr(1)
    for c in range(N):
        piv = next((r for r in range(c, N) if A[r][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det *= A[c][c]
        for r in range(c + 1, N):
            f = A[r][c] / A[c][c]
            A[r] = [A[r][j] - f * A[c][j] for j in range(N)]
    return det


def cmd_e(nmin, nmax):
    ok = True
    for n in range(nmin, nmax + 1):
        basis = E_basis(n)
        rows = []
        good = True
        forms = {}
        for r, d in basis:
            v = E_embed(n, r, d)
            W = minus_n(n, v, gram_apply(n, v))
            for i in range(n):
                forms.setdefault(("R", i), []).append(W[("R", i)])
            for k in range(1, n):
                forms.setdefault(("D", k), []).append(W[("D", k)])
            for i in range(1, n):                                   # E1
                good &= W[("R", i)] - W[("R", i - 1)] == 2 * (d[i] + d[n - i])
            for k in range(1, n):                                   # E2
                good &= W[("D", k)] == -k * d[k] + rho(n, r, k)
                good &= rho(n, r, n - k) == rho(n, r, k)            # E3
            good &= rho(n, r, 0) == 0
        kdim = frac_kernel_dim(list(forms.values()), len(basis))
        good &= kdim == 0
        ok &= good
        print(f"n={n}: E1-E3 {'ok' if good else 'FAIL'}; kernel dim of (E - nI) from board = {kdim}", flush=True)
    print("E LEMMA STEPS: ALL PASS" if ok else "E LEMMA STEPS: FAILURE")
    return 0 if ok else 1


def cmd_b2(nmin, nmax):
    ok = True
    for n in range(nmin, nmax + 1):
        # forms of (B2 - nI) from the board
        forms = []
        for k0 in range(n):
            d = [0] * n
            d[k0] = 1
            v = B2_embed(n, d)
            W = minus_n(n, v, gram_apply(n, v))
            forms.append([W[("D", k)] for k in range(n)])
        rows = [[forms[j][k] for j in range(n)] for k in range(n)]   # row k, column j
        kdim = frac_kernel_dim(rows, n)
        good = kdim == n % 2
        msg = ""
        if n % 2 == 0:
            p = n // 2
            # shooting: Q_0 = 0, E_0 = 1, Q_{j+1} = Q_j + 2E_j/(2p-1-2j), E_i = E_{i-1} - Q_i / i
            E, Q = [Fr(1)], [Fr(0)]
            for j in range(p):
                Q.append(Q[j] + 2 * E[j] / (2 * p - 1 - 2 * j))
                if j + 1 <= p - 1:
                    E.append(E[j] - Q[j + 1] / (j + 1))
            good &= all(E[j] == Fr(2 * p - 1 - 2 * j, 2 * p - 1) for j in range(p))
            good &= all(Q[j] == Fr(2 * j, 2 * p - 1) for j in range(p + 1))
            # rebuild d from (E, O) with O_i = Q_{p-1-i} and check rows k != 1 vanish, row 1 residual
            O = [Q[p - 1 - i] for i in range(p)]
            d = [Fr(0)] * n
            d[0] = E[0]
            for i in range(1, p):
                d[2 * i] = (E[i] - E[i - 1]) / 2
            d[1] = O[0] / 2
            for i in range(1, p):
                d[2 * i + 1] = (O[i] - O[i - 1]) / 2
            res = [sum(rows[k][j] * d[j] for j in range(n)) for k in range(n)]
            supp = [k for k in range(n) if res[k] != 0]
            # row k = 1 is the equation f_{p-1}; the residual there is -Q_p/2 = -p/(2p-1)
            good &= supp == [1] and res[1] == Fr(-p, 2 * p - 1)
            msg = f"shooting closed form ok, residual {res[1]} on rows {supp}"
        else:
            p = (n - 1) // 2
            for i in range(p + 1):          # even rows: coefficients on u_0 = d_0, u_l = 2 d_{2l}
                row = rows[2 * i]
                cu = [Fr(row[0])] + [Fr(row[2 * l], 2) for l in range(1, p + 1)]
                tgt = [-(i if l == i else 0) - (1 if i + l <= p else 0) for l in range(p + 1)]
                good &= cu == tgt and all(row[2 * l + 1] == 0 for l in range(p))
            for i in range(p):              # odd rows (times 2): coefficients on w_l = 2 d_{2l+1}
                row = rows[2 * i + 1]
                cw = [Fr(row[2 * l + 1], 2) for l in range(p)]
                tgt = [-((2 * i + 1) if l == i else 0) - 2 * (1 if i + l <= p - 1 else 0) for l in range(p)]
                tgt = [Fr(t, 2) for t in tgt]
                good &= cw == tgt and all(row[2 * l] == 0 for l in range(p + 1))
            msg = "block form -(G_p (+) (I+2G_(p-1))/2) ok"
        ok &= good
        print(f"n={n}: kernel dim of (B2 - nI) from board = {kdim} (expected {n % 2}); {msg}; "
              f"{'PASS' if good else 'FAIL'}", flush=True)
    print("B2 LEMMA STEPS: ALL PASS" if ok else "B2 LEMMA STEPS: FAILURE")
    return 0 if ok else 1


def cmd_g(qmin, qmax):
    ok = True
    for q in range(qmin, qmax + 1):
        N = q + 1
        S = [[Fr((i if i == j else 0) + (1 if i + j <= q else 0)) for j in range(N)] for i in range(N)]
        m = q // 2
        pivs = []
        good = True
        for k in range(q, -1, -1):
            pk = S[k][k]
            pivs.append(pk)
            if k <= m:   # max-matrix structure on 0..k:  S[a][b] = a [a=b] + c_{max(a,b)}, gamma_k = c_k
                gam = Fr(k, q - k) if k < q else None
                good &= all(S[a][b] == (a if a == b else 0) + S[max(a, b)][max(a, b)] - max(a, b)
                            for a in range(k + 1) for b in range(k + 1))
                good &= S[k][k] - k == gam
            expect = Fr(k) if k > m else Fr(k * (q + 1 - k), q - k)
            good &= pk == expect
            if pk != 0:
                rowk = S[k][:]
                for i in range(k):
                    if S[i][k] != 0:
                        f = S[i][k] / pk
                        S[i] = [S[i][j] - f * rowk[j] for j in range(N)]
            elif k != 0:
                good = False
        good &= pivs[-1] == 0 and all(x > 0 for x in pivs[:-1])
        ok &= good
        if q <= 8 or q % 10 == 0 or not good:
            print(f"q={q}: pivots (k=q..0) {[str(x) for x in pivs]} {'ok' if good else 'FAIL'}", flush=True)
    print(f"G_q PIVOT FORMULA q={qmin}..{qmax}: ALL PASS" if ok else "G_q PIVOT FORMULA: FAILURE")
    return 0 if ok else 1


def cmd_symbolic():
    import sympy as sp
    n = sp.symbols("n", positive=True)
    odd = sp.Matrix([[sp.Rational(1, 2), 1], [2, 1]])
    even = sp.Matrix([[0, n, -n, -2], [-2, -(n - 2), n, -2], [1, n / 2 - 1, n / 2, sp.Rational(1, 2)],
                      [0, 0, n, 2]])
    print("A1 reduced system, n odd: det =", sp.factor(odd.det()))
    print("A1 reduced system, n even: det =", sp.factor(even.det()))
    # gamma recurrence of the G_q lemma: gamma_{k-1} = k gamma_k/(k+gamma_k) - 1/(q-k+1), gamma_k = k/(q-k)
    q, k = sp.symbols("q k", positive=True)
    g = k / (q - k)
    print("G_q recurrence residual:", sp.simplify(k * g / (k + g) - 1 / (q - k + 1) - (k - 1) / (q - k + 1)))
    print("pivot k + gamma_k =", sp.factor(k + g))
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    cmds = {"sectors": cmd_sectors, "a1": cmd_a1, "e": cmd_e, "b2": cmd_b2, "g": cmd_g}
    if a == ["symbolic"]:
        sys.exit(cmd_symbolic())
    if len(a) == 3 and a[0] in cmds:
        sys.exit(cmds[a[0]](int(a[1]), int(a[2])))
    print(__doc__)
    sys.exit(2)
