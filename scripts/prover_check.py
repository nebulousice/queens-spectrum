#!/usr/bin/env python
"""prover_check.py -- queens-spectrum, stage 4 (Prover), 2026-11-27.

Exact replay of every identity used in ../PROOF.md, section by section.  Pure Python
(int / fractions.Fraction; one prime modulus for rank bounds).  Independent of plans/P2/*.py and of
scripts/*.py: everything is rebuilt here from the board.

This is a sanity replay for finitely many n.  The proof in PROOF.md is a pen-and-paper argument for
all n >= 4 and does not depend on this script.

Usage:  python prover_check.py NMIN NMAX        (default 4 40)
        python prover_check.py small            (prints the n = 4 and n = 5 systems in full)

Rank logic (rigorous): for an integer matrix X, rank_Q(X) >= rank_{F_p}(X).  So
  * "kernel is 0"      is certified by full rank mod p;
  * "kernel has dim k" is certified by rank mod p = size - k together with k explicit, exactly
    verified, linearly independent kernel vectors.
"""
import sys
import time
from fractions import Fraction as Fr

P = 2147483647  # 2^31 - 1, prime


# ----------------------------------------------------------------------------- board, lines
def all_lines(n):
    return ([("R", i) for i in range(n)] + [("C", j) for j in range(n)]
            + [("D", k) for k in range(-(n - 1), n)] + [("A", s) for s in range(-(n - 1), n)])


def lines_through(n, i, j):
    return [("R", i), ("C", j), ("D", i - j), ("A", i + j - (n - 1))]


def squares_of(n, L):
    typ, x = L
    out = []
    for i in range(n):
        for j in range(n):
            if (typ, x) in lines_through(n, i, j):
                out.append((i, j))
    return out


def N_apply(n, v):
    """(N v)(i,j) = sum of v over the four lines through (i,j)."""
    return {(i, j): sum(v.get(L, 0) for L in lines_through(n, i, j))
            for i in range(n) for j in range(n)}


def M_apply(n, v):
    """(M v)_L = sum over squares x on L of (N v)(x)   (M = N^T N)."""
    x = N_apply(n, v)
    out = {L: 0 for L in all_lines(n)}
    for (i, j), val in x.items():
        for L in lines_through(n, i, j):
            out[L] += val
    return out


def adjacent(a, b):
    (i, j), (k, l) = a, b
    return a != b and (i == k or j == l or i - j == k - l or i + j == k + l)


def A_apply(n, x):
    sq = [(i, j) for i in range(n) for j in range(n)]
    return {a: sum(x[b] for b in sq if adjacent(a, b)) for a in sq}


# ----------------------------------------------------------------------------- vectors (r,c,d,a)
def vec(n, r=None, c=None, d=None, a=None):
    """r, c: lists of length n; d, a: dicts k -> value for |k| <= n-1 (missing = 0)."""
    v = {}
    for i in range(n):
        v[("R", i)] = (r[i] if r else 0)
        v[("C", i)] = (c[i] if c else 0)
    for k in range(-(n - 1), n):
        v[("D", k)] = (d.get(k, 0) if d else 0)
        v[("A", k)] = (a.get(k, 0) if a else 0)
    return v


def op_t(n, v):   # (r, c, d, a) -> (c, r, d^-, a)
    return vec(n, [v[("C", i)] for i in range(n)], [v[("R", i)] for i in range(n)],
               {k: v[("D", -k)] for k in range(-(n - 1), n)},
               {k: v[("A", k)] for k in range(-(n - 1), n)})


def op_h(n, v):   # (r, c, d, a) -> (r, c^rev, a, d)
    return vec(n, [v[("R", i)] for i in range(n)], [v[("C", n - 1 - i)] for i in range(n)],
               {k: v[("A", k)] for k in range(-(n - 1), n)},
               {k: v[("D", k)] for k in range(-(n - 1), n)})


def op_z(n, v):   # (r, c, d, a) -> (r^rev, c^rev, d^-, a^-)
    return vec(n, [v[("R", n - 1 - i)] for i in range(n)], [v[("C", n - 1 - i)] for i in range(n)],
               {k: v[("D", -k)] for k in range(-(n - 1), n)},
               {k: v[("A", -k)] for k in range(-(n - 1), n)})


def scal(c, v):
    return {L: c * x for L, x in v.items()}


def sub(v, w):
    return {L: v[L] - w[L] for L in v}


def is_zero(v):
    return all(x == 0 for x in v.values())


# ----------------------------------------------------------------------------- sector bases
def even_d(n, dd):
    """dd: list d_0..d_{n-1}  ->  dict with d_{-k} = d_k."""
    return {k: dd[abs(k)] for k in range(-(n - 1), n)}


def odd_d(n, dd):
    """dd: list (dd[0] ignored), d_{-k} = -d_k, d_0 = 0."""
    return {k: (dd[k] if k > 0 else (-dd[-k] if k < 0 else 0)) for k in range(-(n - 1), n)}


def pal_basis(n):      # palindromic r
    out = []
    for i in range((n + 1) // 2):
        r = [0] * n
        r[i] = 1
        r[n - 1 - i] = 1
        out.append(r)
    return out


def anti_basis(n):     # antipalindromic r
    out = []
    for i in range(n // 2):
        r = [0] * n
        r[i] = 1
        r[n - 1 - i] = -1
        out.append(r)
    return out


def unit(n, k):
    d = [0] * n
    d[k] = 1
    return d


def A1_vec(n, r, dd):
    return vec(n, r, r, even_d(n, dd), even_d(n, dd))


def B1_vec(n, r):
    return vec(n, r, [-x for x in r])


def B2_vec(n, dd):
    return vec(n, None, None, even_d(n, dd), {k: -x for k, x in even_d(n, dd).items()})


def E_vec(n, r, dd):
    return vec(n, r, None, odd_d(n, dd), odd_d(n, dd))


def A1_basis(n):
    return [(r, [0] * n) for r in pal_basis(n)] + [([0] * n, unit(n, k)) for k in range(n)]


def E_basis(n):
    return [(r, [0] * n) for r in anti_basis(n)] + [([0] * n, unit(n, k)) for k in range(1, n)]


def T(n, dd, m):
    """T_m = sum_{|s| <= m, s = m mod 2} d_|s|;  T_m = 0 for m < 0."""
    if m < 0:
        return 0
    return sum(dd[abs(s)] for s in range(-m, m + 1, 2))


def rho(r, k):
    return sum(r[k:])


# ----------------------------------------------------------------------------- linear algebra
def rank_mod_p(rows):
    A = [[x % P for x in row] for row in rows]
    if not A:
        return 0
    ncols = len(A[0])
    rank = 0
    for c in range(ncols):
        piv = next((i for i in range(rank, len(A)) if A[i][c]), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        inv = pow(A[rank][c], P - 2, P)
        prow = [(x * inv) % P for x in A[rank]]
        A[rank] = prow
        for i in range(rank + 1, len(A)):
            f = A[i][c]
            if f:
                A[i] = [(a - f * b) % P for a, b in zip(A[i], prow)]
        rank += 1
        if rank == len(A):
            break
    return rank


def nullspace_frac(rows, ncols):
    """Exact nullspace basis (Fractions) of the matrix with the given rows."""
    A = [[Fr(x) for x in row] for row in rows]
    piv_cols = []
    rnk = 0
    for c in range(ncols):
        piv = next((i for i in range(rnk, len(A)) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[rnk], A[piv] = A[piv], A[rnk]
        pv = A[rnk][c]
        A[rnk] = [x / pv for x in A[rnk]]
        for i in range(len(A)):
            if i != rnk and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[rnk])]
        piv_cols.append(c)
        rnk += 1
    free = [c for c in range(ncols) if c not in piv_cols]
    basis = []
    for fcol in free:
        x = [Fr(0)] * ncols
        x[fcol] = Fr(1)
        for i, pc in enumerate(piv_cols):
            x[pc] = -A[i][fcol]
        basis.append(x)
    return basis


def det_frac(m):
    A = [[Fr(x) for x in row] for row in m]
    size = len(A)
    det = Fr(1)
    for c in range(size):
        piv = next((i for i in range(c, size) if A[i][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det *= A[c][c]
        for i in range(c + 1, size):
            f = A[i][c] / A[c][c]
            A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return det


def in_span(vectors, x):
    """x in span(vectors) exactly?"""
    rows = [list(col) for col in zip(*vectors)] if vectors else [[] for _ in x]
    aug = [rows[i] + [x[i]] for i in range(len(x))]
    ns = nullspace_frac(aug, len(vectors) + 1)
    return any(b[-1] != 0 for b in ns)


# ----------------------------------------------------------------------------- checks
def check_reduction(n):
    """Section 2: number of common lines of two squares = 4 (same square), = [adjacent] otherwise."""
    sq = [(i, j) for i in range(n) for j in range(n)]
    ok = True
    for a in sq:
        la = set(lines_through(n, *a))
        for b in sq:
            common = len(la & set(lines_through(n, *b)))
            ok &= common == (4 if a == b else (1 if adjacent(a, b) else 0))
    ok &= len(all_lines(n)) == 6 * n - 2
    return ok


def check_symmetry(n):
    """Section 3: t, h, z are induced by board maps; relations; commute with M; sector dimensions;
    the five sector bases together are a basis of the line space."""
    ok = True
    L = all_lines(n)
    # induced line maps
    maps = {"t": (lambda i, j: (j, i)), "h": (lambda i, j: (i, n - 1 - j)),
            "z": (lambda i, j: (n - 1 - i, n - 1 - j))}
    ops = {"t": op_t, "h": op_h, "z": op_z}
    sqs = {ln: frozenset(squares_of(n, ln)) for ln in L}
    inv = {s: ln for ln, s in sqs.items()}
    ok &= len(inv) == len(L)                       # distinct lines have distinct square sets
    for g, f in maps.items():
        for ln in L:
            img = frozenset(f(i, j) for (i, j) in sqs[ln])
            ok &= img in inv                       # image of a line is a line
            v = vec(n)
            v[ln] = 1                              # indicator of ln; (g v) must be indicator of g(ln)
            gv = ops[g](n, v)
            ok &= gv[inv[img]] == 1 and sum(abs(x) for x in gv.values()) == 1
    # relations and commutation with M, on the standard basis
    for ln in L:
        v = vec(n)
        v[ln] = 1
        tv, hv, zv = op_t(n, v), op_h(n, v), op_z(n, v)
        ok &= op_t(n, tv) == v and op_h(n, hv) == v and op_z(n, zv) == v
        ok &= op_t(n, zv) == op_z(n, tv) and op_h(n, zv) == op_z(n, hv)
        ok &= op_t(n, hv) == op_z(n, op_h(n, tv))                      # th = z ht
        ok &= op_t(n, op_h(n, op_t(n, hv))) == zv                      # (th)^2 = z
        Mv = M_apply(n, v)
        ok &= M_apply(n, tv) == op_t(n, Mv) and M_apply(n, hv) == op_h(n, Mv) \
            and M_apply(n, zv) == op_z(n, Mv)
    # sector bases
    bases = sector_bases(n)
    dims = {k: len(b) for k, b in bases.items()}
    c2 = (n + 1) // 2
    ok &= dims == {"A1": c2 + n, "B1": c2, "B2": n, "E": n // 2 + n - 1, "E'": n // 2 + n - 1}
    ok &= sum(dims.values()) == 6 * n - 2
    for v in bases["A1"]:
        ok &= op_t(n, v) == v and op_h(n, v) == v
    for v in bases["B1"]:
        ok &= op_t(n, v) == scal(-1, v) and op_h(n, v) == v
    for v in bases["B2"]:
        ok &= op_t(n, v) == v and op_h(n, v) == scal(-1, v)
    for v in bases["E"]:
        ok &= op_z(n, v) == scal(-1, v) and op_h(n, v) == v
    for v in bases["E'"]:
        ok &= op_z(n, v) == scal(-1, v) and op_h(n, v) == scal(-1, v)
    allv = [[v[ln] for ln in L] for b in bases.values() for v in b]
    ok &= rank_mod_p(allv) == 6 * n - 2            # together: a basis of the line space
    return ok


def sector_bases(n):
    return {
        "A1": [A1_vec(n, r, dd) for r, dd in A1_basis(n)],
        "B1": [B1_vec(n, r) for r in pal_basis(n)],
        "B2": [B2_vec(n, unit(n, k)) for k in range(n)],
        "E": [E_vec(n, r, dd) for r, dd in E_basis(n)],
        "E'": [op_t(n, E_vec(n, r, dd)) for r, dd in E_basis(n)],
    }


def check_actions(n):
    """Section 4: the action formulas (4.1)-(4.4), from the board."""
    ok = True
    for r, dd in A1_basis(n):
        v = A1_vec(n, r, dd)
        Mv = M_apply(n, v)
        R = sum(r)
        rr = [n * r[i] + R + 2 * sum(dd[abs(k)] for k in range(i - n + 1, i + 1)) for i in range(n)]
        dn = [(n - k) * dd[k] + 2 * rho(r, k) + T(n, dd, n - 1 - k) for k in range(n)]
        ok &= Mv == A1_vec(n, rr, dn)
    for r in pal_basis(n):
        v = B1_vec(n, r)
        ok &= M_apply(n, v) == B1_vec(n, [n * r[i] - sum(r) for i in range(n)])
    for k0 in range(n):
        dd = unit(n, k0)
        v = B2_vec(n, dd)
        ok &= M_apply(n, v) == B2_vec(n, [(n - k) * dd[k] - T(n, dd, n - 1 - k) for k in range(n)])
    for r, dd in E_basis(n):
        v = E_vec(n, r, dd)
        full = odd_d(n, dd)
        rr = [n * r[i] + 2 * sum(full[k] for k in range(i - n + 1, i + 1)) for i in range(n)]
        dn = [0] + [(n - k) * dd[k] + rho(r, k) for k in range(1, n)]
        ok &= M_apply(n, v) == E_vec(n, rr, dn)
    return ok


def check_lemma_B1(n):
    ok = True
    for r in pal_basis(n):
        v = B1_vec(n, r)
        W = sub(M_apply(n, v), scal(n, v))
        ok &= W == B1_vec(n, [-sum(r)] * n)
    return ok


def check_lemma_E(n):
    ok = True
    forms = []
    basis = E_basis(n)
    cols = []
    for r, dd in basis:
        v = E_vec(n, r, dd)
        W = sub(M_apply(n, v), scal(n, v))
        row = [W[("R", i)] for i in range(n)]
        dia = [None] + [W[("D", k)] for k in range(1, n)]
        full = odd_d(n, dd)
        ok &= all(row[i] == 2 * sum(full[k] for k in range(i - n + 1, i + 1)) for i in range(n))
        ok &= all(dia[k] == -k * dd[k] + rho(r, k) for k in range(1, n))
        ok &= all(row[i] - row[i - 1] == 2 * (dd[i] + dd[n - i]) for i in range(1, n))      # E1
        ok &= rho(r, 0) == 0 and all(rho(r, n - k) == rho(r, k) for k in range(0, n + 1))   # E2
        cols.append(row + dia[1:])
    forms = [list(x) for x in zip(*cols)]
    ok &= rank_mod_p(forms) == len(basis)          # kernel of (M - n)|E is 0
    return ok


def check_lemma_A(n):
    ok = True
    basis = A1_basis(n)
    cols = []
    for r, dd in basis:
        v = A1_vec(n, r, dd)
        W = sub(M_apply(n, v), scal(n, v))
        row = [W[("R", i)] for i in range(n)]
        dia = [W[("D", k)] for k in range(n)]
        R, D = sum(r), sum(dd)
        ok &= all(row[i] == R + 2 * sum(dd[abs(k)] for k in range(i - n + 1, i + 1)) for i in range(n))
        ok &= all(dia[k] == -k * dd[k] + 2 * rho(r, k) + T(n, dd, n - 1 - k) for k in range(n))
        ok &= all(row[i] - row[i - 1] == 2 * (dd[i] - dd[n - i]) for i in range(1, n))       # (A.1)
        ok &= row[0] == R + 2 * D                                                            # (A.2)
        ok &= all(rho(r, n - k) == R - rho(r, k) for k in range(0, n + 1))                   # (A.3)
        ok &= all(dia[k] + dia[n - k] == -k * dd[k] - (n - k) * dd[n - k] + 2 * R
                  + T(n, dd, n - 1 - k) + T(n, dd, k - 1) for k in range(1, n))              # (A.4) before (A.1)
        ok &= dia[0] == 2 * R + T(n, dd, n - 1)
        cols.append(row + dia)
    # Lemma 8 (window identity) on a basis of the subspace d_{n-k} = d_k
    for k0 in range(0, n // 2 + 1):
        dd = [0] * n
        dd[k0] = 1
        dd[(n - k0) % n] = 1
        D = sum(dd)
        Pe = [sum(dd[s] for s in range(n) if s % 2 == e) for e in (0, 1)]
        g = lambda s: dd[s % n]
        ok &= all(g(s) == dd[abs(s)] for s in range(-(n - 1), n))
        for k in range(0, n):
            lhs = T(n, dd, n - 1 - k) + T(n, dd, k - 1)
            ok &= lhs == sum(g(k + 1 - n + 2 * j) for j in range(n))
            ok &= lhs == (D if n % 2 else 2 * Pe[(k + 1) % 2])
    # reduced systems
    if n % 2:
        red = det_frac([[1, 2], [2, 1]])
        ok &= red == -3
    else:
        red3 = det_frac([[2, -n, 2], [0, n, 2], [2, n, 1]])
        red4 = det_frac([[0, n, -n, -2], [-2, -(n - 2), n, -2],
                         [1, Fr(n, 2) - 1, Fr(n, 2), Fr(1, 2)], [0, 0, n, 2]])
        ok &= red3 == -10 * n and red4 == 5 * n * n
    forms = [list(x) for x in zip(*cols)]
    ok &= rank_mod_p(forms) == len(basis)          # kernel of (M - n)|A1 is 0
    return ok


def b2_forms(n):
    """Eq(k) as a row vector in the e-variables (e_0 = d_0, e_k = 2 d_k), from the board:
    -((M - n) v)_{D_k} = k d_k + T_{n-1-k}."""
    eq = [[Fr(0)] * n for _ in range(n)]
    for k0 in range(n):
        dd = unit(n, k0)
        v = B2_vec(n, dd)
        W = sub(M_apply(n, v), scal(n, v))
        scale = Fr(1) if k0 == 0 else Fr(1, 2)     # d_k0 = e_k0 * scale
        for k in range(n):
            eq[k][k0] = -W[("D", k)] * scale
    return eq


def F_row(n, k):
    row = [Fr(0)] * n
    row[k] += k
    if k + 2 <= n - 1:
        row[k + 2] -= (k + 2)
    row[n - 1 - k] += 2
    return row


def check_lemma_B(n):
    ok = True
    eq = b2_forms(n)
    # Eq(k) = (k/2) e_k + sum_{j <= n-1-k, j = n-1-k mod 2} e_j
    for k in range(n):
        want = [Fr(0)] * n
        want[k] += Fr(k, 2)
        for j in range(0, n - k):
            if (j - (n - 1 - k)) % 2 == 0:
                want[j] += 1
        ok &= eq[k] == want
    # F_k = 2 Eq(k) - 2 Eq(k+2)  (Eq(n) = Eq(n+1) = 0)
    F = [F_row(n, k) for k in range(n)]
    for k in range(n):
        nxt = eq[k + 2] if k + 2 <= n - 1 else [Fr(0)] * n
        ok &= F[k] == [2 * a - 2 * b for a, b in zip(eq[k], nxt)]
    ones = lambda idx: [Fr(1) if j in idx else Fr(0) for j in range(n)]
    if n % 2 == 0:
        # (i) F_0..F_{n-3}  =>  e_1 = ... = e_{n-1}
        ns = nullspace_frac([F[k] for k in range(0, n - 2)], n)
        ok &= len(ns) == 2 and in_span(ns, ones({0})) and in_span(ns, ones(set(range(1, n))))
        c = ones(set(range(1, n)))
        ok &= sum(a * b for a, b in zip(F[n - 2], c)) == n                    # F_{n-2} = n c
        ok &= rank_mod_p([[int(x) for x in row] for row in F]) == n           # kernel 0
        kdim = 0
    else:
        ev = [k for k in range(n) if k % 2 == 0]
        od = [k for k in range(n) if k % 2 == 1]
        # decoupling: F_k only involves indices of the parity of k
        for k in range(n):
            ok &= all(F[k][j] == 0 for j in range(n) if (j - k) % 2)
        # (ii) even class: F_k, even 2 <= k <= n-3  =>  e_2 = ... = e_{n-1}
        ns = nullspace_frac([[F[k][j] for j in ev] for k in ev if 2 <= k <= n - 3], len(ev))
        ok &= len(ns) == 2 and in_span(ns, [Fr(1)] + [Fr(0)] * (len(ev) - 1)) \
            and in_span(ns, [Fr(0)] + [Fr(1)] * (len(ev) - 1))
        kv = [Fr(0)] * n
        kv[0] = Fr(n - 1)
        for k in ev[1:]:
            kv[k] = Fr(-2)
        ok &= all(sum(a * b for a, b in zip(F[k], kv)) == 0 for k in range(n))   # kernel vector
        ns_even = nullspace_frac([[F[k][j] for j in ev] for k in ev], len(ev))
        ok &= len(ns_even) == 1
        # (iii) odd class: F_k, odd 3 <= k <= n-4  =>  e_3 = ... = e_{n-2}
        sub_rows = [[F[k][j] for j in od] for k in od if 3 <= k <= n - 4]
        ns = nullspace_frac(sub_rows, len(od)) if sub_rows else None
        if ns is not None:
            ok &= len(ns) == 2 and in_span(ns, [Fr(1)] + [Fr(0)] * (len(od) - 1)) \
                and in_span(ns, [Fr(0)] + [Fr(1)] * (len(od) - 1))
        else:
            ok &= len(od) == 2                                                 # n = 5
        w = [Fr(0)] * n
        w[1] = Fr(-(n - 2), 2)
        for k in od[1:]:
            w[k] = Fr(1)
        res = [sum(a * b for a, b in zip(F[k], w)) for k in od]
        ok &= res[0] == Fr(-n, 2) and all(x == 0 for x in res[1:])            # only F_1 fails: -n c/2
        ns_odd = nullspace_frac([[F[k][j] for j in od] for k in od], len(od))
        ok &= len(ns_odd) == 0
        ok &= rank_mod_p([[int(x) for x in row] for row in F]) == n - 1
        kdim = 1
    return ok, kdim


def check_total(n):
    """Section 9: nullity of M - nI on the whole line space, and the eigenvectors on the board."""
    ok = True
    L = all_lines(n)
    rows = []
    for ln in L:
        v = vec(n)
        v[ln] = 1
        W = sub(M_apply(n, v), scal(n, v))
        rows.append([W[x] for x in L])            # symmetric matrix: rows = columns
    expected = (n - 2) // 2 if n % 2 == 0 else (n + 1) // 2
    rk = rank_mod_p(rows)
    ok &= rk == 6 * n - 2 - expected               # nullity <= expected
    # explicit kernel vectors: B1 (palindromic r, zero sum), and for odd n the B2 vector
    kern = []
    pb = pal_basis(n)
    for r in pb[1:]:
        w0, w1 = sum(pb[0]), sum(r)
        rr = [w0 * x - w1 * y for x, y in zip(r, pb[0])]     # zero-sum palindromic
        kern.append(B1_vec(n, rr))
    if n % 2:
        dd = [0] * n
        dd[0] = n - 1
        for k in range(2, n, 2):
            dd[k] = -1
        kern.append(B2_vec(n, dd))
    ok &= len(kern) == expected
    for v in kern:
        ok &= is_zero(sub(M_apply(n, v), scal(n, v)))
    ok &= rank_mod_p([[v[x] for x in L] for v in kern]) == expected      # independent
    return ok, expected, kern


def check_eigvecs(n, kern):
    """Corollary: x = N v is an eigenvector of the adjacency matrix for n - 4, with the stated shape."""
    ok = True
    xs = []
    for idx, v in enumerate(kern):
        x = N_apply(n, v)
        Ax = A_apply(n, x)
        ok &= all(Ax[s] == (n - 4) * x[s] for s in x) and any(x.values())
        if n % 2 and idx == len(kern) - 1:
            ok &= all(x[(i, j)] == n * ((1 if i == j else 0) - (1 if i + j == n - 1 else 0))
                      for (i, j) in x)
        else:
            ok &= all(x[(i, j)] == v[("R", i)] - v[("R", j)] for (i, j) in x)
        xs.append([x[(i, j)] for i in range(n) for j in range(n)])
    ok &= rank_mod_p(xs) == len(kern)
    return ok


def check_G(q):
    """Appendix: G_q = diag(0..q) + [i+j<=q]; elimination from index q down; pivots; kernel vector."""
    size = q + 1
    S = [[Fr((i if i == j else 0) + (1 if i + j <= q else 0)) for j in range(size)] for i in range(size)]
    G = [row[:] for row in S]
    m = q // 2
    ok = True
    for k in range(q, -1, -1):
        pk = S[k][k]
        if k <= m:
            gam = S[k][k] - k
            ok &= gam == Fr(k, q - k)
            ok &= all(S[a][b] == (a if a == b else 0) + (S[max(a, b)][max(a, b)] - max(a, b))
                      for a in range(k + 1) for b in range(k + 1))
            ok &= pk == Fr(k * (q + 1 - k), q - k)
        else:
            ok &= pk == k and all(S[k][b] == (1 if b <= q - k else 0) for b in range(k))
        if k > 0:
            ok &= pk > 0
            for a in range(k):
                f = S[a][k] / pk
                if f:
                    S[a] = [x - f * y for x, y in zip(S[a], S[k])]
        else:
            ok &= pk == 0
    kap = [Fr(q)] + [Fr(-1)] * q
    ok &= all(sum(G[i][j] * kap[j] for j in range(size)) == 0 for i in range(size))
    return ok


def check_block_form(n):
    """Appendix (odd n): in u_0 = d_0, u_l = 2 d_{2l}, w_l = 2 d_{2l+1} the system Eq is G_p u = 0 and
    (1/2)(I + 2 G_{p-1}) w = 0."""
    if n % 2 == 0:
        return True
    p = (n - 1) // 2
    eq = b2_forms(n)       # already in e-variables = (u, w) interleaved
    ok = True
    for i in range(p + 1):
        ok &= all(eq[2 * i][2 * l] == (i if l == i else 0) + (1 if i + l <= p else 0) for l in range(p + 1))
        ok &= all(eq[2 * i][2 * l + 1] == 0 for l in range(p))
    for i in range(p):
        ok &= all(eq[2 * i + 1][2 * l + 1] == Fr((1 if l == i else 0) + 2 * ((i if l == i else 0)
                  + (1 if i + l <= p - 1 else 0)), 2) for l in range(p))
        ok &= all(eq[2 * i + 1][2 * l] == 0 for l in range(p + 1))
    return ok


def check_even_shooting(n):
    """Appendix (even n): E_j, Q_j closed form."""
    if n % 2:
        return True
    p = n // 2
    E, Q = [Fr(1)], [Fr(0)]
    for j in range(p):
        Q.append(Q[j] + 2 * E[j] / (2 * p - 1 - 2 * j))
        if j + 1 <= p - 1:
            E.append(E[j] - Q[j + 1] / (j + 1))
    ok = all(E[j] == Fr(2 * p - 1 - 2 * j, 2 * p - 1) for j in range(p))
    ok &= all(Q[j] == Fr(2 * j, 2 * p - 1) for j in range(p + 1))
    return ok


def run(nmin, nmax):
    allok = True
    for n in range(nmin, nmax + 1):
        t0 = time.time()
        res = {}
        res["reduction"] = check_reduction(n) if n <= 24 else None
        res["symmetry"] = check_symmetry(n)
        res["actions"] = check_actions(n)
        res["B1"] = check_lemma_B1(n)
        res["E"] = check_lemma_E(n)
        res["A"] = check_lemma_A(n)
        okB, kdim = check_lemma_B(n)
        res["B"] = okB
        okT, expected, kern = check_total(n)
        res["total"] = okT
        res["eigvec"] = check_eigvecs(n, kern) if n <= 16 else None
        res["appx"] = check_block_form(n) and check_even_shooting(n)
        good = all(v for v in res.values() if v is not None)
        allok &= good
        flags = " ".join(f"{k}:{'ok' if v else ('--' if v is None else 'FAIL')}" for k, v in res.items())
        print(f"n={n}: {flags} | null(B2-n)={kdim} | null(M-nI)={expected} "
              f"({'(n-2)/2' if n % 2 == 0 else '(n+1)/2'}) | {'PASS' if good else 'FAIL'} "
              f"({time.time() - t0:.1f}s)", flush=True)
    gq = all(check_G(q) for q in range(1, 61))
    allok &= gq
    print(f"Appendix Lemma G, q = 1..60: {'ok' if gq else 'FAIL'}")
    print("PROVER REPLAY: ALL PASS" if allok else "PROVER REPLAY: FAILURE")
    return 0 if allok else 1


def small():
    for n in (4, 5):
        print(f"--- n = {n}: B2 system in e-variables, rows F_0..F_{n - 1}")
        for k in range(n):
            print("   F_%d:" % k, [str(x) for x in F_row(n, k)])
        eq = b2_forms(n)
        print("   Eq rows from the board (e-variables):")
        for k in range(n):
            print("   Eq(%d):" % k, [str(x) for x in eq[k]])
        okB, kdim = check_lemma_B(n)
        print(f"   Lemma B replay: {'ok' if okB else 'FAIL'}; kernel dim {kdim}")
        print(f"   Lemma A replay: {'ok' if check_lemma_A(n) else 'FAIL'};"
              f" Lemma E: {'ok' if check_lemma_E(n) else 'FAIL'};"
              f" Lemma B1: {'ok' if check_lemma_B1(n) else 'FAIL'}")
        okT, expected, kern = check_total(n)
        print(f"   null(M - nI) = {expected}: {'ok' if okT else 'FAIL'};"
              f" eigenvectors on the board: {'ok' if check_eigvecs(n, kern) else 'FAIL'}")
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a == ["small"]:
        sys.exit(small())
    lo, hi = (int(a[0]), int(a[1])) if len(a) == 2 else (4, 40)
    sys.exit(run(lo, hi))
