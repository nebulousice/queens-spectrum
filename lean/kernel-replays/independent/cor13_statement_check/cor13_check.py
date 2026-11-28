"""Independent exact check of Corollary 13 (queens eigenspace), Checker 2026-11-27.

Pure Python, fractions.Fraction only. Builds the n-Queens adjacency matrix from scratch
(0-indexed squares (i,j), distinct squares adjacent iff same row, column, i-j, or i+j),
computes ker(A-(n-4)I) by exact Gaussian elimination, and compares it with the span of the
family in the Lean statement `queens_eigenspace`:
    x(i,j) = r_i - r_j + g*([i=j] - [i+j=n-1]),  r palindromic, g = 0 for even n.
Also checks that the two side conditions are needed (they are not vacuous / not weakenings).
"""
from fractions import Fraction as F
import sys, itertools


def adj(n):
    sq = [(i, j) for i in range(n) for j in range(n)]
    idx = {s: k for k, s in enumerate(sq)}
    A = [[0] * (n * n) for _ in range(n * n)]
    for (a, b) in sq:
        for (c, d) in sq:
            if (a, b) != (c, d) and (a == c or b == d or a - b == c - d or a + b == c + d):
                A[idx[(a, b)]][idx[(c, d)]] = 1
    return sq, idx, A


def rref(rows, ncols):
    m = [list(map(F, r)) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((k for k in range(r, len(m)) if m[k][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        inv = 1 / m[r][c]
        m[r] = [v * inv for v in m[r]]
        for k in range(len(m)):
            if k != r and m[k][c] != 0:
                f = m[k][c]
                m[k] = [a - f * b for a, b in zip(m[k], m[r])]
        piv.append(c)
        r += 1
        if r == len(m):
            break
    return m[:r], piv


def rank(rows, ncols):
    return len(rref(rows, ncols)[1]) if rows else 0


def nullspace(M, ncols):
    R, piv = rref(M, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [F(0)] * ncols
        v[f] = F(1)
        for row, p in zip(R, piv):
            v[p] = -row[f]
        basis.append(v)
    return basis


def matvec(A, v):
    return [sum(a * x for a, x in zip(row, v)) for row in A]


def family_vec(n, sq, r, g):
    return [F(r[i]) - F(r[j]) + F(g) * ((1 if i == j else 0) - (1 if i + j == n - 1 else 0))
            for (i, j) in sq]


def main(lo, hi):
    ok_all = True
    for n in range(lo, hi + 1):
        sq, idx, A = adj(n)
        N2 = n * n
        lam = n - 4
        B = [[A[a][b] - (lam if a == b else 0) for b in range(N2)] for a in range(N2)]
        ker = nullspace(B, N2)
        dimker = len(ker)
        expected = (n - 2) // 2 if n % 2 == 0 else (n + 1) // 2
        # Lean family generators: r = e_k + e_{n-1-k} (k < ceil(n/2)) spans palindromic r;
        # plus g-term for odd n only.
        gens = []
        for k in range((n + 1) // 2):
            r = [0] * n
            r[k] += 1
            if n - 1 - k != k:
                r[n - 1 - k] += 1
            gens.append(family_vec(n, sq, r, 0))
        if n % 2 == 1:
            gens.append(family_vec(n, sq, [0] * n, 1))
        # (a) family is inside the eigenspace
        inside = all(all(x == 0 for x in matvec(B, v)) for v in gens)
        rf = rank(gens, N2)
        # (b) eigenspace inside span(family): rank(family + ker) == rank(family)
        ru = rank(gens + ker, N2)
        equal = inside and ru == rf == dimker
        # (c) side conditions are needed
        # even n: g-term NOT in eigenspace; odd n: the g-term is (already in gens).
        gterm = family_vec(n, sq, [0] * n, 1)
        g_in = all(x == 0 for x in matvec(B, gterm))
        g_ok = (g_in == (n % 2 == 1))
        # non-palindromic r = e_0 gives a vector NOT in the eigenspace
        e0 = [1] + [0] * (n - 1)
        np_in = all(x == 0 for x in matvec(B, family_vec(n, sq, e0, 0)))
        # palindromic r with g = 0 always in (sanity) - covered by inside.
        line = (f"n={n:2d} dim ker(A-(n-4)I)={dimker} expected={expected} rank(family)={rf} "
                f"rank(family+ker)={ru} family_in_eigenspace={inside} "
                f"gterm_in_eigenspace={g_in} (should be {n % 2 == 1}) "
                f"nonpalindromic_e0_in={np_in} (should be False)")
        good = equal and dimker == expected and g_ok and not np_in
        print(line, "OK" if good else "FAIL")
        ok_all &= good
    print("COR13 CHECK:", "ALL PASS" if ok_all else "FAILURE")
    return 0 if ok_all else 1


if __name__ == "__main__":
    lo, hi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (4, 10)
    sys.exit(main(lo, hi))
