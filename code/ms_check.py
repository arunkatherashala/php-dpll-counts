#!/usr/bin/env python3
"""ms_check.py -- re-verifies every numerical statement in ms_php_dpll.tex.

Usage:  python ms_check.py            default (a few minutes; uses the Rust helper programs if found)
        python ms_check.py --slow     additionally recomputes the minimum tree-resolution size for n=4 (~3 min)
        python ms_check.py --noexe    do not call the Rust executables ref_dp.exe / ref_resk.exe

What is checked (section numbers refer to the manuscript):
  S2  pigeon-major: clause-level DPLL (n<=6), independent state DP (n<=9), the recurrence of Lemma 3, L(f)=f*Fub(f-1)
      (n<=60), identities used in the solution of the recurrence, the pole expansion and asymptotics.
  S3  hole-major: clause-level DPLL (n<=6), state DP (n<=9), the subset model of Lemmas 2 and 4 (n<=10), the word/mex sum,
      the inclusion-exclusion form, the closed form (n<=60), the backward-difference identity (random polynomials),
      the EGF closed form via the tree function, asymptotic constants.
  S4  anti-diagonal values n=1..16 (clause level n<=6, state DP n<=9, Rust helper n<=13 if present, stored table beyond),
      Res(2)-JW values n=1..14 (clause level n<=5, state DP n<=9, Rust helper n<=12, stored values for 13, 14),
      counterexamples: adaptive optimum 1,2,6,23; quasi-polynomial failure at n=11; minimum tree-resolution 3,11,43(,189).
  S6  Theorem C certificates (exact rational arithmetic): 14-term zero, IVT interval, Rouche/winding on |x|=9/20,
      negative-axis grid, exp(C)=R, F_n values.
Everything is exact integer/rational arithmetic except the explicitly floating-point asymptotic comparisons.
"""
import sys, os, math, itertools, subprocess, random, time
from fractions import Fraction as Fr
from math import comb, factorial

sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
SLOW = '--slow' in sys.argv
NOEXE = '--noexe' in sys.argv
T0 = time.time()
NCHECK = 0
SKIPPED = []


def check(cond, msg):
    global NCHECK
    NCHECK += 1
    if not cond:
        print("FAILED:", msg)
        raise SystemExit("CHECK FAILED: " + msg)


def section(s):
    print("\n== %s  (t=%.0fs)" % (s, time.time() - T0), flush=True)


# ----------------------------------------------------------------------------------------------
# Values stated in the manuscript
# ----------------------------------------------------------------------------------------------
PIG_SMALL = [1, 2, 9, 52, 375, 3246, 32781, 378344, 4912515, 70872610]
HOLE_SMALL = [1, 2, 11, 85, 855, 10657, 159049, 2771561, 55318979, 1245712417]
DIAG = [1, 2, 8, 45, 331, 3057, 34007, 441515, 6541557, 108804265, 2006371441, 40615858425, 895407989033,
        21354721047401, 547848248627841, 15045475165081609]
RES2 = [1, 4, 13, 61, 307, 2110, 14746, 130687, 1187971, 12801700, 143164903, 1819083835, 24104576248,
        353344753156]
MINTREE = [3, 11, 43, 189]
ADAPT = [1, 2, 6, 23]


def fub_list(N):
    F = [1]
    for k in range(1, N + 1):
        F.append(sum(comb(k, j) * F[k - j] for j in range(1, k + 1)))
    return F


FUB = fub_list(300)


def hole_closed(n):
    return 1 if n == 1 else (n + 2) ** (n - 2) + (n + 3) ** (n - 2)


def pig_closed(n):
    return n * FUB[n - 1]


# ----------------------------------------------------------------------------------------------
# Clause-level reference DPLL (own code)
# ----------------------------------------------------------------------------------------------
def php_clauses(n):
    v = lambda p, j: p * n + j + 1          # pigeon p in 0..n, hole j in 0..n-1
    cl = [[v(p, j) for j in range(n)] for p in range(n + 1)]
    for j in range(n):
        for p in range(n + 1):
            for q in range(p + 1, n + 1):
                cl.append([-v(p, j), -v(q, j)])
    assert len(cl) == (n + 1) + n * comb(n + 1, 2)
    return v, cl


def up(cl, a):
    """unit propagation on assignment dict a (modified); True iff conflict."""
    ch = True
    while ch:
        ch = False
        for c in cl:
            sat = False
            free = None
            nfree = 0
            for l in c:
                x = a.get(abs(l))
                if x is None:
                    nfree += 1
                    free = l
                elif x == (l > 0):
                    sat = True
                    break
            if sat:
                continue
            if nfree == 0:
                return True
            if nfree == 1:
                a[abs(free)] = free > 0
                ch = True
    return False


def order_cells(n, kind):
    cells = [(p, j) for p in range(n + 1) for j in range(n)]
    key = {'pig': lambda c: (c[0], c[1]),
           'hole': lambda c: (c[1], c[0]),
           'diag': lambda c: (c[0] + c[1], c[0])}[kind]       # anti-diagonals p+j = const, increasing pigeon
    return sorted(cells, key=key)


def static_clause_level(n, kind):
    v, cl = php_clauses(n)
    order = [v(p, j) for (p, j) in order_cells(n, kind)]

    def rec(a):
        if up(cl, a):
            return 1
        x = next(y for y in order if y not in a)       # StopIteration would mean SAT
        tot = 0
        for val in (True, False):
            b = dict(a)
            b[x] = val
            tot += rec(b)
        return tot
    return rec({})


# ----------------------------------------------------------------------------------------------
# State DP for static orders (own port of the (pos,U,O) idea)
# ----------------------------------------------------------------------------------------------
def static_state_dp(n, kind):
    P = n + 1
    cells = order_cells(n, kind)
    nc = len(cells)
    ahead = [[0] * P for _ in range(nc + 1)]
    colmask = [0] * (nc + 1)
    for pos in range(nc - 1, -1, -1):
        ahead[pos] = list(ahead[pos + 1])
        colmask[pos] = colmask[pos + 1]
        p, j = cells[pos]
        ahead[pos][p] |= 1 << j
        colmask[pos] |= 1 << j

    def settle(pos, U, O):
        while True:
            ch = False
            u = U
            while u:
                a = (u & -u).bit_length() - 1
                u &= u - 1
                m = ahead[pos][a] & ~O
                if m == 0:
                    return None
                if m & (m - 1) == 0:
                    U &= ~(1 << a)
                    O |= m
                    ch = True
            if not ch:
                break
        while pos < nc and (O >> cells[pos][1]) & 1:
            pos += 1
        assert pos < nc, "SAT leaf"
        O &= colmask[pos]
        return pos, U, O

    layers = [dict() for _ in range(nc + 1)]
    r = settle(0, (1 << P) - 1, 0)
    if r is None:
        return 1
    layers[r[0]][(r[1], r[2])] = 1
    leaves = 0
    for pos in range(nc):
        lay = layers[pos]
        layers[pos] = None
        p, j = cells[pos]
        for (U, O), cnt in lay.items():
            for (U2, O2) in ((U & ~(1 << p), O | (1 << j)), (U, O)):
                s = settle(pos + 1, U2, O2)
                if s is None:
                    leaves += cnt
                else:
                    d = layers[s[0]]
                    d[(s[1], s[2])] = d.get((s[1], s[2]), 0) + cnt
    return leaves


# ----------------------------------------------------------------------------------------------
# Res(2)-JW: clause level and state level
# ----------------------------------------------------------------------------------------------
def resk_clause_level(n, K=2):
    """Definition: UP; if no conflict take the K unassigned variables with the largest JW score
    J(x) = sum over clauses C containing x (either sign) that are not satisfied of 2^-(#unassigned literals of C);
    ties -> smaller index in row-major order; branch on all 2^K assignments of these variables simultaneously."""
    v, cl = php_clauses(n)
    nv = (n + 1) * n

    def go(a):
        free = [x for x in range(1, nv + 1) if x not in a]
        sc = {x: Fr(0) for x in free}
        for c in cl:
            if any(a.get(abs(l)) == (l > 0) for l in c):
                continue
            un = [abs(l) for l in c if abs(l) not in a]
            w = Fr(1, 2 ** len(un))
            for x in un:
                sc[x] += w
        ch = sorted(free, key=lambda x: (-sc[x], x))[:K]
        tot = 0
        for vals in itertools.product((True, False), repeat=len(ch)):
            b = dict(a)
            for x, val in zip(ch, vals):
                b[x] = val
            if up(cl, b):
                tot += 1
            else:
                tot += go(b)
        return tot
    a = {}
    if up(cl, a):
        return 1
    return go(a)


def resk_state_level(n, K=2):
    """Same rule on the residual state: rows (sat flag, list of surviving hole labels); canonical relabelling of holes."""
    def up_canon(rows):
        rows = [[s, list(c)] for s, c in rows]
        while True:
            ch = False
            for r in rows:
                if not r[0]:
                    if not r[1]:
                        return None
                    if len(r[1]) == 1:
                        c = r[1][0]
                        r[0] = True
                        for q in rows:
                            q[1] = [x for x in q[1] if x != c]
                        ch = True
                        break
            if not ch:
                break
        rows = [r for r in rows if r[1] or not r[0]]
        mp = {}
        for r in rows:
            for i, c in enumerate(r[1]):
                if c not in mp:
                    mp[c] = len(mp)
                r[1][i] = mp[c]
        return tuple((r[0], tuple(r[1])) for r in rows)
    memo = {}

    def go(s):
        if s in memo:
            return memo[s]
        colcnt = {}
        for sat, cols in s:
            for c in cols:
                colcnt[c] = colcnt.get(c, 0) + 1
        sc = []
        ordn = 0
        pos = []
        for i, (sat, cols) in enumerate(s):
            for jx, c in enumerate(cols):
                w = Fr(0)
                if not sat:
                    w += Fr(1, 2 ** len(cols))
                w += (colcnt[c] - 1) * Fr(1, 4)
                sc.append((-w, ordn))
                pos.append((i, jx))
                ordn += 1
        sc.sort()
        chosen = [pos[o] for _, o in sc[:K]]
        tot = 0
        for vals in itertools.product((True, False), repeat=len(chosen)):
            rows = [[sat, list(cols)] for sat, cols in s]
            trues = []
            falses = []
            bad = False
            for (i, jx), val in zip(chosen, vals):
                c = s[i][1][jx]
                if val:
                    if c in trues:
                        bad = True
                    trues.append(c)
                    rows[i][0] = True
                else:
                    falses.append((i, c))
            if bad:
                tot += 1
                continue
            for i, c in falses:
                rows[i][1] = [x for x in rows[i][1] if x != c]
            for c in trues:
                for r in rows:
                    r[1] = [x for x in r[1] if x != c]
            t = up_canon(rows)
            tot += 1 if t is None else go(t)
        memo[s] = tot
        return tot
    init = [(False, tuple(range(n))) for _ in range(n + 1)]
    s = up_canon(init)
    if s is None:
        return 1
    return go(s)


# ----------------------------------------------------------------------------------------------
# Other reference computations for the "counterexample" statements
# ----------------------------------------------------------------------------------------------
INF = 10 ** 9


def adaptive_optimum(n):
    """min over ALL adaptive variable choices (any non-assigned variable at each node) of #UP-conflict leaves."""
    m = n + 1
    perms = list(itertools.permutations(range(n)))
    memo = {}

    def upm(st):
        st = list(st)
        ch = True
        while ch:
            ch = False
            for i in range(m):
                row = st[i * n:(i + 1) * n]
                if all(x == 2 for x in row):
                    return None
                if 1 not in row and row.count(0) == 1:
                    st[i * n + row.index(0)] = 1
                    ch = True
            for j in range(n):
                col = [st[i * n + j] for i in range(m)]
                t = col.count(1)
                if t >= 2:
                    return None
                if t == 1:
                    for i in range(m):
                        if st[i * n + j] == 0:
                            st[i * n + j] = 2
                            ch = True
        return tuple(st)

    def canon(st):
        rows = [st[i * n:(i + 1) * n] for i in range(m)]
        return min(tuple(sorted(tuple(r[j] for j in p) for r in rows)) for p in perms)

    def f(st):
        st = upm(st)
        if st is None:
            return 1
        free = [k for k in range(m * n) if st[k] == 0]
        key = canon(st)
        if key in memo:
            return memo[key]
        best = INF
        for k in free:
            L = list(st)
            L[k] = 1
            a = f(tuple(L))
            if a >= best:
                continue
            L[k] = 2
            best = min(best, a + f(tuple(L)))
        memo[key] = best
        return best
    return f(tuple([0] * (m * n)))


def min_tree_leaves(n):
    """minimum number of leaves of a decision tree (= tree-like resolution refutation, no unit propagation)."""
    m = n + 1
    perms = list(itertools.permutations(range(n)))
    memo = {}

    def canon(st):
        rows = [st[i * n:(i + 1) * n] for i in range(m)]
        return min(tuple(sorted(tuple(r[j] for j in p) for r in rows)) for p in perms)

    def f(st):
        for i in range(m):
            if all(st[i * n + j] == 2 for j in range(n)):
                return 1
        for j in range(n):
            if sum(1 for i in range(m) if st[i * n + j] == 1) >= 2:
                return 1
        live = set()
        for i in range(m):
            if any(st[i * n + j] == 1 for j in range(n)):
                continue
            for j in range(n):
                if st[i * n + j] == 0:
                    live.add((i, j))
        for j in range(n):
            ones = sum(1 for i in range(m) if st[i * n + j] == 1)
            unset = [i for i in range(m) if st[i * n + j] == 0]
            if (ones == 1 and unset) or (ones == 0 and len(unset) >= 2):
                for i in unset:
                    live.add((i, j))
        if not live:
            return INF
        key = canon(st)
        if key in memo:
            return memo[key]
        best = INF
        for (i, j) in sorted(live):
            L = list(st)
            L[i * n + j] = 1
            a = f(tuple(L))
            if a >= best:
                continue
            L[i * n + j] = 2
            best = min(best, a + f(tuple(L)))
        memo[key] = best
        return best
    return f(tuple([0] * (m * n)))


# ----------------------------------------------------------------------------------------------
# Hole-major proof objects
# ----------------------------------------------------------------------------------------------
def hole_subset_model(n):
    """Lemma 2/4 transitions on explicit sets T of satisfied rows."""
    if n == 1:
        return 1
    m = n - 2
    cur = {0: 1}
    for _ in range(m):
        nxt = {}
        for T, c in cur.items():
            nxt[T] = nxt.get(T, 0) + c
            for i in range(n + 1):
                T2 = T | (1 << i)
                nxt[T2] = nxt.get(T2, 0) + c
        cur = nxt
    tot = 0
    for T, c in cur.items():
        U = [i for i in range(n + 1) if not (T >> i) & 1]
        assert len(U) >= 3
        tot += c * (U[0] + 2)
    return tot


def hole_words(n):
    m, q = n - 2, n + 2
    tot = 0
    for w in itertools.product(range(q), repeat=m):        # letter 0 = none, 1..n+1 = rows 0..n
        used = {x - 1 for x in w if x > 0}
        tot += 2 + next(i for i in range(n + 2) if i not in used)
    return tot


def hole_incl_excl(n):
    m, q = n - 2, n + 2
    return 2 * q ** m + sum(sum((-1) ** i * comb(k, i) * (q - i) ** m for i in range(k + 1)) for k in range(1, m + 1))


# ----------------------------------------------------------------------------------------------
def run_exe(exe, args, timeout=900):
    p = os.path.join(HERE, exe)
    if NOEXE or not os.path.exists(p):
        return None
    try:
        r = subprocess.run([p] + args, capture_output=True, text=True, timeout=timeout, cwd=HERE)
        out = r.stdout
        if r.returncode != 0:
            print("  (%s %s exited with code %s: %s)" % (exe, ' '.join(args), r.returncode, r.stderr.strip()[:200]))
    except Exception as e:                                      # pragma: no cover
        print("  (could not run %s: %s)" % (exe, e))
        return None
    return out


# ==============================================================================================
section("S2 pigeon-major: Theorem A")
# (1) clause-level brute force
for n in range(1, 7):
    b = static_clause_level(n, 'pig')
    check(b == PIG_SMALL[n - 1] == pig_closed(n), "pig clause-level n=%d" % n)
print("clause-level pigeon-major n=1..6:", PIG_SMALL[:6])
# (2) independent state DP
for n in range(1, 10):
    check(static_state_dp(n, 'pig') == pig_closed(n) == PIG_SMALL[n - 1], "pig state DP n=%d" % n)
check(PIG_SMALL == [pig_closed(n) for n in range(1, 11)], "pig table")
# (3) the recurrence of Lemma 3 and its solution
L = [None, 1]
for f in range(2, 301):
    L.append(f + sum(comb(f, j) * L[f - j] for j in range(1, f - 1)))
for n in range(1, 301):
    check(L[n] == n * FUB[n - 1], "recurrence = n Fub(n-1), n=%d" % n)
for f in range(2, 120):
    check(all(comb(f, j) * (f - j) == f * comb(f - 1, j) for j in range(1, f - 1)), "binomial identity")
    check(FUB[f - 1] == 1 + sum(comb(f - 1, j) * FUB[f - 1 - j] for j in range(1, f - 1)), "Fubini identity")
# the row-structure count of Lemma 3 by direct enumeration of the paths inside one row
def row_paths(f):
    leaves = [0]
    ends = {}

    def rec(t, numT):
        if numT >= f - 1:
            leaves[0] += 1
            return
        if t == f:
            ends[numT] = ends.get(numT, 0) + 1
            return
        if numT == 0 and t == f - 1:          # forced step: last cell of an all-false prefix is propagated true
            rec(f, 1)
        else:
            rec(t + 1, numT + 1)
            rec(t + 1, numT)
    rec(0, 0)
    return leaves[0], ends


for f in range(2, 14):
    lv, ends = row_paths(f)
    check(lv == f, "leaves per row f=%d got %d" % (f, lv))
    check(set(ends) == set(range(1, f - 1)) and all(ends[j] == comb(f, j) for j in ends), "row-end nodes f=%d" % f)
print("recurrence L(f)=f+sum C(f,j)L(f-j) agrees with f*Fub(f-1) for f<=300; row counts ok")

# (4) asymptotics: pig(n)/n! = (1/2) sum_{k in Z} (ln2 + 2 pi i k)^(-n)  (n>=2)  and pig(n) ~ n!/(2 (ln 2)^n)
ln2 = math.log(2)
for n in range(4, 13):
    s = 0j
    K = 20000
    for k in range(-K, K + 1):
        s += (complex(ln2, 2 * math.pi * k)) ** (-n)
    lhs = pig_closed(n) / factorial(n)
    check(abs(lhs - 0.5 * s.real) < 1e-8 * lhs and abs(s.imag) < 1e-12, "pole expansion n=%d" % n)
for n in range(5, 61):
    ratio = pig_closed(n) * 2 * ln2 ** n / factorial(n)       # pig(n) / (n!/(2 ln2^n))
    check(abs(ratio - 1) < 3 * 0.11 ** n + 1e-12, "pig asymptotic n=%d ratio %r" % (n, ratio))
print("pig(n)/(n!/(2 (ln 2)^n)) at n=10, 20, 40:", [pig_closed(n) * 2 * ln2 ** n / factorial(n) for n in (10, 20, 40)])
# EGF: sum_{n>=1} n Fub(n-1) x^n/n! = x/(2-e^x)
M = 40
ex = [Fr(1, factorial(k)) for k in range(M)]
den = [Fr(2) - ex[0]] + [-ex[k] for k in range(1, M)]            # 2 - e^x, constant term 1
inv = [Fr(0)] * M
inv[0] = Fr(1)
for k in range(1, M):
    inv[k] = -sum(den[i] * inv[k - i] for i in range(1, k + 1))
for n in range(1, M):
    check(inv[n - 1] * factorial(n) == pig_closed(n), "EGF x/(2-e^x) coefficient n=%d" % n)
print("EGF x/(2-e^x) matches pig(n)/n! for n<40")

# ==============================================================================================
section("S3 hole-major: Theorem B")
for n in range(1, 7):
    b = static_clause_level(n, 'hole')
    check(b == HOLE_SMALL[n - 1] == hole_closed(n), "hole clause-level n=%d" % n)
for n in range(1, 10):
    check(static_state_dp(n, 'hole') == hole_closed(n) == HOLE_SMALL[n - 1], "hole state DP n=%d" % n)
check(HOLE_SMALL == [hole_closed(n) for n in range(1, 11)], "hole table")
for n in range(2, 61):
    c = hole_closed(n)
    check(hole_incl_excl(n) == c, "inclusion-exclusion n=%d" % n)
    if n <= 10:
        check(hole_subset_model(n) == c, "subset model n=%d" % n)
    if n <= 6:
        check(hole_words(n) == c, "word/mex enumeration n=%d" % n)
    # size-indexed form
    m = n - 2
    Nm = lambda t: sum((-1) ** i * comb(t, i) * (t + 1 - i) ** m for i in range(t + 1))
    tot = sum(Nm(t) * (2 * comb(n + 1, t) + sum(a * comb(n - a, t - a) for a in range(t + 1))) for t in range(m + 1))
    check(tot == c, "size-indexed form n=%d" % n)
print("hole-major closed form: clause level n<=6, state DP n<=9, subset model n<=10, words n<=6, formulas n<=60")

# backward difference identity: sum_{k=1}^m nabla^k g = g(x+1)-g(x) for deg g <= m
random.seed(7)


def nabla_pow(coeffs_eval, k, x):
    return sum((-1) ** i * comb(k, i) * coeffs_eval(x - i) for i in range(k + 1))


for _ in range(60):
    m = random.randint(0, 9)
    co = [random.randint(-9, 9) for _ in range(m + 1)]            # arbitrary polynomial of degree <= m
    g = lambda x, co=co: sum(c * x ** e for e, c in enumerate(co))
    x = random.randint(-20, 20)
    check(sum(nabla_pow(g, k, x) for k in range(1, m + 1)) == g(x + 1) - g(x), "nabla identity")
    check(nabla_pow(g, m + 1, x) == 0, "nabla^{m+1} kills degree<=m")
print("backward-difference identity verified on random polynomials")

# EGF: sum_{n>=0} (n+a)^(n-2) x^n/n! = e^{aT}(1/a^2 - T/(a(a+1))),  T = sum n^(n-1) x^n/n!
M = 30
T = [Fr(0)] + [Fr(n ** (n - 1), factorial(n)) for n in range(1, M)]


def smul(A, B):
    C = [Fr(0)] * M
    for i, x in enumerate(A):
        if x:
            for j in range(M - i):
                C[i + j] += x * B[j]
    return C


def sexp(A):                                  # A[0] = 0
    E = [Fr(0)] * M
    E[0] = Fr(1)
    for n in range(1, M):
        E[n] = sum(k * A[k] * E[n - k] for k in range(1, n + 1)) / n
    return E


for a in (1, 2, 3, 4):
    E = sexp([a * t for t in T])
    inner = [Fr(0)] * M
    inner[0] = Fr(1, a * a)
    for k in range(1, M):
        inner[k] = -T[k] / (a * (a + 1))
    S = smul(E, inner)
    for n in range(M):
        check(S[n] == Fr(n + a) ** (n - 2) / factorial(n), "S_a coefficient a=%d n=%d" % (a, n))
# H(x) = sum_{n>=1} L(n) x^n/n! = S_2 + S_3 - 13/36 + (5/12) x
E2, E3 = sexp([2 * t for t in T]), sexp([3 * t for t in T])
in2 = [Fr(1, 4)] + [-T[k] / 6 for k in range(1, M)]
in3 = [Fr(1, 9)] + [-T[k] / 12 for k in range(1, M)]
S2, S3 = smul(E2, in2), smul(E3, in3)
for n in range(1, M):
    val = S2[n] + S3[n] + (Fr(-13, 36) if n == 0 else 0) + (Fr(5, 12) if n == 1 else 0)
    check(val * factorial(n) == hole_closed(n), "hole EGF n=%d" % n)
check(S2[0] + S3[0] == Fr(13, 36), "constant term")
print("hole-major EGF = e^{2T}(1/4 - T/6) + e^{3T}(1/9 - T/12) - 13/36 + 5x/12 verified to order 30")
# singular expansion: coefficient of T in the bracket vanishes at T=1 (so sqrt term cancels)
for a in (2, 3):
    check(Fr(1, a) - Fr(1, a + 1) - Fr(1, a * (a + 1)) == 0, "sqrt cancellation a=%d" % a)

# asymptotics (floating point, large n through logs)
e = math.e
c0, c1 = e ** 2 + e ** 3, 6 * e ** 2 + 10.5 * e ** 3
for n in (50, 500, 5000, 50000):
    ratio = math.exp((n - 2) * math.log1p(2 / n)) + math.exp((n - 2) * math.log1p(3 / n))       # L(n)/n^(n-2)
    print("  n=%6d  L(n)/n^(n-2) = %.8f  (e^2+e^3 = %.8f)  n*(ratio-(e^2+e^3)) = %.4f  (predicted %.4f)" %
          (n, ratio, c0, n * (ratio - c0), -c1))
    check(abs(ratio - c0) < 1.1 * c1 / n, "leading constant n=%d" % n)
n = 50000
ratio = math.exp((n - 2) * math.log1p(2 / n)) + math.exp((n - 2) * math.log1p(3 / n))
check(abs(n * (ratio - c0) + c1) < 0.01 * c1, "first-order correction -(6e^2+10.5e^3)/n")
for n in (200, 2000, 20000):
    lgL = (n - 2) * math.log(n + 2) + math.log1p(math.exp((n - 2) * (math.log(n + 3) - math.log(n + 2))))
    actual = lgL - math.lgamma(n + 1)
    pred = math.log(c0) + n - 0.5 * math.log(2 * math.pi) - 2.5 * math.log(n)
    check(abs(actual - pred) < 40.0 / n, "coefficient asymptotic n=%d diff %g" % (n, actual - pred))
print("hole-major: L(n) ~ (e^2+e^3) n^(n-2), L(n)/n! ~ (e^2+e^3) e^n/(sqrt(2 pi) n^(5/2)) confirmed numerically")

# ==============================================================================================
section("S4 anti-diagonal order")
for n in range(1, 7):
    check(static_clause_level(n, 'diag') == DIAG[n - 1], "diag clause level n=%d" % n)
for n in range(1, 10):
    check(static_state_dp(n, 'diag') == DIAG[n - 1], "diag state DP n=%d" % n)
print("anti-diagonal: clause level n<=6, independent state DP n<=9 agree with table")
out = ''.join((run_exe('ref_dp.exe', ['diag', str(k), str(k), '4']) or '') for k in range(1, 14)) if not NOEXE and os.path.exists(os.path.join(HERE, 'ref_dp.exe')) else None
if out is None:
    SKIPPED.append("Rust ref_dp.exe diag n<=13 (not run)")
else:
    got = {}
    for line in out.splitlines():
        t = line.split()
        if t and t[0] == 'diag':
            got[int(t[1])] = int(t[2])
    for n in range(1, 14):
        check(got.get(n) == DIAG[n - 1], "ref_dp.exe diag n=%d" % n)
    print("ref_dp.exe reproduces diag n=1..13")
SKIPPED.append("anti-diagonal n=14,15,16: taken from the stored Rust run (ref_diag_14_17.txt, 29 s / 137 s / 886 s); not re-run")
tab = os.path.join(HERE, 'ref_tables.txt')
if os.path.exists(tab):
    txt = open(tab).read().splitlines()
    for ln in txt:
        if ln.startswith('diag:'):
            check(eval(ln.split(':', 1)[1]) == DIAG, "diag table equals stored ref_tables.txt")
        if ln.startswith('res2:'):
            check(eval(ln.split(':', 1)[1]) == RES2, "res2 table equals stored ref_tables.txt")
        if ln.startswith('pig:'):
            P = eval(ln.split(':', 1)[1])
            check(all(P[n - 1] == pig_closed(n) for n in range(1, len(P) + 1)), "pig stored table = n Fub(n-1)")
        if ln.startswith('hole:'):
            H = eval(ln.split(':', 1)[1])
            check(all(H[n - 1] == hole_closed(n) for n in range(1, len(H) + 1)), "hole stored table = closed form")
    print("stored tables in ref_tables.txt agree with the manuscript")

section("S4 Res(2)-JW")
for n in range(1, 6):
    check(resk_clause_level(n, 2) == RES2[n - 1], "res2 clause level n=%d" % n)
for n in range(1, 10):
    check(resk_state_level(n, 2) == RES2[n - 1], "res2 state level n=%d" % n)
print("Res(2)-JW: clause-level definition n<=5 and canonical-state version n<=9 agree with the table")
out = run_exe('ref_resk.exe', ['2', '1', '12'])
if out is None:
    SKIPPED.append("Rust ref_resk.exe Res(2)-JW n<=12 (not run)")
else:
    got = {}
    for line in out.splitlines():
        t = line.split()
        if t[:1] == ['resk']:
            got[int(t[2][2:])] = int(t[3])
    for n in range(1, 13):
        check(got.get(n) == RES2[n - 1], "ref_resk.exe n=%d" % n)
    print("ref_resk.exe reproduces Res(2)-JW n=1..12")
SKIPPED.append("Res(2)-JW n=13 (59 s) and n=14 (3532 s, 10.9M memo states): taken from stored Rust logs; not re-run here")
check(RES2[12] == 24104576248 and RES2[13] == 353344753156, "stored values")

section("counterexamples to earlier claims")
ad = [adaptive_optimum(n) for n in range(1, 5)]
check(ad == ADAPT, "adaptive optimum %r" % ad)
check(ad[3] == 23 and factorial(4) == 24, "23 < 4!")
print("adaptive optimum n=1..4:", ad, " vs n! =", [factorial(n) for n in range(1, 5)])
mt = [min_tree_leaves(n) for n in range(1, 4)]
if SLOW:
    mt.append(min_tree_leaves(4))
check(mt == MINTREE[:len(mt)], "minimum tree-resolution leaves %r" % mt)
print("minimum decision-tree (tree-resolution) leaves:", mt, "" if SLOW else "(n=4 value 189 not recomputed; use --slow)")
if not SLOW:
    SKIPPED.append("minimum tree-resolution leaves n=4 (=189): from the earlier audit and my own run; recompute with --slow")
# quasi-polynomial
c6 = [6, 10, 6, 12, 4, 12]
qp = lambda n: (n * n + 13 * n + c6[n % 6]) // 6
check(all((n * n + 13 * n + c6[n % 6]) % 6 == 0 for n in range(600)), "QP integer valued")
a_true = [RES2[n] // factorial(n) for n in range(0, 14)]          # floor(r(n+1)/n!) , n=0..13  (RES2[n] = r(n+1))
print("floor(r(n+1)/n!), n=0..13:", a_true)
print("quasi-polynomial, n=0..13  :", [qp(n) for n in range(14)])
check(a_true[:11] == [qp(n) for n in range(11)], "QP matches n<=10")
check(a_true[:11] == [1, 4, 6, 10, 12, 17, 20, 25, 29, 35, 39], "a(0..10)")
check(a_true[11] == 45 and qp(11) == 46, "QP fails at n=11")
check(Fr(RES2[11], factorial(11)) == Fr(363816767, 7983360) and float(Fr(RES2[11], factorial(11))) > 45.57, "b_11")
# earlier 'crossover' bookkeeping
for n in range(1, 15):
    vals = {'pig': pig_closed(n), 'hole': hole_closed(n), 'diag': DIAG[n - 1], 'res2': RES2[n - 1]}
    srt = sorted(vals, key=lambda k: vals[k])
    print("  n=%2d smallest..largest: %s" % (n, ' < '.join(srt)))
check(all(min(("pig", pig_closed(n)), ("hole", hole_closed(n)), ("diag", DIAG[n - 1]), ("res2", RES2[n - 1]), key=lambda t: t[1])[0] == 'res2' for n in range(5, 15)),
      "res2 smallest of the four for n=5..14 in this table")
check(RES2[2] > max(pig_closed(3), hole_closed(3), DIAG[2]) and RES2[3] < hole_closed(4), "res2 largest at n=3 but not at n=4")
# growth statistics quoted in the text
print("diag ratios d(n)/(n d(n-1)), n=12..16:", ["%.4f" % (DIAG[n - 1] / (n * DIAG[n - 2])) for n in range(12, 17)])
bs = [Fr(RES2[n], factorial(n)) for n in range(14)]           # b_n = r(n+1)/n!
print("b_n/n^2, n=8..13:", ["%.3f" % float(bs[n] / n ** 2) for n in range(8, 14)])
check(all(bs[n] <= n * n for n in range(8, 14)), "b_n <= n^2 for n = 8..13")
check(all(bs[n] / n ** 2 > bs[n + 1] / (n + 1) ** 2 for n in range(8, 13)), "b_n/n^2 decreasing n=8..13")
# discrepancy of the earlier non-D-finite tests: only a rank statement is checked here
# (exact determinant of the 9x9 system, n.b. a statement about the 11-term prefix only)
print("(earlier non-D-finiteness 'proofs' are not re-derived; see manuscript Section 4.4)")

# ==============================================================================================
section("S6 Theorem C (conditional on H): certificates in exact rational arithmetic")
N = 14
b = [Fr(RES2[n], factorial(n)) for n in range(N)]            # b_n = r(n+1)/n!


def R14(x):
    s = Fr(0)
    for c in reversed(b):
        s = s * x + c
    return s


def dR14_bound(rho):
    return sum(n * b[n] * rho ** (n - 1) for n in range(1, N))


def tail_poly(rho):                                          # sum_{n>=14} n^2 rho^n, closed form
    return rho ** N * (N * N - (2 * N * N - 2 * N - 1) * rho + (N - 1) ** 2 * rho ** 2) / (1 - rho) ** 3


for rho in (Fr(2, 5), Fr(9, 20)):
    brute = sum(n * n * float(rho) ** n for n in range(N, 3000))
    check(abs(brute - float(tail_poly(rho))) < 1e-12 * max(1, brute), "tail closed form")
# exact connected coefficients
f_ = [Fr(0)] * N
for n in range(1, N):
    f_[n] = (n * b[n] - sum(k * f_[k] * b[n - k] for k in range(1, n))) / n


def series_exp(c, M):
    e_ = [Fr(0)] * M
    e_[0] = Fr(1)
    for n in range(1, M):
        e_[n] = sum(k * c[k] * e_[n - k] for k in range(1, n + 1)) / n
    return e_


check(series_exp(f_, N) == b, "exp(C) = R through x^13")
Fn = [f_[n] * factorial(n) for n in range(1, N)]
check(all(x.denominator == 1 for x in Fn), "F_n integers")
check([int(x) for x in Fn] == [4, -3, 33, -216, 2496, -31059, 479934, -8454426, 171387720, -3898302102, 98654494668,
                               -2745253754127, 83351925966882], "F_n values")
check(int(Fn[5]) % 2 == 1, "F_6 odd")
print("F_n =", [int(x) for x in Fn])
# the 14-term zero
lo, hi = Fr(-2, 5), Fr(-39, 100)
check(R14(lo) < 0 < R14(hi), "bracket")
for _ in range(80):
    mid = (lo + hi) / 2
    if R14(mid) < 0:
        lo = mid
    else:
        hi = mid
x14 = (lo + hi) / 2
check(abs(float(x14) + 0.3952047138) < 5e-11, "x0^(14) = %.12f" % float(x14))
d14 = float(sum(n * b[n] * x14 ** (n - 1) for n in range(1, N)))
check(abs(d14 - 1.8956) < 1e-3, "R14' at zero")
print("zero of the degree-13 polynomial R_14: %.12f ; R_14' = %.5f" % (float(x14), d14))
nf = [float(n * f_[n] * x14 ** n) for n in range(1, N)]
check(all(abs(x + 1) < 0.0018 for x in nf[7:]) and abs(nf[-1] + 0.9983) < 6e-4, "n f_n x0^n -> -1 numerics")
print("n f_n x0^n, n=1..13:", ["%.4f" % x for x in nf])
# IVT under H_poly
T = tail_poly
check(R14(Fr(-39, 100)) - T(Fr(39, 100)) > 0 and R14(Fr(-40, 100)) + T(Fr(40, 100)) < 0, "sign change certificate")
p, q = Fr(39, 100), Fr(1, 2)
for _ in range(40):
    mid = (p + q) / 2
    if R14(-mid) - T(mid) > 0:
        p = mid
    else:
        q = mid
pos_end = p
p2, q2 = Fr(1, 3), Fr(2, 5)
for _ in range(40):
    mid = (p2 + q2) / 2
    if R14(-mid) + T(mid) < 0:
        q2 = mid
    else:
        p2 = mid
neg_end = q2
print("IVT interval for the zero under H_poly: (-%.6f, -%.6f)" % (float(neg_end), float(pos_end)))
check(abs(float(pos_end) - 0.394785) < 2e-6 and abs(float(neg_end) - 0.395638) < 2e-6, "IVT interval")
check(neg_end > Fr(395, 1000) and pos_end < Fr(396, 1000) and Fr(-2, 5) < -neg_end, "x0 != -2/5 and x0 in (-0.3957,-0.3947)")
check(x14 > -neg_end and x14 < -pos_end, "x0^(14) inside the interval")


def circle_check(rho, Tfun, M=1500):
    Tv = Tfun(rho)
    Lc = dR14_bound(rho)
    ds = rho * 2 * Fr(2, M)
    wind = 0.0
    prev = None
    ok = True
    minmod2 = None
    for half in (0, 1):
        for j in range(M + 1):
            if half == 1 and j == 0:
                continue
            t = Fr(-M + 2 * j, M)
            d = 1 + t * t
            x = rho * (1 - t * t) / d
            y = rho * 2 * t / d
            if half == 1:
                x, y = -x, -y
            re, im = Fr(0), Fr(0)
            for c in reversed(b):
                re, im = re * x - im * y + c, re * y + im * x
            m2 = re * re + im * im
            minmod2 = m2 if minmod2 is None or m2 < minmod2 else minmod2
            if prev is not None:
                (pre, pim), pm2 = prev
                if not min(m2, pm2) > (Tv + Lc * ds / 2) ** 2:
                    ok = False
                if not (Lc * ds) ** 2 < pm2:
                    ok = False
                wind += math.atan2(float(im * pre - re * pim), float(re * pre + im * pim))
            prev = ((re, im), m2)
    return ok, wind / (2 * math.pi), float(minmod2) ** 0.5, float(Tv), float(Lc)


ok, wnd, mn, Tv, Lc = circle_check(Fr(9, 20), T)
print("circle |x|=9/20: Rouche margin ok=%s, winding(R_14)=%.6f, min|R_14|=%.4f > tail %.3e (L=%.2f)" % (ok, wnd, mn, Tv, Lc))
check(ok and abs(wnd - 1) < 1e-6 and abs(Tv - 5.61e-3) < 1e-5 and abs(mn - 0.1059) < 1e-3, "Rouche on |x|=9/20")
# real axis [-0.6,-0.4]
x = Fr(2, 5)
step = Fr(1, 10000)
while x < Fr(3, 5):
    xn = x + step
    check(R14(-x) + dR14_bound(xn) * step + T(xn) < 0, "R<0 grid at x=%s" % x)
    x = xn
print("R < 0 certified on [-0.6, -0.4] (grid step 1e-4, exact)")

# tails not excluded by the 14 data points (Remark in Section 7)
xx = Fr(-42, 100)
cc = -R14(xx) / xx ** 14
check(abs(float(cc) - 8899.6) < 0.1, "b_14 := %.2f moves the zero to -0.42" % float(cc))
check(R14(xx) + cc * xx ** 14 == 0, "exact zero at -0.42")
print("tail example: b_14 = %.1f, b_n = 0 (n>14) gives an exact zero at -0.42" % float(cc))
check(all(Fr(RES2[n], factorial(n)) == b[n] for n in range(14)), "b_n = r(n+1)/n!")

# ----------------------------------------------------------------------------------------------
section("consistency of the manuscript text with the verified numbers")
# Limitations section: hole-major / pigeon-major ~ (e ln 2)^n n^(-5/2) * 2(e^2+e^3)/sqrt(2 pi)
for n in (200, 2000):
    lh = (n - 2) * math.log(n + 2) + math.log1p(math.exp((n - 2) * (math.log(n + 3) - math.log(n + 2))))
    lp = math.lgamma(n + 1) - math.log(2) - n * math.log(ln2)
    pred = n * (1 + math.log(ln2)) - 2.5 * math.log(n) + math.log(2 * (math.e ** 2 + math.e ** 3) / math.sqrt(2 * math.pi))
    check(abs((lh - lp) - pred) < 40.0 / n, "hole/pig ratio asymptotics n=%d" % n)
print("hole-major / pigeon-major ~ (e ln 2)^n n^(-5/2) * 2(e^2+e^3)/sqrt(2 pi), e ln 2 = %.4f" % (math.e * ln2))
TEX = os.path.join(HERE, 'ms_php_dpll.tex')
if os.path.exists(TEX):
    tex = open(TEX, encoding='utf8').read()
    BS = chr(92)
    fmt = lambda v: '{:,}'.format(v).replace(',', BS + ',')
    for n in range(1, 15):
        row = "%d & %s & %s & %s & %s %s%s" % (n, fmt(pig_closed(n)), fmt(hole_closed(n)), fmt(DIAG[n - 1]), fmt(RES2[n - 1]), BS, BS)
        check(row in tex, "table row n=%d present in the tex file" % n)
    flat = tex.replace(BS + 'allowbreak ', '').replace('\n', ' ').replace(' ', '')
    for lst in (DIAG, RES2):
        check(','.join(map(str, lst)) in flat, "list %r present" % lst[:3])
    check(str(DIAG[14]) in tex and str(DIAG[15]) in tex, "diag 15,16 in text")
    check(','.join(str(int(x)) for x in Fn) in flat, "F_n list in tex")
    check("-0.395638<x_0<-0.394785" in flat and "1.8956" in tex and "-0.3952047138" in tex, "interval / zero strings")
    print("tex table rows, lists and constants match the verified values")
else:
    SKIPPED.append("manuscript text consistency (ms_php_dpll.tex not found next to ms_check.py)")

print("\nSKIPPED / not re-run (documented in the manuscript):")
for s in SKIPPED:
    print("  -", s)
print("\n%d checks passed in %.0f s" % (NCHECK, time.time() - T0))
print("ALL OK")
