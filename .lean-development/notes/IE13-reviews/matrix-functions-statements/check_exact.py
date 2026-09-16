"""Independent bounded diagnostics for the IE13 statement review.

No Lean is executed. Finite checks supplement the universal mathematical
statement review; they neither prove the theorem nor certify any Lean source.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random


def sequence(p, count):
    h = [0]
    for t in range(count):
        h.append(1 + sum(h[max(0, t-r)] for r in range(p)))
    return h


def envelope(p, t, h):
    return [0 if t == 0 else 1 + sum(h[max(0, t-r-1)]
            for r in range(p-i)) for i in range(p)]


def witness(p, q):
    n, target = 2*p+q+1, p+q
    lower = [[F(1 if i == j else -1 if j < i <= j+p else 0)
              for j in range(n)] for i in range(n)]
    factor = [i+1 if i < p else 0 if i == p else i for i in range(n)]
    a = [[F(0) for _ in range(n)] for _ in range(n)]
    for j in range(n):
        for i in range(n):
            if j < target:
                u = [F((1 if r == 0 else 2**(r-1) if r <= j else 0)
                       if j <= p else int(r == j)) for r in range(n)]
                a[i][j] = F(1, 2**p) * sum(lower[factor[i]][r]*u[r]
                                           for r in range(n))
            elif j == target:
                a[i][j] = F(int(p <= i))
            else:
                a[i][j] = F(int(i == j))
    return a


def bareiss_det(a):
    """Independent integer determinant; witness inputs are scaled first."""
    a = [r[:] for r in a]
    n, prev, sign = len(a), 1, 1
    for k in range(n-1):
        piv = next((i for i in range(k, n) if a[i][k]), None)
        if piv is None:
            return 0
        if piv != k:
            a[k], a[piv] = a[piv], a[k]
            sign = -sign
        v = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                num = a[i][j]*v-a[i][k]*a[k][j]
                assert num % prev == 0
                a[i][j] = num//prev
            a[i][k] = 0
        prev = v
    return sign*a[-1][-1]


def check_witness(p, q):
    a = witness(p, q)
    n, t = len(a), p+q
    h = sequence(p, t)
    assert n >= 1+max(p, q)
    assert max(abs(x) for row in a for x in row) == 1
    assert all(not (j+p < i or i+q < j) or a[i][j] == 0
               for i in range(n) for j in range(n))
    assert bareiss_det([[int(x*2**p) for x in row] for row in a]) != 0
    s = [r[:] for r in a]
    origin, maximum = list(range(n)), F(1)
    for k in range(n):
        if k == t:
            assert s[t][t] == h[t]
            assert origin == [p if i == 0 else i-1 if i <= p else i for i in range(n)]
        maximum = max(maximum, *(abs(s[i][j]) for i in range(k, n) for j in range(k, n)))
        # Fix exactly the proposed prefix, then choose an actually maximal row.
        piv = p if k < t and k <= p else k if k < t else max(range(k, n), key=lambda i: abs(s[i][k]))
        assert k <= piv and s[piv][k] != 0
        assert all(abs(s[i][k]) <= abs(s[piv][k]) for i in range(k, n))
        s[k], s[piv] = s[piv], s[k]
        origin[k], origin[piv] = origin[piv], origin[k]
        b = [[F(0) for _ in range(n)] for _ in range(n)]
        for i in range(k+1, n):
            for j in range(k+1, n):
                b[i][j] = s[i][j] - s[i][k]/s[k][k]*s[k][j]
        s = b
    assert maximum == h[t]
    return {"p": p, "q": q, "dimension": n, "growth": str(maximum)}


class QComplex:
    """Only exact Gaussian rational arithmetic, including modulus squared."""
    __slots__ = ("r", "i")
    def __init__(self, r=0, i=0):
        self.r, self.i = F(r), F(i)
    def __add__(self, z):
        return QComplex(self.r+z.r, self.i+z.i)
    def __sub__(self, z):
        return QComplex(self.r-z.r, self.i-z.i)
    def __mul__(self, z):
        return QComplex(self.r*z.r-self.i*z.i, self.r*z.i+self.i*z.r)
    def __truediv__(self, z):
        d = z.norm2()
        return QComplex((self.r*z.r+self.i*z.i)/d, (self.i*z.r-self.r*z.i)/d)
    def __eq__(self, z):
        return isinstance(z, QComplex) and self.r == z.r and self.i == z.i
    def __bool__(self):
        return bool(self.r or self.i)
    def norm2(self):
        return self.r*self.r+self.i*self.i
    def rational_norm(self):
        q = self.norm2()
        a, b = isqrt(q.numerator), isqrt(q.denominator)
        assert a*a == q.numerator and b*b == q.denominator
        return F(a, b)


def determinant_nonzero(a):
    b = [r[:] for r in a]
    n = len(a)
    for k in range(n):
        piv = next((i for i in range(k, n) if b[i][k]), None)
        if piv is None:
            return False
        b[k], b[piv] = b[piv], b[k]
        for i in range(k+1, n):
            m = b[i][k]/b[k][k]
            for j in range(k+1, n):
                b[i][j] = b[i][j]-m*b[k][j]
    return True


def check_all_paths(a, p, q, rational_norms):
    n, nodes, leaves, tied_nodes = len(a), 0, 0, 0
    h = sequence(p, 2*n+p+q+2)
    amax2 = max(x.norm2() for row in a for x in row)
    bound = 1 if p == 0 else h[p+q]
    amax = max(x.rational_norm() for row in a for x in row) if rational_norms else None
    assert determinant_nonzero(a)

    def visit(s, origin, k):
        nonlocal nodes, leaves, tied_nodes
        if k == n:
            leaves += 1
            return
        nodes += 1
        pos = {original: physical for physical, original in enumerate(origin)}
        old = {i for i in range(n) if pos[i] >= k and i < k+p}
        front = {i for i in range(n) if pos[i] >= k and i <= k+p}
        assert len(old) <= p
        for i in range(k+p, n):
            assert pos[i] >= k
            assert all(s[pos[i]][j] == a[i][j] for j in range(k, n))
        for j in range(k, n):
            assert all(s[i][j].norm2() <= bound**2*amax2 for i in range(k, n))
            if k+p+q <= j:
                assert all(not s[pos[i]][j] for i in old)
            if p > 0 and rational_norms:
                age = k+1 if j < p+q else max(0, k-(j-(p+q)))
                env = envelope(p, age, h)
                values = sorted((s[pos[i]][j].rational_norm() for i in old), reverse=True)
                for size in range(len(old)+1):
                    assert sum(values[:size]) <= sum(env[:size])*amax
        pivot_norm2 = max(s[i][k].norm2() for i in range(k, n))
        assert pivot_norm2 > 0
        choices = [i for i in range(k, n) if s[i][k].norm2() == pivot_norm2]
        tied_nodes += int(len(choices) > 1)
        for piv in choices:
            assert origin[piv] in front
            b = [r[:] for r in s]
            b[k], b[piv] = b[piv], b[k]
            next_origin = origin[:]
            next_origin[k], next_origin[piv] = next_origin[piv], next_origin[k]
            next_old = {i for physical, i in enumerate(next_origin) if physical >= k+1 and i < k+1+p}
            assert next_old == front-{origin[piv]}
            t = [[QComplex() for _ in range(n)] for _ in range(n)]
            for i in range(k+1, n):
                m = b[i][k]/b[k][k]
                assert m.norm2() <= 1
                for j in range(k+1, n):
                    t[i][j] = b[i][j]-m*b[k][j]
            visit(t, next_origin, k+1)
    visit(a, list(range(n)), 0)
    return {"n": n, "p": p, "q": q, "nodes": nodes, "full_paths": leaves,
            "tie_branch_nodes": tied_nodes, "all_subset_sums_checked": rational_norms}


def main():
    histories = 0
    for p in range(7):
        h = sequence(p, 20)
        hist = [0]*25
        for t in range(20):
            assert all(hist[r] == h[max(0, t-r)] for r in range(25))
            histories += 25
            hist = [1+sum(hist[:p])]+hist[:-1]
        assert all(h[t] <= h[t+1] and h[t+1] > 0 for t in range(20))
        if p:
            for t in range(1, 19):
                x, nxt = envelope(p, t, h), envelope(p, t+1, h)
                assert x[0] == h[t]
                assert all(x[i] >= x[i+1] for i in range(p-1)) and min(x) >= 1
                assert nxt == [h[t]+(x[i+1] if i+1 < p else 1) for i in range(p)]
    sorted_front_cases = 0
    for p in range(1, 5):
        for vals in product(range(4), repeat=p+1):
            y = sorted(vals, reverse=True)
            optimal = [y[0]+y[i] for i in range(1, p+1)]
            for a in range(p+1):
                survivors = sorted([y[a]+y[i] for i in range(p+1) if i != a], reverse=True)
                assert all(s <= b for s, b in zip(survivors, optimal))
                sorted_front_cases += 1
    witnesses = [check_witness(p, q) for p in range(1, 6) for q in range(7)]
    # The rotation contract is stronger than witness existence and includes p=q=0.
    rotations = 0
    for p in range(7):
        for q in range(8):
            n = 2*p+q+1
            origin = list(range(n))
            for k in range(p+q):
                piv = p if k <= p else k
                assert k <= piv < n
                origin[k], origin[piv] = origin[piv], origin[k]
            assert origin == [p if i == 0 else i-1 if i <= p else i for i in range(n)]
            rotations += 1
    rng = random.Random(131313)
    paths = []
    phases = [QComplex(1), QComplex(0, 1), QComplex(-1), QComplex(0, -1)]
    for q in range(7):
        n = q+1
        a = [[QComplex(int(i == j)) for j in range(n)] for i in range(n)]
        paths.append(check_all_paths(a, 0, q, True))
    for n, p, q in [(3, 1, 0), (3, 1, 1), (3, 1, 2), (4, 2, 0), (4, 2, 1),
                    (4, 2, 3), (5, 3, 0), (5, 3, 1), (5, 1, 3)]:
        for rational_norms in [True, False]:
            accepted = 0
            while accepted < 3:
                a = []
                for i in range(n):
                    phase = phases[rng.randrange(4)]
                    row = []
                    for j in range(n):
                        if j+p < i or i+q < j:
                            row.append(QComplex())
                        elif rational_norms:
                            row.append(phase*QComplex(rng.choice([-1, 0, 1])))
                        else:
                            row.append(QComplex(rng.choice([-1, 0, 1]), rng.choice([-1, 0, 1])))
                    a.append(row)
                if determinant_nonzero(a):
                    paths.append(check_all_paths(a, p, q, rational_norms))
                    accepted += 1
    result = {"status": "all bounded exact diagnostics passed", "local_Lean_execution": False,
              "universal_or_formal_proof": False, "history_slot_checks": histories,
              "sorted_front_pivot_cases": sorted_front_cases, "rotation_cases": rotations,
              "rational_witnesses": witnesses, "all_legal_path_diagnostics": paths,
              "total_full_paths": sum(x["full_paths"] for x in paths),
              "total_tie_branch_nodes": sum(x["tie_branch_nodes"] for x in paths)}
    output = Path(__file__).with_name("EXACT-DIAGNOSTICS.json")
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: v for k, v in result.items() if not isinstance(v, list)}, indent=2))


if __name__ == "__main__":
    main()
