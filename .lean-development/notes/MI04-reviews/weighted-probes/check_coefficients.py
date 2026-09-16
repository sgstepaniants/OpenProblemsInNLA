"""Bounded independent exact checks of row/column index and probe constants.

No eigenvalue approximation, Lean execution or theorem verification is claimed.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def normsq(z):
    return F(z[0]**2 + z[1]**2)


def main():
    peaks = probes = 0
    for n in range(1, 7):
        x = [[(2*i-j+1, i+3*j-2) for j in range(n)] for i in range(n)]
        zero = (0, 0)
        v = [[zero for _ in range(2*n)] for _ in range(2*n)]
        for r in range(n):
            for s in range(n):
                v[r][n+s] = x[r][s]
                v[n+s][r] = (x[r][s][0], -x[r][s][1])
        for i in range(n):
            d = [F(1) if j == i else [F(-1, 2), F(0), F(1, 2)][j % 3] for j in range(n)]
            left_diag = d+[-t for t in d]
            right_diag = [-t for t in d]+d
            left = sum(normsq(v[j][i])/(1-left_diag[j]) for j in range(2*n) if j != i)
            right = sum(normsq(v[j][n+i])/(1-right_diag[j]) for j in range(2*n) if j != n+i)
            row = sum(normsq(x[i][j])/(1+d[j]) for j in range(n))
            col = sum(normsq(x[j][i])/(1+d[j]) for j in range(n))
            assert left == row and right == col
            assert left_diag[i] == right_diag[n+i] == 1
            assert max(left_diag[:i]+left_diag[i+1:]) <= F(1, 2)
            assert max(right_diag[:n+i]+right_diag[n+i+1:]) <= F(1, 2)
            peaks += 1
            for j in range(n):
                if j == i:
                    continue
                q = [F((k+1)*(k-2)) for k in range(n)]
                d0 = [F(int(k == i)) for k in range(n)]
                d1 = [F(1) if k == i else F(1, 2) if k == j else F(0) for k in range(n)]
                difference = sum(q[k]/(1+d0[k])-q[k]/(1+d1[k]) for k in range(n))
                assert difference == q[j]/3
                probes += 1
    result = {'exact_peak_row_column_checks': peaks, 'exact_one_coordinate_probe_checks': probes,
              'all_passed': True, 'scope': 'bounded indexing/rational diagnostics only',
              'Lean_execution_or_universal_proof': False}
    Path(__file__).with_name('EXACT-DIAGNOSTICS.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
