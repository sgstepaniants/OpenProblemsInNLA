#!/usr/bin/env python3
"""Bounded exact data checks for the proposed IE-13 indexing.

This is neither a Lean proof nor a test of the universal upper theorem.
It checks the rational source construction and actual physical pivot prefix
at small parameters, then extends with ordinary maximum-modulus pivots.
"""
from fractions import Fraction as Q
import json


def sequence(p, stop):
    values = [0]
    for t in range(1, stop + 1):
        values.append(1 + sum(values[max(0, t - r)] for r in range(1, p + 1)))
    return values


def source_matrix(p, q):
    n, target = 2 * p + q + 1, p + q
    sigma = [p] + list(range(p)) + list(range(p + 1, n))
    matrix = [[Q(0) for _ in range(n)] for _ in range(n)]
    for column in range(target):
        # Written in the source's one-based factor-row notation.
        if column + 1 <= p + 1:
            upper = [Q(1)] + [Q(2 ** (i - 2)) if i <= column + 1 else Q(0)
                              for i in range(2, n + 1)]
        else:
            upper = [Q(int(i == column)) for i in range(n)]
        for factor_row in range(n):
            entry = upper[factor_row] - sum(upper[max(0, factor_row - p):factor_row])
            matrix[sigma[factor_row]][column] = entry / (2 ** p)
    for i in range(n):
        matrix[i][target] = Q(int(p <= i))
    for column in range(target + 1, n):
        matrix[column][column] = Q(1)
    return matrix, sigma


def check(p, q):
    a, sigma = source_matrix(p, q)
    n, target = len(a), p + q
    assert max(abs(x) for row in a for x in row) == 1
    assert all(a[i][j] == 0 for i in range(n) for j in range(n)
               if j + p < i or i + q < j)
    s = [row[:] for row in a]
    labels = list(range(n))
    peak = max(abs(x) for row in s for x in row)
    determinant = Q(1)
    h = sequence(p, target)[target]
    for k in range(n):
        if k == target:
            assert labels == sigma
            assert s[k][k] == h
        pivot = (p if k <= p else k) if k < target else max(
            range(k, n), key=lambda i: abs(s[i][k]))
        assert k <= pivot and s[pivot][k] != 0
        assert all(abs(s[i][k]) <= abs(s[pivot][k]) for i in range(k, n))
        if pivot != k:
            s[k], s[pivot] = s[pivot], s[k]
            labels[k], labels[pivot] = labels[pivot], labels[k]
            determinant = -determinant
        determinant *= s[k][k]
        for i in range(k + 1, n):
            multiplier = s[i][k] / s[k][k]
            for j in range(k + 1, n):
                s[i][j] -= multiplier * s[k][j]
                peak = max(peak, abs(s[i][j]))
            s[i][k] = 0
    assert determinant != 0
    assert peak == h
    return {"p": p, "q": q, "order": n, "growth": h,
            "nonzero_determinant": str(determinant)}


if __name__ == "__main__":
    cases = [check(p, q) for p in range(1, 5) for q in range(5)]
    print(json.dumps({"case_count": len(cases), "cases": cases,
                     "scope": "Exact small rational witness checks only; no universal proof, Lean execution or acceptance."},
                    indent=2))
