"""The chart delta of the odd alternate (alternateOddDelta in Lean): (N - D - dq, N + D - nq) in phase one, zero in phase zero."""
from seventh_jet import parents_of, phase


def chart_delta(w):
    if phase(w) == 0:
        return (0, 0)
    (N, D), (nq, dq) = parents_of(w)
    return ((N - D) - dq, (N + D) - nq)
