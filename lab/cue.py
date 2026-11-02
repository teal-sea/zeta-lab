"""CUE(N) eigenphase gaps and their exact periodic HVG statistics.

Haar unitaries by QR of a complex Ginibre matrix with the phase fix of Mezzadri (Notices AMS
54, 592, 2007). The N eigenphases of one matrix, scaled by N/(2 pi), have unit mean density
exactly, so no unfolding is needed; the N gaps (including the wrap-around gap) form a
circular sequence.

Periodic HVG: the degrees of the bi-infinite periodic extension of a circular sequence are
read off the middle copy of three. That is exact: every view stops at or before the next
copy of the period maximum (an equal value is joined, then blocks), which lies within one
period, so no view from the middle copy leaves the three copies.
"""
from __future__ import annotations

import numpy as np

import hvg


def cue_gaps(n: int, batch: int, rng: np.random.Generator) -> np.ndarray:
    """(batch, n) array of unit-mean circular gaps, one row per Haar unitary."""
    z = (rng.normal(size=(batch, n, n)) + 1j * rng.normal(size=(batch, n, n))) / np.sqrt(2.0)
    q, r = np.linalg.qr(z)
    d = np.diagonal(r, axis1=1, axis2=2)
    q = q * (d / np.abs(d))[:, None, :]
    phases = np.sort(np.mod(np.angle(np.linalg.eigvals(q)), 2.0 * np.pi), axis=1)
    u = phases * n / (2.0 * np.pi)
    return np.diff(np.concatenate([u, u[:, :1] + n], axis=1), axis=1)


def periodic_degrees(gaps: np.ndarray) -> np.ndarray:
    """Exact HVG degrees of the periodic extension of one circular sequence."""
    n = gaps.size
    deg, _, _ = hvg.degrees(np.concatenate([gaps, gaps, gaps]))
    return deg[n:2 * n]


def local_min_fraction(rows: np.ndarray) -> np.ndarray:
    """Per-row fraction of circular strict local minima (the HVG degree-2 nodes)."""
    left = np.roll(rows, 1, axis=1)
    right = np.roll(rows, -1, axis=1)
    return np.mean((left > rows) & (rows < right), axis=1)
