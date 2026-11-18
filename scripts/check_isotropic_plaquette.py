"""Numerical character-basis check for one interacting SU(2) plaquette.

The one-plaquette physical state space is the space of class functions on
SU(2).  Its orthonormal basis is chi_l(theta)=sin((l+1)theta)/sin(theta).
Normalize C_b as convolution by exp(b cos(theta)) divided by its Haar integral.
The physical one-plaquette operator has the nonzero spectrum of

    C_b**2 D_b**2 C_b**2,    D_b**2 = multiplication by exp(b cos(theta)).

The four powers of C_b come from the four independent link increments.
We multiply the displayed operator by exp(-b), which leaves eigenvalue ratios
unchanged and prevents overflow.  Every integral uses the SU(2) Weyl measure
(2/pi) sin(theta)**2 dtheta.  Midpoint sine quadrature and a symmetric
eigenproblem give an approximation at finite b.

The default run independently refines both character cutoff and angle grid
at b=16,64,256,1024.  It compares the first excited-to-vacuum ratio to the
radial Gaussian limit (3-2 sqrt(2))**2.  An auxiliary table checks only
the Gaussian covariance 3 I_m + 11^T for m=1,2,3,4.  The m>1 rows do not
compute an interacting Wilson spectrum.  A separate table constructs the
oriented edge-by-face curl on open cubic boxes with L=1,2,3,4 intervals per
edge, checks its smallest positive squared singular value, and evaluates
the associated Gaussian two-quantum energy formula.

Run from any directory:
    python scripts/check_isotropic_plaquette.py

Requires NumPy.  No files are written.  These Float64 computations are
numerical cross-checks, without interval error bounds or a continuum-gap
certificate.
"""

import argparse
from itertools import combinations, product
import math

import numpy as np


def next_power_of_two(value):
    """Return the first power of two at least as large as a positive integer."""
    return 1 << (value - 1).bit_length()


def character_matrix(coupling, degree, grid):
    """Approximate the shifted operator in characters chi_0,...,chi_degree."""
    if grid <= degree + 1:
        raise ValueError("The angle grid must exceed the number of characters.")
    theta = np.pi * (np.arange(grid, dtype=float) + 0.5) / grid
    modes = np.arange(1, degree + 2, dtype=float)
    sine = np.sin(modes[:, None] * theta[None, :])
    # cos(theta)-1=-2 sin(theta/2)^2 avoids loss near theta=0.
    weight = np.exp(-2 * coupling * np.sin(theta / 2) ** 2)
    sine_theta = np.sin(theta)
    normalization = (2 / grid) * np.dot(weight, sine_theta**2)
    if not np.isfinite(normalization) or normalization <= 0:
        raise ArithmeticError("The normalized Haar integral is not positive.")

    # c_l = integral exp(b*x) chi_l / ((l+1) integral exp(b*x)).
    # This also equals I_(l+1)(b)/I_1(b), but no Bessel package is needed.
    kinetic = (2 / grid) * (sine @ (weight * sine_theta))
    kinetic /= modes * normalization
    if abs(kinetic[0] - 1) > 5e-13:
        raise ArithmeticError("The trivial character does not have coefficient one.")
    if np.min(kinetic) < -5e-12 or np.max(kinetic) > 1 + 5e-12:
        raise ArithmeticError("Kinetic Fourier coefficients exceed numerical tolerances.")

    # The sin(theta)^2 Haar factor cancels the two character denominators.
    potential = (2 / grid) * ((sine * weight[None, :]) @ sine.T)
    matrix = kinetic[:, None] ** 2 * potential * kinetic[None, :] ** 2
    return (matrix + matrix.T) / 2


def spectral_ratio(matrix, degree):
    """Return the two largest Ritz eigenvalues and their residual check."""
    block = matrix[: degree + 1, : degree + 1]
    eigenvalues, eigenvectors = np.linalg.eigh(block)
    largest = eigenvalues[-1]
    excited = eigenvalues[-2]
    if not np.isfinite(largest) or largest <= 0:
        raise ArithmeticError("The largest approximate eigenvalue is not positive.")
    if eigenvalues[0] < -5e-12 * largest:
        raise ArithmeticError("The approximate positive operator has a negative eigenvalue.")
    ratio = excited / largest
    if not 0 <= ratio < 1:
        raise ArithmeticError("The approximate excited ratio is outside [0,1).")
    residual = np.linalg.norm(
        block @ eigenvectors[:, -2:] - eigenvectors[:, -2:] * eigenvalues[-2:]
    ) / largest
    if residual > 5e-11:
        raise ArithmeticError(f"The relative eigenvector residual is too large: {residual}.")
    return ratio, largest, residual


def check_one_coupling(coupling, tolerance):
    """Use all four combinations of independent cutoff and grid refinements."""
    coarse_degree = max(8, math.ceil(6 * math.sqrt(coupling)))
    fine_degree = max(coarse_degree + 4, math.ceil(8 * math.sqrt(coupling)))
    coarse_grid = next_power_of_two(max(512, 8 * (fine_degree + 1)))
    fine_grid = 2 * coarse_grid
    coarse_matrix = character_matrix(coupling, fine_degree, coarse_grid)
    fine_matrix = character_matrix(coupling, fine_degree, fine_grid)

    coarse_both = spectral_ratio(coarse_matrix, coarse_degree)
    fine_cutoff = spectral_ratio(coarse_matrix, fine_degree)
    fine_grid_only = spectral_ratio(fine_matrix, coarse_degree)
    fine_both = spectral_ratio(fine_matrix, fine_degree)
    cutoff_change = max(
        abs(fine_cutoff[0] - coarse_both[0]),
        abs(fine_both[0] - fine_grid_only[0]),
    )
    grid_change = max(
        abs(fine_grid_only[0] - coarse_both[0]),
        abs(fine_both[0] - fine_cutoff[0]),
    )
    if max(cutoff_change, grid_change) > tolerance:
        raise ArithmeticError(
            f"b={coupling:g}: refinement differences exceed {tolerance:g} "
            f"(cutoff {cutoff_change:.3e}, grid {grid_change:.3e})."
        )
    return {
        "b": coupling,
        "degrees": (coarse_degree, fine_degree),
        "grids": (coarse_grid, fine_grid),
        "ratio": fine_both[0],
        "cutoff_change": cutoff_change,
        "grid_change": grid_change,
        "residual": max(
            coarse_both[2], fine_cutoff[2], fine_grid_only[2], fine_both[2]
        ),
    }


def gaussian_covariance_check():
    """Check the linearized shared-edge covariance with no Wilson extrapolation."""
    print("\nAuxiliary Gaussian calculation for 3 I_m + 11^T")
    print("faces    minimum eigenvalue    maximum eigenvalue    radial ratio")
    for count in range(1, 5):
        covariance = 3 * np.eye(count) + np.ones((count, count))
        eigenvalues = np.linalg.eigvalsh(covariance)
        expected = np.array([3.0] * (count - 1) + [count + 3.0])
        if not np.allclose(eigenvalues, expected, rtol=0, atol=1e-12):
            raise ArithmeticError("The auxiliary Gaussian covariance check failed.")
        minimum = eigenvalues[0]
        mehler_ratio = 2 / (2 + minimum + math.sqrt(minimum * (minimum + 4)))
        print(
            f"{count:5d}    {minimum:18.12f}    "
            f"{eigenvalues[-1]:18.12f}    {mehler_ratio**2:.12f}"
        )
    print("The rows with more than one face are Gaussian calculations only.")


def open_box_curl(intervals):
    """Build the oriented edge-by-face incidence matrix of [0,L]^3."""
    vertices = list(product(range(intervals + 1), repeat=3))
    edges = [
        (vertex, axis)
        for vertex in vertices
        for axis in range(3)
        if vertex[axis] < intervals
    ]
    faces = [
        (vertex, first, second)
        for vertex in vertices
        for first, second in combinations(range(3), 2)
        if vertex[first] < intervals and vertex[second] < intervals
    ]
    edge_index = {edge: index for index, edge in enumerate(edges)}
    curl = np.zeros((len(edges), len(faces)), dtype=float)
    for column, (vertex, first, second) in enumerate(faces):
        along_first = list(vertex)
        along_first[first] += 1
        along_second = list(vertex)
        along_second[second] += 1
        boundary = [
            ((vertex, first), 1),
            ((tuple(along_first), second), 1),
            ((tuple(along_second), first), -1),
            ((vertex, second), -1),
        ]
        for edge, orientation in boundary:
            curl[edge_index[edge], column] = orientation
    expected_edges = 3 * intervals * (intervals + 1) ** 2
    expected_faces = 3 * intervals**2 * (intervals + 1)
    if curl.shape != (expected_edges, expected_faces):
        raise ArithmeticError("The open cubic box has inconsistent incidence counts.")
    return curl, len(vertices), len(edges)


def gaussian_open_box_check():
    """Check the positive curl spectrum and its Gaussian singlet benchmark."""
    print("\nIndependent open-cube incidence calculation")
    print(
        "    L    smallest positive squared singular value"
        "    predicted value    singlet Gaussian energy"
    )
    for intervals in range(1, 5):
        curl, vertices, edges = open_box_curl(intervals)
        singular_values = np.linalg.svd(curl, compute_uv=False)
        positive = singular_values[singular_values > 1e-10]
        # The box is contractible, so rank(boundary_2)=edges-vertices+1.
        if len(positive) != edges - vertices + 1:
            raise ArithmeticError("The computed curl rank differs from the cycle rank.")
        smallest = positive[-1] ** 2
        angle = math.pi / (2 * (intervals + 1))
        predicted = 8 * math.sin(angle) ** 2
        if not math.isclose(smallest, predicted, rel_tol=5e-12, abs_tol=5e-12):
            raise ArithmeticError(
                f"L={intervals}: curl eigenvalue {smallest} differs from {predicted}."
            )
        singlet_energy = 4 * math.asinh(math.sqrt(2) * math.sin(angle))
        print(
            f"{intervals:5d}    {smallest:42.12f}"
            f"    {predicted:15.12f}    {singlet_energy:23.12f}"
        )
    print(
        "This checks the finite incidence spectrum and a linearized Gaussian "
        "two-quantum energy formula."
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--couplings",
        type=float,
        nargs="+",
        default=[16.0, 64.0, 256.0, 1024.0],
        help="Positive finite Wilson couplings, default: 16 64 256 1024",
    )
    parser.add_argument(
        "--refinement-tolerance",
        type=float,
        default=5e-11,
        help="Maximum accepted cutoff or grid change, default: 5e-11",
    )
    args = parser.parse_args(argv)
    if any(not math.isfinite(b) or b <= 0 for b in args.couplings):
        parser.error("Every coupling must be positive and finite.")
    if not math.isfinite(args.refinement_tolerance) or args.refinement_tolerance <= 0:
        parser.error("The refinement tolerance must be positive and finite.")

    target = (3 - 2 * math.sqrt(2)) ** 2
    print(f"NumPy {np.__version__}; Float64 midpoint Weyl-angle quadrature")
    print(f"Predicted one-plaquette radial limit: {target:.15f}")
    print(
        "\n     b    degrees       angle grids       first excited ratio"
        "    cutoff change    grid change      ratio - limit"
    )
    results = []
    for coupling in args.couplings:
        result = check_one_coupling(coupling, args.refinement_tolerance)
        results.append(result)
        low_degree, high_degree = result["degrees"]
        low_grid, high_grid = result["grids"]
        print(
            f"{coupling:6g}    {low_degree:3d}/{high_degree:<3d}    "
            f"{low_grid:5d}/{high_grid:<5d}    {result['ratio']:.15f}"
            f"    {result['cutoff_change']:.3e}    {result['grid_change']:.3e}"
            f"    {result['ratio'] - target:.6e}",
            flush=True,
        )
    if args.couplings == [16.0, 64.0, 256.0, 1024.0]:
        deviations = [result["ratio"] - target for result in results]
        if not all(
            deviations[index] > deviations[index + 1] > 0
            for index in range(len(deviations) - 1)
        ):
            raise ArithmeticError("The requested sequence does not approach the limit from above.")
        print("The requested finite-coupling ratios approach the predicted limit from above.")
    gaussian_covariance_check()
    gaussian_open_box_check()
    print("\nPASS: cutoff, angle-grid, eigenvector-residual and incidence checks passed.")
    print(
        "These are finite one-plaquette numerical checks. Rigorous truncation and "
        "quadrature error bounds and the full four-dimensional Wilson estimate "
        "are still required."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
