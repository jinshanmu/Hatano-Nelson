#!/usr/bin/env python3
"""Reproduce three manuscript figures for A_n(a)=tridiag(a,0,1).

Requires Python 3.9+, NumPy 1.23+, SciPy 1.9+, and Matplotlib 3.6+.
Run with

    python3 make_hatano_nelson_figures.py

The script writes vector PDF and 300 dpi PNG files to ``figures/``.  All
singular values are computed directly with LAPACK through NumPy.  The maxima
defining gamma_n are estimated gap by gap with bounded scalar optimization;
independent Lipschitz grid bounds certify the displayed topology labels.
"""

from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from scipy.optimize import minimize_scalar


OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(parents=True, exist_ok=True)
A_VALUE = 0.25
EPSILON = 1.0e-2


def set_style() -> None:
    """Compact, colorblind-safe styling suitable for a journal article."""
    mpl.rcParams.update(
        {
            "font.family": "serif",
            "font.serif": ["STIX Two Text", "STIXGeneral", "DejaVu Serif"],
            "mathtext.fontset": "stix",
            "font.size": 9.2,
            "axes.labelsize": 9.2,
            "axes.titlesize": 9.0,
            "legend.fontsize": 8.5,
            "xtick.labelsize": 8.5,
            "ytick.labelsize": 8.5,
            "axes.linewidth": 0.7,
            "lines.linewidth": 1.2,
            "xtick.major.width": 0.7,
            "ytick.major.width": 0.7,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "savefig.bbox": "tight",
            "savefig.pad_inches": 0.025,
        }
    )


def matrix(n: int, a: float) -> np.ndarray:
    """Return A_n(a), with 1 above and a below the main diagonal."""
    ans = np.zeros((n, n), dtype=float)
    j = np.arange(n - 1)
    ans[j, j + 1] = 1.0
    ans[j + 1, j] = a
    return ans


def obc_eigenvalues(n: int, a: float) -> np.ndarray:
    k = np.arange(1, n + 1)
    return np.sort(2.0 * np.sqrt(a) * np.cos(k * np.pi / (n + 1)))


def smin_grid(n: int, a: float, xs: np.ndarray, ys: np.ndarray) -> np.ndarray:
    """Directly sample s_min(zI-A_n) on a Cartesian complex grid."""
    A = matrix(n, a)
    eye = np.eye(n)
    vals = np.empty((ys.size, xs.size))
    for iy, y in enumerate(ys):
        for ix, x in enumerate(xs):
            vals[iy, ix] = np.linalg.svd(
                (x + 1j * y) * eye - A, compute_uv=False
            )[-1]
    return vals


def gap_maxima(n: int, a: float) -> list[tuple[float, float]]:
    """Estimate (height, abscissa) for every real spectral-gap maximum.

    A 121-point scan first brackets the maximum.  A bounded optimization then
    refines it.  The scan makes the routine robust if the maximizing gap shifts
    as n changes.
    """
    A = matrix(n, a)
    eye = np.eye(n)
    eig = obc_eigenvalues(n, a)

    def smin_real(x: float) -> float:
        return np.linalg.svd(x * eye - A, compute_uv=False)[-1]

    maxima: list[tuple[float, float]] = []
    for left, right in zip(eig[:-1], eig[1:]):
        trial_x = np.linspace(left, right, 121)
        trial_y = np.array([smin_real(x) for x in trial_x])
        j = int(np.argmax(trial_y))
        lo = trial_x[max(0, j - 1)]
        hi = trial_x[min(trial_x.size - 1, j + 1)]
        result = minimize_scalar(
            lambda x: -smin_real(x),
            bounds=(lo, hi),
            method="bounded",
            options={"xatol": 5.0e-14, "maxiter": 250},
        )
        if not result.success:
            raise RuntimeError(f"gap optimization failed for n={n}: {result.message}")
        optimized = (smin_real(result.x), float(result.x))
        sampled = (float(trial_y[j]), float(trial_x[j]))
        maxima.append(max(optimized, sampled, key=lambda pair: pair[0]))
    return maxima


def gamma(n: int, a: float) -> tuple[float, float]:
    """Return a numerical estimate of gamma_n and one maximizing abscissa."""
    return max(gap_maxima(n, a), key=lambda pair: pair[0])


def gamma_certificate(
    n: int, a: float, points_per_gap: int = 1001
) -> tuple[float, float]:
    """Enclose gamma_n using the 1-Lipschitz property of the least singular value.

    On a uniform gap grid of spacing h, the sampled maximum is a lower bound
    and the sampled maximum plus h/2 is an upper bound.  Taking the largest
    lower and upper bounds over all real spectral gaps encloses gamma_n.
    """
    if points_per_gap < 2:
        raise ValueError("points_per_gap must be at least 2")
    A = matrix(n, a)
    eye = np.eye(n)
    eig = obc_eigenvalues(n, a)
    lower = 0.0
    upper = 0.0
    for left, right in zip(eig[:-1], eig[1:]):
        grid = np.linspace(left, right, points_per_gap)
        sampled_max = max(
            np.linalg.svd(x * eye - A, compute_uv=False)[-1] for x in grid
        )
        spacing = (right - left) / (points_per_gap - 1)
        lower = max(lower, float(sampled_max))
        upper = max(upper, float(sampled_max + spacing / 2.0))
    return lower, upper


def analytic_bounds(n: int, a: float) -> tuple[float, float]:
    """Return the lower and upper bounds L_n(a), U_n(a) in the theorem."""
    r = np.sqrt(a)
    N = n + 1
    upper = r**n / np.sin(np.pi / N)
    lower = (
        (1.0 + r**2 - 2.0 * r * np.cos(np.pi / N))
        * r**n
        * (1.0 - r**2)
        / ((1.0 - r ** (2 * N)) * np.sin(3.0 * np.pi / (2.0 * N)))
    )
    return lower, upper


def save_both(fig: mpl.figure.Figure, stem: str) -> None:
    fig.savefig(OUT / f"{stem}.pdf")
    fig.savefig(OUT / f"{stem}.png", dpi=300)
    plt.close(fig)


def figure_topology(
    gamma_cache: dict[int, tuple[float, float]],
    certificate_cache: dict[int, tuple[float, float]],
) -> None:
    """Five-panel view of the transition at the exact threshold N_c=7."""
    ns = (5, 6, 7, 8, 9)
    xs = np.linspace(-1.12, 1.12, 561)
    ys = np.linspace(-0.30, 0.30, 361)
    fill = "#9bd8d6"
    edge = "#213b70"
    eig_color = "#b23a48"

    fig = plt.figure(figsize=(7.15, 4.10))
    grid = fig.add_gridspec(2, 6)
    panel_slots = (
        (0, slice(1, 3)),
        (0, slice(3, 5)),
        (1, slice(0, 2)),
        (1, slice(2, 4)),
        (1, slice(4, 6)),
    )
    axes = []
    for row, columns in panel_slots:
        shared = axes[0] if axes else None
        axes.append(
            fig.add_subplot(grid[row, columns], sharex=shared, sharey=shared)
        )

    for panel, (ax, n) in enumerate(zip(axes, ns)):
        vals = smin_grid(n, A_VALUE, xs, ys)
        ax.contourf(xs, ys, vals, levels=[-1.0, EPSILON], colors=[fill])
        ax.contour(xs, ys, vals, levels=[EPSILON], colors=[edge], linewidths=1.15)
        eig = obc_eigenvalues(n, A_VALUE)
        ax.plot(eig, np.zeros(n), "x", color=eig_color, ms=4.0, mew=1.0)
        ax.axhline(0.0, color="0.55", lw=0.45, zorder=0)
        g, _ = gamma_cache[n]
        lower, upper = certificate_cache[n]
        if lower >= EPSILON:
            relation = ">"
            state = "disconnected"
        elif upper < EPSILON:
            relation = "<"
            state = "connected"
        else:
            raise RuntimeError(f"topology is not certified for n={n}")
        ax.set_title(
            rf"({chr(97 + panel)}) $n={n}$: {state}"
            + "\n"
            + rf"$\widehat{{\gamma}}_n={g:.4f}\ {relation}\ \varepsilon$",
            pad=3,
        )
        ax.set_xlim(xs[0], xs[-1])
        ax.set_ylim(ys[0], ys[-1])
        ax.set_xticks([-1.0, -0.5, 0.0, 0.5, 1.0])
        ax.set_yticks([-0.25, 0.0, 0.25])
        ax.set_xlabel(r"$\operatorname{Re}z$")
        if panel not in (0, 2):
            ax.tick_params(labelleft=False)
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
    axes[0].set_ylabel(r"$\operatorname{Im}z$")
    axes[2].set_ylabel(r"$\operatorname{Im}z$")
    fig.subplots_adjust(wspace=0.42, hspace=0.62)
    save_both(fig, "fig1_connectedness_transition")


def figure_barrier_bounds(gamma_cache: dict[int, tuple[float, float]]) -> None:
    """Exact barrier sequence and the sharp-order theoretical enclosure."""
    ns = np.arange(2, 19)
    gammas = np.array([gamma_cache[int(n)][0] for n in ns])
    bounds = np.array([analytic_bounds(int(n), A_VALUE) for n in ns])
    lower, upper = bounds[:, 0], bounds[:, 1]
    nc = int(ns[np.flatnonzero(gammas < EPSILON)[0]])

    fig, ax = plt.subplots(figsize=(4.85, 3.05))
    ax.fill_between(ns, lower, upper, color="#d9d9d9", alpha=0.72, label="analytic enclosure")
    ax.semilogy(ns, upper, "--", color="#777777", lw=1.0, label=r"$\mathcal{U}_n$")
    ax.semilogy(ns, lower, ":", color="#555555", lw=1.2, label=r"$\mathcal{L}_n$")
    ax.semilogy(
        ns,
        gammas,
        "o-",
        color="#176d8c",
        markerfacecolor="white",
        markeredgewidth=0.9,
        ms=3.8,
        label=r"SVD estimate $\widehat{\gamma}_n$",
        zorder=3,
    )
    ax.axhline(EPSILON, color="#b23a48", lw=1.0, label=r"$\varepsilon=10^{-2}$")
    ax.axvline(nc, color="0.25", lw=0.75)
    ax.text(nc + 0.25, 2.0e-1, rf"$N_c={nc}$", ha="left", va="center")
    ax.axvspan(nc, ns[-1] + 0.5, color="#9bd8d6", alpha=0.15, lw=0)
    ax.set_xlim(ns[0] - 0.4, ns[-1] + 0.4)
    ax.set_ylim(2.0e-6, 8.0e-1)
    ax.set_xticks(np.arange(2, 19, 2))
    ax.set_xlabel(r"matrix order $n$")
    ax.set_ylabel(r"real-gap barrier")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.legend(
        loc="lower center",
        bbox_to_anchor=(0.5, 1.025),
        frameon=False,
        ncol=5,
        borderaxespad=0.0,
        columnspacing=0.75,
        handlelength=1.6,
        handletextpad=0.45,
        fontsize=8.0,
    )
    fig.subplots_adjust(top=0.82, bottom=0.18)
    save_both(fig, "fig2_gap_barrier_bounds")


def figure_physical_interpretation() -> None:
    """PBC/OBC spectral geometry and the right-eigenvector skin effect."""
    a = A_VALUE
    n = 20
    xs = np.linspace(-1.40, 1.40, 501)
    ys = np.linspace(-0.90, 0.90, 361)
    vals = smin_grid(n, a, xs, ys)
    contour_levels = (1.0e-6, 1.0e-4, 1.0e-2)
    contour_colors = ("#3b4cc0", "#168aad", "#d1495b")
    contour_styles = ("-", ":", "-.")

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.15, 3.40))

    ax.contour(
        xs,
        ys,
        vals,
        levels=contour_levels,
        colors=contour_colors,
        linestyles=contour_styles,
        linewidths=(1.0, 1.1, 1.2),
    )
    theta = np.linspace(0.0, 2.0 * np.pi, 801)
    symbol = np.exp(1j * theta) + a * np.exp(-1j * theta)
    ax.plot(symbol.real, symbol.imag, "--", color="0.20", lw=1.0)
    eig = obc_eigenvalues(n, a)
    ax.plot(eig, np.zeros(n), "x", color="#222222", ms=2.8, mew=0.75)
    ax.axhline(0.0, color="0.7", lw=0.45, zorder=0)
    ax.axvline(0.0, color="0.7", lw=0.45, zorder=0)
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlim(xs[0], xs[-1])
    ax.set_ylim(ys[0], ys[-1])
    ax.set_xlabel(r"$\operatorname{Re}z$")
    ax.set_ylabel(r"$\operatorname{Im}z$")
    ax.set_title(r"(a) OBC pseudospectra and PBC symbol")
    handles = [
        Line2D(
            [0],
            [0],
            color=color,
            ls=style,
            lw=1.2,
            label=rf"$\varepsilon=10^{{{int(np.log10(level))}}}$",
        )
        for level, color, style in zip(
            contour_levels, contour_colors, contour_styles
        )
    ]
    handles += [
        Line2D([0], [0], color="0.20", lw=1.0, ls="--", label="PBC ellipse"),
        Line2D([0], [0], color="#222222", marker="x", lw=0, ms=3, label="OBC eigenvalues"),
    ]
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

    sites = np.arange(1, n + 1)
    r = np.sqrt(a)
    modes = (1, 5, 10)
    mode_colors = ("#3b4cc0", "#168aad", "#d1495b")
    mode_styles = (("-", "o"), ("--", "s"), (":", "^"))
    all_density = []
    for m in range(1, n + 1):
        vector = r ** (sites - 1) * np.sin(m * np.pi * sites / (n + 1))
        density = np.abs(vector) ** 2
        density /= density.sum()
        all_density.append(density)
        if m in modes:
            mode_position = modes.index(m)
            color = mode_colors[mode_position]
            line_style, marker = mode_styles[mode_position]
            bx.semilogy(
                sites,
                density,
                marker=marker,
                linestyle=line_style,
                color=color,
                ms=2.5,
                lw=0.9,
                label=rf"mode $m={m}$",
            )
    mean_density = np.mean(np.asarray(all_density), axis=0)
    bx.semilogy(sites, mean_density, color="#222222", lw=1.6, label="mode average")
    bx.axhline(1.0 / n, color="0.45", ls="--", lw=0.9, label=r"reciprocal mean $1/n$")
    bx.set_xlim(0.5, n + 0.5)
    bx.set_ylim(1.0e-12, 1.2)
    bx.set_xticks([1, 5, 10, 15, 20])
    bx.set_xlabel(r"site $j$")
    bx.set_ylabel(r"normalized $|\psi_m^R(j)|^2$")
    bx.set_title(r"(b) OBC right-eigenvector skin modes")
    bx.set_box_aspect((ys[-1] - ys[0]) / (xs[-1] - xs[0]))
    right_handles, right_labels = bx.get_legend_handles_labels()
    bx.spines["top"].set_visible(False)
    bx.spines["right"].set_visible(False)
    fig.subplots_adjust(wspace=0.38, bottom=0.36, top=0.89)
    fig.canvas.draw()
    left_box = ax.get_position()
    right_box = bx.get_position()
    legend_y = 0.255
    legend_style = {
        "loc": "upper left",
        "frameon": False,
        "ncol": 2,
        "mode": "expand",
        "borderaxespad": 0.0,
        "columnspacing": 1.0,
        "handlelength": 2.0,
        "handleheight": 1.5,
        "labelspacing": 0.35,
    }
    fig.legend(
        handles=handles,
        bbox_to_anchor=(left_box.x0, legend_y, left_box.width, 0.0),
        **legend_style,
    )
    fig.legend(
        handles=right_handles,
        labels=right_labels,
        bbox_to_anchor=(right_box.x0 - 0.02, legend_y, right_box.width + 0.02, 0.0),
        **legend_style,
    )
    save_both(fig, "fig3_hatano_nelson_physics")


def main() -> None:
    set_style()
    gamma_cache = {n: gamma(n, A_VALUE) for n in range(2, 19)}
    certificate_cache = {
        n: gamma_certificate(n, A_VALUE) for n in range(2, 19)
    }
    for n, (g, _) in gamma_cache.items():
        lower, upper = certificate_cache[n]
        if not lower - 1.0e-12 <= g <= upper + 1.0e-12:
            raise RuntimeError(f"optimized estimate lies outside certificate for n={n}")
    figure_topology(gamma_cache, certificate_cache)
    figure_barrier_bounds(gamma_cache)
    figure_physical_interpretation()

    gammas = np.array([gamma_cache[n][0] for n in range(2, 19)])
    ambiguous = [
        n
        for n, (lower, upper) in certificate_cache.items()
        if lower < EPSILON <= upper
    ]
    if ambiguous:
        raise RuntimeError(f"uncertified topology at n={ambiguous}")
    nc = next(n for n in range(2, 19) if certificate_cache[n][1] < EPSILON)
    lower_threshold = 1 + max(
        [n for n in range(2, 100) if analytic_bounds(n, A_VALUE)[0] >= EPSILON],
        default=1,
    )
    upper_threshold = next(
        n for n in range(2, 100) if analytic_bounds(n, A_VALUE)[1] < EPSILON
    )
    print(f"Parameters: a={A_VALUE:g}, epsilon={EPSILON:g}")
    print(f"Numerical connectedness threshold: N_c={nc}")
    print(f"Theorem's explicit bracket: {lower_threshold} <= N_c <= {upper_threshold}")
    for n in (5, 6, 7, 8, 9):
        g, x = gamma_cache[n]
        lower, upper = certificate_cache[n]
        state = "connected" if upper < EPSILON else "disconnected"
        print(
            f"n={n:2d}: gamma_n~{g:.12g} at x={x:+.8g}; "
            f"certificate [{lower:.9g}, {upper:.9g}]; {state}"
        )
    drops = gammas[:-1] - gammas[1:]
    print(f"Smallest observed drop gamma_n-gamma_(n+1): {drops.min():.6e}")
    print("Created:")
    for stem in (
        "fig1_connectedness_transition",
        "fig2_gap_barrier_bounds",
        "fig3_hatano_nelson_physics",
    ):
        print(f"  {OUT / (stem + '.pdf')}")
        print(f"  {OUT / (stem + '.png')}")


if __name__ == "__main__":
    main()
