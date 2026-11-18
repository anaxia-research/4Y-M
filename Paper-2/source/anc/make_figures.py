"""Black-and-white schematics for the paper. Run from detailed/: python3 figures/make_figures.py"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection

OUT = os.path.dirname(os.path.abspath(__file__))
plt.rcParams.update({"font.family": "serif", "font.size": 9, "mathtext.fontset": "stix",
                     "axes.edgecolor": "black", "text.color": "black"})
K = "black"


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + ".png"), dpi=200, bbox_inches="tight",
                facecolor="white")
    plt.close(fig)


def clean3d(ax, elev=22, azim=-55):
    ax.view_init(elev=elev, azim=azim)
    ax.set_axis_off()
    ax.set_facecolor("white")
    try:
        ax.set_box_aspect((1, 1, 1))
    except Exception:
        pass


def cube_faces(x0, y0, z0, dx, dy, dz):
    v = np.array([[x0, y0, z0], [x0 + dx, y0, z0], [x0 + dx, y0 + dy, z0], [x0, y0 + dy, z0],
                  [x0, y0, z0 + dz], [x0 + dx, y0, z0 + dz], [x0 + dx, y0 + dy, z0 + dz], [x0, y0 + dy, z0 + dz]])
    f = [[0, 1, 2, 3], [4, 5, 6, 7], [0, 1, 5, 4], [2, 3, 7, 6], [1, 2, 6, 5], [0, 3, 7, 4]]
    return [v[i] for i in f]


def draw_cube(ax, x0, y0, z0, dx, dy, dz, fc="white", ec=K, lw=0.8, alpha=1.0, hatch=None):
    pc = Poly3DCollection(cube_faces(x0, y0, z0, dx, dy, dz), facecolors=fc, edgecolors=ec,
                          linewidths=lw, alpha=alpha)
    if hatch:
        pc.set_hatch(hatch)
    ax.add_collection3d(pc)


def lattice_lines(ax, n, lw=0.3, color="0.55", z0=0, nz=None):
    nz = n if nz is None else nz
    segs = []
    for i in range(n + 1):
        for j in range(n + 1):
            segs.append([(i, j, z0), (i, j, z0 + nz)])
            segs.append([(i, z0 if False else j, 0), (i, j, 0)])
    segs = []
    for i in range(n + 1):
        for k in range(nz + 1):
            segs.append([(i, 0, k), (i, n, k)])
            segs.append([(0, i, k), (n, i, k)])
        for j in range(n + 1):
            segs.append([(i, j, 0), (i, j, nz)])
    ax.add_collection3d(Line3DCollection(segs, colors=color, linewidths=lw))


# ---------------------------------------------------------------- 1. the cube and finite speed
def cube_edges(x0, y0, z0, d):
    c = [(x0 + i * d, y0 + j * d, z0 + k * d) for i in (0, 1) for j in (0, 1) for k in (0, 1)]
    return [[p, q] for p in c for q in c if p < q and sum(abs(u - v) > 1e-9 for u, v in zip(p, q)) == 1]


def leader(ax, p, q, s, fs=8, **kw):
    """label s at q with a thin leader from the object point p."""
    ax.plot([p[0], q[0]], [p[1], q[1]], [p[2], q[2]], color="0.25", lw=0.5)
    ax.text(q[0], q[1], q[2], s, color=K, fontsize=fs, zorder=50, bbox=dict(fc="white", ec="none", pad=0.6), **kw)


def fig_cube():
    fig = plt.figure(figsize=(7.2, 3.5))
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    L, n = 7, 3
    lattice_lines(ax, L, lw=0.2, color="0.72")
    draw_cube(ax, 2, 2, 2, n, n, n, fc="0.45", alpha=0.9)
    ax.add_collection3d(Line3DCollection(cube_edges(1, 1, 1, n + 2), colors=K, linewidths=1.1,
                                         linestyles="--"))
    ax.plot([2], [2], [2], marker="o", color=K, ms=3.5, zorder=20)
    leader(ax, (2, 2, 2), (3.0, -3.0, -0.6), r"corner $x$", ha="left", va="top")
    leader(ax, (3.5, 2, 4.5), (5.5, -1.0, 8.4), r"cube $V_x$, side $n$", ha="left", va="bottom")
    leader(ax, (6, 1, 3.5), (9.3, -0.5, 3.0), "links meeting\n" + r"$V_x$ from outside", ha="left", va="center", fs=7.5)
    ax.set_xlim(0, L); ax.set_ylim(0, L); ax.set_zlim(0, L)
    clean3d(ax, elev=20, azim=-50)
    ax.set_title(r"(a) one cube $V_x$ and the links that enter its law", fontsize=8.5)

    ax = fig.add_subplot(1, 2, 2, projection="3d")
    L = 9
    c = 4
    segs = []
    for i in range(L + 1):
        segs.append([(i, 0, 0), (i, L, 0)])
        segs.append([(0, i, 0), (L, i, 0)])
    ax.add_collection3d(Line3DCollection(segs, colors="0.75", linewidths=0.25))
    for m, ls, lw in [(3, ":", 1.0), (2, "--", 1.0), (1, "-", 1.0)]:
        ax.add_collection3d(Line3DCollection(cube_edges(c - m, c - m, c - m, 2 * m + 1), colors=K,
                                             linewidths=lw, linestyles=ls))
    draw_cube(ax, c, c, c, 1, 1, 1, fc="0.2", alpha=1)
    leader(ax, (c + 1, c, c + 0.5), (L + 4.6, -0.5, 6.4), r"$S$", ha="left", va="center")
    leader(ax, (c + 2, c - 1, c + 1), (L + 4.6, -0.5, 4.8), r"$Y_1(S)$", ha="left", va="center")
    leader(ax, (c + 3, c - 2, c), (L + 4.6, -0.5, 3.2), r"$Y_2(S)$", ha="left", va="center")
    leader(ax, (c + 4, c - 3, c - 1), (L + 4.6, -0.5, 1.6), r"$Y_3(S)$", ha="left", va="center")
    ax.set_xlim(0, L); ax.set_ylim(0, L); ax.set_zlim(0, L)
    clean3d(ax, elev=20, azim=-50)
    ax.set_title(r"(b) the sets $Y_m(S)$: each step moves at most $n$ links", fontsize=8.5)
    save(fig, "fig_cube")


# ---------------------------------------------------------------- 4. lattice gap surface and the spectrum
def fig_spectrum():
    fig = plt.figure(figsize=(7.2, 3.3))
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    # curvature route: m_G(beta) = arccosh(1 + (1/(2 beta) - 29/2)/12), beta < 1/29, every SU(N)
    b1 = np.linspace(0.0025, 1 / 29 - 0.0003, 200)
    m1 = np.arccosh(1 + (1 / (2 * b1) - 29 / 2) / 12)
    # Dobrushin route for SU(2): m >= -log(3 beta_W) = -log(12 beta), beta < 1/12
    b2 = np.linspace(0.0025, 1 / 12 - 0.0005, 200)
    m2 = -np.log(12 * b2)
    ax.plot(b2, [1.0] * len(b2), np.minimum(m2, 4), color=K, lw=1.1, ls="--")
    ax.plot(b1, [0.0] * len(b1), np.minimum(m1, 4), color=K, lw=1.3)
    for bb, mm, yv in ((b1, m1, 0.0), (b2, m2, 1.0)):
        sel = np.arange(0, len(bb), 25)
        for i in sel:
            ax.plot([bb[i], bb[i]], [yv, yv], [0, min(mm[i], 4)], color="0.6", lw=0.4)
    ax.plot([1 / 29, 1 / 29], [0, 0], [0, 4], color="0.3", lw=0.6, ls=":")
    ax.plot([1 / 12, 1 / 12], [1, 1], [0, 4], color="0.3", lw=0.6, ls=":")
    ax.text2D(0.03, 0.80, "solid: curvature route,\nevery SU($N$), " + r"$\beta<\frac{1}{29}$", color=K, fontsize=7, ha="left", transform=ax.transAxes)
    ax.text2D(0.62, 0.80, "dashed: Dobrushin\nroute, SU(2), " + r"$\beta<\frac{1}{12}$", color=K, fontsize=7, ha="left", transform=ax.transAxes)
    ax.set_xlabel(r"$\beta$", labelpad=2)
    ax.set_yticks([0, 1]); ax.set_yticklabels(["", ""])
    ax.set_zlabel("rate", labelpad=2)
    ax.set_xticks([0, 0.03, 0.06, 0.09])
    ax.set_xlim(0, 0.09); ax.set_ylim(-0.3, 1.3); ax.set_zlim(0, 4)
    ax.view_init(elev=22, azim=-62)
    ax.set_title(r"(a) Theorem A: $m_G(\beta)$ and $-\log(3\beta_W)$", fontsize=8)
    for a_ in (ax.xaxis, ax.yaxis, ax.zaxis):
        a_.pane.fill = False
        a_.pane.set_edgecolor("0.7")
    ax.grid(False)
    ax.tick_params(labelsize=6)

    ax = fig.add_subplot(1, 2, 2, projection="3d")
    # spectrum picture: energy axis, with vacuum at 0, gap, continuum above Delta
    ax.plot([0, 0], [0, 0], [0, 1.1], color=K, lw=1)
    ax.text(0, 0, 1.15, r"$\sigma(H)$", color=K, ha="center")
    ax.plot([0], [0], [0], marker="o", color=K, ms=5)
    ax.text(0.08, 0, 0.0, r"$0$: simple, $\Omega$", color=K, fontsize=8)
    th = np.linspace(0, 2 * np.pi, 60)
    for z in np.linspace(0.45, 1.05, 14):
        r = 0.3 * (z - 0.45) / 0.6 + 0.05
        ax.plot(r * np.cos(th), r * np.sin(th), z, color="0.3", lw=0.5)
    ax.plot([0, 0.5], [0, 0], [0.45, 0.45], color=K, lw=0.6, ls="--")
    ax.text(0.52, 0, 0.45, r"$\Delta=\frac{16\varpi}{625e^2\ell}$", color=K, fontsize=9)
    ax.annotate("", xy=(0, 0), xytext=(0, 0))
    ax.plot([-0.35, -0.35], [0, 0], [0.0, 0.45], color=K, lw=1)
    ax.plot([-0.4, -0.3], [0, 0], [0.0, 0.0], color=K, lw=1)
    ax.plot([-0.4, -0.3], [0, 0], [0.45, 0.45], color=K, lw=1)
    ax.text(-0.75, 0, 0.2, "gap", color=K, fontsize=8)
    ax.text(0.45, 0, 0.9, r"$[\Delta,\infty)$", color=K, fontsize=8)
    ax.set_xlim(-0.6, 0.6); ax.set_ylim(-0.6, 0.6); ax.set_zlim(0, 1.2)
    clean3d(ax, elev=12, azim=-80)
    ax.set_title(r"(b) the spectrum of $H$ under Theorems B and E", fontsize=8)
    save(fig, "fig_spectrum")


# ---------------------------------------------------------------- 6. a star
def fig_star():
    fig = plt.figure(figsize=(7.2, 3.2))
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    lattice_lines(ax, 4, lw=0.25)
    c = np.array([2, 2, 2])
    for e in np.eye(3):
        for s in (+1, -1):
            p = c + s * e
            ax.plot([c[0], p[0]], [c[1], p[1]], [c[2], p[2]], color=K, lw=2.2)
    # fourth direction drawn as a short diagonal stub, both ways
    for s in (+1, -1):
        p = c + s * np.array([0.55, 0.55, 0.55])
        ax.plot([c[0], p[0]], [c[1], p[1]], [c[2], p[2]], color=K, lw=2.2, ls=(0, (2, 1)))
    ax.plot([2], [2], [2], marker="o", color=K, ms=5)
    leader(ax, (2, 2, 3), (1.0, -1.0, 5.3), r"vertex $x$ and its eight links", ha="center", va="bottom")
    leader(ax, (2.55, 2.55, 2.55), (5.6, 1.5, 3.2), r"$\pm e_0$ (dashed)", ha="left", va="center", fs=7.5)
    ax.set_xlim(0, 4); ax.set_ylim(0, 4); ax.set_zlim(0, 4)
    clean3d(ax, elev=20, azim=-55)
    ax.set_title("(a) a star: the links at one vertex", fontsize=8.5)

    ax = fig.add_subplot(1, 2, 2, projection="3d")
    lattice_lines(ax, 4, lw=0.25)
    for x in range(5):
        for y in range(5):
            for z in range(5):
                if (x + y + z) % 2 == 0:
                    ax.plot([x], [y], [z], marker="o", color=K, ms=3.5)
                else:
                    ax.plot([x], [y], [z], marker="o", color="white", mec=K, ms=3.5, mew=0.5)
    ax.text2D(0.5, 0.02, "filled: the vertices of one parity", color=K, fontsize=8, ha="center", transform=ax.transAxes)
    ax.set_xlim(0, 4); ax.set_ylim(0, 4); ax.set_zlim(0, 4)
    clean3d(ax, elev=20, azim=-55)
    ax.set_title("(b) the stars of one parity cover every link once", fontsize=8.5)
    save(fig, "fig_star")


# ---------------------------------------------------------------- 8. the line field
def fig_linefield():
    fig = plt.figure(figsize=(7.2, 3.3))
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    n = 3
    lattice_lines(ax, n, lw=0.35, color="0.6")
    # one marked link per site: alternate directions by site parity (schematic)
    dirs = [np.array([1, 0, 0]), np.array([0, 1, 0]), np.array([0, 0, 1])]
    for x in range(n):
        for y in range(n):
            for z in range(n):
                dvec = dirs[(x + 2 * y + z) % 3]
                p = np.array([x, y, z]); q = p + dvec
                ax.plot([p[0], q[0]], [p[1], q[1]], [p[2], q[2]], color=K, lw=2.4)
    ax.text2D(0.5, 0.86, "one marked link at every site (thick),\nset to the identity", color=K, fontsize=8, ha="center", transform=ax.transAxes)
    ax.set_xlim(0, n); ax.set_ylim(0, n); ax.set_zlim(0, n)
    clean3d(ax, elev=22, azim=-55)
    ax.set_title("(a) a direction field: schematic", fontsize=8.5)

    ax = fig.add_subplot(1, 2, 2, projection="3d")
    # one plaquette with one fixed link, and the twelve partners of an active link
    draw_cube(ax, 0, 0, 0, 1, 1, 0.0001, fc="0.8", alpha=0.6)
    ax.plot([0, 1], [0, 0], [0, 0], color=K, lw=3)
    ax.plot([1, 1], [0, 1], [0, 0], color=K, lw=1)
    ax.plot([0, 1], [1, 1], [0, 0], color=K, lw=1)
    ax.plot([0, 0], [0, 1], [0, 0], color=K, lw=1)
    ax.text(0.5, -0.25, 0.02, r"$\in F$", color=K, fontsize=8, ha="center")
    ax.text(0.5, 0.5, 0.05, r"$Q_p$", color=K, fontsize=9, ha="center")
    ax.text(1.5, 0.5, 0.0, "every plaquette\ncontains exactly\none link of $F$", color=K, fontsize=8)
    ax.set_xlim(-0.2, 2.2); ax.set_ylim(-0.4, 1.4); ax.set_zlim(-0.6, 0.6)
    clean3d(ax, elev=35, azim=-60)
    ax.set_title("(b) the gauge: twelve partners instead of eighteen", fontsize=8.5)
    save(fig, "fig_linefield")



# ---------------------------------------------------------------- oblique (cabinet) projection helpers, 2D axes
from matplotlib.patches import Polygon, FancyArrowPatch

DX, DY = 0.5, 0.32  # depth direction on the page


def P(x, y, z):
    """oblique projection: x to the right, z up, y into the page (up and to the right)."""
    return (x + DX * y, z + DY * y)


def poly(ax, pts3, fc="white", ec=K, lw=0.8, alpha=1.0, zorder=2, hatch=None, ls="-"):
    pg = Polygon([P(*p) for p in pts3], closed=True, facecolor=fc, edgecolor=ec, linewidth=lw,
                 alpha=alpha, zorder=zorder, hatch=hatch, linestyle=ls)
    ax.add_patch(pg)
    return pg


def box(ax, x0, y0, z0, dx, dy, dz, fc="white", ec=K, lw=0.8, alpha=1.0, zorder=2, top=None, side=None):
    """a box drawn as its three visible faces (front, top, right side)."""
    top = fc if top is None else top
    side = fc if side is None else side
    # back faces first for translucency
    poly(ax, [(x0, y0 + dy, z0), (x0 + dx, y0 + dy, z0), (x0 + dx, y0 + dy, z0 + dz), (x0, y0 + dy, z0 + dz)],
         fc=fc, ec=ec, lw=lw * 0.6, alpha=alpha * 0.6, zorder=zorder)
    poly(ax, [(x0, y0, z0), (x0, y0 + dy, z0), (x0, y0 + dy, z0 + dz), (x0, y0, z0 + dz)],
         fc=side, ec=ec, lw=lw * 0.6, alpha=alpha * 0.6, zorder=zorder)
    poly(ax, [(x0, y0, z0 + dz), (x0 + dx, y0, z0 + dz), (x0 + dx, y0 + dy, z0 + dz), (x0, y0 + dy, z0 + dz)],
         fc=top, ec=ec, lw=lw, alpha=alpha, zorder=zorder + 1)
    poly(ax, [(x0 + dx, y0, z0), (x0 + dx, y0 + dy, z0), (x0 + dx, y0 + dy, z0 + dz), (x0 + dx, y0, z0 + dz)],
         fc=side, ec=ec, lw=lw, alpha=alpha, zorder=zorder + 1)
    poly(ax, [(x0, y0, z0), (x0 + dx, y0, z0), (x0 + dx, y0, z0 + dz), (x0, y0, z0 + dz)],
         fc=fc, ec=ec, lw=lw, alpha=alpha, zorder=zorder + 2)


def line(ax, p, q, lw=0.8, color=K, ls="-", zorder=3):
    a, b = P(*p), P(*q)
    ax.plot([a[0], b[0]], [a[1], b[1]], color=color, lw=lw, ls=ls, zorder=zorder, solid_capstyle="round")


def arrow(ax, p, q, lw=0.9, color=K, ls="-", zorder=5, ms=7):
    a, b = P(*p), P(*q)
    ax.add_patch(FancyArrowPatch(a, b, arrowstyle="-|>", mutation_scale=ms, lw=lw, color=color,
                                 linestyle=ls, zorder=zorder, shrinkA=0, shrinkB=0))


def txt(ax, p, s, **kw):
    a = P(*p)
    kw.setdefault("color", K)
    kw.setdefault("zorder", 10)
    ax.text(a[0], a[1], s, **kw)


def flat(fig, w, h, xlim, ylim):
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(*xlim); ax.set_ylim(*ylim)
    ax.set_aspect("equal")
    ax.set_axis_off()
    return ax


# ---------------------------------------------------------------- 2. the two orders of limits
def fig_limits():
    fig = plt.figure(figsize=(7.2, 4.0))
    ax = flat(fig, 7.2, 4.0, (-0.6, 7.0), (-0.5, 3.7))
    # parameter space: x = mesh a (0 at the left, continuum), y (depth) = side L_p, z = time extent
    A, Lm, Tm = 4.0, 3.0, 3.0
    arrow(ax, (0, 0, 0), (A + 0.4, 0, 0))
    arrow(ax, (0, 0, 0), (0, Lm + 0.6, 0))
    arrow(ax, (0, 0, 0), (0, 0, Tm + 0.4))
    txt(ax, (A + 0.5, 0, -0.05), r"mesh $a_N=1/N$", va="center")
    txt(ax, (0.05, Lm + 0.7, 0), r"side $L_p$", va="center")
    txt(ax, (0, 0, Tm + 0.5), r"time extent $Ma_N$", ha="center", va="bottom")
    txt(ax, (-0.08, 0, 0), r"$a=0$", ha="right", va="center", fontsize=8)
    # the symmetric tori: time extent = side; a sheet over the (a, L) plane, drawn as a grid
    for L in np.linspace(0.6, Lm, 5):
        line(ax, (0, L, L), (A, L, L), lw=0.5, color="0.55")
    for a in np.linspace(0, A, 6):
        line(ax, (a, 0.6, 0.6), (a, Lm, Lm), lw=0.5, color="0.55")
    txt(ax, (A + 0.25, 1.5, 1.5), "sheet of symmetric\n" + r"tori, $M=NL_p$", fontsize=8, color="0.2", va="center")
    # (W): N -> infinity (a -> 0) at fixed L_p, along the sheet; then L_p -> infinity along a = 0
    for L in (1.2, 1.8, 2.4):
        arrow(ax, (A - 0.2, L, L), (0.0, L, L), lw=1.4)
    arrow(ax, (0, 1.2, 1.2), (0, Lm + 0.2, Lm + 0.2), lw=1.4, ls="--")
    txt(ax, (0.9, 2.1, 2.1), r"(W): $N\to\infty$ at fixed $L_p$, then $L_p\to\infty$", fontsize=8,
        ha="left", va="bottom", bbox=dict(fc="white", ec="none", pad=1))
    # (U): cylinders: M -> infinity first (vertical), then N -> infinity, then L_p -> infinity
    for a in (2.4, 1.2):
        for L in (1.2, 1.8):
            arrow(ax, (a, L, L), (a, L, Tm + 0.15), lw=0.9, ls=":")
    arrow(ax, (2.4, 1.2, Tm + 0.15), (0.0, 1.2, Tm + 0.15), lw=0.9, ls=":")
    txt(ax, (2.55, 1.2, Tm + 0.3), r"(U): $M\to\infty$ first (cylinders), then $N$, then $L_p$", fontsize=8,
        ha="left", va="bottom", bbox=dict(fc="white", ec="none", pad=1))
    txt(ax, (A + 0.3, 0.2, 0.25), r"(D$_\ell$): BP on each cylinder" + "\n" + r"$(\mathbb{Z}/NL_p)^3\times\mathbb{Z}/M$",
        fontsize=8, ha="left", va="center")
    txt(ax, (0.2, 0, -0.18), r"the limits on the edge $a=0$ are the theories $\mathbb{T}$, $\mathbb{T}^{(n)}$ of Theorem E", fontsize=8,
        ha="left", va="top")
    save(fig, "fig_limits")


# ---------------------------------------------------------------- 3. the transfer matrix of a cylinder
def fig_transfer():
    fig = plt.figure(figsize=(7.2, 3.0))
    ax = flat(fig, 7.2, 3.2, (-0.6, 14.0), (-1.5, 5.3))
    M, w, s, w2 = 11, 3, 7, 2
    S = 2.2  # spatial side drawn
    # time axis
    line(ax, (-0.3, S / 2, S / 2), (M + 1.0, S / 2, S / 2), lw=0.6, color="0.4")
    arrow(ax, (M + 0.6, S / 2, S / 2), (M + 1.2, S / 2, S / 2), lw=0.6, color="0.4")
    txt(ax, (M + 1.3, S / 2, S / 2), r"$t\in\mathbb{Z}/M\mathbb{Z}$", va="center", fontsize=8)
    # time slices, back to front is irrelevant here (all parallel); draw every slice
    for t in range(M + 1):
        dark = t in (0, w, s, s + w2)
        poly(ax, [(t, 0, 0), (t, S, 0), (t, S, S), (t, 0, S)], fc="0.6" if dark else "0.93",
             ec=K, lw=0.9 if dark else 0.4, alpha=0.95, zorder=4)
    # the two slabs as translucent boxes
    box(ax, 0, 0, 0, w, S, S, fc="0.75", alpha=0.35, lw=1.0, zorder=6)
    box(ax, s, 0, 0, w2, S, S, fc="0.75", alpha=0.35, lw=1.0, zorder=6)
    # labels
    for t, lab in ((0, r"$Q_0$"), (w, r"$Q_w$"), (s, r"$Q_s$"), (s + w2, r"$Q_{s+w'}$"), (M, r"$Q_M=Q_0$")):
        txt(ax, (t, 0, -0.25), lab, ha="center", va="top", fontsize=8)
    txt(ax, (w / 2, S, S + 0.25), r"$\hat F$ on the slab $[0,w]$", ha="center", va="bottom", fontsize=8.5)
    txt(ax, (s + w2 / 2, S, S + 0.25), r"$\hat H$ on $[s,s+w']$", ha="center", va="bottom", fontsize=8.5)
    # transfer matrix powers between the slabs
    for a, b, lab in ((w, s, r"$\mathbb{T}^{\,s-w}$"), (s + w2, M, r"$\mathbb{T}^{\,M-s-w'}$")):
        line(ax, (a + 0.15, 0, -0.9), (b - 0.15, 0, -0.9), lw=0.7)
        line(ax, (a + 0.15, 0, -1.05), (a + 0.15, 0, -0.75), lw=0.7)
        line(ax, (b - 0.15, 0, -1.05), (b - 0.15, 0, -0.75), lw=0.7)
        txt(ax, ((a + b) / 2, 0, -1.0), lab, ha="center", va="top", fontsize=8.5)
    txt(ax, (M / 2 + 0.6, 0, S + 1.75), r"$\langle F\,\tau_s H\rangle_{\Lambda}=\mathrm{Tr}\,(\hat F\,\mathbb{T}^{\,s-w}\hat H\,\mathbb{T}^{\,M-s-w'})/\mathrm{Tr}\,\mathbb{T}^{M}$",
        ha="center", va="bottom", fontsize=8.5)
    txt(ax, (-0.4, 0, -0.95), r"each slice: space $(\mathbb{Z}/NL_p)^3$", ha="left", va="top", fontsize=7.5, color="0.3")
    save(fig, "fig_transfer")


# ---------------------------------------------------------------- 5. the slab splitting
def fig_slab():
    fig = plt.figure(figsize=(7.2, 3.3))
    ax = flat(fig, 7.2, 3.3, (-0.8, 12.6), (-1.6, 5.2))
    d = 3
    Wd, Hh = 4.0, 3.0  # depth and height drawn
    # the fixed outside: a dashed frame
    poly(ax, [(-0.6, -0.5, -0.4), (3 * d - 1 + 0.6, -0.5, -0.4), (3 * d - 1 + 0.6, Wd + 0.5, -0.4), (-0.6, Wd + 0.5, -0.4)],
         fc="none", ec="0.4", lw=0.7, ls="--", zorder=1)
    # back to front: far blocks first; all at the same depth, draw left to right with grey for Q_-, Q_+
    box(ax, 0, 0, 0, d, Wd, Hh, fc="0.62", top="0.75", side="0.5", alpha=1.0, zorder=3)
    box(ax, d, 0, 0, d - 1, Wd, Hh, fc="white", top="0.97", side="0.9", alpha=1.0, zorder=3)
    box(ax, 2 * d - 1, 0, 0, d, Wd, Hh, fc="0.62", top="0.75", side="0.5", alpha=1.0, zorder=3)
    # lattice lines on the front faces
    for x in range(0, 3 * d):
        line(ax, (x, 0, 0), (x, 0, Hh), lw=0.25, color="0.3", zorder=8)
    for z in range(0, int(Hh) + 1):
        line(ax, (0, 0, z), (3 * d - 1, 0, z), lw=0.25, color="0.3", zorder=8)
    txt(ax, (d / 2, 0, -0.3), r"$Q_-$, width $d$", ha="center", va="top", fontsize=8.5)
    txt(ax, (2 * d - 1 + d / 2, 0, -0.3), r"$Q_+$, width $d$", ha="center", va="top", fontsize=8.5)
    txt(ax, (d + (d - 1) / 2, 0, -0.3), r"width $d-1$", ha="center", va="top", fontsize=8)
    txt(ax, (3 * d - 1 + 1.0, 0, -0.75), r"$\omega$ fixed on every link outside the dashed region", fontsize=8, va="top", color="0.25")
    txt(ax, (3 * d - 1 + 0.4, Wd, Hh / 2), r"$\rho^{\omega}(Q_-,Q_+)\leq c<\frac{1}{2}$" + "\n" +
        r"for every $\omega$: the slab decorrelation", fontsize=8.5, va="center")
    txt(ax, (d + (d - 1) / 2, Wd, Hh + 0.2), r"no plaquette meets both $Q_-$ and $Q_+$", ha="center", va="bottom", fontsize=8)
    txt(ax, (-0.4, 0, -1.2), r"$Q_-\cup Q_+$ is one slab of the torus; the middle layer separates them", fontsize=8, va="top")
    save(fig, "fig_slab")


# ---------------------------------------------------------------- 7. roadmap
def fig_roadmap():
    fig = plt.figure(figsize=(7.2, 4.6))
    ax = flat(fig, 7.2, 4.6, (-1.9, 13.9), (-0.6, 7.6))
    Wb, Hb, Dp = 3.15, 1.15, 0.35
    col = [0.0, 3.45, 6.9, 10.35]
    row = [0.0, 2.1, 4.2, 6.3]

    def node(c, r, text, open_=False, fs=6.9):
        x, z = col[c], row[r]
        box(ax, x, 0, z, Wb, Dp, Hb, fc="0.86" if open_ else "white", top="0.7" if open_ else "0.92",
            side="0.6" if open_ else "0.8", lw=0.9, zorder=3)
        txt(ax, (x + Wb / 2, 0, z + Hb / 2), text, ha="center", va="center", fontsize=fs, zorder=12)
        return x, z

    def link(c1, r1, c2, r2, ls="-", lw=0.9):
        x1, z1 = col[c1] + Wb / 2, row[r1] + Hb
        x2, z2 = col[c2] + Wb / 2, row[r2]
        arrow(ax, (x1, 0, z1), (x2, 0, z2), ls=ls, lw=lw, zorder=2)

    node(0, 0, "Theorem A\nlattice gap $m_G(\\beta)$\nstrong coupling, every $G$")
    node(1, 0, "Theorem C\ncube condition BP$(n,\\varpi)$\nSU(2) to $\\beta_W=\\frac{7}{20}$, SU(3) to $0.45$")
    node(2, 0, "Theorem D\nslab decorrelation $c<\\frac{1}{2}$\nimplies BP$(n,\\varpi)$")
    node(3, 0, "Appendices\nreflection positivity, Haar\nmoments, SU(3) one-link law")
    node(0, 1, "(E) continuum limit exists\n(Osterwalder--Schrader)", open_=True)
    node(1, 1, "(D) BP$(n_k,\\varpi)$ along the\nweak-coupling tuning $\\beta_k\\to\\infty$", open_=True)
    node(2, 1, "(D$_\\ell$) BP$(n_N,\\varpi)$ on the\ncylinders $(\\mathbb{Z}/NL_p)^3\\times\\mathbb{Z}/M$", open_=True)
    node(3, 1, "(U), or (Z): the two orders\nof the volume limits agree", open_=True)
    node(1, 2, "Theorem B\n$\\sigma(H)\\subset\\{0\\}\\cup[\\Delta,\\infty)$,\n$\\Delta=16\\varpi/(625e^2\\ell)$")
    node(2, 2, "Theorem E\ngap $\\Delta$, one phase, $0$ simple,\nin the theories on tori")
    node(3, 2, "(W) Wightman limit on\nsymmetric tori\n(unrefereed input)", open_=True)
    node(2, 3, "Clay statement for the\ntheories of (W): reduced to\n(W) and the one bound (B$^{*}$)", fs=7.3)
    node(1, 3, "Theorem F\n(W) and (B$^{*}$) give the gap\n$\\Delta\\geq 0.172/t_0$, $0$ simple")
    node(0, 2, "(B$^{*}$) one bound at one scale\n$\\log\\mathcal{Z}_s(T_0)\\leq\\gamma V(s)$", open_=True)
    link(0, 2, 1, 3)
    arrow(ax, (col[1] + Wb, 0, row[3] + Hb / 2), (col[2], 0, row[3] + Hb / 2), lw=0.9)
    link(0, 0, 1, 0 + 0) if False else None
    link(1, 0, 1, 1, ls=":")   # strong coupling result, open along the tuning
    link(2, 0, 1, 1, ls="--")
    link(2, 0, 2, 1, ls="--")
    link(0, 1, 1, 2)
    link(1, 1, 1, 2)
    link(2, 1, 2, 2)
    link(3, 1, 2, 2)
    link(3, 2, 2, 2)
    link(2, 2, 2, 3)
    arrow(ax, (col[0] + Wb, 0, row[0] + Hb / 2), (col[1], 0, row[0] + Hb / 2), lw=0.9)
    arrow(ax, (col[3], 0, row[0] + Hb / 2), (col[2] + Wb, 0, row[0] + Hb / 2), lw=0.9)
    txt(ax, (-0.3, 0, row[0] + Hb / 2), "proved\n(lattice)", ha="right", va="center", fontsize=7.5)
    txt(ax, (-0.3, 0, row[1] + Hb / 2), "hypotheses\n(open)", ha="right", va="center", fontsize=7.5)
    txt(ax, (-0.3, 0, row[2] + Hb / 2), "continuum\n(proved from\nthe hypotheses)", ha="right", va="center", fontsize=7.5)
    txt(ax, (-0.3, 0, row[3] + Hb / 2), "the gap", ha="right", va="center", fontsize=7.5)
    txt(ax, (col[3] + 0.25, 0, row[3] + Hb / 2),
        "solid: an implication proved here\ndashed: Theorem D gives the\nhypothesis when the slab\nconstant is below $\\frac{1}{2}$\ndotted: proved at strong\ncoupling only",
        ha="left", va="center", fontsize=7)
    save(fig, "fig_roadmap")


# ---------------------------------------------------------------- 9. thermal versus zero temperature
def fig_thermal():
    fig = plt.figure(figsize=(7.2, 3.4))
    ax = flat(fig, 7.2, 3.4, (-0.9, 8.6), (-1.1, 3.5))
    m = 1.6
    Ms = [1.5, 2.5, 3.5]
    H = 2.2  # height scale
    # floor grid: s along x (0..4), M along depth (0..4)
    for s in range(0, 5):
        line(ax, (s, 0, 0), (s, 4, 0), lw=0.3, color="0.6")
    for yv in range(0, 5):
        line(ax, (0, yv, 0), (4, yv, 0), lw=0.3, color="0.6")
    arrow(ax, (0, 0, 0), (4.6, 0, 0), lw=0.8)
    arrow(ax, (0, 0, 0), (0, 4.6, 0), lw=0.8)
    arrow(ax, (0, 0, 0), (0, 0, H + 0.5), lw=0.8)
    txt(ax, (4.7, 0, 0), r"separation $s$", va="center", fontsize=8.5)
    
    txt(ax, (0, 0, H + 0.6), "two-point function", ha="center", va="bottom", fontsize=8.5)
    # thermal curves at depth M: sum of two exponentials, symmetric about M/2; drawn from back to front
    for M in reversed(Ms):
        ss = np.linspace(0, M, 120)
        f = (np.exp(-m * ss) + np.exp(-m * (M - ss))) / (1 + np.exp(-m * M))
        pts = [P(x, M, H * v) for x, v in zip(ss, f)]
        ax.plot([p[0] for p in pts], [p[1] for p in pts], color=K, lw=1.1, zorder=5)
        # drop lines at both ends and the midpoint marker
        line(ax, (0, M, 0), (0, M, H * f[0]), lw=0.4, color="0.5")
        line(ax, (M, M, 0), (M, M, H * f[-1]), lw=0.4, color="0.5")
        mid = P(M / 2, M, H * f[60])
        ax.plot([mid[0]], [mid[1]], marker="o", color=K, ms=3, zorder=6)
        txt(ax, (M + 0.1, M, 0.05), r"period $M=%.1f$" % M, fontsize=7.5, va="bottom")
    # zero temperature: single decaying exponential at the back
    ss = np.linspace(0, 4, 120)
    pts = [P(x, 4.3, H * np.exp(-m * x)) for x in ss]
    ax.plot([p[0] for p in pts], [p[1] for p in pts], color=K, lw=1.4, ls="--", zorder=5)
    txt(ax, (4.1, 4.3, H * np.exp(-m * 4.1) + 0.1),
        r"$M=\infty$: $\sum_j r_j^{\,s}\,|\langle\phi_j,\Psi_F\rangle|^2$", fontsize=8, va="bottom")
    txt(ax, (2.0, 0, -0.55), r"thermal: $\sum_{i,j} r_i^{\,M-s} r_j^{\,s}\,\overline{F}_{ij}H_{ji}/\mathrm{Tr}\,\mathbb{T}^M$, symmetric about $s=M/2$",
        ha="center", va="top", fontsize=8)
    txt(ax, (2.0, 0, -0.9), r"the terms with $i,j\geq1$ are each at most $r_1^{\,M}$, but their sum is not controlled by the gap",
        ha="center", va="top", fontsize=7.5, color="0.25")
    save(fig, "fig_thermal")


# ---------------------------------------------------------------- 10. coupling ranges
def fig_couplings():
    fig = plt.figure(figsize=(7.2, 3.6))
    ax = flat(fig, 7.2, 3.4, (-0.4, 13.4), (-1.6, 2.9))
    rows = [
        (r"Theorem A, SU(2), curvature route: $\beta_W<\frac{4}{29}$", 4 / 29),
        (r"Theorem C(i), SU(2), weighted count: $|\beta_W|<\frac{5}{18}$", 5 / 18),
        (r"Theorem A, SU(2), Dobrushin route: $\beta_W<\frac{1}{3}$", 1 / 3),
        (r"Theorem C(iii), SU(2), stars, every $n$: $\beta_W\leq\frac{7}{20}$", 7 / 20),
        (r"Theorem C(iii), SU(2), lattice gap: $\beta_W\leq\frac{9}{25}$", 9 / 25),
        (r"Theorem C(i), SU(3), cube condition: $\beta_W\leq0.45$", 0.45),
    ]
    sc = 9.0  # page units per unit of beta_W
    gap = 0.9
    for i, (lab, b) in enumerate(reversed(rows)):
        yv = i * gap
        box(ax, 0, yv, 0, sc * b, gap * 0.8, 0.35, fc=str(0.45 + 0.08 * i), top=str(0.6 + 0.06 * i), side="0.35", lw=0.7, zorder=3 + i)
        line(ax, (sc * b, yv + gap * 0.4, 0.18), (sc * 0.5, yv + gap * 0.4, 0.18), lw=0.4, color="0.5", ls=":", zorder=15)
        txt(ax, (sc * 0.5 + 0.1, yv + gap * 0.4, 0.18), lab, fontsize=7.2, va="center", zorder=20,
            bbox=dict(fc="white", ec="none", pad=0.5))
    # scale on the front edge, with guide lines into the depth
    line(ax, (0, -0.15, 0), (sc * 0.55, -0.15, 0), lw=0.9)
    for b in (0.1, 0.2, 0.3, 0.4, 0.5):
        line(ax, (sc * b, -0.15, 0), (sc * b, -0.3, 0), lw=0.8)
        line(ax, (sc * b, -0.15, 0), (sc * b, len(rows) * gap, 0), lw=0.3, color="0.7", zorder=1)
        txt(ax, (sc * b, -0.4, 0), "%.1f" % b, ha="center", va="top", fontsize=7)
    txt(ax, (sc * 0.27, -0.9, 0), r"$\beta_W$ (Wilson's coupling; SU(2): $\beta_W=4\beta$, SU(3): $\beta_W=9\beta$)",
        ha="center", va="top", fontsize=8)
    arrow(ax, (sc * 0.55, -0.15, 0), (sc * 0.62, -0.15, 0), lw=0.9)
    txt(ax, (sc * 0.63, -0.15, -0.72), r"weak coupling $\beta_W\to\infty$, where the continuum limit lives: hypothesis (D)", fontsize=7.5, va="top")
    save(fig, "fig_couplings")




def fig_ascent():
    fig, (a, b) = plt.subplots(1, 2, figsize=(7.2, 3.1), gridspec_kw={"width_ratios": [1, 1.15]})
    # (a) the recursion y -> 16 (e^y - 1)^2
    y = np.linspace(0, 0.07, 400)
    g = 16 * (np.exp(y) - 1) ** 2
    a.plot(y, g, color=K, lw=1.3)
    a.plot(y, y, color="0.45", lw=0.8, ls="--")
    yc = 0.0589
    for _ in range(40):
        yc = yc - (16 * (np.exp(yc) - 1) ** 2 - yc) / (32 * (np.exp(yc) - 1) * np.exp(yc) - 1)
    a.plot([yc], [yc], "o", ms=4.5, mfc="white", mec=K)
    a.annotate(r"$y_c\approx%.4f$" % yc, (yc, yc), (0.034, 0.066), fontsize=8,
               arrowprops=dict(arrowstyle="-", lw=0.5, color=K))
    y0 = 0.05
    pts = [(y0, 0.0)]
    yy = y0
    for _ in range(3):
        nx = 16 * (np.exp(yy) - 1) ** 2
        pts += [(yy, nx), (nx, nx)]
        yy = nx
    px, py = zip(*pts)
    a.plot(px, py, color=K, lw=0.7)
    a.plot([y0], [0], "s", ms=4, color=K, clip_on=False)
    a.annotate(r"$y_0=\frac{1}{20}$", (y0, 0), (0.052, 0.008), fontsize=8)
    a.text(0.006, 0.060, r"$y_{i+1}=16\,(e^{y_i}-1)^2$", fontsize=9)
    a.text(0.006, 0.052, r"$16.83\,y_i\leq u_0^{\,2^i}$", fontsize=9)
    a.set_xlim(0, 0.07); a.set_ylim(0, 0.07)
    a.set_xlabel(r"$y_i$"); a.set_ylabel(r"$y_{i+1}$")
    a.set_title("(a) one doubling of the time", fontsize=9)
    for s in ("top", "right"):
        a.spines[s].set_visible(False)
    # (b) the ladder of scales
    b.set_xlim(0, 10); b.set_ylim(0, 7.2); b.axis("off")
    b.set_title("(b) the ladder of scales", fontsize=9)
    rows = [(r"$T_0$", r"$[2T_0,\,48T_0)$", "0.82", r"hypothesis (B$^{*}$)"),
            (r"$2T_0$", r"$[4T_0,\,192T_0)$", "white", r"$y_1\leq 16(e^{y_0}-1)^2$"),
            (r"$4T_0$", r"$[8T_0,\,384T_0)$", "white", r"$y_2\leq 16(e^{y_1}-1)^2$"),
            (r"$2^iT_0$", r"$[2^{i+1}T_0,\,2^i\,96T_0)$", "white", r"$r_1\leq u_0^{1/T_0}$")]
    for i, (t, s, fc, note) in enumerate(rows):
        y0_ = 0.4 + 1.55 * i + (0.35 if i == 3 else 0)
        b.add_patch(plt.Rectangle((0.2, y0_), 1.5, 1.0, fc=fc, ec=K, lw=0.9))
        b.text(0.95, y0_ + 0.5, t, ha="center", va="center", fontsize=9)
        b.add_patch(plt.Rectangle((2.1, y0_), 3.4, 1.0, fc=fc, ec=K, lw=0.9))
        b.text(3.8, y0_ + 0.5, s, ha="center", va="center", fontsize=8.5)
        b.text(5.8, y0_ + 0.5, note, ha="left", va="center", fontsize=8.5)
        if i < 2:
            b.annotate("", (0.95, y0_ + 1.5), (0.95, y0_ + 1.05), arrowprops=dict(arrowstyle="-|>", lw=0.9, color=K))
    b.text(0.95, 0.4 + 1.55 * 2 + 1.2, r"$\vdots$", ha="center", va="center", fontsize=11)
    b.text(0.95, 0.12, "time", ha="center", va="center", fontsize=8)
    b.text(3.8, 0.12, "spatial sides", ha="center", va="center", fontsize=8)
    save(fig, "fig_ascent")


if __name__ == "__main__":
    fig_cube(); fig_limits(); fig_transfer(); fig_spectrum(); fig_slab()
    fig_star(); fig_roadmap(); fig_linefield(); fig_thermal(); fig_couplings(); fig_ascent()
    print("done")
