"""Shared style for the figures of the paper (print, light background).
   Palette: validated categorical slots 1-3 (blue, orange, aqua) and neutral inks; one axis per panel."""
import matplotlib as mpl
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
INK, INK2, MUTED, GRID, SURF = "#0b0b0b", "#52514e", "#8a8984", "#e4e3df", "#fcfcfb"
def setup():
    mpl.rcParams.update({
        "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF,
        "font.size": 9, "axes.labelsize": 9, "axes.titlesize": 9.5, "legend.fontsize": 8,
        "xtick.labelsize": 8, "ytick.labelsize": 8, "axes.edgecolor": MUTED, "axes.labelcolor": INK2,
        "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.titlecolor": INK,
        "axes.spines.top": False, "axes.spines.right": False, "axes.grid": True, "grid.color": GRID,
        "grid.linewidth": 0.6, "lines.linewidth": 2.0, "legend.frameon": False, "pdf.fonttype": 42})
def save(fig, name):
    import os, inspect
    here = os.path.dirname(os.path.abspath(inspect.stack()[1].filename))   # the folder of the calling script, not the cwd
    name = os.path.join(here, name)
    fig.savefig(name + ".pdf", bbox_inches="tight"); fig.savefig(name + ".png", dpi=300, bbox_inches="tight")
    print("wrote", name + ".pdf/.png")
