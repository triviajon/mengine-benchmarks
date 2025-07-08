#!/usr/bin/env python3
import json
import matplotlib.pyplot as plt
import os
import sys

RESULTS_FILE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
colors = {'mengine': 'blue', 'repeatrewrite': 'red', 'repeatsetoidrewrite': 'red', 'rewritebottomup': 'red', 'rewritetopdown': 'red', 'rewritebng': 'red', 'lean': 'green'}
markers = {'mengine': 'x', 'repeatrewrite': 'o', 'repeatsetoidrewrite': '*', 'rewritebottomup': 's', 'rewritetopdown': 'D', 'rewritebng': 'P', 'lean': 'v'}
engine_strat_to_label = {
    "mengine": "MEngine",
    "repeatrewrite": "Rocq: repeat rewrite",
    "repeatsetoidrewrite": "Rocq: repeat setoid_rewrite",
    "rewritebottomup": "Rocq: rewrite_strat bottomup",
    "rewrite!": "Rocq: rewrite_strat bottomup",
    "rewritetopdown": "Rocq: rewrite_strat topdown",
    "rewritebng": "Rocq: rewrite!",
    'lean': "Lean: simp only"
}


plt.style.use('seaborn-v0_8-whitegrid')
plt.rcParams.update({
    "font.size": 14,
    "axes.titlesize": 16,
    "axes.labelsize": 14,
    "legend.fontsize": 12,
    "xtick.labelsize": 12,
    "ytick.labelsize": 12,
    "axes.grid": False,
    "font.family": "serif",
})

def load_results():
    if not os.path.exists(RESULTS_FILE_PATH):
        print(f"Results file {RESULTS_FILE_PATH} not found.")
        return {}
    with open(RESULTS_FILE_PATH, "r") as f:
        return json.load(f)

def parse_key(key):
    # Example key: "mengine_n26_m3"
    parts = key.split('_')
    engine = None
    m = None
    for part in parts:
        if part in ('mengine', 'repeatrewrite', 'repeatsetoidrewrite', 'rewritebottomup', 'rewritetopdown', 'lean'):
            engine = part
        elif part.startswith('m'):
            m = int(part[1:])
    return engine, m

def plot_benchmark(results, output_dir):
    data_by_engine_strat = {'mengine': [], 'repeatrewrite': [], 'repeatsetoidrewrite': [], 'rewritebottomup': [], 'rewritetopdown': [], 'lean': [], 'rewritebng': []}

    for key, value in results.items():
        if not value.get("success", False):
            continue
        engine_strat, n = parse_key(key)
        if engine_strat and n is not None:
            data_by_engine_strat.setdefault(engine_strat, []).append((n, value["time_taken"]))

    plt.figure(figsize=(8,6))

    for engine, points in data_by_engine_strat.items():
        if not points:
            continue
        ns, ts = zip(*sorted(points))
        plt.plot(ns, ts, label=engine_strat_to_label[engine], color=colors.get(engine, 'black'), marker=markers.get(engine, 'o'), alpha=0.7)

    plt.xlabel("m (# let-bindings)")
    plt.ylabel("Time (seconds)")
    plt.title("(n = 3)")
    plt.legend()
    plt.grid(True, which='major', axis='both', linestyle='--', linewidth=0.5)
    plt.tight_layout()

    output_path = os.path.join(output_dir, "benchmark_plot.png")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Plot saved to {output_path}")

def main():
    output_dir = sys.argv[1] if len(sys.argv) > 1 else "."
    results = load_results()
    if not results:
        print("No benchmark results to plot.")
        return
    plot_benchmark(results, output_dir)

if __name__ == "__main__":
    main()
