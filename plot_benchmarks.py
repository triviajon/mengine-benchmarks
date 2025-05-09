import json
import re
import matplotlib.pyplot as plt
import matplotlib.style as style
import matplotlib as mpl
import numpy as np

style.use('seaborn-v0_8-muted')

ENGINE_ROOT = "/Users/jonros/Documents/mengine"
BENCHMARKS_ROOT = "/Users/jonros/Documents/mengine-benchmarks"

eq_f_a_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_with_eq_f_a/mengine_benchmark_2_results.json"
eq_haa_a_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_with_eq_haa_a/mengine_benchmark_results.json"
native_addr0_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_addr0/nativemengine_benchmark_results.json"
tree_addr0_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_addr0/treemengine_benchmark_results.json"
letin_addr0_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_addr0/letinmengine_benchmark_results.json"
sym_exec_main_file = f"{ENGINE_ROOT}/benchmark/symbolic_execution/mengine_benchmark_results.json"

main_files = [
    {"name": "MEngine: rewrite gfa", "path": eq_f_a_main_file, "type": "mengine"},
    {"name": "eq_haa_a_main_file", "path": eq_haa_a_main_file, "type": "mengine"},
    {"name": "MEngine (No sharing): rewrite add_r_O", "path": tree_addr0_main_file, "type": "mengine"},
    {"name": "MEngine (Native sharing): rewrite add_r_O", "path": native_addr0_main_file, "type": "mengine"},
    {"name": "MEngine (With LetIn Const): rewrite add_r_O", "path": letin_addr0_main_file, "type": "mengine"},
    {"name": "Our Approach (Get to and Solve Post)", "path": sym_exec_main_file, "type": "mengine"},
]

markers = ['o', 's', 'D', '^', 'v', 'p', 'H', 'x']

def spaced_colors(cmap_name, n, alpha=1.0):
    cmap = mpl.cm.get_cmap(cmap_name)
    return [(*cmap(i)[0:3], alpha) for i in np.linspace(0.25, 0.85, n)]

reds = spaced_colors("Reds", 4)
greens = spaced_colors("Greens", 4)
blues = spaced_colors("Blues", 4)

def load_config():
    with open("benchmark_suite.json") as f:
        return json.load(f)

def parse_coq_benchmark_data(summary_file):
    n_values = []
    coq_times = []
    total_times = []
    pattern = r"n=(\d+).*?InternalTime=\(([\w.]+),\).*?TotalTime=([\d.]+)s"
    with open(summary_file, 'r') as file:
        for line in file:
            match = re.search(pattern, line)
            if match:
                n_values.append(int(match.group(1)))
                internal_time = match.group(2)
                if internal_time != "None":
                    coq_times.append(float(internal_time))
                total_times.append(float(match.group(3)))
    return n_values, coq_times, total_times

def parse_lean_benchmark_data(summary_file):
    n_values = []
    internal_times = []
    total_times = []
    pattern = r"haa=(\d+).*?InternalTime=\(([\d.]+),\).*?TotalTime=([\d.]+)s"
    with open(summary_file, 'r') as file:
        for line in file:
            match = re.search(pattern, line)
            if match:
                n_values.append(int(match.group(1)))
                internal_times.append(float(match.group(2)))
                total_times.append(float(match.group(3)))
    return n_values, internal_times, total_times

def plot_dual_benchmark(n_values, times1, times2, label1, label2, marker, colors):
    if len(times1) >= 5:
        times1 = np.convolve(times1, np.ones(5)/5, mode='valid')
        times2 = np.convolve(times2, np.ones(5)/5, mode='valid')
        n_values = n_values[2:-2]
    if (len(times1) > 0):
        plt.plot(n_values, times1, marker=marker, linestyle='-', color=colors[0], label=label1)
    if (len(times2) > 0):
        plt.plot(n_values, times2, marker=marker, linestyle='--', color=colors[1], label=label2)

def parse_mengine_output(file_name):
    with open(file_name, 'r') as f:
        data = json.load(f)
    results = {}
    for entry in data.values():
        n = entry["N"]
        t = entry["time"]
        if n not in results:
            results[n] = []
        results[n].append(t)
    n_values = sorted(results.keys())
    times = [min(results[n]) for n in n_values]
    return n_values, times

def parse_lean_benchmark(file_name):
    with open(file_name, 'r') as f:
        data = json.load(f)
    n_values = sorted(int(k) for k in data.keys())
    strategy_names = list(next(iter(data.values())).keys())
    strategy_times = {name: [] for name in strategy_names}
    for n in n_values:
        entry = data[str(n)]
        for name in strategy_names:
            strategy_times[name].append(entry[name]["time"])
    return n_values, strategy_times

def plot_benchmark_results(n_values, times, benchmark_name, color, marker):
    if len(times) >= 5:
        times = np.convolve(times, np.ones(5)/5, mode='valid')
        n_values = n_values[2:-2]
    plt.plot(n_values, times, marker=marker, linestyle='-', color=color, label=benchmark_name)

def main():
    config = load_config()

    print("Available benchmarks:")
    for i, bench in enumerate(config["benchmarks"], start=1):
        print(f"{i}) {bench['name']}")

    color_indices = {"mengine": 0, "lean": 0, "coq": 0}

    for i, main_file in enumerate(main_files, start=len(config["benchmarks"]) + 1):
        print(f"{i}) {main_file['name']}")

    choices = input("Select benchmarks to plot (comma separated, e.g., 1,2,3): ")
    selected_choices = choices.split(',')

    for idx, choice in enumerate(selected_choices):
        if choice.strip().isdigit():
            choice = int(choice.strip())
            if 1 <= choice <= len(config["benchmarks"]):
                benchmark = config["benchmarks"][choice - 1]
                template_file = benchmark["template"]
                summary_file = benchmark["summary"]
                marker = markers[idx % len(markers)]
                try:
                    if template_file.endswith(".v"):
                        color = greens[color_indices["coq"] % len(greens)]
                        color_indices["coq"] += 1
                        n_values, tactic_times, total_times = parse_coq_benchmark_data(summary_file)
                    elif template_file.endswith(".lean"):
                        color = blues[color_indices["lean"] % len(blues)]
                        color_indices["lean"] += 1
                        n_values, tactic_times, total_times = parse_lean_benchmark_data(summary_file)
                    else:
                        raise ValueError("Unsupported template file type")
                    plot_dual_benchmark(n_values, tactic_times, total_times,
                                        f"{benchmark['name']} [Tactic]", f"{benchmark['name']}",
                                        marker, (color, color))
                except Exception as e:
                    print(f"Error processing {summary_file}: {e}")
            elif len(config["benchmarks"]) < choice <= len(config["benchmarks"]) + len(main_files):
                main_file = main_files[choice - len(config["benchmarks"]) - 1]
                marker = markers[idx % len(markers)]
                try:
                    n_values, times = parse_mengine_output(main_file["path"])
                    color = reds[color_indices["mengine"] % len(reds)]
                    color_indices["mengine"] += 1
                    plot_benchmark_results(n_values, times, main_file["name"], color, marker)
                except Exception as e:
                    print(f"Error processing {main_file['path']}: {e}")

    plt.xlabel(r'$n$')
    plt.ylabel('Execution Time (secs)', fontsize=14)
    plt.xticks(fontsize=12)
    plt.yticks(fontsize=12)
    plt.title('Benchmark Execution Time', fontsize=16)
    plt.legend(fontsize=12)
    plt.tight_layout()
    plt.grid(True)
    plt.savefig("result.png", bbox_inches='tight', dpi=500)
    plt.show()

if __name__ == "__main__":
    main()
