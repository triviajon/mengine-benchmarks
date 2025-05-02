import json
import re
import matplotlib.pyplot as plt
import matplotlib.style as style
import matplotlib as mpl
import numpy as np

ENGINE_ROOT = "/Users/jonros/Documents/mengine"
BENCHMARKS_ROOT = "/Users/jonros/Documents/mengine-benchmarks"

eq_f_a_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_with_eq_f_a/mengine_benchmark_2_results.json"
eq_haa_a_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_with_eq_haa_a/mengine_benchmark_results.json"
native_addr0_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_addr0/native_execution_times.txt"
tree_addr0_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_addr0/tree_execution_times.txt"
letin_addr0_main_file = f"{ENGINE_ROOT}/benchmark/rewrite_addr0/letin_execution_times.txt"
sym_exec_main_file = f"{ENGINE_ROOT}/benchmark/symbolic_execution/execution_times.txt"

main_files = [
    {"name": "eq_f_a_main_file", "path": eq_f_a_main_file, "type": "mengine"},
    {"name": "eq_haa_a_main_file", "path": eq_haa_a_main_file, "type": "mengine"},
    {"name": "Approach A", "path": tree_addr0_main_file, "type": "mengine"},
    {"name": "Approach B", "path": native_addr0_main_file, "type": "mengine"},
    {"name": "Approach C", "path": letin_addr0_main_file, "type": "mengine"},
    {"name": "Our Approach (Get to and Solve Post)", "path": sym_exec_main_file, "type": "mengine"},
]

markers = ['o', 's', 'D', '^', 'v', 'p', 'H', 'x']

reds = plt.cm.Reds(np.linspace(0.4, 0.9, 10))
blues = plt.cm.Blues(np.linspace(0.4, 0.9, 10))
greens = plt.cm.Greens(np.linspace(0.4, 0.9, 10))

def load_config():
    with open("benchmarks.json") as f:
        return json.load(f)

def parse_coq_benchmark_data(summary_file):
    n_values = []
    coq_times = []
    total_times = []
    pattern = r"haa=(\d+).*?Finished transaction in ([\d.]+) secs.*?TotalTime=([\d.]+)s"
    with open(summary_file, 'r') as file:
        for line in file:
            match = re.search(pattern, line)
            if match:
                n_values.append(int(match.group(1)))
                coq_times.append(float(match.group(2)))
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
    plt.plot(n_values, times1, marker=marker, linestyle='-', color=colors[0], label=label1)
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
                                        f"{benchmark['name']} [Tactic]", f"{benchmark['name']} [Total]",
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
    plt.title('Benchmark Execution Time vs n', fontsize=16)
    plt.legend(fontsize=12)
    plt.tight_layout()
    plt.grid(True)
    plt.savefig("result.png", bbox_inches='tight', dpi=500)
    plt.show()

if __name__ == "__main__":
    main()
