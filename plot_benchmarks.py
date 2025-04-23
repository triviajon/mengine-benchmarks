import json
import re
import matplotlib.pyplot as plt
import matplotlib.style as style
import matplotlib as mpl
import numpy as np

style.use('seaborn-paper')

eq_f_a_main_file = "/home/jonros/engine/benchmark/rewrite_with_eq_f_a/execution_times.txt"
native_addr0_main_file = "/home/jonros/engine/benchmark/rewrite_addr0/native_execution_times.txt"
tree_addr0_main_file = "/home/jonros/engine/benchmark/rewrite_addr0/tree_execution_times.txt"
letin_addr0_main_file = "/home/jonros/engine/benchmark/rewrite_addr0/letin_execution_times.txt"
sym_exec_main_file = "/home/jonros/engine/benchmark/symbolic_execution/execution_times.txt"

markers = ['o', 's', 'D', '^', 'v', 'p', 'H', 'x']
colors = ['b', 'g', 'c', 'm', 'y', 'k']

def load_config():
    with open("benchmarks.json") as f:
        return json.load(f)

def parse_benchmark_data(summary_file):
    n_values = []
    times = []

    pattern = r"n=(\d+)\s+Finished\s+transaction\s+in\s+([\d\.]+)\s+secs"
    
    with open(summary_file, 'r') as file:
        for line in file:
            match = re.search(pattern, line)
            if match:
                n_values.append(int(match.group(1)))
                times.append(float(match.group(2)))

    return n_values, times

def parse_mengine_output(file_name):
    n_values = []
    times = []
    pattern = r"n=(\d+)\s+Executed\s+in\s+([\d\.]+)\s+secs"
    with open(file_name, 'r') as f:
        for line in f:
            match = re.search(pattern, line)
            if match:
                n_values.append(int(match.group(1)))
                times.append(float(match.group(2)))
    return n_values, times

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

    # Add main files as selectable options
    main_files = [
        {"name": "eq_f_a_main_file", "path": eq_f_a_main_file},
        {"name": "Approach A", "path": tree_addr0_main_file},
        {"name": "Approach B", "path": native_addr0_main_file},
        {"name": "Approach C", "path": letin_addr0_main_file},
        {"name": "Our Approach (Get to and Solve Post)", "path": sym_exec_main_file},
    ]
    for i, main_file in enumerate(main_files, start=len(config["benchmarks"]) + 1):
        print(f"{i}) {main_file['name']}")

    choices = input("Select benchmarks to plot (comma separated, e.g., 1,2,3): ")
    selected_choices = choices.split(',')

    for idx, choice in enumerate(selected_choices):
        if choice.strip().isdigit():
            choice = int(choice.strip())
            if 1 <= choice <= len(config["benchmarks"]):
                benchmark = config["benchmarks"][choice - 1]
                summary_file = benchmark.get("summary", "summary.txt")

                marker = markers[idx % len(markers)]
                color = colors[idx % len(colors)]

                try:
                    n_values, times = parse_benchmark_data(summary_file)
                    plot_benchmark_results(n_values, times, benchmark["name"], color, marker)
                except FileNotFoundError:
                    print(f"Error: {summary_file} not found!")
                except Exception as e:
                    print(f"An error occurred while processing {summary_file}: {e}")
            elif len(config["benchmarks"]) < choice <= len(config["benchmarks"]) + len(main_files):
                main_file = main_files[choice - len(config["benchmarks"]) - 1]
                marker = markers[idx % len(markers)]
                color = colors[idx % len(colors)]

                try:
                    n_values, times = parse_mengine_output(main_file["path"])
                    plot_benchmark_results(n_values, times, main_file["name"], color, marker)
                except FileNotFoundError:
                    print(f"Error: {main_file['path']} not found!")
                except Exception as e:
                    print(f"An error occurred while processing {main_file['path']}: {e}")

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
