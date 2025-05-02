import re
import json
import subprocess
import os
from pathlib import Path
from itertools import product
import time  

def load_config(path="benchmarks.json"):
    with open(path) as f:
        return json.load(f)
    
def generated_substituted_code(content, generated_code_type, name_val_zip):
    if generated_code_type == "addr0_let_bindings":
        n = dict(name_val_zip)["n"]
        lines = []
        for i in range(1, n + 1):
            vprev = "v0" if i == 1 else f"v{i-1}"
            lines.append(f"  let v{i} := add (add {vprev} {vprev}) O in")
        lines.append(f"  add (add v{n} v{n}) O")
        generated = "\n".join(lines)
        return content.replace("__LETS__", generated)
    elif generated_code_type == "haa_gen":
        n = dict(name_val_zip)["haa"]
        lines = ["let HAA0 := h a a in"]
        for i in range(1, n + 1):
            lines.append(f"let HAA{i} := h HAA{i-1} HAA{i-1} in")
        lines.append(f"HAA{n}")
        expr = "\n".join(lines)
        print(content)
        return content.replace("__HAA__", expr)
    elif generated_code_type == "lean_haa_gen":
        n = dict(name_val_zip)["haa"]
        lines = ["let HAA0 := h a a;"]
        for i in range(1, n + 1):
            lines.append(f"let HAA{i} := h HAA{i-1} HAA{i-1};")
        lines.append(f"HAA{n}")
        expr = "\n".join(lines)
        print(content)
        return content.replace("__HAA__", expr)
    return content

def substitute_template(content, param_vals, param_ranges, bench):
    """Helper function to substitute parameters in the template content."""
    param_names = list(param_ranges.keys())

    if 'codeGenerator' in bench:
        return generated_substituted_code(content, bench["codeGenerator"], zip(param_names, param_vals))

    for name, val in zip(param_names, param_vals):
        print(name, val)
        content = content.replace(param_ranges[name][0], str(val))

    return content

def collect_parameters(bench):
    """Collect all parameters for a given benchmark up front."""
    param_ranges = {}
    for param in bench.get("parameters", []):
        name = param["name"]
        placeholder = param["placeholder"]
        min_val = int(input(f"Enter {param['prompt_min']} for {name}: "))
        max_val = int(input(f"Enter {param['prompt_max']} for {name}: "))
        skip = int(input(f"Enter {param['prompt_skip']} for {name}: "))
        param_ranges[name] = (placeholder, min_val, max_val, skip)
    return param_ranges

def run_benchmark(bench, param_ranges):
    template_file = bench["template"]
    summary_file = bench.get("summary", "summary.txt")
    out_dir = Path("timing_logs") / Path(template_file).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    param_names = list(param_ranges.keys())
    ranges = [range(v[1], v[2] + 1, v[3]) for v in param_ranges.values()]
    is_lean = template_file.endswith(".lean")
    compiler = "lean" if is_lean else "coqc"

    with open(summary_file, "w") as summary:
        for param_vals in product(*ranges):
            with open(template_file) as f:
                content = f.read()
            content = substitute_template(content, param_vals, param_ranges, bench)

            param_str = [f"{name}={val}" for name, val in zip(param_names, param_vals)]
            tmp_file = "tmp_benchmark.lean" if is_lean else "tmp_benchmark.v"
            with open(tmp_file, "w") as tmp:
                tmp.write(content)

            log_file = out_dir / ("output_" + "_".join(param_str) + ".log")
            print(f"Running benchmark with {' '.join(param_str)}...")

            start_time = time.perf_counter()
            result = subprocess.run(
                [compiler, tmp_file],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True
            )
            end_time = time.perf_counter()
            total_time = end_time - start_time

            with open(log_file, "w") as log:
                log.write(result.stdout + result.stderr)

            times = re.findall(
                r"\[Elab.command\] \[(\d+\.\d+)\] example",
                result.stdout,
            )

            internal_time = max(map(float, times)) if len(times) != 0 else None,
            summary.write(f"{' '.join(param_str)}  InternalTime={internal_time}  TotalTime={total_time:.4f}s\n")

            os.remove(tmp_file)

def select_benchmarks(benchmarks):
    """Select the benchmarks to run."""
    print("Available benchmarks:")
    for i, bench in enumerate(benchmarks, start=1):
        print(f"{i}) {bench['name']}")
    print(f"*) All benchmarks")

    choice = input("Select benchmarks to run (e.g. 1,3 or *): ").strip()

    if choice == "*":
        return benchmarks

    indices = [s.strip() for s in choice.split(",")]
    if not all(i.isdigit() and 1 <= int(i) <= len(benchmarks) for i in indices):
        raise ValueError("Invalid benchmark selection.")

    selected_benchmarks = [benchmarks[int(i) - 1] for i in indices]
    return selected_benchmarks

def main():
    config = load_config()
    selected_benchmarks = select_benchmarks(config["benchmarks"])

    params = []
    
    for bench in selected_benchmarks:
        param_ranges = collect_parameters(bench)
        params.append(param_ranges)

    for i, bench in enumerate(selected_benchmarks):
        run_benchmark(bench, params[i])

if __name__ == "__main__":
    main()