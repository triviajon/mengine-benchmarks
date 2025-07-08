import sys
import itertools
import subprocess
import shutil
import os
import json

DEFAULT_CONFIG_PATH = "config.json"
default_config = {
    "benchmark_file": "benchmarks.json",
    "mengine_path": "~/mengine/main",
    "coqc_path": "coqc",
    "lean_path": "lean",
    "coqutil_root_path": "~/coqutil",
    "output_dir": "benchmarks_output",
}

DEFAULT_TIMEOUT = 30

def load_config(path=DEFAULT_CONFIG_PATH):
    """Load benchmark configuration from a JSON file."""
    with open(path, 'r') as f:
        return json.load(f)

def verify_proof_engine_paths(config):
    """Verify that the proof engine paths in the configuration are valid."""
    for key in ['mengine_path', 'coqc_path', 'lean_path']:
        path = os.path.expanduser(config[key])
        # If path is a file and executable
        if os.path.isabs(path) or path.startswith(('.', './', '../')):
            if not (os.path.isfile(path) and os.access(path, os.X_OK)):
                raise FileNotFoundError(
                    f"{key} executable '{path}' not found or not executable. "
                    f"Please check your configuration ({DEFAULT_CONFIG_PATH})."
            )
        else:
            # Search PATH
            if shutil.which(path) is None:
                raise FileNotFoundError(
                    f"{key} executable '{path}' not found in PATH. "
                    f"Please check your configuration ({DEFAULT_CONFIG_PATH}).")

def load_benchmarks(path):
    """Load benchmarks from a JSON file."""
    with open(path, 'r') as f:
        return json.load(f)

def setup():
    """Load or create the configuration file and verify proof engine paths."""
    try:
        config = load_config()
        print("Configuration loaded successfully.")
    except FileNotFoundError as e:
        print(f"Error: Configuration file not found: {e}")
        print("Creating a default configuration file...")
        with open(DEFAULT_CONFIG_PATH, 'w') as f:
            json.dump(default_config, f, indent=4)
        config = default_config
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

    # Verify configuration file
    try:
        verify_proof_engine_paths(config)
        benchmarks = load_benchmarks(config['benchmark_file'])
        print("Configuration verified successfully.")
    except FileNotFoundError as e:
        print(f"Error: {e}")
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON format in configuration file: {e}")
    except Exception as e:
        print(f"An unexpected error occurred while verifying the configuration: {e}")
    return config, benchmarks
    
def generate_range(param):
    return range(param['start'], param['stop'], param['step'])

def run_benchmark(config, benchmark):
    name, details = benchmark
    print(f"Running benchmark: {name}")

    subdirectory = details.get('subdirectory', '')
    params_path = os.path.join(subdirectory, 'params.json')

    if not os.path.isfile(params_path):
        print(f"No params.json found for benchmark '{name}' at {params_path}, skipping.")
        return

    with open(params_path, 'r') as f:
        params = json.load(f)

    engines = params.get('engines', {})

    for engine, engine_params in engines.items():
        args_names = engine_params.get('args', [])
        timeout = engine_params.get('timeout', DEFAULT_TIMEOUT)
        exe_path = config.get(f"{engine}_path", '')

        # Build list of ranges for each arg
        ranges = []
        for arg in args_names:
            if arg not in engine_params:
                raise ValueError(f"Missing range definition for argument '{arg}' in engine '{engine}' params.")
            ranges.append(generate_range(engine_params[arg]))

        # Cartesian product of all argument values
        for args_values in itertools.product(*ranges):
            args_strs = [str(val) for val in args_values]
            cmd = ['python3', f'{subdirectory}/run.py', engine] + [DEFAULT_CONFIG_PATH] + args_strs + [exe_path] + [str(timeout)]

            print(f"Executing: {' '.join(cmd)} with timeout {timeout}s")
            try:
                result = subprocess.run(cmd, capture_output=True, text=True)
                if result.stdout:
                    print(f"Output for {engine} with args {args_values}:\n{result.stdout}")
                if result.stderr:
                    print(f"Error output for {engine} with args {args_values}:\n{result.stderr}")
                result.check_returncode()
            except subprocess.TimeoutExpired:
                    print(f"Timeout expired for {engine} with args {args_values} after {timeout}s")
            except subprocess.CalledProcessError as e:
                    print(f"Error occurred while running {engine} with args {args_values}: {e}")

def plot_benchmark(config, benchmark):
    name, details = benchmark
    print(f"Plotting benchmark: {name}")

    subdirectory = details.get('subdirectory', '')
    plot_script = os.path.join(subdirectory, 'plot.py')

    if not os.path.isfile(plot_script):
        print(f"No plot script found for benchmark '{name}' at {plot_script}, skipping.")
        return

    output_dir = os.path.join(config['output_dir'], subdirectory)
    cmd = ['python3', plot_script, output_dir]

    print(f"Executing: {' '.join(cmd)}")
    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error occurred while plotting benchmark '{name}': {e}")

if __name__ == "__main__":
    config, benchmarks = setup()
    if len(sys.argv) < 2:
        print("Usage: python benchmark.py [run|plot] [benchmark_name (optional)]")
        sys.exit(1)

    mode = sys.argv[1].lower()
    benchmark_name = sys.argv[2] if len(sys.argv) > 2 else None

    if mode == "run":
        if benchmark_name:
            if benchmark_name in benchmarks:
                print(f"\033[1mStarting benchmark: {benchmark_name}\033[0m")
                run_benchmark(config, (benchmark_name, benchmarks[benchmark_name]))
            else:
                print(f"Benchmark '{benchmark_name}' not found.")
                sys.exit(1)
        else:
            for benchmark in benchmarks.items():
                print(f"\033[1mStarting benchmark: {benchmark[0]}\033[0m")
                run_benchmark(config, benchmark)
    elif mode == "plot":
        if benchmark_name:
            if benchmark_name in benchmarks:
                print(f"\033[1mPlotting benchmark: {benchmark_name}\033[0m")
                plot_benchmark(config, (benchmark_name, benchmarks[benchmark_name]))
            else:
                print(f"Benchmark '{benchmark_name}' not found.")
                sys.exit(1)
        else:
            for benchmark in benchmarks.items():
                print(f"\033[1mPlotting benchmark: {benchmark[0]}\033[0m")
                plot_benchmark(config, benchmark)
    else:
        print("Unknown mode. Use 'run' or 'plot'.")
        sys.exit(1)