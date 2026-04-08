test = "../tests/examples/tail_arity_big.dbk"
# test = "../tests/examples/local_multiply_tail_stress.dbk"
# opts = "-O=cp,ar,dce,vls"
# opts = "-O=cp,ar,dce"
# opts = "-O=cp"
opts = "-O"
# regs = "-R=none"
regs = "-R=all"

build = f"cargo run -- -vv {opts} {regs} -t=exe {test}"
run = ["runtime/stub.exe", "12345678910"]

import subprocess
import time
import statistics
import os

def time_executable(cmd, runs=10):
    times = []

    for _ in range(runs):
        start = time.perf_counter()
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.perf_counter()
        times.append(end - start)

    return {
        "mean": statistics.mean(times),
        "stdev": statistics.stdev(times),
        "min": min(times),
        "max": max(times),
        "all_runs": times
    }

# build
if os.system(build) != 0:
    print("Build failed")
    exit(1)

# get the hash of executable
hash = subprocess.check_output(["sha256sum", "runtime/stub.exe"]).decode("utf-8").split()[0]
print(f"Hash: {hash}")

# time the executable
result = time_executable(run, runs=10)
print(f"Results for {test}")
print(f"opts={opts}")
print(f"regs={regs}")
print(f"Mean:  {result['mean']:.4f} s")
print(f"Std:   {result['stdev']:.4f} s")
print(f"Min:   {result['min']:.4f} s")
print(f"Max:   {result['max']:.4f} s")
