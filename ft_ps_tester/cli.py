#!/usr/bin/env python3

import sys
import os
import random
import subprocess
import glob
import time
import math
import re
import shutil
import signal
from itertools import permutations
from collections import deque

# ==========================================
# CONFIGURATION
# ==========================================
COLORS = {
    "GREEN": "\033[1;32m",
    "RED": "\033[1;31m",
    "YELLOW": "\033[1;33m",
    "BLUE": "\033[1;34m",
    "CYAN": "\033[1;36m",
    "MAGENTA": "\033[1;35m",
    "RESET": "\033[0m",
    "BOLD": "\033[1m"
}

THRESHOLDS = {
    100: {"excellent": 700, "good": 1500, "pass": 2000},
    500: {"excellent": 5500, "good": 8000, "pass": 12000}
}

MODES = {
    "simple": (15.0, 19.9),
    "medium": (20.0, 49.9),
    "complex": (50.0, 55.0),
    "adaptive": (15.0, 55.0)
}

# 32-bit signed integer bounds.
INT_MAX = 2147483647
INT_MIN = -2147483648

# Random-number generation range (inclusive lo, hi, label). The default spans the
# full 32-bit signed range; --1m / --u1m narrow it. Mutated by main().
NUMBER_RANGES = {
    "intmax": (INT_MIN, INT_MAX, "INT_MIN..INT_MAX"),
    "1m":     (-1_000_000, 1_000_000, "-1M..1M"),
    "u1m":  (0, 1_000_000, "0..1M"),
}
GEN_RANGE = NUMBER_RANGES["intmax"]


def compute_timeout(size):
    """Per-call ./push_swap timeout (seconds), scaled by input size.

    ~5s floor for small/basic inputs, ~10s at 500, ~15s at 800; capped at 30s.
    """
    return max(5.0, min(30.0, size / 60.0 + 1.67))

# ==========================================
# DATA GENERATOR
# ==========================================
def generate_sequence(size, target_disorder):
    lo, hi, _ = GEN_RANGE
    raw_sequence = random.sample(range(lo, hi + 1), size)
    raw_sequence.sort()

    total_pairs = (size * (size - 1)) / 2.0
    target_inv = int((target_disorder / 100.0) * total_pairs)

    if target_inv > 0:
        inv = [0] * size
        indices = list(range(size))
        random.shuffle(indices)
        
        remaining = target_inv
        for i in indices:
            max_cap = size - 1 - i
            take = random.randint(0, min(remaining, max_cap))
            inv[i] = take
            remaining -= take
            
        if remaining > 0:
            random.shuffle(indices)
            for i in indices:
                max_cap = size - 1 - i
                space = max_cap - inv[i]
                if space > 0:
                    take = min(remaining, space)
                    inv[i] += take
                    remaining -= take
                if remaining == 0:
                    break

        result_sequence = []
        for i in range(size - 1, -1, -1):
            val = raw_sequence[i]
            insert_pos = inv[i]
            result_sequence.insert(insert_pos, val)
            
        return result_sequence
    
    return raw_sequence

# ==========================================
# VALIDATOR (CHECKER)
# ==========================================
class PushSwapChecker:
    def __init__(self, sequence):
        self.stack_a = deque(sequence)
        self.stack_b = deque()
        self.has_unnecessary_ops = False
        self.unnecessary_ops = {}

    def _count_unnecessary(self, op):
        self.has_unnecessary_ops = True
        self.unnecessary_ops[op] = self.unnecessary_ops.get(op, 0) + 1

    def exec_op(self, op):
        if op == "sa":
            if len(self.stack_a) >= 2:
                self.stack_a[0], self.stack_a[1] = self.stack_a[1], self.stack_a[0]
            else:
                self._count_unnecessary("sa")
        elif op == "sb":
            if len(self.stack_b) >= 2:
                self.stack_b[0], self.stack_b[1] = self.stack_b[1], self.stack_b[0]
            else:
                self._count_unnecessary("sb")
        elif op == "ss":
            if len(self.stack_a) >= 2 or len(self.stack_b) >= 2:
                if len(self.stack_a) >= 2:
                    self.stack_a[0], self.stack_a[1] = self.stack_a[1], self.stack_a[0]
                if len(self.stack_b) >= 2:
                    self.stack_b[0], self.stack_b[1] = self.stack_b[1], self.stack_b[0]
            else:
                self._count_unnecessary("ss")

        elif op == "pa":
            if len(self.stack_b) >= 1:
                self.stack_a.appendleft(self.stack_b.popleft())
            else:
                self._count_unnecessary("pa")
        elif op == "pb":
            if len(self.stack_a) >= 1:
                self.stack_b.appendleft(self.stack_a.popleft())
            else:
                self._count_unnecessary("pb")
        elif op == "ra":
            if len(self.stack_a) >= 2:
                self.stack_a.append(self.stack_a.popleft())
            else:
                self._count_unnecessary("ra")
        elif op == "rb":
            if len(self.stack_b) >= 2:
                self.stack_b.append(self.stack_b.popleft())
            else:
                self._count_unnecessary("rb")
        elif op == "rr":
            if len(self.stack_a) >= 2 or len(self.stack_b) >= 2:
                if len(self.stack_a) >= 2:
                    self.stack_a.append(self.stack_a.popleft())
                if len(self.stack_b) >= 2:
                    self.stack_b.append(self.stack_b.popleft())
            else:
                self._count_unnecessary("rr")
        elif op == "rra":
            if len(self.stack_a) >= 2:
                self.stack_a.appendleft(self.stack_a.pop())
            else:
                self._count_unnecessary("rra")
        elif op == "rrb":
            if len(self.stack_b) >= 2:
                self.stack_b.appendleft(self.stack_b.pop())
            else:
                self._count_unnecessary("rrb")
        elif op == "rrr":
            if len(self.stack_a) >= 2 or len(self.stack_b) >= 2:
                if len(self.stack_a) >= 2:
                    self.stack_a.appendleft(self.stack_a.pop())
                if len(self.stack_b) >= 2:
                    self.stack_b.appendleft(self.stack_b.pop())
            else:
                self._count_unnecessary("rrr")
        else:
            return False
        return True
        
    def validate(self, ops_list):
        for op in ops_list:
            if not self.exec_op(op):
                return False, False, {}

        if len(self.stack_b) != 0:
             return False, False, {}
           
        lst = list(self.stack_a)
        is_sorted = all(lst[i] <= lst[i+1] for i in range(len(lst)-1))
        return is_sorted, self.has_unnecessary_ops, self.unnecessary_ops

# ==========================================
# REPORT GENERATOR
# ==========================================
def get_next_report_number(report_dir, size, mode):
    """Find the next available report number for a given size and mode.
    
    A report number n is considered 'used' if either ops or nums file exists.
    Returns the next available number (1-based).
    """
    pattern_ops = os.path.join(report_dir, f"report_{size}_{mode}_ops_*.txt")
    pattern_nums = os.path.join(report_dir, f"report_{size}_{mode}_nums_*.txt")
    
    max_n = 0
    
    for pattern in [pattern_ops, pattern_nums]:
        for filepath in glob.glob(pattern):
            basename = os.path.basename(filepath)
            try:
                parts = basename.replace('.txt', '').split('_')
                n = int(parts[-1])
                max_n = max(max_n, n)
            except (ValueError, IndexError):
                continue
    
    return max_n + 1

def write_report(report_dir, size, mode, sequence_str, ops_str):
    n = get_next_report_number(report_dir, size, mode)
    
    ops_filename = os.path.join(report_dir, f"report_{size}_{mode}_ops_{n}.txt")
    nums_filename = os.path.join(report_dir, f"report_{size}_{mode}_nums_{n}.txt")
    
    with open(ops_filename, 'w') as f:
        f.write(ops_str)
    
    with open(nums_filename, 'w') as f:
        f.write(sequence_str)

# ==========================================
# TEST ENGINE
# ==========================================
def get_grade_info(size, ops):
    if size not in THRESHOLDS:
        return ("UNKNOWN", COLORS["CYAN"])
        
    t = THRESHOLDS[size]
    if ops == 0:
        return ("N/A", COLORS["RESET"])
    elif ops < t["excellent"]:
        return ("EXCELLENT", COLORS["GREEN"])
    elif ops < t["good"]:
        return ("GOOD", COLORS["BLUE"])
    elif ops <= t["pass"]:
        return ("PASS", COLORS["YELLOW"])
    else:
        return ("FAIL", COLORS["RED"])

def format_grade_column(ops, grade_text, color):
    visible_str = f"{ops} ({grade_text})"
    padding = 18 - len(visible_str)
    return f"{ops} ({color}{grade_text}{COLORS['RESET']}){' ' * padding}"

def run_test_suite(executable, size, mode, reports_enabled=False):
    min_disorder, max_disorder = MODES[mode]
    
    print(f"{COLORS['CYAN']}>> Testing Size: {size} | Mode: {mode.upper()} {COLORS['RESET']}", end=" ")
    
    total_ops = 0
    max_ops = 0
    min_ops = float('inf')
    warnings_count = 0
    
    failures = []
    warnings = []
    report_dir = os.path.dirname(os.path.abspath(executable)) if reports_enabled else None
    
    for i in range(1, 101):
        disorder = random.uniform(min_disorder, max_disorder)
        sequence = generate_sequence(size, disorder)
        str_seq = [str(x) for x in sequence]
        result = None
        try:
            result = subprocess.run(
                [executable, f'--{mode}'] + str_seq,
                capture_output=True,
                text=True,
                check=False,
                timeout=compute_timeout(size)
            )
            
            ops = result.stdout.strip().split()
            if ops == ['']:
                ops = []
                
            op_count = len(ops)
            checker = PushSwapChecker(sequence)
            is_sorted, has_warnings, unnecessary_counts = checker.validate(ops)
            
            if not is_sorted:
                sys.stdout.write(f"{COLORS['RED']}!{COLORS['RESET']}")
                failures.append({
                    "size": size,
                    "mode": mode,
                    "disorder": disorder,
                    "reason": "Failed to sort stack properly (or invalid operation).",
                    "ops": op_count,
                    "limit": THRESHOLDS[size]["pass"],
                    "sequence": " ".join(str_seq)
                })
                if reports_enabled:
                    write_report(report_dir, size, mode, " ".join(str_seq), result.stdout)
            else:
                total_ops += op_count
                max_ops = max(max_ops, op_count)
                min_ops = min(min_ops, op_count)
                
                if op_count > THRESHOLDS[size]["pass"]:
                    sys.stdout.write(f"{COLORS['RED']}F{COLORS['RESET']}")
                    failures.append({
                        "size": size,
                        "mode": mode,
                        "disorder": disorder,
                        "reason": "Operation limit exceeded.",
                        "ops": op_count,
                        "limit": THRESHOLDS[size]["pass"],
                        "sequence": " ".join(str_seq)
                    })
                    if reports_enabled:
                        write_report(report_dir, size, mode, " ".join(str_seq), result.stdout)
                elif has_warnings:
                    sys.stdout.write(f"{COLORS['YELLOW']}:{COLORS['RESET']}")
                    warnings_count += 1
                    warnings.append({
                        "size": size,
                        "mode": mode,
                        "disorder": disorder,
                        "reason": "Unnecessary operations detected (e.g., sa/sb/pa/pb/rotate on insufficient elements).",
                        "ops": op_count,
                        "limit": THRESHOLDS[size]["pass"],
                        "sequence": " ".join(str_seq),
                        "unnecessary_counts": unnecessary_counts
                    })
                else:
                    sys.stdout.write(f"{COLORS['GREEN']}.{COLORS['RESET']}")
                    
        except subprocess.TimeoutExpired:
            sys.stdout.write(f"{COLORS['MAGENTA']}T{COLORS['RESET']}")
            failures.append({
                "size": size,
                "mode": mode,
                "disorder": disorder,
                "reason": "Timeout (infinite loop?).",
                "ops": "N/A",
                "limit": THRESHOLDS[size]["pass"],
                "sequence": " ".join(str_seq)
            })
            if reports_enabled:
                write_report(report_dir, size, mode, " ".join(str_seq), "")
            
        sys.stdout.flush()
        
    print()
    
    successful_runs = 100 - len(failures)
    avg_ops = (total_ops // successful_runs) if successful_runs > 0 else 0
    
    return {
        "size": size,
        "mode": mode,
        "max": max_ops,
        "min": min_ops if min_ops != float('inf') else 0,
        "avg": avg_ops,
        "fails": len(failures),
        "warnings": warnings_count
    }, failures, warnings

def print_failures(failures):
    if not failures:
        return
        
    filtered_failures = []
    seen_limits = {} 
    
    # Filter failures: max 1 timeout and 1 standard error per (size, mode)
    for f in failures:
        key = (f['size'], f['mode'])
        if key not in seen_limits:
            seen_limits[key] = {"timeout": False, "standard": False}
            
        is_timeout = "Timeout" in f['reason']
        
        if is_timeout and not seen_limits[key]["timeout"]:
            filtered_failures.append(f)
            seen_limits[key]["timeout"] = True
        elif not is_timeout and not seen_limits[key]["standard"]:
            filtered_failures.append(f)
            seen_limits[key]["standard"] = True
            
    print("\n" + "="*80)
    print(f"{COLORS['RED']}{COLORS['BOLD']}FAILURE REPORT {COLORS['RESET']}")
    print("="*80)
    
    for idx, f in enumerate(filtered_failures):
        print(f"\n{COLORS['YELLOW']}--- Failure {idx + 1} ---{COLORS['RESET']}")
        print(f"Size       : {f['size']}")
        print(f"Mode       : {f['mode'].upper()}")
        print(f"Disorder   : {f['disorder']:.2f}%")
        print(f"Reason     : {COLORS['RED']}{f['reason']}{COLORS['RESET']}")
        print(f"Operations : {f['ops']} / Limit: {f['limit']}")
        print("-" * 80)

def print_warnings(warnings):
    if not warnings:
        return

    # Accumulate unnecessary op counts per (size, mode) across all runs
    accumulated_counts = {}
    for w in warnings:
        key = (w['size'], w['mode'])
        if key not in accumulated_counts:
            accumulated_counts[key] = {}
        counts = w.get('unnecessary_counts', {})
        for op, count in counts.items():
            accumulated_counts[key][op] = accumulated_counts[key].get(op, 0) + count

    filtered_warnings = []
    seen = {}

    # Filter warnings: max 1 per (size, mode)
    for w in warnings:
        key = (w['size'], w['mode'])
        if key not in seen:
            filtered_warnings.append(w)
            seen[key] = True

    print("\n" + "="*80)
    print(f"{COLORS['YELLOW']}{COLORS['BOLD']}WARNING REPORT {COLORS['RESET']}")
    print("="*80)

    for idx, w in enumerate(filtered_warnings):
        key = (w['size'], w['mode'])
        counts = accumulated_counts.get(key, {})
        counts_str = ", ".join(f"{op}={count}" for op, count in sorted(counts.items())) if counts else "N/A"

        print(f"\n{COLORS['YELLOW']}--- Warning {idx + 1} ---{COLORS['RESET']}")
        print(f"Size       : {w['size']}")
        print(f"Mode       : {w['mode'].upper()}")
        print(f"Disorder   : {w['disorder']:.2f}%")
        print(f"Unnecessary: {COLORS['YELLOW']}{counts_str}{COLORS['RESET']}")
        print(f"Operations : {w['ops']} / Limit: {w['limit']}")
        print("-" * 80)

# ==========================================
# BIG O ANALYSIS
# ==========================================
BIGO_SIZES = [50, 100, 200, 400, 800]

BIGO_THRESHOLDS_OPS = {
    "O(n)":       {"coef": 1.0,     "ratio_max": 2.2},
    "O(n log n)": {"coef": 1.14,   "ratio_max": 3.0},
    "O(n sqrt(n))": {"coef": 1.09, "ratio_max": 3.5},
    "O(n^2)":     {"coef": 0.152,  "ratio_max": 4.0},
    "O(n^3)":     {"coef": 0.00095,"ratio_max": 8.0},
}

BIGO_THRESHOLDS_TIME = {
    "O(n)":       {"coef": 0.05,   "ratio_max": 2.2},
    "O(n log n)": {"coef": 0.08,   "ratio_max": 3.0},
    "O(n sqrt(n))": {"coef": 0.12, "ratio_max": 3.5},
    "O(n^2)":     {"coef": 0.25,   "ratio_max": 4.0},
    "O(n^3)":     {"coef": 1.0,    "ratio_max": 8.0},
}

def max_value_for(thresholds, complexity, n):
    """Calculate expected max value for a given complexity class and input size n."""
    if complexity == "O(n)":
        return thresholds["O(n)"]["coef"] * n
    elif complexity == "O(n log n)":
        return thresholds["O(n log n)"]["coef"] * n * math.log2(n)
    elif complexity == "O(n sqrt(n))":
        return thresholds["O(n sqrt(n))"]["coef"] * n * math.sqrt(n)
    elif complexity == "O(n^2)":
        return thresholds["O(n^2)"]["coef"] * n * n
    elif complexity == "O(n^3)":
        return thresholds["O(n^3)"]["coef"] * n * n * n
    else:
        return float('inf')

def classify_by_metric(values_by_size, thresholds, metric_name):
    sizes = sorted(values_by_size.keys())
    if len(sizes) < 2:
        return "UNKNOWN", "Insufficient data"

    ratios = []
    for i in range(1, len(sizes)):
        prev = values_by_size[sizes[i-1]]
        curr = values_by_size[sizes[i]]
        if prev > 0:
            ratios.append(curr / prev)

    if not ratios:
        return "UNKNOWN", "No ratio data"

    avg_ratio = sum(ratios) / len(ratios)
    max_n = max(sizes)
    max_val = max(values_by_size.values())

    for comp in ["O(n)", "O(n log n)", "O(n sqrt(n))", "O(n^2)"]:
        limit = max_value_for(thresholds, comp, max_n)
        if max_val <= limit and avg_ratio <= thresholds[comp]["ratio_max"]:
            return comp, f"Avg ratio: {avg_ratio:.2f}x, Max {metric_name} at n={max_n}: {max_val:.2f}"

    if avg_ratio <= thresholds["O(n^3)"]["ratio_max"]:
        return "O(n^3)", f"Avg ratio: {avg_ratio:.2f}x, Max {metric_name} at n={max_n}: {max_val:.2f}"
    else:
        return "O(>n^3)", f"Avg ratio: {avg_ratio:.2f}x, Max {metric_name} at n={max_n}: {max_val:.2f}"

# Expected complexity per mode (best to worst acceptable)
BIGO_EXPECTATIONS = {
    "simple":   {"max_acceptable": "O(n^2)",       "target": "O(n^2)",       "description": "<= O(n^2)"},
    "medium":   {"max_acceptable": "O(n sqrt(n))", "target": "O(n sqrt(n))", "description": "<= O(n sqrt(n))"},
    "complex":  {"max_acceptable": "O(n log n)",   "target": "O(n log n)",   "description": "O(n log n)"},
    "adaptive": {"max_acceptable": "O(n^2)",       "target": "O(n log n)",   "description": "O(n^2) down to O(n log n)"},
}

BIGO_ORDER = ["O(n)", "O(n log n)", "O(n sqrt(n))", "O(n^2)", "O(n^3)", "O(>n^3)"]

def check_expectation(complexity, mode):
    """Returns (is_acceptable, expectation_str)"""
    exp = BIGO_EXPECTATIONS.get(mode)
    if not exp:
        return True, ""

    max_acceptable = exp["max_acceptable"]
    try:
        comp_idx = BIGO_ORDER.index(complexity)
    except ValueError:
        comp_idx = len(BIGO_ORDER) - 1

    try:
        max_idx = BIGO_ORDER.index(max_acceptable)
    except ValueError:
        max_idx = len(BIGO_ORDER) - 1

    is_ok = comp_idx <= max_idx
    return is_ok, exp["description"]

def run_bigo_test(executable, mode):
    min_disorder, max_disorder = MODES[mode]
    ops_by_size = {}
    time_by_size = {}
    all_failures = []

    print(f"\n{COLORS['BOLD']}>> Big-O Analysis | Mode: {mode.upper()}{COLORS['RESET']}")
    print(f"{'Size':>6} | {'Tests':>6} | {'Avg Ops':>10} | {'Ops Ratio':>9} | {'Avg Time(ms)':>12} | {'Time Ratio':>10} | {'Sorted'}")
    print("-" * 82)

    prev_avg_ops = None
    prev_avg_time = None

    for size in BIGO_SIZES:
        total_ops = 0
        total_time_ms = 0.0
        failed = 0

        # Warm-up runs: execute a few times without measuring to stabilize caches
        for _ in range(3):
            disorder = random.uniform(min_disorder, max_disorder)
            sequence = generate_sequence(size, disorder)
            str_seq = [str(x) for x in sequence]
            try:
                subprocess.run(
                    [executable, f'--{mode}'] + str_seq,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=compute_timeout(size)
                )
            except subprocess.TimeoutExpired:
                pass

        # Official measurement runs
        for _ in range(100):
            disorder = random.uniform(min_disorder, max_disorder)
            sequence = generate_sequence(size, disorder)
            str_seq = [str(x) for x in sequence]

            start_time = time.perf_counter()
            try:
                result = subprocess.run(
                    [executable, f'--{mode}'] + str_seq,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=compute_timeout(size)
                )
                elapsed_ms = (time.perf_counter() - start_time) * 1000

                ops = result.stdout.strip().split()
                if ops == ['']:
                    ops = []
                op_count = len(ops)

                checker = PushSwapChecker(sequence)
                is_sorted, _, _ = checker.validate(ops)

                if not is_sorted:
                    failed += 1
                    all_failures.append({
                        "size": size,
                        "mode": mode,
                        "reason": "Failed to sort properly",
                        "ops": op_count,
                        "sequence": " ".join(str_seq)
                    })
                else:
                    total_ops += op_count
                    total_time_ms += elapsed_ms

            except subprocess.TimeoutExpired:
                failed += 1
                all_failures.append({
                    "size": size,
                    "mode": mode,
                    "reason": "Timeout",
                    "ops": "N/A",
                    "sequence": " ".join(str_seq)
                })

        successful = 100 - failed
        if successful > 0:
            avg_ops = total_ops / successful
            avg_time = total_time_ms / successful
        else:
            avg_ops = float('inf')
            avg_time = float('inf')

        ops_by_size[size] = avg_ops
        time_by_size[size] = avg_time

        if prev_avg_ops and prev_avg_ops > 0:
            ops_ratio = avg_ops / prev_avg_ops
            ops_ratio_str = f"{ops_ratio:.2f}x"
        else:
            ops_ratio_str = "N/A"

        if prev_avg_time and prev_avg_time > 0:
            time_ratio = avg_time / prev_avg_time
            time_ratio_str = f"{time_ratio:.2f}x"
        else:
            time_ratio_str = "N/A"

        if failed > 0:
            status = f"{COLORS['RED']}FAIL ({failed}/100){COLORS['RESET']}"
        else:
            status = f"{COLORS['GREEN']}PASS{COLORS['RESET']}"

        ops_str = f"{avg_ops:.0f}" if avg_ops != float('inf') else "INF"
        time_str = f"{avg_time:.2f}" if avg_time != float('inf') else "INF"

        print(f"{size:>6} | {successful:>6} | {ops_str:>10} | {ops_ratio_str:>9} | {time_str:>12} | {time_ratio_str:>10} | {status}")
        prev_avg_ops = avg_ops if avg_ops != float('inf') else None
        prev_avg_time = avg_time if avg_time != float('inf') else None

    ops_complexity, ops_details = classify_by_metric(ops_by_size, BIGO_THRESHOLDS_OPS, "ops")
    time_complexity, time_details = classify_by_metric(time_by_size, BIGO_THRESHOLDS_TIME, "time(ms)")

    print("-" * 82)
    print(f"{COLORS['BOLD']}Ops Complexity:  {COLORS['CYAN']}{ops_complexity}{COLORS['RESET']} ({ops_details})")
    print(f"{COLORS['BOLD']}Time Complexity: {COLORS['CYAN']}{time_complexity}{COLORS['RESET']} ({time_details})")
    print()

    return {
        "mode": mode,
        "ops_complexity": ops_complexity,
        "ops_details": ops_details,
        "time_complexity": time_complexity,
        "time_details": time_details,
        "ops_by_size": ops_by_size,
        "time_by_size": time_by_size,
        "failures": all_failures
    }

def run_bigo_analysis(executable):
    print(f"\n{COLORS['YELLOW']}{COLORS['BOLD']}{'='*80}")
    print(f"  WARNING — INFORMATIONAL ONLY, DO NOT USE TO FAIL ANYONE")
    print(f"{'='*80}{COLORS['RESET']}")
    print(f"{COLORS['YELLOW']}  The subject defines the complexity MODEL (four strategies; complexity measured")
    print(f"  in the NUMBER OF push_swap OPERATIONS generated — not time, not classical array")
    print(f"  complexity), but it does NOT specify how to validate or test it (no sizes, thresholds")
    print(f"  or method). Execution time below is shown for reference only and is NOT part of the")
    print(f"  model — the Overall verdict uses operation count alone. A rough indicator, never a")
    print(f"  pass/fail criterion for an evaluation.{COLORS['RESET']}")

    print(f"\n{COLORS['BOLD']}{'='*80}")
    print(f"  BIG-O COMPLEXITY ANALYSIS")
    print(f"{'='*80}{COLORS['RESET']}")
    print(f"\nThis analysis runs 100 tests per size per mode.")
    print(f"Sizes tested: {BIGO_SIZES}")
    print(f"Each test measures operations and execution time.")
    print(f"Growth ratio between consecutive sizes determines complexity.\n")

    all_results = []
    all_failures = []

    for mode in ["simple", "medium", "complex", "adaptive"]:
        res = run_bigo_test(executable, mode)
        all_results.append(res)
        all_failures.extend(res["failures"])

    def strip_ansi(s):
        import re
        return re.sub(r'\x1b\[[0-9;]*m', '', s)

    def cell(text, color, width):
        """Return text with color, padded to visible width."""
        plain = strip_ansi(text)
        pad = width - len(plain)
        if pad < 0:
            pad = 0
        return f"{color}{plain}{COLORS['RESET']}{' ' * pad}"

    # Summary table
    print(f"{COLORS['BOLD']}{'='*100}")
    print(f"  BIG-O SUMMARY")
    print(f"{'='*100}{COLORS['RESET']}")
    print(f"\n{'Mode':<10} | {'Ops Big-O':<12} | {'Ops Status':<10} | {'Time Big-O':<12} | {'Time (info)':<11} | {'Overall':<8} | {'Expected':<25}")
    print("-" * 115)
    for r in all_results:
        mode = r["mode"].upper()
        ops_comp = r["ops_complexity"]
        time_comp = r["time_complexity"]
        ops_ok, expected_desc = check_expectation(ops_comp, r["mode"])

        # The subject's metric is OPERATION COUNT; time is informational only,
        # so the Overall verdict is based on operations alone.
        ops_status_color = COLORS["GREEN"] if ops_ok else COLORS["RED"]
        overall_color = COLORS["GREEN"] if ops_ok else COLORS["RED"]
        overall_text = "PASS" if ops_ok else "FAIL"

        ops_color = COLORS["GREEN"] if ops_comp in ["O(n)", "O(n log n)"] else COLORS["YELLOW"] if ops_comp in ["O(n sqrt(n))", "O(n^2)"] else COLORS["RED"]
        time_color = COLORS["GREEN"] if time_comp in ["O(n)", "O(n log n)"] else COLORS["YELLOW"] if time_comp in ["O(n sqrt(n))", "O(n^2)"] else COLORS["RED"]

        line = f"{mode:<10} | "
        line += cell(ops_comp, ops_color, 12) + " | "
        line += cell("OK" if ops_ok else "FAIL", ops_status_color, 10) + " | "
        line += cell(time_comp, time_color, 12) + " | "
        line += cell("info", COLORS["CYAN"], 11) + " | "
        line += cell(overall_text, overall_color, 8) + " | "
        line += f"{expected_desc:<25}"
        print(line)
    print()

    # Per-mode details
    print(f"{COLORS['BOLD']}Details by mode:{COLORS['RESET']}")
    for r in all_results:
        mode = r["mode"].upper()
        print(f"  {mode:<8} | Ops:  {r['ops_details']}")
        print(f"           | Time: {r['time_details']}")
    print()

    # Expected classification reference (operation count — the subject's metric)
    print(f"{COLORS['BOLD']}Reference (operation-count complexity — the subject's metric):{COLORS['RESET']}")
    print(f"  Simple  : Expected <= O(n^2)  (nearly sorted)")
    print(f"  Medium  : Expected <= O(n sqrt(n))")
    print(f"  Complex : Expected O(n log n) (optimal comparison sort)")
    print(f"  Adaptive: Expected O(n^2) down to O(n log n) (should adapt to disorder)")
    print()
    print(f"{COLORS['BOLD']}Note:{COLORS['RESET']} Overall reflects OPERATIONS only — the subject's metric. "
          f"Time is shown for reference and is NOT part of the subject's complexity model.")

    if all_failures:
        print(f"{COLORS['RED']}Failures detected during Big-O analysis:{COLORS['RESET']}")
        for f in all_failures[:10]:
            print(f"  Size {f['size']} {f['mode']}: {f['reason']}")
        if len(all_failures) > 10:
            print(f"  ... and {len(all_failures) - 10} more failures")
        print()

    if any("Timeout" in str(f.get("reason", "")) for f in all_failures):
        print_timeout_suggestion()

    return all_results

# ==========================================
# BASIC & EDGE-CASE TESTS
# ==========================================
BASIC_MODES = ["simple", "medium", "complex", "adaptive"]

# (good, pass) operation-count thresholds for small N (42 small sorts).
SMALL_THRESHOLDS = {
    3: {"good": 3,  "pass": 5},
    5: {"good": 12, "pass": 15},
}

# A non-matching mode must beat the matching mode by MORE than this fraction
# to be flagged. This is the "tolerable error margin" for mode specialization.
MODE_COMPARISON_MARGIN = 0.10


def _visible_len(s):
    """Length of a string ignoring ANSI color codes."""
    return len(re.sub(r'\x1b\[[0-9;]*m', '', s))


def _pad(s, width):
    """Right-pad a (possibly colored) string to a visible width."""
    return s + ' ' * max(0, width - _visible_len(s))


def _shellify(argv):
    """Render an argv list the way it would be typed in a shell."""
    return " ".join(f'"{a}"' if (a == "" or " " in a) else a for a in argv)


def _disorder_pct(nums):
    """Disorder % = inversions / max-inversions * 100 (same model as generate_sequence)."""
    n = len(nums)
    if n < 2:
        return 0.0
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if nums[i] > nums[j])
    return inv / (n * (n - 1) / 2.0) * 100.0


def _run_ps(executable, str_args, mode=None, timeout=5):
    """Run push_swap with an optional --mode flag. Returns CompletedProcess or None on timeout."""
    cmd = [executable]
    if mode:
        cmd.append(f"--{mode}")
    cmd += str_args
    try:
        return subprocess.run(cmd, capture_output=True, text=True, check=False, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None


def _exec_and_check(executable, seq, mode=None, timeout=None):
    """Run push_swap on a VALID integer sequence and analyse the result."""
    if timeout is None:
        timeout = compute_timeout(len(seq))
    res = _run_ps(executable, [str(x) for x in seq], mode, timeout)
    if res is None:
        return {"timeout": True, "errored": False, "ops": [], "op_count": 0,
                "is_sorted": False, "has_warn": False}
    # fd1 (stdout) carries the operations; fd2 (stderr) carries "Error" on
    # invalid input (and the benchmark report only when --bench is used).
    errored = "Error" in res.stderr
    ops = res.stdout.split()
    is_sorted, has_warn, _ = PushSwapChecker(list(seq)).validate(ops)
    return {
        "timeout": False,
        "errored": errored,
        "ops": ops,
        "op_count": len(ops),
        "is_sorted": is_sorted and not errored,
        "has_warn": has_warn,
    }


def _grade_small(n, ops):
    t = SMALL_THRESHOLDS.get(n)
    if t is None:
        return ("--", COLORS["CYAN"])
    if ops <= t["good"]:
        return ("GOOD", COLORS["GREEN"])
    if ops <= t["pass"]:
        return ("PASS", COLORS["YELLOW"])
    return ("FAIL", COLORS["RED"])


def _grade_any(n, ops):
    """Grade an op count by size, using whichever threshold table applies."""
    if n in SMALL_THRESHOLDS:
        return _grade_small(n, ops)
    if n in THRESHOLDS:
        return get_grade_info(n, ops)
    return ("--", COLORS["CYAN"])


def _ok_cell(passed, ok_text="OK", bad_text="FAIL"):
    color = COLORS["GREEN"] if passed else COLORS["RED"]
    return f"{color}{ok_text if passed else bad_text}{COLORS['RESET']}"


def test_small_n(executable):
    """[1/10] Exhaustive op-count check for N=3 and N=5 across every permutation."""
    print(f"\n{COLORS['BOLD']}>> [1/10] Small-N operation counts (exhaustive permutations){COLORS['RESET']}")
    print(f"   N=3: GOOD<={SMALL_THRESHOLDS[3]['good']}, PASS<={SMALL_THRESHOLDS[3]['pass']}    "
          f"N=5: GOOD<={SMALL_THRESHOLDS[5]['good']}, PASS<={SMALL_THRESHOLDS[5]['pass']}")
    print("   " + _pad("N", 4) + "| " + _pad("MODE", 9) + "| " + _pad("MAX OPS", 8)
          + "| " + _pad("GRADE", 7) + "| " + _pad("SORTED", 9) + "| PERMS")
    print("   " + "-" * 52)

    fails = 0
    for n in (3, 5):
        perms = list(permutations(range(1, n + 1)))
        for mode in BASIC_MODES:
            max_ops = 0
            bad = 0
            for perm in perms:
                r = _exec_and_check(executable, perm, mode)
                if r["timeout"] or not r["is_sorted"]:
                    bad += 1
                    continue
                max_ops = max(max_ops, r["op_count"])
            grade, color = _grade_small(n, max_ops)
            sort_ok = (bad == 0)
            if grade == "FAIL" or not sort_ok:
                fails += 1
            row = "   " + _pad(str(n), 4) + "| " + _pad(mode, 9) + "| " + _pad(str(max_ops), 8) + "| "
            row += _pad(f"{color}{grade}{COLORS['RESET']}", 7) + "| "
            row += _pad(_ok_cell(sort_ok, "OK", f"{bad} BAD"), 9) + "| " + str(len(perms))
            print(row)
    return fails


def test_reversed(executable):
    """[2/10] Fully reversed input (100% disorder) for a range of sizes."""
    print(f"\n{COLORS['BOLD']}>> [2/10] Reversed input — 100% disorder (worst case){COLORS['RESET']}")
    print("   " + _pad("N", 5) + "| " + _pad("MODE", 9) + "| " + _pad("OPS", 8)
          + "| " + _pad("GRADE", 11) + "| SORTED")
    print("   " + "-" * 48)

    fails = 0
    for n in [3, 5, 10, 50, 100, 500]:
        seq = list(range(n, 0, -1))  # n, n-1, ..., 1  -> fully inverse
        for mode in BASIC_MODES:
            r = _exec_and_check(executable, seq, mode)
            grade, color = _grade_any(n, r["op_count"])
            sort_ok = (not r["timeout"]) and r["is_sorted"]
            if not sort_ok or grade == "FAIL":
                fails += 1
            ops_txt = "TIMEOUT" if r["timeout"] else str(r["op_count"])
            row = "   " + _pad(str(n), 5) + "| " + _pad(mode, 9) + "| " + _pad(ops_txt, 8) + "| "
            row += _pad(f"{color}{grade}{COLORS['RESET']}", 11) + "| "
            row += _ok_cell(sort_ok)
            print(row)
    return fails


def test_sorted(executable):
    """[3/10] Already-sorted input must produce zero operations."""
    print(f"\n{COLORS['BOLD']}>> [3/10] Already-sorted input — must output 0 operations{COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Rule:{COLORS['RESET']} sorted input must produce 0 ops (empty output) and no Error.")
    print("   " + _pad("N", 5) + "| " + _pad("MODE", 9) + "| " + _pad("OPS", 8)
          + "| " + _pad("RESULT", 9) + "| DETAIL")
    print("   " + "-" * 52)

    fails = 0
    for n in [1, 2, 3, 5, 10, 50, 100, 500]:
        seq = list(range(1, n + 1))
        for mode in BASIC_MODES:
            r = _exec_and_check(executable, seq, mode)
            passed = (not r["timeout"]) and (not r["errored"]) and r["op_count"] == 0 and r["is_sorted"]
            if r["timeout"]:
                detail = "timeout"
            elif r["errored"]:
                detail = "errored on valid input"
            elif r["op_count"] > 0:
                detail = f"{r['op_count']} ops (expected 0)"
            elif not r["is_sorted"]:
                detail = "not sorted"
            else:
                detail = ""
            if not passed:
                fails += 1
            ops_txt = "TIMEOUT" if r["timeout"] else str(r["op_count"])
            row = "   " + _pad(str(n), 5) + "| " + _pad(mode, 9) + "| " + _pad(ops_txt, 8) + "| "
            row += _pad(_ok_cell(passed, "PASS", "FAIL"), 9) + "| " + detail
            print(row)
    return fails


def test_nearly_sorted(executable):
    """[4/10] Nearly-sorted input: a single adjacent swap at each boundary."""
    print(f"\n{COLORS['BOLD']}>> [4/10] Nearly-sorted input — single adjacent swap (edge cases){COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Note:{COLORS['RESET']} only one inversion; must sort correctly "
          f"(0 ops here would mean it wrongly thinks the input is sorted).")
    print("   " + _pad("CASE", 20) + "| " + _pad("INPUT", 24) + "| " + _pad("MODE", 9)
          + "| " + _pad("OPS", 8) + "| " + _pad("SORTED", 9) + "| DETAIL")
    print("   " + "-" * 80)

    n = 10
    base = list(range(1, n + 1))
    cases = [
        ("last two swapped",  base[:-2] + [base[-1], base[-2]]),   # 1..8, 10, 9
        ("first two swapped", [base[1], base[0]] + base[2:]),      # 2, 1, 3..10
    ]

    fails = 0
    for label, seq in cases:
        seq_str = " ".join(str(x) for x in seq)
        for mode in BASIC_MODES:
            r = _exec_and_check(executable, seq, mode)
            passed = (not r["timeout"]) and r["is_sorted"]
            if r["timeout"]:
                detail = "timeout"
            elif r["errored"]:
                detail = "errored on valid input"
            elif not r["is_sorted"]:
                detail = "not sorted (0 ops on unsorted input?)" if r["op_count"] == 0 else "not sorted"
            else:
                detail = ""
            if not passed:
                fails += 1
            ops_txt = "TIMEOUT" if r["timeout"] else str(r["op_count"])
            row = "   " + _pad(label, 20) + "| " + _pad(seq_str, 24) + "| " + _pad(mode, 9) + "| "
            row += _pad(ops_txt, 8) + "| " + _pad(_ok_cell(passed), 9) + "| " + detail
            print(row)
    return fails


def _parse_ints(argv):
    """Parse argv tokens (whitespace-split) into ints; None if any token is invalid."""
    out = []
    for arg in argv:
        for tok in arg.split():
            if not re.fullmatch(r'[-+]?\d+', tok):
                return None
            out.append(int(tok))
    return out


def test_errors(executable):
    """[5/10] Error management: invalid -> 'Error\\n' on fd2; valid edges accepted; no args -> nothing."""
    print(f"\n{COLORS['BOLD']}>> [5/10] Error handling{COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Rule:{COLORS['RESET']} invalid input -> exactly \"Error\\n\" on fd2 (nothing on fd1); "
          f"valid edge inputs must sort; no args -> no output.")
    print("   " + _pad("CASE", 30) + "| " + _pad("INPUT", 22) + "| " + _pad("RESULT", 9) + "| DETAIL")
    print("   " + "-" * 80)

    # expect: "error" | "valid" | "error_or_empty" | "empty"
    cases = [
        ('"1a" trailing char',         ["1", "2", "1a"],                  "error"),
        ('"1.0" float',                ["1", "2.0", "3"],                 "error"),
        ('"abc" non-numeric',          ["abc"],                           "error"),
        ('lone "-"',                   ["4", "-", "3"],                   "error"),
        ('lone "+"',                   ["4", "+", "3"],                   "error"),
        ('"6-" malformed',             ["4", "6-", "3"],                  "error"),
        ('"6-1" malformed',            ["4", "6-1", "3"],                 "error"),
        ('"6+1" malformed',            ["4", "6+1", "3"],                 "error"),
        ('> INT_MAX',                  [str(INT_MAX + 1)],                "error"),
        ('< INT_MIN',                  [str(INT_MIN - 1)],                "error"),
        ('LONG overflow',              ["9", "9223372036854775808"],      "error"),
        ('duplicate value',            ["1", "2", "2", "3"],              "error"),
        ('0 and +0 duplicate',         ["2", "22", "0", "+0"],            "error"),
        ('0 and -0 duplicate',         ["2", "22", "0", "-0"],            "error"),
        ('empty number in middle',     ["3", "2", "", "1", "4", "5"],     "error"),
        ('empty arg ""',              [""],                              "error_or_empty"),
        ('space arg " "',             [" "],                             "error_or_empty"),
        ('INT_MAX & INT_MIN valid',    [str(INT_MAX), str(INT_MIN)],      "valid"),
        ('"+0" valid (no dup)',        ["2", "22", "12", "+0"],           "valid"),
        ('negatives valid',            ["9", "8", "7", "-6"],             "valid"),
        ('no arguments -> no output',  [],                                "empty"),
    ]

    fails = 0
    for label, argv, expect in cases:
        res = _run_ps(executable, argv, None)
        if res is None:
            passed, detail = False, "timeout"
        else:
            errored = res.stderr.strip() == "Error" and res.stdout.strip() == ""
            empty = res.stdout == "" and res.stderr == ""
            if expect == "error":
                passed = errored
                detail = _error_detail(res, errored)
            elif expect == "empty":
                passed = empty
                detail = ("no output (correct)" if passed
                          else f"displayed: fd1={repr(res.stdout[:18])} fd2={repr(res.stderr[:18])}")
            elif expect == "error_or_empty":
                passed = errored or empty
                detail = ("Error on fd2" if errored else "no output" if empty
                          else "should Error or print nothing")
            else:  # valid -> must be accepted and sort
                ints = _parse_ints(argv)
                sorted_ok = (ints is not None and "Error" not in res.stderr
                             and PushSwapChecker(ints).validate(res.stdout.split())[0])
                passed = sorted_ok
                detail = ("accepted & sorted" if passed
                          else "wrongly rejected (Error)" if "Error" in res.stderr
                          else "did not sort correctly")
        if not passed:
            fails += 1
        row = "   " + _pad(label, 30) + "| " + _pad(_shellify(argv) or "(none)", 22) + "| "
        row += _pad(_ok_cell(passed, "PASS", "FAIL"), 9) + "| " + detail
        print(row)
    return fails


def _error_detail(res, errored):
    if errored:
        return "Error on fd2" + ("" if res.stderr == "Error\n" else " (not exactly 'Error\\n')")
    if res.stderr.strip() == "" and res.stdout.strip() == "":
        return "no Error printed (invalid input accepted?)"
    if "Error" in res.stdout and res.stderr.strip() != "Error":
        return "Error is on fd1 (stdout) — must be on fd2 (stderr)"
    if res.stderr.strip() != "Error":
        return "fd2 not exactly Error: " + repr(res.stderr.strip()[:40])
    return "fd1 should be empty, got: " + repr(res.stdout.strip()[:30])


def test_split(executable):
    """[6/10] Multi-number argument support (optional but recommended)."""
    print(f"\n{COLORS['BOLD']}>> [6/10] Argument parsing — split / multi-number args{COLORS['RESET']}")
    print("   " + _pad("FORM", 18) + "| " + _pad("EXAMPLE", 22) + "| " + _pad("RESULT", 24) + "| DETAIL")
    print("   " + "-" * 78)

    forms = [
        ("separate args",  ["1", "2", "3", "4", "5"],          [1, 2, 3, 4, 5],       True),
        ("single arg",     ["1 2 3 4 5"],                       [1, 2, 3, 4, 5],       False),
        ("mixed / split",  ["1", "2", "3 4", "5", "6 7"],       [1, 2, 3, 4, 5, 6, 7], False),
    ]

    fails = 0
    warns = 0
    for label, argv, expected, mandatory in forms:
        res = _run_ps(executable, argv, None)
        if res is None:
            accepted, note = False, "timeout"
        else:
            if "Error" in res.stderr:  # "Error" goes to fd2 (stderr)
                accepted, note = False, "returned Error"
            else:
                ops = res.stdout.split()
                is_sorted, _, _ = PushSwapChecker(list(expected)).validate(ops)
                accepted = is_sorted
                note = "sorted OK" if is_sorted else "did not sort correctly"

        if accepted:
            status = f"{COLORS['GREEN']}ACCEPTED{COLORS['RESET']}"
        elif mandatory:
            status = f"{COLORS['RED']}FAIL (mandatory){COLORS['RESET']}"
            fails += 1
        else:
            status = f"{COLORS['YELLOW']}NOT ACCEPTED (warning){COLORS['RESET']}"
            warns += 1
        row = "   " + _pad(label, 18) + "| " + _pad(_shellify(argv), 22) + "| " + _pad(status, 24) + "| " + note
        print(row)

    if warns:
        print(f"\n   {COLORS['YELLOW']}Warning:{COLORS['RESET']} multi-number arguments "
              f"(e.g. {COLORS['BOLD']}1 2 \"3 4\" 5{COLORS['RESET']}) were not accepted.")
        print(f"   This is {COLORS['BOLD']}not mandatory{COLORS['RESET']} for the 42 subject, "
              f"but supporting it is recommended.")
    return fails, warns


def test_mode_specialization(executable):
    """[7/10] Each mode should produce the fewest ops on its own number type."""
    print(f"\n{COLORS['BOLD']}>> [7/10] Mode specialization — each mode should win on its own number type{COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Idea:{COLORS['RESET']} on '<type>' numbers, --<type> should use the fewest ops "
          f"(tolerance {int(MODE_COMPARISON_MARGIN * 100)}%).")

    size = 100
    samples = 20
    types = ["simple", "medium", "complex"]
    cmp_modes = ["simple", "medium", "complex", "adaptive"]

    table = {}
    for t in types:
        lo, hi = MODES[t]
        seqs = [generate_sequence(size, random.uniform(lo, hi)) for _ in range(samples)]
        row = {}
        for m in cmp_modes:
            tot, cnt = 0, 0
            for seq in seqs:
                r = _exec_and_check(executable, seq, m)
                if r["timeout"] or not r["is_sorted"]:
                    continue
                tot += r["op_count"]
                cnt += 1
            row[m] = (tot / cnt) if cnt else None
        table[t] = row

    header = "   " + _pad("NUMBERS \\ MODE", 16) + "| "
    for m in cmp_modes:
        header += _pad(m, 10) + "| "
    print(header)
    print("   " + "-" * (18 + 12 * len(cmp_modes)))

    warns = 0
    warn_msgs = []
    identical_rows = 0
    for t in types:
        row = table[t]
        cand = {m: row[m] for m in types if row[m] is not None}
        best_mode = min(cand, key=cand.get) if cand else None
        vals = [row[m] for m in cmp_modes if row[m] is not None]
        identical = len(vals) >= 2 and (max(vals) - min(vals) < 0.5)
        if identical:
            identical_rows += 1
        line = "   " + _pad(f"{t} numbers", 16) + "| "
        for m in cmp_modes:
            v = row[m]
            cell = "--" if v is None else f"{v:.0f}"
            if identical:
                cell = f"{COLORS['RED']}{cell}{COLORS['RESET']}"
            elif m == t:
                cell = f"{COLORS['CYAN']}{cell}*{COLORS['RESET']}"
            elif best_mode == m and m in types:
                cell = f"{COLORS['GREEN']}{cell}{COLORS['RESET']}"
            line += _pad(cell, 10) + "| "
        print(line)

        expected = row.get(t)
        if expected is not None and not identical:
            for m in types:
                if m == t:
                    continue
                v = row[m]
                if v is not None and v < expected * (1 - MODE_COMPARISON_MARGIN):
                    warns += 1
                    warn_msgs.append((t, m, expected, v))

    print(f"   {COLORS['CYAN']}*{COLORS['RESET']} = matching mode (expected best for that number type)")

    # If every number type yields identical op counts across modes, the strategy
    # flags are not differentiated at all -> invalid.
    fails = 0
    if identical_rows == len(types):
        fails = 1
        print(f"   {COLORS['RED']}{COLORS['BOLD']}INVALID:{COLORS['RESET']} all strategies produce "
              f"identical operation counts — the --simple/--medium/--complex flags are not "
              f"differentiated (each mode must run a different algorithm).")
    elif identical_rows:
        print(f"   {COLORS['YELLOW']}Note:{COLORS['RESET']} {identical_rows} of {len(types)} number "
              f"types showed identical op counts across modes.")
        warns += identical_rows

    for (t, m, exp, v) in warn_msgs:
        print(f"   {COLORS['YELLOW']}Warning:{COLORS['RESET']} on {t} numbers, --{m} used {v:.0f} ops "
              f"vs --{t} {exp:.0f} (>{int(MODE_COMPARISON_MARGIN * 100)}% better). "
              f"--{t} should specialize best for {t} inputs.")
    return fails, warns


def test_default_flag(executable):
    """[8/10] Running with no strategy flag should behave like --adaptive."""
    print(f"\n{COLORS['BOLD']}>> [8/10] Default strategy — no flag should behave like --adaptive{COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Rule:{COLORS['RESET']} running with no flag must sort, and should match --adaptive.")
    print("   " + _pad("INPUT", 22) + "| " + _pad("NO-FLAG OPS", 12) + "| " + _pad("ADAPTIVE OPS", 13)
          + "| " + _pad("SORTS", 8) + "| MATCHES ADAPTIVE")
    print("   " + "-" * 78)

    cases = [[5, 4, 3, 2, 1], [2, 1, 0], [1, 5, 2, 4, 3]]
    fails = 0
    warns = 0
    for seq in cases:
        r_none = _exec_and_check(executable, seq, None)
        r_adap = _exec_and_check(executable, seq, "adaptive")
        sorts = (not r_none["timeout"]) and r_none["is_sorted"]
        adap_ok = (not r_adap["timeout"]) and r_adap["is_sorted"]
        match = sorts and adap_ok and r_none["op_count"] == r_adap["op_count"]
        if not sorts:
            fails += 1
        elif not match:
            warns += 1
        none_ops = "TIMEOUT" if r_none["timeout"] else str(r_none["op_count"])
        adap_ops = "TIMEOUT" if r_adap["timeout"] else str(r_adap["op_count"])
        match_cell = _ok_cell(match, "yes", "differs") if sorts else f"{COLORS['CYAN']}n/a{COLORS['RESET']}"
        row = "   " + _pad(" ".join(map(str, seq)), 22) + "| " + _pad(none_ops, 12) + "| "
        row += _pad(adap_ops, 13) + "| " + _pad(_ok_cell(sorts), 8) + "| " + match_cell
        print(row)
    if warns:
        print(f"\n   {COLORS['YELLOW']}Note:{COLORS['RESET']} no-flag op counts differ from --adaptive; "
              f"it sorts, but may not default to the adaptive strategy.")
    return fails, warns


def test_bench(executable):
    """[9/10] Benchmark mode (--bench): fd1 = ops, fd2 = report (strategy + disorder %)."""
    print(f"\n{COLORS['BOLD']}>> [9/10] Benchmark mode (--bench){COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Optional:{COLORS['RESET']} fd1 must still sort; the fd2 report should name the "
          f"strategy and show the disorder %.")
    print("   " + _pad("RUN", 27) + "| " + _pad("FD1 SORTS", 10) + "| " + _pad("STRATEGY", 12)
          + "| " + _pad("DISORDER", 18) + "| RESULT")
    print("   " + "-" * 84)

    def pcts(text):
        return [float(x) for x in re.findall(r'(\d+(?:\.\d+)?)\s*%', text)]

    warns = 0

    # Per mode on reversed input -> strategy must be named, disorder ~100%.
    rev = [5, 4, 3, 2, 1]
    for mode in BASIC_MODES:
        res = _run_ps(executable, ["--bench", f"--{mode}"] + [str(x) for x in rev], None,
                      timeout=compute_timeout(len(rev)))
        if res is None:
            warns += 1
            print("   " + _pad(f"--bench --{mode} (rev)", 27) + "| " + _pad("--", 10) + "| "
                  + _pad("--", 12) + "| " + _pad("--", 18) + f"| {COLORS['YELLOW']}timeout{COLORS['RESET']}")
            continue
        bench = res.stderr.lower()
        sorts = PushSwapChecker(list(rev)).validate(res.stdout.split())[0]
        strat_ok = mode in bench
        vals = pcts(bench)
        dis_ok = any(p >= 99.0 for p in vals)
        dis_txt = f"{max(vals):.2f}%" if vals else "none"
        ok = sorts and strat_ok and dis_ok
        if not ok:
            warns += 1
        result = f"{COLORS['GREEN']}OK{COLORS['RESET']}" if ok else f"{COLORS['YELLOW']}check{COLORS['RESET']}"
        row = "   " + _pad(f"--bench --{mode} (rev)", 27) + "| " + _pad(_ok_cell(sorts), 10) + "| "
        row += _pad(_ok_cell(strat_ok, mode, "missing"), 12) + "| "
        row += _pad(_ok_cell(dis_ok, dis_txt, dis_txt + " !~100"), 18) + "| " + result
        print(row)

    # Disorder accuracy: random sequences (0..100%) -> bench % must match the
    # disorder we compute ourselves (same inversion model as generate_sequence).
    print(f"   {COLORS['CYAN']}disorder accuracy{COLORS['RESET']} (random sizes; expected vs reported):")
    print("   " + _pad("INPUT", 27) + "| " + _pad("SIZE", 6) + "| " + _pad("EXPECTED", 12)
          + "| " + _pad("BENCH %", 18) + "| RESULT")
    print("   " + "-" * 74)
    dis_cases = [random.sample(range(-100000, 100000), s) for s in [5, 5, 5, 10, 20, 100]]
    dis_cases.append([1, 2, 3, 4, 5])      # 0%
    dis_cases.append([5, 4, 3, 2, 1])      # 100%
    for seq in dis_cases:
        expected = _disorder_pct(seq)
        res = _run_ps(executable, ["--bench", "--adaptive"] + [str(x) for x in seq], None,
                      timeout=compute_timeout(len(seq)))
        if res is None:
            ok, got = False, "timeout"
        else:
            vals = pcts(res.stderr.lower())
            if vals:
                closest = min(vals, key=lambda p: abs(p - expected))
                ok = abs(closest - expected) <= 1.0
                got = f"{closest:.2f}%"
            else:
                ok, got = False, "none"
        if not ok:
            warns += 1
        result = f"{COLORS['GREEN']}OK{COLORS['RESET']}" if ok else f"{COLORS['YELLOW']}check{COLORS['RESET']}"
        row = "   " + _pad(f"{len(seq)} random nums", 27) + "| " + _pad(str(len(seq)), 6) + "| "
        row += _pad(f"{expected:.2f}%", 12) + "| " + _pad(_ok_cell(ok, got, got + " !=exp"), 18) + "| " + result
        print(row)

    if warns:
        print(f"\n   {COLORS['YELLOW']}Note:{COLORS['RESET']} --bench is optional (not a failing requirement), "
              f"but its fd2 report should name the strategy and report the disorder accurately (0..100%).")
    return warns


def _run_memcheck(executable, argv, timeout=30, input_data=None):
    """Crash detection (direct run) + leak/error check (valgrind/leaks).

    input_data feeds stdin (used by the bonus checker, which reads operations there).
    """
    r = {"segfault": False, "mem_ok": False, "leaked": 0, "errors": 0,
         "tool": None, "timeout": False}

    # 1) Direct run -> reliable crash detection, independent of valgrind.
    try:
        d = subprocess.run([executable] + argv, input=input_data, capture_output=True,
                           text=True, timeout=compute_timeout(len(argv)))
        r["segfault"] = (d.returncode == -signal.SIGSEGV) or ("Segmentation fault" in (d.stdout + d.stderr))
    except subprocess.TimeoutExpired:
        r["timeout"] = True

    # 2) Memory tool (optional; only trusted when it actually produced a report).
    if shutil.which("valgrind"):
        r["tool"], cmd = "valgrind", ["valgrind", "--leak-check=full", executable] + argv
    elif shutil.which("leaks"):
        r["tool"], cmd = "leaks", ["leaks", "--atExit", "--", executable] + argv
    else:
        return r

    try:
        res = subprocess.run(cmd, input=input_data, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        r["timeout"] = True
        return r

    out = res.stdout + res.stderr
    if "SIGSEGV" in out or "Segmentation fault" in out:
        r["segfault"] = True
    if r["tool"] == "valgrind":
        if "ERROR SUMMARY" in out:  # valgrind actually ran (else: setup error)
            r["mem_ok"] = True
            for pat in (r"definitely lost: ([\d,]+) bytes", r"indirectly lost: ([\d,]+) bytes"):
                m = re.search(pat, out)
                if m:
                    r["leaked"] += int(m.group(1).replace(",", ""))
            m = re.search(r"ERROR SUMMARY: (\d+) errors", out)
            if m:
                r["errors"] = int(m.group(1))
    else:
        m = re.search(r"(\d+) total leaked bytes", out)
        if m:
            r["mem_ok"] = True
            r["leaked"] = int(m.group(1))
    return r


def test_memory(executable):
    """[10/10] Memory leaks (valgrind / leaks) and crashes on representative inputs."""
    print(f"\n{COLORS['BOLD']}>> [10/10] Memory & crashes (valgrind / leaks){COLORS['RESET']}")
    if not (shutil.which("valgrind") or shutil.which("leaks")):
        print(f"   {COLORS['YELLOW']}Skipped:{COLORS['RESET']} neither 'valgrind' nor 'leaks' found on PATH.")
        return 0

    cases = [
        ("valid 5",        [str(x) for x in random.sample(range(-1000, 1000), 5)]),
        ("valid 100",      [str(x) for x in random.sample(range(-100000, 100000), 100)]),
        ("already sorted", ["0", "1", "2", "3", "4"]),
        ("error (dup)",    ["1", "2", "2"]),
        ("no args",        []),
    ]

    print("   " + _pad("CASE", 16) + "| " + _pad("TOOL", 9) + "| " + _pad("LEAKED", 14)
          + "| " + _pad("MEM ERRORS", 12) + "| " + _pad("CRASH", 8) + "| RESULT")
    print("   " + "-" * 78)

    fails = 0
    any_mem_ok = False
    na = f"{COLORS['CYAN']}n/a{COLORS['RESET']}"
    for label, argv in cases:
        r = _run_memcheck(executable, argv)
        if r["timeout"]:
            print("   " + _pad(label, 16) + "| " + _pad(r["tool"] or "--", 9) + "| " + _pad("--", 14)
                  + "| " + _pad("--", 12) + "| " + _pad("--", 8) + f"| {COLORS['YELLOW']}timeout{COLORS['RESET']}")
            continue
        seg, memok, leaked, errors = r["segfault"], r["mem_ok"], r["leaked"], r["errors"]
        any_mem_ok = any_mem_ok or memok
        bad = seg or (memok and (leaked > 0 or errors > 0))
        if bad:
            fails += 1
        if bad:
            result = f"{COLORS['RED']}FAIL{COLORS['RESET']}"
        elif memok:
            result = f"{COLORS['GREEN']}OK{COLORS['RESET']}"
        else:
            result = f"{COLORS['YELLOW']}no crash (leaks n/a){COLORS['RESET']}"
        leak_cell = _ok_cell(leaked == 0, "0 B", f"{leaked} B") if memok else na
        err_cell = _ok_cell(errors == 0, "0", str(errors)) if memok else na
        row = "   " + _pad(label, 16) + "| " + _pad(r["tool"] or "--", 9) + "| " + _pad(leak_cell, 14) + "| "
        row += _pad(err_cell, 12) + "| " + _pad(_ok_cell(not seg, "no", "SEGV"), 8) + "| " + result
        print(row)

    if not any_mem_ok:
        print(f"   {COLORS['YELLOW']}Note:{COLORS['RESET']} the memory tool could not produce a report "
              f"(broken/!installed); only crash detection was performed.")
    return fails


def run_basic_tests(executable):
    """Run all basic / edge-case tests and print a consolidated summary."""
    print(f"\n{COLORS['BOLD']}{'=' * 80}")
    print(f"  BASIC & EDGE-CASE TESTS")
    print(f"{'=' * 80}{COLORS['RESET']}")

    f_small = test_small_n(executable)
    f_rev = test_reversed(executable)
    f_sort = test_sorted(executable)
    f_near = test_nearly_sorted(executable)
    f_err = test_errors(executable)
    f_split, w_split = test_split(executable)
    f_mode, w_mode = test_mode_specialization(executable)
    f_default, w_default = test_default_flag(executable)
    w_bench = test_bench(executable)
    f_mem = test_memory(executable)

    total_fails = f_small + f_rev + f_sort + f_near + f_err + f_split + f_mode + f_default + f_mem
    total_warns = w_split + w_mode + w_default + w_bench

    print(f"\n{COLORS['BOLD']}{'=' * 80}")
    print(f"  BASICS SUMMARY")
    print(f"{'=' * 80}{COLORS['RESET']}")

    def line(label, fails, warns=0):
        if fails > 0:
            tag = f"{COLORS['RED']}FAIL ({fails}){COLORS['RESET']}"
        elif warns > 0:
            tag = f"{COLORS['YELLOW']}WARN ({warns}){COLORS['RESET']}"
        else:
            tag = f"{COLORS['GREEN']}PASS{COLORS['RESET']}"
        print("  " + _pad(label, 28) + ": " + tag)

    line("Small-N op counts (3,5)", f_small)
    line("Reversed input", f_rev)
    line("Sorted -> 0 ops", f_sort)
    line("Nearly-sorted (1 swap)", f_near)
    line("Error handling", f_err)
    line("Split / multi-number args", 0, w_split)
    line("Mode specialization", f_mode, w_mode)
    line("Default flag (adaptive)", f_default, w_default)
    line("Benchmark mode (--bench)", 0, w_bench)
    line("Memory & crashes", f_mem)
    print("  " + "-" * 40)
    overall = (f"{COLORS['GREEN']}ALL BASIC TESTS PASSED{COLORS['RESET']}" if total_fails == 0
               else f"{COLORS['RED']}{total_fails} BASIC FAILURE(S){COLORS['RESET']}")
    if total_warns:
        overall += f"   {COLORS['YELLOW']}({total_warns} warning(s)){COLORS['RESET']}"
    print("  " + overall)
    return total_fails, total_warns


# ==========================================
# BONUS — CHECKER TESTS
# ==========================================
def _checker_verdict(stack, ops):
    """Expected checker verdict ('OK'/'KO') for a list of VALID ops applied to stack."""
    is_sorted, _, _ = PushSwapChecker(list(stack)).validate(ops)
    return "OK" if is_sorted else "KO"


def run_bonus_tests(executable, checker):
    """Test the bonus `checker` program (next to push_swap)."""
    print(f"\n{COLORS['BOLD']}{'=' * 80}")
    print(f"  BONUS — CHECKER TESTS")
    print(f"{'=' * 80}{COLORS['RESET']}")
    print(f"   checker: {checker}")

    def run_checker(stack, ops, timeout=5):
        args = [str(x) for x in stack]
        stdin = ("\n".join(ops) + "\n") if ops else ""
        try:
            return subprocess.run([checker] + args, input=stdin, capture_output=True,
                                  text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None

    fails = 0

    # --- 1) Error management: invalid input -> exactly "Error\n" on fd2 ---
    print(f"\n{COLORS['BOLD']}>> Error management{COLORS['RESET']}  (must print \"Error\\n\" on fd2)")
    print("   " + _pad("CASE", 28) + "| " + _pad("RESULT", 9) + "| DETAIL")
    print("   " + "-" * 60)
    err_cases = [
        ('non-numeric arg',          [3, 2, "one", 0],  None),
        ('duplicate arg',            [1, 2, 2],         None),
        ('> INT_MAX arg',            [1, INT_MAX + 1],  None),
        ('empty arg ""',            ["", 1],           None),
        ('non-existent instruction', [3, 2, 1, 0],      ["rra", "zz"]),
        ('instruction with spaces',  [3, 2, 1, 0],      [" sa "]),
    ]
    for label, stack, ops in err_cases:
        res = run_checker(stack, ops)
        if res is None:
            passed, detail = False, "timeout"
        else:
            errored = res.stderr.strip() == "Error"
            clean = res.stdout.strip() == ""
            passed = errored and clean
            if passed:
                detail = "Error on fd2"
            elif res.stderr.strip() == "" and res.stdout.strip() == "":
                detail = "no Error (accepted bad input?)"
            elif not errored:
                detail = "fd2 not exactly Error: " + repr(res.stderr.strip()[:28])
            else:
                detail = "fd1 not empty: " + repr(res.stdout.strip()[:22])
        if not passed:
            fails += 1
        print("   " + _pad(label, 28) + "| " + _pad(_ok_cell(passed, "PASS", "FAIL"), 9) + "| " + detail)

    res = run_checker([], None)
    if res is None:
        passed, detail = False, "timeout"
    else:
        passed = res.stdout == "" and res.stderr == ""
        detail = ("no output (correct)" if passed
                  else f"displayed: fd1={repr(res.stdout[:15])} fd2={repr(res.stderr[:15])}")
    if not passed:
        fails += 1
    print("   " + _pad("no arguments -> nothing", 28) + "| "
          + _pad(_ok_cell(passed, "PASS", "FAIL"), 9) + "| " + detail)

    # --- 2) & 3) Verdict tests (KO = doesn't sort, OK = sorts) ---
    def verdict_section(title, cases, expected):
        print(f"\n{COLORS['BOLD']}>> {title}{COLORS['RESET']}  (valid ops -> {expected})")
        print("   " + _pad("STACK", 26) + "| " + _pad("OPS", 6) + "| " + _pad("EXPECT", 7)
              + "| " + _pad("GOT", 9) + "| RESULT")
        print("   " + "-" * 60)
        f = 0
        for stack, ops in cases:
            res = run_checker(stack, ops)
            if res is None:
                got, ok = "timeout", False
            else:
                got = res.stdout.strip() or "(none)"
                ok = got == expected
            if not ok:
                f += 1
            stack_txt = " ".join(str(x) for x in stack)
            print("   " + _pad(stack_txt[:25], 26) + "| " + _pad(str(len(ops)), 6) + "| "
                  + _pad(expected, 7) + "| " + _pad(got, 9) + "| " + _ok_cell(ok, "PASS", "FAIL"))
        return f

    # KO cases: subject examples + push_swap output deliberately corrupted (+sa).
    ko_cases = [
        ([0, 9, 1, 8, 2, 7, 3, 6, 4, 5], ["sa", "pb", "rrr"]),
        ([3, 2, 1, 0], ["sa", "rra", "pb"]),
    ]
    for _ in range(4):
        stack = random.sample(range(-100, 100), 5)
        res = _run_ps(executable, [str(x) for x in stack], None)
        ops = (res.stdout.split() if res else []) + ["sa"]
        if _checker_verdict(stack, ops) == "KO":
            ko_cases.append((stack, ops))
    fails += verdict_section("False tests", ko_cases, "KO")

    # OK cases: subject examples + push_swap output (verified to sort via simulation).
    ok_cases = [
        ([0, 1, 2], []),
        ([0, 9, 1, 8, 2], ["pb", "ra", "pb", "ra", "sa", "ra", "pa", "pa"]),
        ([3, 2, 1, 0], ["rra", "pb", "sa", "rra", "pa"]),
    ]
    for _ in range(4):
        stack = random.sample(range(-100, 100), 5)
        res = _run_ps(executable, [str(x) for x in stack], None)
        ops = res.stdout.split() if res else []
        if _checker_verdict(stack, ops) == "OK":
            ok_cases.append((stack, ops))
    fails += verdict_section("Right tests", ok_cases, "OK")

    # --- 4) Memory & crashes on the checker ---
    print(f"\n{COLORS['BOLD']}>> Memory & crashes{COLORS['RESET']}")
    if not (shutil.which("valgrind") or shutil.which("leaks")):
        print(f"   {COLORS['YELLOW']}Skipped:{COLORS['RESET']} no valgrind/leaks on PATH (crash check still runs).")
    print("   " + _pad("CASE", 18) + "| " + _pad("TOOL", 9) + "| " + _pad("LEAKED", 14)
          + "| " + _pad("MEM ERRORS", 12) + "| " + _pad("CRASH", 8) + "| RESULT")
    print("   " + "-" * 78)
    na = f"{COLORS['CYAN']}n/a{COLORS['RESET']}"
    mem_cases = [
        ("valid + sort ops", ["0", "9", "1", "8", "2"], "pb\nra\npb\nra\nsa\nra\npa\npa\n"),
        ("error (dup)",       ["1", "2", "2"],           ""),
        ("no args",           [],                         ""),
    ]
    for label, argv, stdin in mem_cases:
        r = _run_memcheck(checker, argv, input_data=stdin)
        if r["timeout"]:
            print("   " + _pad(label, 18) + "| " + _pad(r["tool"] or "--", 9) + "| " + _pad("--", 14)
                  + "| " + _pad("--", 12) + "| " + _pad("--", 8) + f"| {COLORS['YELLOW']}timeout{COLORS['RESET']}")
            continue
        seg, memok, leaked, errors = r["segfault"], r["mem_ok"], r["leaked"], r["errors"]
        bad = seg or (memok and (leaked > 0 or errors > 0))
        if bad:
            fails += 1
        result = (f"{COLORS['RED']}FAIL{COLORS['RESET']}" if bad
                  else f"{COLORS['GREEN']}OK{COLORS['RESET']}" if memok
                  else f"{COLORS['YELLOW']}no crash (leaks n/a){COLORS['RESET']}")
        leak_cell = _ok_cell(leaked == 0, "0 B", f"{leaked} B") if memok else na
        err_cell = _ok_cell(errors == 0, "0", str(errors)) if memok else na
        print("   " + _pad(label, 18) + "| " + _pad(r["tool"] or "--", 9) + "| " + _pad(leak_cell, 14)
              + "| " + _pad(err_cell, 12) + "| " + _pad(_ok_cell(not seg, "no", "SEGV"), 8) + "| " + result)

    print(f"\n{COLORS['BOLD']}{'=' * 80}")
    print(f"  BONUS SUMMARY")
    print(f"{'=' * 80}{COLORS['RESET']}")
    if fails == 0:
        print(f"  {COLORS['GREEN']}ALL CHECKER TESTS PASSED{COLORS['RESET']}")
    else:
        print(f"  {COLORS['RED']}{fails} CHECKER FAILURE(S){COLORS['RESET']}")
    return fails


# ==========================================
# MAIN ENTRY
# ==========================================
def print_range_banner():
    """Print the active number-generation range at the top of a run."""
    lo, hi, label = GEN_RANGE
    print(f"{COLORS['BOLD']}Number range:{COLORS['RESET']} {COLORS['CYAN']}{label}{COLORS['RESET']} "
          f"[{lo}, {hi}] {COLORS['YELLOW']}— your push_swap must support these values.{COLORS['RESET']}")
    print(f"   {COLORS['CYAN']}Range flags:{COLORS['RESET']} default "
          f"{COLORS['BOLD']}INT_MIN..INT_MAX{COLORS['RESET']}, "
          f"{COLORS['BOLD']}--1m{COLORS['RESET']} (-1M..1M), {COLORS['BOLD']}--u1m{COLORS['RESET']} (0..1M)")
    print(f"   {COLORS['CYAN']}Timeouts:{COLORS['RESET']} scaled by input size "
          f"(~5s small, ~10s @500, ~15s @800).\n")


def print_timeout_suggestion():
    """Hint shown when timeouts occur: try a narrower value range."""
    _, _, label = GEN_RANGE
    print(f"\n{COLORS['MAGENTA']}{COLORS['BOLD']}Timeouts detected.{COLORS['RESET']} "
          f"Some ./push_swap calls exceeded their (size-scaled) time limit.")
    if label == "INT_MIN..INT_MAX":
        print(f"   Try a narrower value range to check whether large/negative values are the cause: "
              f"{COLORS['BOLD']}--1m{COLORS['RESET']} (-1M..1M) or {COLORS['BOLD']}--u1m{COLORS['RESET']} (0..1M).")
    else:
        print(f"   Already using a narrowed range ({label}); the algorithm is likely just slow at this size.")


def print_reports_suggestion():
    """Hint shown on failures when --reports was not enabled."""
    print(f"\n{COLORS['CYAN']}Tip:{COLORS['RESET']} re-run with {COLORS['BOLD']}--reports{COLORS['RESET']} "
          f"to dump each failing case (input numbers + operations) to files next to your push_swap,")
    print(f"   so you can replay them in {COLORS['BOLD']}ft_ps_visu{COLORS['RESET']} or the official 42 checker.")


def main():
    global GEN_RANGE
    args = sys.argv[1:]

    reports_enabled = False
    if '--reports' in args:
        reports_enabled = True
        args = [a for a in args if a != '--reports']

    bigo_mode = False
    if '--big-o' in args:
        bigo_mode = True
        args = [a for a in args if a != '--big-o']

    basic_only = False
    if '--basic' in args:
        basic_only = True
        args = [a for a in args if a != '--basic']

    bonus = False
    if '--bonus' in args:
        bonus = True
        args = [a for a in args if a != '--bonus']

    range_key = "intmax"
    if '--1m' in args:
        range_key = "1m"
        args = [a for a in args if a != '--1m']
    if '--u1m' in args:
        range_key = "u1m"
        args = [a for a in args if a != '--u1m']
    GEN_RANGE = NUMBER_RANGES[range_key]

    if len(args) < 1 or len(args) > 3:
        print(f"Usage:")
        print(f"  Full Test Suite : {sys.argv[0]} [--reports] [--1m|--u1m] <path_to_push_swap>")
        print(f"  Specific Test   : {sys.argv[0]} [--reports] [--1m|--u1m] <path_to_push_swap> <size> <mode>")
        print(f"  Basic Tests     : {sys.argv[0]} --basic [--1m|--u1m] <path_to_push_swap>")
        print(f"  Big-O Analysis  : {sys.argv[0]} --big-o [--1m|--u1m] <path_to_push_swap>")
        print(f"  Bonus checker   : add --bonus to any run (needs ./checker next to push_swap)")
        print(f"  Ranges          : default INT_MIN..INT_MAX, --1m (-1M..1M), --u1m (0..1M)")
        sys.exit(1)
        
    executable = args[0]
    if not os.path.isfile(executable) or not os.access(executable, os.X_OK):
        print(f"Error: '{executable}' not found or not executable.")
        sys.exit(1)

    print_range_banner()

    checker = None
    if bonus:
        checker = os.path.join(os.path.dirname(os.path.abspath(executable)), "checker")
        if not (os.path.isfile(checker) and os.access(checker, os.X_OK)):
            print(f"{COLORS['RED']}--bonus: 'checker' not found or not executable next to push_swap:{COLORS['RESET']} {checker}")
            print(f"   Build your bonus checker (e.g. `make bonus`) and place it there. Skipping bonus.\n")
            checker = None

    if bigo_mode:
        run_bigo_analysis(executable)
        if checker:
            run_bonus_tests(executable, checker)
        sys.exit(0)

    if basic_only:
        fails, _ = run_basic_tests(executable)
        bonus_fails = run_bonus_tests(executable, checker) if checker else 0
        sys.exit(1 if (fails or bonus_fails) else 0)

    all_failures = []
    all_warnings = []
    results = []

    if len(args) == 1:
        print(f"{COLORS['BOLD']}Running FULL TEST SUITE for {executable}{COLORS['RESET']}\n")

        # Basic / edge-case tests run first, before the performance suite.
        run_basic_tests(executable)

        sizes = [100, 500]
        modes = ["simple", "medium", "complex", "adaptive"]

        for size in sizes:
            for mode in modes:
                stats, fails, warns = run_test_suite(executable, size, mode, reports_enabled)
                results.append(stats)
                all_failures.extend(fails)
                all_warnings.extend(warns)
                
    else:
        try:
            size = int(args[1])
        except ValueError:
            print("Error: Size must be an integer.")
            sys.exit(1)
            
        mode = args[2].lower() if len(args) == 3 else "adaptive"
        if mode not in MODES:
            print(f"Error: Invalid mode. Choose from {list(MODES.keys())}")
            sys.exit(1)

        if size not in THRESHOLDS:
            print(f"Error: single-test size must be one of {sorted(THRESHOLDS)} "
                  f"(small sizes are covered by --basic).")
            sys.exit(1)

        print(f"{COLORS['BOLD']}Running SINGLE TEST SUITE for {executable}{COLORS['RESET']}\n")
        stats, fails, warns = run_test_suite(executable, size, mode, reports_enabled)
        results.append(stats)
        all_failures.extend(fails)
        all_warnings.extend(warns)

    # Print detailed failures and warnings if any exist
    print_failures(all_failures)
    print_warnings(all_warnings)
    if any("Timeout" in str(f.get("reason", "")) for f in all_failures):
        print_timeout_suggestion()
    if all_failures and not reports_enabled:
        print_reports_suggestion()

    # Print global summary
    print("\n" + "="*96)
    print(f"{COLORS['BOLD']}PERFORMANCE SUMMARY{COLORS['RESET']}")
    print("="*96)
    print(f"{'SIZE':<6} | {'MODE':<8} | {'MAX (GRADE)':<18} | {'MIN (GRADE)':<18} | {'AVG (GRADE)':<18} | {'FAILS':<6} | {'WARN'}")
    print("-" * 96)
    
    for r in results:
        # Get grade info (text and color)
        max_text, max_color = get_grade_info(r['size'], r['max'])
        min_text, min_color = get_grade_info(r['size'], r['min'])
        avg_text, avg_color = get_grade_info(r['size'], r['avg'])
        
        # Format columns properly to align ignoring ansi color codes
        col_max = format_grade_column(r['max'], max_text, max_color)
        col_min = format_grade_column(r['min'], min_text, min_color)
        col_avg = format_grade_column(r['avg'], avg_text, avg_color)
        
        fail_str = f"{COLORS['RED']}{r['fails']}{COLORS['RESET']}" if r['fails'] > 0 else f"{COLORS['GREEN']}0{COLORS['RESET']}"
        warn_str = f"{COLORS['YELLOW']}{r['warnings']}{COLORS['RESET']}" if r['warnings'] > 0 else f"{COLORS['GREEN']}0{COLORS['RESET']}"
        
        print(f"{r['size']:<6} | {r['mode'].upper():<8} | {col_max} | {col_min} | {col_avg} | {fail_str:<6} | {warn_str}")

    print("="*96)

    if checker:
        run_bonus_tests(executable, checker)


if __name__ == "__main__":
    main()
