#!/usr/bin/env python3

import sys
import os
import random
import subprocess
import glob
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

# ==========================================
# DATA GENERATOR
# ==========================================
def generate_sequence(size, target_disorder):
    raw_sequence = random.sample(range(-1000000, 1000000), size)
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
                timeout=10
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
# MAIN ENTRY
# ==========================================
def main():
    args = sys.argv[1:]
    
    reports_enabled = False
    if '--reports' in args:
        reports_enabled = True
        args = [a for a in args if a != '--reports']
    
    if len(args) < 1 or len(args) > 3:
        print(f"Usage:")
        print(f"  Full Test Suite : {sys.argv[0]} [--reports] <path_to_push_swap>")
        print(f"  Specific Test   : {sys.argv[0]} [--reports] <path_to_push_swap> <size> <mode>")
        sys.exit(1)
        
    executable = args[0]
    if not os.path.isfile(executable) or not os.access(executable, os.X_OK):
        print(f"Error: '{executable}' not found or not executable.")
        sys.exit(1)
        
    all_failures = []
    all_warnings = []
    results = []

    if len(args) == 1:
        print(f"{COLORS['BOLD']}Running FULL TEST SUITE for {executable}{COLORS['RESET']}\n")
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
            
        print(f"{COLORS['BOLD']}Running SINGLE TEST SUITE for {executable}{COLORS['RESET']}\n")
        stats, fails, warns = run_test_suite(executable, size, mode, reports_enabled)
        results.append(stats)
        all_failures.extend(fails)
        all_warnings.extend(warns)

    # Print detailed failures and warnings if any exist
    print_failures(all_failures)
    print_warnings(all_warnings)

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


if __name__ == "__main__":
    main()
