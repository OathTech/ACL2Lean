import subprocess
import sys
import json
import re

def run_acl2(expr):
    """Run an expression in ACL2 and return the result."""
    script = f"{expr}\n(quit)\n"
    process = subprocess.Popen(
        ['acl2'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    stdout, stderr = process.communicate(input=script)
    
    lines = [l.strip() for l in stdout.splitlines() if l.strip()]
    for i in range(len(lines) - 1, -1, -1):
        if "ACL2 !>" in lines[i]:
            res = lines[i].replace("ACL2 !>", "").strip()
            if res and res != "Bye.":
                return res
            if i > 0:
                res = lines[i-1].strip()
                if not res.startswith("+++") and not res.startswith("Type"):
                    return res
    return None

def run_lean(expr):
    """Run an expression in Lean and return the result."""
    process = subprocess.Popen(
        ['lake', 'exe', 'acl2lean', 'eval', expr],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    stdout, stderr = process.communicate()
    lines = stdout.strip().splitlines()
    if not lines:
        return None
    return lines[-1].strip()

def run_lean_in(path, expr):
    """Run an expression in Lean in the context of a file."""
    process = subprocess.Popen(
        ['lake', 'exe', 'acl2lean', 'eval-in', path, expr],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    stdout, stderr = process.communicate()
    lines = stdout.strip().splitlines()
    if not lines:
        return None
    return lines[-1].strip()

def normalize_lean_output(s):
    """Crude normalization of Lean SExpr repr to ACL2-like string."""
    if not s: return s
    if "ACL2.Number.int" in s:
        match = re.search(r"ACL2\.Number\.int\s+(-?\d+)", s)
        if match:
            return match.group(1)
    if "ACL2.Atom.bool true" in s or "ACL2.Atom.symbol { package := \"ACL2\", name := \"T\" }" in s:
        return "T"
    if "ACL2.SExpr.nil" in s:
        return "NIL"
    return s.upper()

def normalize_acl2_output(s):
    if not s: return s
    if "ACL2 !>" in s:
        s = s.split("ACL2 !>")[1].strip()
    return s.strip().upper()

def verify(expr):
    print(f"Verifying: {expr}")
    acl2_res_raw = run_acl2(expr)
    acl2_res = normalize_acl2_output(acl2_res_raw)
    lean_res_raw = run_lean(expr)
    lean_res = normalize_lean_output(lean_res_raw)
    
    print(f"  ACL2: {acl2_res} (raw: {acl2_res_raw})")
    print(f"  Lean: {lean_res} (raw: {lean_res_raw})")
    
    if acl2_res == lean_res:
        print("  SUCCESS ✅")
    else:
        print("  FAILURE ❌")

def verify_in(path, expr):
    print(f"Verifying in {path}: {expr}")
    script = f"(ld \"{path}\")\n{expr}\n(quit)\n"
    process = subprocess.Popen(
        ['acl2'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    stdout, stderr = process.communicate(input=script)
    
    lines = [l.strip() for l in stdout.splitlines() if l.strip()]
    acl2_res_raw = None
    for i in range(len(lines) - 1, -1, -1):
        if "ACL2 !>" in lines[i]:
            res = lines[i].replace("ACL2 !>", "").strip()
            if res and res != "Bye.":
                acl2_res_raw = res
                break
            if i > 0:
                res = lines[i-1].strip()
                if not res.startswith("+++") and not res.startswith("Type"):
                    acl2_res_raw = res
                    break
    
    acl2_res = normalize_acl2_output(acl2_res_raw)
    lean_res_raw = run_lean_in(path, expr)
    lean_res = normalize_lean_output(lean_res_raw)
    
    print(f"  ACL2: {acl2_res} (raw: {acl2_res_raw})")
    print(f"  Lean: {lean_res} (raw: {lean_res_raw})")
    
    if acl2_res == lean_res:
        print("  SUCCESS ✅")
    else:
        print("  FAILURE ❌")

if __name__ == "__main__":
    tests = [
        "(+ 1 2)",
        "(- 10 3)",
        "(* 4 5)",
        "(equal 1 1)",
        "(equal 1 2)",
        "(if t 1 2)",
        "(IF T 1 2)",
        "(if nil 1 2)",
        "(let ((x 5)) (+ x 10))",
        "(LET ((X 5)) (BINARY-+ X 10))",
        "(zp 0)",
        "(zp 1)",
        "(evenp 4)",
        "(evenp 5)",
        "(consp '(1 2))",
        "(consp '())",
        "(atom 1)",
        "(atom '(1))",
        "(true-listp '(1 2 3))",
        "(true-listp 1)",
        "(integerp 10)",
        "(natp -1)",
        "(posp 5)",
        "(symbolp 'abc)",
        "(stringp \"hello\")"
    ]
    for t in tests:
        verify(t)
    
    print("\n--- Contextual Tests ---")
    verify_in("acl2_samples/2009-log2.lisp", "(flog2 10)")
    verify_in("acl2_samples/2009-log2.lisp", "(FLOG2 10)")
    verify_in("acl2_samples/2009-log2.lisp", "(flog2 32)")
    verify_in("acl2_samples/2009-log2.lisp", "(clog2 10)")
    verify_in("acl2_samples/2009-log2.lisp", "(CLOG2 10)")
    verify_in("acl2_samples/2009-log2.lisp", "(clog2 32)")
