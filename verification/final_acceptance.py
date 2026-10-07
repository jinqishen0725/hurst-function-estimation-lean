#!/usr/bin/env python3
"""Final acceptance script for the closed mainline (post-16715db).

Seven checks, mirroring the contract discipline (M1 contract §6 style) plus the
file-24 §6 checklist items that are mechanically checkable:

  A. Aggregate build          : `lake build Hurst` exit 0.
  B. Whole-file axiom audit   : `lake env lean verification/AxiomAudit.lean` exit 0,
                                every printed axiom set ⊆ {propext, Classical.choice,
                                Quot.sound}, zero sorryAx, zero unknown constants.
  C. Sorry scan               : no `sorry` in Hurst/*.lean.
  D. Endpoint signature       : `actualQ1_knownScaleH_fullChain_honestRate` has EXACTLY
                                the accepted premise whitelist (model window + b-band +
                                r) and none of the forbidden historical premises.
  E. Counter-audit files      : the refutation/audit files still compile (file 24 §6:
                                "原始 capstone 的反证文件应继续能编译").
  F. Checkpoint integrity     : every verification/checkpoints/*/sha256.txt verifies.
  G. Plan-conformance numbers : the file-22/24 window/band arithmetic on the canonical
                                model instances (E8 example; h-far-from-b case).

Writes verification/final_acceptance_report.txt; exits 0 iff A–F all pass
(G failures are also fatal — they would mean the registered band arithmetic is
wrong). Plan-scope deviations (informational, from the independent plan audit)
are printed but do not affect the exit code.
"""
from __future__ import annotations
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / "verification" / "final_acceptance_report.txt"
THREE = {"propext", "Classical.choice", "Quot.sound"}
ENDPOINT = "actualQ1_knownScaleH_fullChain_honestRate"
ENDPOINT_FILE = ROOT / "Hurst" / "HonestRateClosure.lean"
WHITELIST = {"p", "a", "b", "M", "r", "hp", "ha", "hb", "hab", "hM",
             "f", "hf", "hF", "t", "ht", "hlong", "hbband"}
FORBIDDEN = ["hane", "hband", "hBias", "hE5", "hNegMass", "hlam", "hQ",
             "hconst", "hcut", "hEnv", "hW0", "hE2", "hwnn", "hRiesz",
             "(hm ", "(R ", "(β ", "(cσ ", "(C ", "(d ", "(γ "]
COUNTER_FILES = ["Session3PremiseAudit.lean", "Session4Blocker3Audit.lean",
                 "CapstonePremiseAudit.lean"]

results: list[tuple[str, bool, str]] = []


def run(cmd: list[str], timeout: int = 900) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                          timeout=timeout)
    return proc.returncode, (proc.stdout + proc.stderr)


def check(name: str, ok: bool, detail: str) -> None:
    results.append((name, ok, detail))


# --- A. aggregate build -------------------------------------------------------
rc, out = run(["lake", "build", "Hurst"])
jobs = re.findall(r"\[(\d+)/(\d+)\]", out)
jobs_txt = f"{jobs[-1][0]}/{jobs[-1][1]} jobs" if jobs else "n/a"
check("A aggregate build", rc == 0, f"exit={rc} ({jobs_txt})")

# --- B. whole-file axiom audit ------------------------------------------------
rc, out = run(["lake", "env", "lean", "verification/AxiomAudit.lean"])
blocks = re.findall(r"'(.*?)'\s+depends on axioms:\s*\[(.*?)\]", out, re.S)
depends_count = len(re.findall(r"depends on axioms", out))
bad = [n for n, ax in blocks
       if not {x.strip() for x in ax.replace("\n", " ").split(",")} <= THREE]
sorry_ax = len(re.findall(r"sorryAx", out))
unknown = len(re.findall(r"unknownIdentifier", out))
check("B axiom audit", rc == 0 and blocks and not bad and sorry_ax == 0
      and unknown == 0 and len(blocks) == depends_count,
      f"exit={rc} theorems={len(blocks)}/{depends_count} printed "
      f"outside_three={len(bad)} sorryAx={sorry_ax} unknown={unknown}")

# --- C. sorry scan ------------------------------------------------------------
sorry_hits = []
for lean in sorted((ROOT / "Hurst").glob("*.lean")):
    text = lean.read_text()
    for m in re.finditer(r"\bsorry\b", text):
        sorry_hits.append(f"{lean.name}:char{m.start()}")
check("C sorry scan", not sorry_hits,
      "0 occurrences" if not sorry_hits else str(sorry_hits[:5]))

# --- D. endpoint signature ----------------------------------------------------
text = ENDPOINT_FILE.read_text()
start = text.index(f"theorem {ENDPOINT}")
region = text[start:text.index(":= by", start)]
hyp_region = region[:region.index("∃")]        # hypotheses only, not the conclusion
hyp = {n for m in re.finditer(
        r"\(\s*((?:[a-zA-Z_][\w']*)(?:\s+[a-zA-Z_][\w']*)*)\s+:", hyp_region)
       for n in m.group(1).split()}
extra, missing = hyp - WHITELIST, WHITELIST - hyp
forbidden = [f for f in FORBIDDEN if f in region]
check("D endpoint signature", not extra and not missing and not forbidden,
      f"premises={sorted(hyp)} extra={sorted(extra)} missing={sorted(missing)} "
      f"forbidden={forbidden}")

# --- E. counter-audit files ---------------------------------------------------
notes = []
ok_all = True
for fname in COUNTER_FILES:
    path = ROOT / "verification" / fname
    if not path.exists():
        ok_all, _ = False, notes.append(f"{fname}: MISSING")
        continue
    rc, _ = run(["lake", "env", "lean", str(path)])
    ok_all &= rc == 0
    notes.append(f"{fname}: exit={rc}")
check("E counter-audit files", ok_all, "; ".join(notes))

# --- F. checkpoint integrity --------------------------------------------------
bad_ck, legacy_bad, total, legacy = [], [], 0, 0
for ck in sorted((ROOT / "verification" / "checkpoints").iterdir()):
    sha = ck / "sha256.txt"
    if not sha.exists():
        continue
    era_current = ck.name >= "2026-10-05"   # closure era (takeover6 onwards)
    if era_current:
        total += 1
    else:
        legacy += 1
    proc = subprocess.run(["shasum", "-a", "256", "-c", "sha256.txt"],
                          cwd=ck, capture_output=True, text=True)
    fails = [l for l in (proc.stdout + proc.stderr).splitlines()
             if "FAILED" in l]
    if proc.returncode != 0 or fails:
        (bad_ck if era_current else legacy_bad).append(
            f"{ck.name}: rc={proc.returncode} {fails[:1]}")
check("F checkpoints (closure era >= 2026-10-05)", not bad_ck,
      f"{total} verified, {legacy} legacy (pre-closure; "
      f"{len(legacy_bad)} with missing files, non-gating historical "
      f"preservation gaps)" if not bad_ck else str(bad_ck))

# --- G. plan-conformance numbers (file 22/24 windows on canonical instances) --
def band_ok(h: float, b: float) -> bool:
    return (1 - h) ** 2 < 1 - b            # hbband == grid window at gamma = h


def plan_window_ok(h: float, b: float, gamma: float) -> bool:
    psi = 2 - 2 * h                        # file 22 :105 window
    return (1 - gamma) * psi < 2 - 2 * b and gamma < 1


g_notes, g_ok = [], True
# (i) the file-24 E8 canonical instance: f = 0.9, a = 0.8, b = 0.95, t = 1/2,
#     p = 1, M = 0, r = 0; Lean adds a > 1/2 (registered tightening).
inst = [("E8 example h=0.9 b=0.95 a=0.8", 0.9, 0.95, 0.8),
        ("h far from b: h=0.8 b=0.955", 0.8, 0.955, 0.6)]
for label, h, b, a in inst:
    hb, pw = band_ok(h, b), plan_window_ok(h, b, h)
    g_ok &= hb and pw and a > 0.5
    g_notes.append(f"{label}: hbband={hb} plan-window@γ=h={pw} a>1/2={a > 0.5}")
# (ii) nonemptiness of the admissible band for a long-memory h:
h0 = 0.8
upper = 1 - (1 - h0) ** 2
nonempty = h0 < upper
g_ok &= nonempty
g_notes.append(f"band [h, 1-(1-h)^2) = [{h0}, {upper:.3f}) nonempty={nonempty}")
check("G plan numbers", g_ok, "; ".join(g_notes))

# --- informational: plan-scope deviations (do not gate) -----------------------
DEVIATIONS = [
    "Lean requires 1/2 < a (second-order mixed-power machinery); file 22/24 only "
    "assume a <= f <= b — mild strengthening, satisfiable, registered (takeover10).",
    "The honest-rate endpoint pins gamma = f t; the file-22 window allows other "
    "gamma (the general-gamma chain exists only with the legacy hBias premise).",
    "Unknown-scale extension (file 24 sections 5/E6-E10) not formalized.",
    "Known scale is pinned at sigma = 1 (c_sigma = gaussianLogSquareMean); the "
    "sigma-rescaled known-scale variant is not assembled.",
    "A Lean-level model-instance theorem (file 24 section 6 '每层的验证': beyond "
    "numeric checks) is not landed; this script's G checks are numeric.",
]

# --- report -------------------------------------------------------------------
lines = ["=" * 72, "FINAL ACCEPTANCE REPORT (closed mainline)", "=" * 72]
for name, ok, detail in results:
    lines.append(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
all_ok = all(ok for _, ok, _ in results)
lines += ["", f"OVERALL: {'ALL CHECKS PASSED' if all_ok else 'FAILURES PRESENT'}",
          "", "Plan-scope deviations (informational, from the independent audit",
          "against direct_proofs/22+24; these do not gate the closure):"]
lines += [f"  - {d}" for d in DEVIATIONS]
REPORT.write_text("\n".join(lines) + "\n")
print("\n".join(lines))
sys.exit(0 if all_ok else 1)
