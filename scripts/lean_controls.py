"""lean_controls.py: run the Lean controls in lean/controls/ and check each one fails as it should.

    python3 scripts/lean_controls.py        (from the repository root, after the Lean build)

* The three `*-must-fail.lean` files hold 17 controls: `M1`–`M5` (the CNF's soundness, `M3Sound`),
  `R1`–`R5` (the reduction to the CNF's shape, `M3Reduce`) and `C1`–`C7` (the 60 codes, `M3Codes`).
  Each is a theorem whose statement has been mutated, keeping the original proof verbatim; each
  comment says what changed. Every control must FAIL, and the error that Lean reports inside its
  declaration must be the one its mutation causes: `EXPECTED` below gives, for each control, a
  pattern for that diagnostic. Further errors inside a control are reported but allowed. An error
  outside every control (an import, a helper `def`) fails the check, since a broken file would make
  every control fail for the wrong reason.
* The three `*-witness.lean` files must build with no error. They show that the hypotheses and
  conclusions are about predicates real circuits meet, and that several mutated claims are false,
  not merely unprovable by the reused proof.

This is MOD3_6's script (github.com/wevial/mod3-6-circuit-size) with the file list and patterns changed.
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, 'lean')
MUST_FAIL = ['controls/2026-10-27-m3-must-fail.lean', 'controls/2026-10-27-m3reduce-must-fail.lean',
             'controls/2026-10-27-m3codes-must-fail.lean']
WITNESS = ['controls/2026-10-27-m3-witness.lean', 'controls/2026-10-27-m3reduce-witness.lean',
           'controls/2026-10-27-m3codes-witness.lean']

# The diagnostic each mutation causes (the "fails at" column of the controls' tables in the research
# logs of 2026-10-27 10:20, 17:00 and 19:08), as a regex over the full error message.
EXPECTED = {
    'M1': r'argument\s+hp\s+has type\s+Option\.map \(fun x => !x\)',      # complemented projection
    'M2': r'argument\s+hA\s+has type\s+M3Gen\.allowed cls k \(shift \+ 1\)',  # word clauses for shift + 1
    'M3': r'omega could not prove the goal',                                  # elim one tighter
    'M4': r'Function expected at\s+hc\s+but this term has type\s+True',      # no cube condition
    'M5': r'argument\s+hno\s+has type\s+∀ g ∈ gs, ¬Reads g \(v \+ 1\)',      # the next input read
    'R1': r'argument\s+hu\s+has type\s+1 ≤ u ∧ u < k \+ 2',                  # code bit x1 symmetric
    'R2': r'`decide` proved that the proposition[\s\S]*excl 4 4 0',          # no code table
    'R3': r'omega could not prove the goal',                                  # elim + 1
    'R4': r'unsolved goals[\s\S]*\+ \(shift \+ c\.toNat\)\) % 3\) ↔[\s\S]*\+ shift\) % 3\)',  # fixed bit, no shift
    'R5': r'`rcases` failed[\s\S]*is not an inductive datatype',              # no output exemption
    'C1': r'`decide` proved that the proposition[\s\S]*relabels\.any[\s\S]*is false',   # no shifts
    'C2': r'`decide` proved that the proposition[\s\S]*moves\.any[\s\S]*is false',      # no cover
    'C3': r'`decide` proved that the proposition\s+∀ \(p q d0 d1 : Bool\)',  # output 0 not flipped
    'C4': r'`decide` proved that the proposition\s+∀ \(p q d0 d1 : Bool\)',  # no node-0 correction
    'C5': r'argument\s+h1\s+has type\s+o1 < k \+ 2 \+ gs\.length',           # outputs not exchanged
    'C6': r'omega could not prove the goal',                                  # 12 gates
    'C7': r'argument\s+hc\s+has type\s+∀ \(w : Bool × Bool\) \(r : ℕ\), c w = some r → r < 3',  # no cover
}
# For the controls whose pattern alone is generic, the source line the error is reported at must
# contain this text (the step the mutation breaks).
AT = {'M3': 'h.elim L hL', 'R3': 'omega', 'C6': '(by omega)'}
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|example|structure|inductive|section|end|namespace)\b\s*(\S*)')
CONTROL = re.compile(r'^([MRC]\d+)_\w*$')
MSG = re.compile(r'^\S+\.lean:(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: ', re.M)  # Lean may tag a message: error(lean.unknownIdentifier):


def run(path):
    """Exit code and the (line, full message) of every error Lean reports for one file."""
    p = subprocess.run(['lake', 'env', 'lean', path], cwd=LEAN, capture_output=True, text=True)
    out = p.stdout + p.stderr
    starts = list(MSG.finditer(out))
    errors = []
    for k, m in enumerate(starts):
        end = starts[k + 1].start() if k + 1 < len(starts) else len(out)
        if m.group(3) == 'error':
            errors.append((int(m.group(1)), out[m.end():end].strip()))
    return p.returncode, errors, out


def main():
    ok = True
    present = sorted('controls/' + f for f in os.listdir(os.path.join(LEAN, 'controls')))
    if present != sorted(MUST_FAIL + WITNESS):
        print('lean/controls/ holds %s, expected %s' % (present, sorted(MUST_FAIL + WITNESS)))
        ok = False
    for rel in WITNESS:
        code, errors, out = run(rel)
        good = code == 0 and not errors
        print('%s: %s (exit %d, %d errors)' % (rel, 'builds, as required' if good else 'DOES NOT BUILD', code,
                                               len(errors)))
        if not good:
            print(out[-3000:])
        ok &= good
    seen = set()
    for rel in MUST_FAIL:
        lines = open(os.path.join(LEAN, rel)).read().splitlines()
        code, errors, out = run(rel)
        decls = [(n, m.group(1), m.group(2)) for n, line in enumerate(lines, 1) for m in [DECL.match(line)] if m]
        controls = [(n, CONTROL.match(name).group(1), name) for n, kind, name in decls
                    if kind == 'theorem' and CONTROL.match(name)]
        # A control's span runs from its `theorem` line to the line before the next line that starts
        # in column 0 (its statement and proof lines are indented). An error anywhere else, a stray
        # command between controls included, fails the check.
        def span_end(n0):
            for m in range(n0 + 1, len(lines) + 1):
                if lines[m - 1][:1] not in ('', ' '):
                    return m - 1
            return len(lines)
        spans = [(n, span_end(n), tag) for n, tag, _ in controls]
        by_control, stray = {}, []
        for n, msg in errors:
            owner = [tag for a, b, tag in spans if a <= n <= b]
            if owner:
                by_control.setdefault(owner[0], []).append((n, msg))
            else:
                stray.append((n, msg.splitlines()[0]))
        dup = sorted({t for _, t, _ in controls if [c[1] for c in controls].count(t) > 1} | (seen & {t for _, t, _ in controls}))
        if dup:
            print('  controls named twice: %s' % ', '.join(dup))
            ok = False
        print('%s: exit %d, %d controls' % (rel, code, len(controls)))
        if code == 0:
            ok = False
        for _, tag, name in controls:
            seen.add(tag)
            errs = by_control.get(tag, [])
            pat = EXPECTED.get(tag)
            hit = [n for n, msg in errs if pat and re.search(pat, msg)
                   and (tag not in AT or AT[tag] in lines[n - 1])]
            other = [(n, msg.splitlines()[0]) for n, msg in errs if n not in hit]
            if hit:
                status = 'fails as intended (line %d)' % hit[0]
                if other:
                    status += '; also: ' + '; '.join('line %d: %s' % e for e in other)
            else:
                status = 'DOES NOT FAIL AS INTENDED: ' + ('; '.join('line %d: %s' % e for e in other)
                                                          or 'no error')
                ok = False
            print('  %-34s %s' % (name, status[:200]))
        for n, first in stray:
            print('  ERROR OUTSIDE ANY CONTROL, line %d: %s' % (n, first))
            ok = False
    missing = sorted(set(EXPECTED) - seen)
    if missing:
        print('controls not found: %s' % ', '.join(missing))
        ok = False
    print('LEAN CONTROLS %s' % ('PASSED: all %d must-fail controls fail with their intended error, all three '
                                'witness files build' % len(EXPECTED) if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
