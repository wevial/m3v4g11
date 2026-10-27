"""m3codes_controls.py (2026-10-27): write lean/controls/2026-10-27-m3codes-must-fail.lean.

Each control is a theorem of lean/Garden/M3Codes.lean, its proof copied verbatim from the source by
this script, on a statement changed by one string replacement. Every control must fail to build.
Usage (from research/): python3 circuits/m3codes_controls.py
"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, '../lean/Garden/M3Codes.lean')).read()
OUT = os.path.join(HERE, '../lean/controls/2026-10-27-m3codes-must-fail.lean')


def thm(name):
    i = SRC.index('theorem ' + name + ' ')
    prev = SRC[SRC.rfind('\n', 0, i - 1) + 1:i]
    j = re.search(r'\n(?=/-|theorem |lemma |def |set_option |end |inductive |abbrev )', SRC[i + 1:]).start() + i + 1
    return (prev if prev.startswith('set_option') else '') + SRC[i:j].rstrip() + '\n'


def mut(name, new, old, rep):
    t = thm(name)
    assert t.count(old) == 1, (name, old)
    return t.replace('theorem ' + name + ' ', 'theorem ' + new + ' ', 1).replace(old, rep)


CONTROLS = [
    ('C1', 'the moves without the residue shifts (relabelings only). Fails at `decide`: under relabeling alone the 60 codes do not fall into 3 classes',
     mut('classify', 'C1_no_shift', '(moves.any fun os', '(relabels.any fun os')),
    ('C2', 'the cover condition dropped from the orbit check. Fails at `decide`: the all-`none` table reaches no representative',
     mut('classify', 'C2_no_cover', 'covers [a, b, d, e] = true →\n    ', '')),
    ('C3', 'negating bit 0 without flipping output 0 (`n0` for `!n0`). Fails at the final `decide`',
     mut('computes_neg0', 'C3_neg0_output_not_flipped', '(!n0 ^^ decide (o0 < 1))', '(n0 ^^ decide (o0 < 1))')),
    ('C4', 'negating bit 0 without the correction for an output that is the input node `x0`. Fails at the final `decide`; the claim is false (witness file, `neg0_no_fix_false`)',
     mut('computes_neg0', 'C4_neg0_no_node0_fix', '(!n0 ^^ decide (o0 < 1)) (n1 ^^ decide (o1 < 1))', '(!n0) n1')),
    ('C5', 'exchanging the code bits without exchanging the two outputs. Fails at the output bounds and the final `exact`',
     mut('computes_swap', 'C5_swap_outputs_kept', '(tr 0 1 o1) (tr 0 1 o0) n1 n0', '(tr 0 1 o0) (tr 0 1 o1) n0 n1')),
    ('C6', 'the final theorem at ≤ 12 gates. Fails at the last `omega`',
     mut('m3v4g11_all', 'C6_twelve_gates', 'gs.length ≤ 11 →', 'gs.length ≤ 12 →')),
    ('C7', 'the final theorem with the cover condition dropped from `ValidCode`. Fails where `exists_moves` needs a `ValidCode`; the claim is false (witness file, `no_cover_false`)',
     mut('m3v4g11_all', 'C7_no_cover', '∀ c : Code, ValidCode c →', '∀ c : Code, (∀ w : Bool × Bool, ∀ r, c w = some r → r < 3) →')),
]

if __name__ == '__main__':
    head = ('import Garden.M3Codes\n/-! Must-fail controls for `Garden/M3Codes.lean`. Every `C…` below must FAIL to build. Each is a\n'
            'theorem of `M3Codes` with its proof copied verbatim from the source (by\n'
            '`research/circuits/m3codes_controls.py`, which writes this file) onto a mutated statement.\n'
            'Not part of the library; run with `lake env lean controls/2026-10-27-m3codes-must-fail.lean`.\n'
            'The witnesses are in `controls/2026-10-27-m3codes-witness.lean`, which builds.\n\n'
            + ''.join('* %s, %s.\n' % (k, d) for k, d, _ in CONTROLS) + '-/\n'
            'open CircuitDual GateElim SymCanon M3Codes\n\nnamespace Ctl\n\n')
    body = ''.join('-- %s\n%s\n' % (k, t) for k, _, t in CONTROLS)
    open(OUT, 'w').write(head + body + 'end Ctl\n')
    print('wrote %s: %d controls' % (OUT, len(CONTROLS)))
