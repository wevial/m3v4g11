"""m3v4g11.py (2026-10-27, live session): Kulikov's open problem m3v4g11 as CNFs, one per code class.

The problem (github.com/alexanderskulikov/circuit-synthesis, openproblems/m3v4g11.py, 2018): inputs
x1..x4 and a 2-bit word coding a residue mod 3; two outputs that code (residue + x1 + .. + x4) mod 3
in the same code; is there a circuit of 11 gates over B2? The code is existential: each of the four
words means a residue or nothing, every residue has a word. m3v4g11_codes.py: 60 codes, 3 classes
under bit relabeling (on input and output alike) and residue shift. One representative each:

  class 1  00->0 01->1 10->2 11->2   KPS's own code (2 = (1,*)); the output's second bit is a
                                     don't-care when the residue is 2
  class 2  00->0 01->1 10->1 11->2   relational: residue 1 is 01 or 10, so an output row with
                                     residue 1 says y0 XOR y1 = 1, which no per-bit table states
  class 3  00->0 01->1 10->2 11->-   one unused word: input rows with word 11 are don't-cares,
                                     and the output must never be 11 (automatic: every residue
                                     has exactly one word)

The representatives are checked to lie in three different orbits (`classes_ok`, using the orbit
code of m3v4g11_codes.py).

Layout: x0, x1 = the code word (a, b) = (bit 0, bit 1 of the row index); x2 .. x_{k+1} = the k
counted bits (k = 4 for the problem; k = 1, 2, 3 for controls). Row t has word (t & 1, (t >> 1) & 1).

Generalizations against Kulikov's own CNF, each making UNSAT here imply UNSAT there:
  - outputs may be negated (encode's neg bits). His gates are normal and his outputs are not
    negated, so his circuits are ours with neg = 0. B2 has all 16 gates, so ours is the B2 question.
  - nothing else: same r, outputs are gates, every word with a residue must be accepted.
Swapping or negating output bits alone is free (reorder outputs; neg bits), so the problem with
output code g(c) for a bit relabeling g is the same question; an output *shift* s (out code
c + s) is a different function, available here as `shift` but not Kulikov's question (s = 0).

The CNF: optimal_circuit.encode on the per-bit projection of the spec (a bit is defined on a row
iff every allowed output word agrees on it), plus, on rows where the allowed words are not a
product set (class 2, residue 1), variables y[o, t] = value of output o on row t and one clause per
forbidden word. On product rows the projection is exactly the spec; on the others the projection is
implied by the spec and the word clauses state it, so the CNF says "the output word is allowed on
every row whose input word has a residue".

Options, each sound for the relational spec as argued in encode's docstring:
  sym, order: the arguments never look at the targets beyond "an output is a gate".
  allin on the projection: an input essential for the projection (two defined, different values
    on rows t, t ^ (1 << v)) is essential for every circuit meeting the spec, which implies it.
  distinct: encode asserts that no output of the projection can be a constant or an input
    literal; the spec implies the projection, so neither can an output here.
  symvars (2, .., k+1): the spec depends on the counted bits only through their sum; checked on
    the allowed-word sets themselves (`symmetric_spec`), not only on the projection.
Gate elimination (optional, `elim_bounds`): encode's `elim` as a dict, on the counted bits only.
  Set a counted bit x_v = c in an r-gate circuit for the k-bit block. Each gate reading x_v becomes a
  constant or +-(one node), and so does each gate reading a gate that is constant once x_v = c; delete
  them all (the set E that encode counts) and rewire readers to that node, folding negations into
  their tables or into an output's neg bit. An output cannot be deleted into a constant or an input
  literal, because the restricted spec's outputs are neither (checked: oc.encode's distinct assert on
  the restricted projection). What is left computes the (k-1)-bit block of the same class with output
  shift s + c on the other inputs (the code bits untouched, x_v contributing c to the sum), so
  r - |E| >= size(block_{k-1}, class, shift + c) >= L_c, i.e. |E| <= r - L_c =: B_c. The L_c must be
  certified lower bounds (an LRAT-checked UNSAT scan below L_c). The code bits x0, x1 get no bound:
  fixing one changes the code, not the count.

Usage: python3 m3v4g11.py dimacs <class> <r> <out.cnf> [k] [shift]   (writes the CNF + a .map JSON)
       python3 m3v4g11.py check <class> <r> <model-file> [k] [shift] (decode a CaDiCaL model, evaluate)
"""
import itertools, json, os, sys, types

sys.modules.setdefault('pysat', types.ModuleType('pysat'))      # encode needs none of pysat
_s = types.ModuleType('pysat.solvers'); _s.Glucose4 = None
sys.modules.setdefault('pysat.solvers', _s)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import optimal_circuit as oc

WORDS = [(0, 0), (0, 1), (1, 0), (1, 1)]
CODES = {1: {(0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 2},
         2: {(0, 0): 0, (0, 1): 1, (1, 0): 1, (1, 1): 2},
         3: {(0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): None}}


def orbit(code):
    """Orbit of a code (dict word -> residue/None) under bit swap/negations x residue shift."""
    out = set()
    for sw, na, nb, s in itertools.product((0, 1), (0, 1), (0, 1), range(3)):
        d = {}
        for w, v in code.items():
            g = (w[sw] ^ na, w[1 - sw] ^ nb)
            d[g] = None if v is None else (v + s) % 3
        out.add(tuple(d[w] for w in WORDS))
    return out


def classes_ok():
    orbs = [orbit(CODES[c]) for c in (1, 2, 3)]
    allc = {c for c in itertools.product((0, 1, 2, None), repeat=4) if {0, 1, 2} <= set(c)}
    return (all(not (a & b) for a, b in itertools.combinations(orbs, 2))
            and set().union(*orbs) == allc and len(allc) == 60)


def spec(cls, k=4, shift=0, code=None):
    """n and, per row, the set of allowed output words (None: input word unused, row is free)."""
    code = code or CODES[cls]
    n = k + 2
    W = []
    for t in range(1 << n):
        res = code[(t & 1, (t >> 1) & 1)]
        if res is None:
            W.append(None)
            continue
        want = (res + sum((t >> v) & 1 for v in range(2, n)) + shift) % 3
        W.append(frozenset(w for w in WORDS if code[w] == want))
    return n, W


def projection(W):
    tts = []
    for o in (0, 1):
        tts.append(tuple(None if A is None or len({w[o] for w in A}) > 1 else next(iter(A))[o] for A in W))
    return tts


def is_product(A):
    return A == frozenset(itertools.product({w[0] for w in A}, {w[1] for w in A}))


def symmetric_spec(n, W, vs):
    for a, b in itertools.combinations(vs, 2):
        for t in range(1 << n):
            ba, bb = (t >> a) & 1, (t >> b) & 1
            u = t & ~((1 << a) | (1 << b)) | (bb << a) | (ba << b)
            if W[t] != W[u]:
                return False
    return True


def val_ids(n, r, sel, fbit):
    """Recover encode's val[i, t] variable ids by replaying its allocation order, and check the
    replay against the sel and fbit dicts encode returned (so the layout is not assumed)."""
    rows, nv, val = 1 << n, 0, {}
    for i in range(n, n + r):
        for j, k in itertools.combinations(range(i), 2):
            nv += 1
            assert sel[i, j, k] == nv
        for p, q in ((0, 1), (1, 0), (1, 1)):
            nv += 1
            assert fbit[i, p, q] == nv
        for t in range(rows):
            nv += 1
            val[i, t] = nv
    return val


def default_opts(k):
    o = dict(order=True, allin=True, distinct=True)
    if k >= 2:
        o['symvars'] = tuple(range(2, k + 2))
    return o


def encode(cls, r, k=4, shift=0, code=None, sym=True, **opts):
    """CNF for 'a circuit of r gates computes the block' (with sym: exactly r, see oc.encode).
    Returns cnf, sel, fbit, outsel, neg, n, W."""
    n, W = spec(cls, k, shift, code)
    if sym:
        opts = {**default_opts(k), **opts}
    if opts.get('symvars'):
        assert symmetric_spec(n, W, opts['symvars']), 'symvars needs the spec itself symmetric'
    targets = projection(W)
    cnf, sel, fbit, outsel, neg = oc.encode(n, targets, r, sym, **opts)
    val = val_ids(n, r, sel, fbit)
    nv = max(abs(l) for c in cnf for l in c)
    for t, A in enumerate(W):
        if A is None or is_product(A):
            continue
        y = {}
        for o in (0, 1):
            nv += 1
            y[o] = nv
            for i in range(n, n + r):
                g, v, ng = outsel[o, i], val[i, t], neg[o]
                cnf += [[-g, -y[o], v, ng], [-g, -y[o], -v, -ng], [-g, y[o], -v, ng], [-g, y[o], v, -ng]]
        for w in WORDS:
            if w not in A:
                cnf.append([-y[0] if w[0] else y[0], -y[1] if w[1] else y[1]])
    return cnf, sel, fbit, outsel, neg, n, W


def elim_bounds(r, k, L):
    """encode's elim dict: counted bits x2..x_{k+1}, B_c = max(r - L_c, 0) (0 is weaker, still sound,
    and with allin refutes r < L_c at once)."""
    return {v: tuple(max(r - l, 0) for l in L) for v in range(2, k + 2)}


def restricted_ok(cls, k, shift):
    """The (k-1)-bit restrictions' outputs are never constant or literals (needed by the elim argument):
    oc.encode's distinct option asserts exactly that on the restricted projection."""
    for c in (0, 1):
        n, W = spec(cls, k - 1, shift + c)
        oc.encode(n, projection(W), 1, True, distinct=True)
    return True


def evaluate_block(circ, outs, n, t):
    """Independent of oc.evaluate: circ = [(j, k, {(p, q): bit})], outs = [(node, neg)]."""
    v = [(t >> x) & 1 for x in range(n)]
    for j, k, tt in circ:
        v.append(tt[v[j], v[k]])
    return tuple(v[g] ^ ng for g, ng in outs)


def check_block(circ, outs, cls, k=4, shift=0, code=None):
    """Brute force on all 2^(k+2) inputs, straight from the code table (not from spec/W)."""
    code = code or CODES[cls]
    n = k + 2
    for t in range(1 << n):
        res = code[(t & 1, (t >> 1) & 1)]
        if res is None:
            continue
        y = evaluate_block(circ, outs, n, t)
        if code.get(y) != (res + sum((t >> v) & 1 for v in range(2, n)) + shift) % 3:
            return False
    return True


def write_dimacs(cnf, path):
    nv = max(abs(l) for c in cnf for l in c)
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(cnf)}\n')
        for c in cnf:
            f.write(' '.join(map(str, c)) + ' 0\n')


def read_model(path):
    lits = []
    for line in open(path):
        if line.startswith('v '):
            lits += [int(x) for x in line.split()[1:] if x != '0']
    return lits


if __name__ == '__main__':
    cmd, cls, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rest = sys.argv[5:]
    k = int(rest[0]) if rest else 4
    shift = int(rest[1]) if len(rest) > 1 else 0
    if cmd == 'dimacs':
        cnf, *_ = encode(cls, r, k, shift)
        write_dimacs(cnf, sys.argv[4])
        print(f'class {cls} k={k} shift={shift} r={r}: {len(cnf)} clauses')
    elif cmd == 'check':
        cnf, sel, fbit, outsel, neg, n, W = encode(cls, r, k, shift)
        circ, outs = oc.decode(read_model(sys.argv[4]), n, r, sel, fbit, outsel, neg, 2)
        print(json.dumps({'circuit': [[j, kk, [tt[0, 1], tt[1, 0], tt[1, 1]]] for j, kk, tt in circ],
                          'outputs': outs, 'check_block': check_block(circ, outs, cls, k, shift)}))
