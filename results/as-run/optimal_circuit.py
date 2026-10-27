"""Exact circuit size over the full binary basis B2, by SAT, with certificates both ways.

Usage:  PYTHONPATH=/cache/pydeps python3 optimal_circuit.py [controls | <name>]

For a target f: {0,1}^n -> {0,1}^m and a gate budget r, build a CNF that is satisfiable
iff some circuit of r binary gates (any of the 16 two-input functions) computes f.
The encoding is the standard one (Kojevnikov, Kulikov & Yaroslavtsev 2009; Knuth TAOCP 7.1.2):
per gate, a one-hot choice of an ordered input pair j < k, a 4-bit truth table, and its value
on every row of the truth table. Gates are *normal* (output 0 on input 00); an output may be
negated, which loses no generality because a non-normal gate is a normal one negated and the
negation can be pushed into its successors' truth tables.

Certificates, so no answer rests on trusting the solver:
  SAT   -> the model is decoded into a circuit and evaluated on all 2^n inputs here.
  UNSAT -> Glucose's DRUP proof is checked by `drup_check` below, an independent
           reverse-unit-propagation checker (forward, with deletions), ~60 lines.
The size is exact when size r is certified SAT and size r-1 is certified UNSAT.
"""
import itertools, os, shutil, sys, time
from pysat.solvers import Glucose4
from drup_fast import drup_check_fast


def essential_inputs(n, targets):
    """Inputs x_v that every completion of the don't-cares depends on: some output has two
    defined, different values on rows t and t ^ (1 << v)."""
    return [v for v in range(n)
            if any(tt[t] is not None and tt[t ^ (1 << v)] is not None and tt[t] != tt[t ^ (1 << v)]
                   for tt in targets for t in range(1 << n))]


def fully_symmetric(n, targets):
    """True iff the targets (don't-cares included) are invariant under every permutation of
    the inputs; checking the transposition (0 1) and the n-cycle suffices (they generate S_n)."""
    def permuted(tt, perm):          # input i of the new table is input perm[i] of the old
        out = [None] * (1 << n)
        for t in range(1 << n):
            u = sum(((t >> i) & 1) << perm[i] for i in range(n))
            out[t] = tt[u]
        return tuple(out)
    if n < 2:
        return True
    gens = [[1, 0] + list(range(2, n)), list(range(1, n)) + [0]]
    return all(permuted(tt, g) == tt for tt in targets for g in gens)


def symmetric_in(n, targets, vs):
    """True iff the targets are invariant under every permutation of the inputs vs (2026-10-04;
    checked on all transpositions of vs, which generate Sym(vs))."""
    def swapped(tt, a, b):
        out = [None] * (1 << n)
        for t in range(1 << n):
            ba, bb = (t >> a) & 1, (t >> b) & 1
            u = t & ~((1 << a) | (1 << b)) | (bb << a) | (ba << b)
            out[t] = tt[u]
        return tuple(out)
    return all(swapped(tt, a, b) == tt for tt in targets for a, b in itertools.combinations(vs, 2))


def encode(n, targets, r, sym=True, order=False, allin=False, first01=False, distinct=False,
           maxfan=None, elim=None, elim2=None, sem=None, semxor=None, symin=False, semeq=None, semrows=None,
           symvars=None):
    """targets: list of m tuples of length 2^n (row t = input bits of t, bit 0 = x0);
    an entry None is a don't-care.
    sym=True adds two constraints that every *minimum* circuit satisfies, so the exact size
    found by exact_size (which tries r = 1, 2, ... and stops at the first SAT) is unchanged:
      (i) no degenerate gate: a gate's function is not 0, not x_j, not x_k (normal gates;
          a degenerate gate could be deleted and its successors rewired to x_j or x_k, or,
          for 0, their functions restricted; either way a smaller circuit);
      (ii) no dead gate: every gate is an output or an input of a later gate (else delete it).
    A circuit of size < r padded with junk gates violates (i)/(ii), so with sym=True an
    UNSAT at r only says "no circuit of size exactly r"; that is why exact_size must scan
    every r from 1 upward.

    Three further options, each also satisfied by some minimum circuit (so, again, sound only
    under the upward scan):
      order:   if gate i+1 does not read gate i, then pair(i) <= pair(i+1) lexicographically.
               Proof: list the gates greedily, each time taking, among gates whose inputs are
               already listed, one with the lex-smallest input pair. If gate t+1 does not read
               gate t, it was already available at step t, so pair(t) <= pair(t+1).
      allin:   every input in essential_inputs(...) is read by some gate (else f would not
               depend on it).
      first01: the first gate reads (x0, x1). Sound only if fully_symmetric(...): rename the
               inputs so that some gate reading two inputs reads x0 and x1; under `order`, the
               greedy listing then starts with it, since (0, 1) is the smallest pair. Without
               `order`, list that gate first (it reads only inputs, so it can go first).
      distinct: no gate computes a constant, x_v or NOT x_v, and no two gates compute the same
               function or complementary ones. Else delete the later/redundant gate and let its
               readers read the earlier gate (or x_v), folding a negation into their truth
               tables or into the output's `neg` bit. Only sound when that deletion is possible
               for outputs too, i.e. no output can be constant or an input literal: enforced
               by the assert (an output of that kind is never needed here).

    maxfan (2026-09-30), unlike the options above, holds in *every* r-gate circuit, not just
    in some minimum one, so it composes with all of them: each input is read by at most
    maxfan gates. The caller must justify the bound; fanout_bound() does it by gate
    elimination from certified sizes of the restrictions.

    elim (2026-09-30) = (B0, B1), also true of every r-gate circuit, and stronger: for each
    input x_v and c in {0, 1}, the gates removed by setting x_v = c number at most B_c. The
    removed set counted is E = (gates reading x_v) + (gates reading a gate that reads x_v and
    is constant when x_v = c). Each gate of E becomes a constant or a function of one node
    and is deleted as in fanout_bound; the second kind is a gate by the same argument (a
    constant gate cannot be the output, since restrictions are not constant). The caller
    passes B_c = r - size(f restricted to x_v = c).

    elim2 (2026-09-30) = (B0, B1, B2), the same for two inputs at once: for inputs x_u, x_v and
    constants a, b, the removed set counted is (gates reading x_u or x_v) + (gates reading a
    gate that is constant once x_u = a, x_v = b: one that reads x_u in a slot made constant
    by a, or x_v by b, or reads both x_u and x_v). B_s bounds the count when a + b = s; the
    caller passes r - size(f restricted to x_u = a, x_v = b), which for a symmetric f
    depends on a + b only. Requires elim (it reuses its K variables).

    symin (2026-10-02), for fully symmetric targets, with order and first01: for u < v the
    first gate reading x_v is not earlier than the first gate reading x_u. Holds in some
    minimum circuit jointly with order, first01 and cubes.py's table clause, by one canonical
    choice instead of the greedy listing: give gate i the key (pair(i), rank(table(i))), rank
    putting (1,0,0) last, and among all relabelings of the inputs (f is symmetric) and all
    topological listings of a minimum circuit take one whose key sequence is lex-least.
      order:   if gate i+1 does not read gate i and pair(i) > pair(i+1), swapping the two is
               another listing; keys before i are unchanged and key i drops. Contradiction.
      first01: the first gate reads two inputs; relabel them x0, x1; (0, 1) is least.
      table:   if gate n (pair (0, 1)) has table (1,0,0), swap x0 and x1: its pair stays,
               its table becomes (0,1,0), so key n drops. Contradiction.
      symin:   if a > b and x_a is first read at gate g, strictly before x_b, swap x_a and
               x_b. Gates before g read neither, so their keys are unchanged; gate g reads x_a
               and not x_b, and replacing one entry of a sorted pair by a smaller one makes
               the pair lex-smaller. Contradiction.
    sym, distinct and allin hold in every minimum circuit, and maxfan/elim/elim2/sem/semxor
    in every r-gate circuit, and relabeling/relisting keeps a minimum circuit minimum, so all
    of them compose. Encoded for consecutive inputs u, u+1 (the chain gives the rest):
    a gate reading x_{u+1} implies some gate at or before it reads x_u.

    symvars (2026-10-04), for targets symmetric in the inputs of the tuple symvars only (w2_5^q in
    x1..x4), with order and without first01: symin on consecutive members of symvars, plus the
    table clause for a first gate reading two of them. Same canonical form, with relabelings
    restricted to Sym(symvars): order by the same exchange; symin by swapping x_a and x_b, both in
    symvars (f is invariant, and the pair argument above does not use b < a beyond b, a in the
    sorted pair); table: if gate n reads (a, b), both in symvars, with table (1,0,0), swapping
    x_a and x_b keeps its pair and makes its table (0,1,0), so key n drops. first01 is NOT
    implied (x0 may be outside symvars) and must not be combined with this."""
    rows = 1 << n
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    gates = range(n, n + r)
    sel = {}                                   # sel[i,j,k]
    fbit = {}                                  # fbit[i,p,q], with fbit[i,0,0] = 0 fixed
    val = {}                                   # val[i,t] for gates
    for i in gates:
        for j, k in itertools.combinations(range(i), 2):
            sel[i, j, k] = new()
        for p, q in ((0, 1), (1, 0), (1, 1)):
            fbit[i, p, q] = new()
        for t in range(rows):
            val[i, t] = new()
    outsel = {(o, i): new() for o in range(len(targets)) for i in gates}
    neg = {o: new() for o in range(len(targets))}
    cnf = []
    def exactly_one(lits):
        cnf.append(list(lits))
        cnf.extend([[-a, -b] for a, b in itertools.combinations(lits, 2)])
    def lit_val(node, t, b):
        """Literal meaning 'node has value b on row t'; True/False for inputs."""
        if node < n:
            return ((t >> node) & 1) == b
        v = val[node, t]
        return v if b else -v
    for i in gates:
        exactly_one([sel[i, j, k] for j, k in itertools.combinations(range(i), 2)])
        for j, k in itertools.combinations(range(i), 2):
            s = sel[i, j, k]
            for t in range(rows):
                for p in (0, 1):
                    for q in (0, 1):
                        a, b = lit_val(j, t, p), lit_val(k, t, q)
                        if a is False or b is False:
                            continue        # premise false: clause satisfied
                        prem = [-s] + [-x for x in (a, b) if x is not True]
                        if (p, q) == (0, 0):
                            cnf.append(prem + [-val[i, t]])
                        else:
                            f = fbit[i, p, q]
                            cnf.append(prem + [-val[i, t], f])
                            cnf.append(prem + [val[i, t], -f])
    if sym:
        for i in gates:
            f01, f10, f11 = fbit[i, 0, 1], fbit[i, 1, 0], fbit[i, 1, 1]
            cnf.append([f01, f10, f11])            # not constant 0
            cnf.append([f01, -f10, -f11])          # not x_j  (f = p: 0,1,1)
            cnf.append([-f01, f10, -f11])          # not x_k  (f = q: 1,0,1)
            users = [outsel[o, i] for o in range(len(targets))]
            users += [v for (ii, j, k), v in sel.items() if ii > i and (j == i or k == i)]
            cnf.append(users)
    if order:
        for i in list(gates)[:-1]:
            ps = [(j, k) for j, k in itertools.combinations(range(i), 2)]
            qs = [(j, k) for j, k in itertools.combinations(range(i + 1), 2) if i not in (j, k)]
            for a in ps:
                for b in qs:
                    if b < a:
                        cnf.append([-sel[i, a[0], a[1]], -sel[i + 1, b[0], b[1]]])
    if allin:
        for v in essential_inputs(n, targets):
            cnf.append([x for (i, j, k), x in sel.items() if v in (j, k)])
    if distinct:
        for tt in targets:
            defined = [t for t in range(rows) if tt[t] is not None]
            trivial = [lambda t: 0] + [lambda t, v=v: (t >> v) & 1 for v in range(n)]
            assert not any(len({tt[t] ^ g(t) for t in defined}) <= 1 for g in trivial), \
                'distinct needs outputs that are not constant or input literals'
        for i in gates:
            # not constant, not x_v, not NOT x_v: for each such g, i differs from g somewhere
            # and agrees with g somewhere
            for g in [lambda t: 0] + [lambda t, v=v: (t >> v) & 1 for v in range(n)]:
                cnf.append([val[i, t] if not g(t) else -val[i, t] for t in range(rows)])
                cnf.append([-val[i, t] if not g(t) else val[i, t] for t in range(rows)])
        for i, i2 in itertools.combinations(gates, 2):
            d = {t: new() for t in range(rows)}        # d_t <-> val_i,t xor val_i2,t
            for t in range(rows):
                a, b = val[i, t], val[i2, t]
                cnf += [[-d[t], a, b], [-d[t], -a, -b], [d[t], -a, b], [d[t], a, -b]]
            cnf.append([d[t] for t in range(rows)])     # not equal
            cnf.append([-d[t] for t in range(rows)])    # not complementary
    if maxfan is not None:
        for v in range(n):
            u = {i: new() for i in gates}          # u[i] <- gate i reads x_v
            for (i, j, k), x in sel.items():
                if v in (j, k):
                    cnf.append([-x, u[i]])
            for c in itertools.combinations(gates, maxfan + 1):
                cnf.append([-u[i] for i in c])
    Kall = {}
    if elim is not None:
        # 2026-10-27: elim may also be a dict {v: (B0, B1)}, bounding only the inputs listed, each with
        # its own bounds (m3v4g11: the counted bits, not the code bits). A tuple means every input.
        elim_v = elim if isinstance(elim, dict) else {v: elim for v in range(n)}
        assert elim2 is None or not isinstance(elim, dict), 'elim2 needs K for every input'
        for v in range(n):
            if v not in elim_v:
                continue
            # K[g, c]: gate g reads x_v and is constant once x_v = c (only the -> direction
            # K <- (reads x_v in that slot and the table says so) is needed: K is only used
            # to force e up, and e is bounded above)
            K = {(g, c): new() for g in gates for c in (0, 1)}
            for (g, j, k), x in sel.items():
                f01, f10, f11 = fbit[g, 0, 1], fbit[g, 1, 0], fbit[g, 1, 1]
                if j == v:      # x_v is the first argument p: f(c, q) constant in q
                    cnf.append([-x, f01, K[g, 0]])                  # f(0,0)=0=f(0,1)
                    cnf.append([-x, -f10, -f11, K[g, 1]])           # f(1,0)=f(1,1)=1
                    cnf.append([-x, f10, f11, K[g, 1]])             # f(1,0)=f(1,1)=0
                if k == v:      # x_v is the second argument q: f(p, c) constant in p
                    cnf.append([-x, f10, K[g, 0]])
                    cnf.append([-x, -f01, -f11, K[g, 1]])
                    cnf.append([-x, f01, f11, K[g, 1]])
            Kall[v] = K
            for c in (0, 1):
                e = {h: new() for h in gates}
                for (h, j, k), x in sel.items():
                    if v in (j, k):
                        cnf.append([-x, e[h]])
                    for g in (j, k):
                        if g >= n:
                            cnf.append([-x, -K[g, c], e[h]])
                for cc in itertools.combinations(gates, elim_v[v][c] + 1):
                    cnf.append([-e[h] for h in cc])
    if elim2 is not None:
        assert elim is not None, 'elim2 reuses the K variables of elim'
        for u, v in itertools.combinations(range(n), 2):
            both = {g: sel[g, u, v] for g in gates if (g, u, v) in sel}   # g reads x_u and x_v
            for a in (0, 1):
                for b in (0, 1):
                    e = {h: new() for h in gates}
                    for (h, j, k), x in sel.items():
                        if u in (j, k) or v in (j, k):
                            cnf.append([-x, e[h]])
                        for g in (j, k):
                            if g >= n:
                                cnf.append([-x, -Kall[u][g, a], e[h]])
                                cnf.append([-x, -Kall[v][g, b], e[h]])
                                cnf.append([-x, -both[g], e[h]])
                    for cc in itertools.combinations(gates, elim2[a + b] + 1):
                        cnf.append([-e[h] for h in cc])
    if sem is not None or semxor is not None or semeq is not None or semrows is not None:
        # 2026-10-01: semantic gate elimination, true of every r-gate circuit. Fix the inputs
        # in S to a. Call gate g *redundant* if on the rows T = {t : t|S = a} it computes a
        # constant, x_u or NOT x_u, or the function of an earlier gate h or its complement.
        # Delete every redundant gate; rewire each reader to the earliest gate (or literal,
        # or constant) computing the same function on T, folding negations into tables or
        # into the output's neg bit. A kept gate reads two earlier non-constant nodes of
        # distinct classes (else it would be redundant), so this is a circuit, and it
        # computes f|S with the non-redundant gates. Hence #redundant <= r - size(f|S).
        # Every gate counted by elim/elim2 is redundant here, so this subsumes them.
        # sem = {k: (B_0, ..., B_k)}: the bound for |S| = k and sum(a) = s (symmetric f).
        assert sem is None or fully_symmetric(n, targets), 'sem bounds are indexed by sum(a): symmetric f only'
        diff, same = {}, {}                        # diff -> values differ; same -> values agree
        def dlit(h, g, t, want_diff):
            store = diff if want_diff else same
            if (h, g, t) not in store:
                x = store[h, g, t] = new()
                a, b = val[h, t], val[g, t]
                cnf.extend([[-x, a, b], [-x, -a, -b]] if want_diff else [[-x, a, -b], [-x, -a, b]])
            return store[h, g, t]
        def redundancy(T, B):
            """At most B gates are redundant on the rows T (constant, +-x_u, +-an earlier gate)."""
            if B >= r:
                return
            d = {g: new() for g in gates}
            for g in gates:
                cnf.append([val[g, t] for t in T] + [d[g]])        # constant 0
                cnf.append([-val[g, t] for t in T] + [d[g]])       # constant 1
                for u in range(n):                                 # constant on T for u fixed: harmless
                    cnf.append([-val[g, t] if (t >> u) & 1 else val[g, t] for t in T] + [d[g]])
                    cnf.append([val[g, t] if (t >> u) & 1 else -val[g, t] for t in T] + [d[g]])
                for h in gates:
                    if h >= g:
                        break
                    cnf.append([dlit(h, g, t, True) for t in T] + [d[g]])
                    cnf.append([dlit(h, g, t, False) for t in T] + [d[g]])
            for cc in itertools.combinations(gates, max(B, 0) + 1):
                cnf.append([-d[g] for g in cc])
        for k, bounds in (sem or {}).items():
            for S in itertools.combinations(range(n), k):
                for a in itertools.product((0, 1), repeat=k):
                    redundancy([t for t in range(rows) if all((t >> v) & 1 == b for v, b in zip(S, a))],
                               bounds[sum(a)])
        if semxor is not None:
            # x_u := NOT x_v, i.e. the rows where they differ. For mod3, x_u + x_v = 1 there, so the
            # circuit, with x_u replaced by NOT x_v (folded into readers' tables), computes
            # mod3_{n-2}^{q-1} on the other inputs and ignores x_v; the reduced circuit, with x_v
            # then fixed to 0 (never adds a gate), computes it with the kept gates. The caller
            # passes semxor = r - size(mod3_{n-2}^{q-1}).
            for u, v in itertools.combinations(range(n), 2):
                redundancy([t for t in range(rows) if (t >> u) & 1 != (t >> v) & 1], semxor)
        for T, B in (semrows or ()):
            # 2026-10-03: the same bound for any target, one restriction at a time: T = the rows of
            # S = a, B = r - (certified lower bound on size(f|S)), computed by the caller (sem_general).
            redundancy(T, B)
        if semeq is not None:
            # 2026-10-03: x_u := x_v, i.e. the rows where they agree. Replace x_u by x_v in every
            # reader; a gate reading (x_u, x_v) becomes a function of x_v alone (constant or +-x_v),
            # so it is redundant and counted. The reduced circuit computes f with x_u = x_v, which for
            # mod3_n^q is w2_{n-1}^q = [2 x_v + sum(rest) = q mod 3] on n - 1 inputs (the same
            # function for every pair, f symmetric). The caller passes semeq = r - L, L a certified
            # LOWER bound on size(w2_{n-1}^q); a lower bound is all soundness needs.
            for u, v in itertools.combinations(range(n), 2):
                redundancy([t for t in range(rows) if (t >> u) & 1 == (t >> v) & 1], semeq)
    if first01:
        assert fully_symmetric(n, targets), 'first01 needs a fully symmetric target'
        cnf.append([sel[n, 0, 1]])
    if symin:
        assert order and first01, 'symin is argued jointly with order and first01'
        for u in range(n - 1):
            for (i, j, k), x in sel.items():
                if u + 1 in (j, k):
                    cnf.append([-x] + [y for (ii, jj, kk), y in sel.items() if ii <= i and u in (jj, kk)])
    if symvars is not None:
        assert order and not first01 and not symin, 'symvars is argued with order, alone'
        assert symmetric_in(n, targets, symvars), 'symvars needs f symmetric in those inputs'
        for u, w in zip(symvars, symvars[1:]):
            for (i, j, k), x in sel.items():
                if w in (j, k):
                    cnf.append([-x] + [y for (ii, jj, kk), y in sel.items() if ii <= i and u in (jj, kk)])
        for a, b in itertools.combinations(symvars, 2):
            cnf.append([-sel[n, a, b], -fbit[n, 0, 1], fbit[n, 1, 0], fbit[n, 1, 1]])
    for o, tt in enumerate(targets):
        exactly_one([outsel[o, i] for i in gates])
        for i in gates:
            for t in range(rows):
                if tt[t] is None:
                    continue
                # outsel -> (val xor neg == tt[t])
                v, g, ng = val[i, t], outsel[o, i], neg[o]
                if tt[t]:
                    cnf += [[-g, v, ng], [-g, -v, -ng]]
                else:
                    cnf += [[-g, v, -ng], [-g, -v, ng]]
    return cnf, sel, fbit, outsel, neg


def decode(model, n, r, sel, fbit, outsel, neg, m):
    pos = {abs(l) for l in model if l > 0}
    circ = []
    for i in range(n, n + r):
        (j, k), = [(j, k) for (ii, j, k), v in sel.items() if ii == i and v in pos]
        tt = {(0, 0): 0}
        tt.update({(p, q): int(fbit[i, p, q] in pos) for p, q in ((0, 1), (1, 0), (1, 1))})
        circ.append((j, k, tt))
    outs = []
    for o in range(m):
        (g,), = [(i,) for (oo, i), v in outsel.items() if oo == o and v in pos]
        outs.append((g, int(neg[o] in pos)))
    return circ, outs


def evaluate(circ, outs, n, t):
    vals = [(t >> x) & 1 for x in range(n)]
    for j, k, tt in circ:
        vals.append(tt[vals[j], vals[k]])
    return tuple(vals[g] ^ ng for g, ng in outs)


def matches(circ, outs, n, targets):
    return all(tt[t] is None or evaluate(circ, outs, n, t)[o] == tt[t]
               for t in range(1 << n) for o, tt in enumerate(targets))


def drup_check(cnf, proof, honour_deletions=False):
    """Forward DRUP check: every added lemma must follow by unit propagation from the
    original clauses plus earlier lemmas; the proof must derive the empty clause.
    Deletions are ignored by default. That is sound (every kept clause is implied by the
    formula, so a superset can't make an invalid lemma pass) and it avoids the known
    false rejections when a solver deletes a clause that is the reason for a top-level
    literal it keeps (drat-trim ignores unit deletions for the same reason)."""
    clauses = [list(c) for c in cnf]
    live = [True] * len(clauses)
    index = {}
    for ci, c in enumerate(clauses):
        index.setdefault(tuple(sorted(c)), []).append(ci)
    def propagate(assumed):
        assign = {}
        for l in assumed:
            if assign.get(-l):
                return True
            assign[l] = True
        changed = True
        while changed:
            changed = False
            for ci, c in enumerate(clauses):
                if not live[ci]:
                    continue
                unassigned, sat = None, False
                count = 0
                for l in c:
                    if assign.get(l):
                        sat = True
                        break
                    if not assign.get(-l):
                        count += 1
                        unassigned = l
                if sat:
                    continue
                if count == 0:
                    return True                 # conflict
                if count == 1:
                    assign[unassigned] = True
                    changed = True
        return False
    for line in proof:
        toks = line.split()
        if not toks:
            continue
        if toks[0] == 'd':
            if not honour_deletions:
                continue
            key = tuple(sorted(int(x) for x in toks[1:-1]))
            if index.get(key):
                live[index[key].pop()] = False
            continue
        lemma = [int(x) for x in toks[:-1]]
        if not propagate([-l for l in lemma]):
            return False
        if not lemma:
            return True
        clauses.append(lemma)
        live.append(True)
        index.setdefault(tuple(sorted(lemma)), []).append(len(clauses) - 1)
    return propagate([])                        # empty clause implied at the end


BACKEND = os.environ.get('BACKEND', 'glucose')   # 'cadical': CaDiCaL + LRAT (lrat.py);
                                                # 'lean': CaDiCaL + Lean's verified checker (lrat.cadical_lean)


def solve(n, targets, r, check_unsat=True, sym=True, **opts):
    cnf, sel, fbit, outsel, neg = encode(n, targets, r, sym, **opts)
    if BACKEND == 'lean':
        import lrat
        st, x, detail, _ = lrat.cadical_lean(cnf)
        if st == 'SAT':
            circ, outs = decode(x, n, r, sel, fbit, outsel, neg, len(targets))
            return 'SAT', matches(circ, outs, n, targets), (circ, outs), len(cnf)
        return 'UNSAT', x, detail.split('(')[-1].split(' actions')[0] + ' actions', len(cnf)
    if BACKEND == 'cadical':
        import lrat
        st, out = lrat.cadical(cnf)
        if st == 'SAT':
            circ, outs = decode(out, n, r, sel, fbit, outsel, neg, len(targets))
            return 'SAT', matches(circ, outs, n, targets), (circ, outs), len(cnf)
        ok, nlines = lrat.lrat_check_file(cnf, out) if check_unsat else (None, -1)
        shutil.rmtree(os.path.dirname(out), ignore_errors=True)
        return 'UNSAT', ok, nlines, len(cnf)
    with Glucose4(bootstrap_with=cnf, with_proof=True) as s:
        sat = s.solve()
        if sat:
            circ, outs = decode(s.get_model(), n, r, sel, fbit, outsel, neg, len(targets))
            ok = matches(circ, outs, n, targets)
            return 'SAT', ok, (circ, outs), len(cnf)
        proof = s.get_proof()
    ok = drup_check_fast(cnf, proof) if check_unsat else None
    return 'UNSAT', ok, len(proof), len(cnf)


def tt_of(n, fn):
    return tuple(fn([(t >> x) & 1 for x in range(n)]) for t in range(1 << n))


FUNCS = {
    'xor3':      (3, [lambda x: x[0] ^ x[1] ^ x[2]]),
    'maj3':      (3, [lambda x: int(sum(x) >= 2)]),
    'fulladder': (3, [lambda x: sum(x) & 1, lambda x: sum(x) >> 1]),
    'xor4':      (4, [lambda x: x[0] ^ x[1] ^ x[2] ^ x[3]]),
    # trivial control: one gate
    'and2':      (2, [lambda x: x[0] & x[1]]),
}

# MOD3^r_n = [x1 + ... + xn = r mod 3]; Knuth (TAOCP Vol. 4 Fascicle 6 / 4B, ans. to 7.2.2.2-480; this said 7.1.2 until 2026-10-24) found the exact
# sizes for 3 <= n <= 5, quoted in Kulikov-Pechenev-Slezkin, MFCS 2022 (arXiv 2102.12579), p. 3.
KNOWN = {'and2': 1, 'xor3': 2, 'maj3': 4, 'fulladder': 5, 'xor4': 3}
for _n, _row in ((3, (3, 4, 4)), (4, (7, 7, 6)), (5, (10, 9, 10))):
    for _r in range(3):
        FUNCS[f'mod3_{_n}_{_r}'] = (_n, [lambda x, r=_r: int(sum(x) % 3 == r)])
        KNOWN[f'mod3_{_n}_{_r}'] = _row[_r]
for _r in (1, 2):
    FUNCS[f'mod3_6_{_r}'] = (6, [lambda x, r=_r: int(sum(x) % 3 == r)])
FUNCS['mod3_6_0'] = (6, [lambda x: int(sum(x) % 3 == 0)])
# 2026-10-03: what mod3_6^q becomes under x_u := x_v (y = the merged input, weight 2), for semeq.
for _m in (2, 3, 4, 5):
    for _r in range(3):
        FUNCS[f'w2_{_m}_{_r}'] = (_m, [lambda x, r=_r: int((2 * x[0] + sum(x[1:])) % 3 == r)])
KNOWN['mod3_6_0'] = 12                    # Knuth, by SAT (KPS p. 3); r = 1, 2: open, conjectured 13


# KPS's MOD3 building blocks (their Sect. 3.2 and Appendix). A remainder mod 3 travels as two
# bits (z0, z1): 0 = (0,0), 1 = (0,1), 2 = (1, anything). Outputs use don't-cares for the free bit;
# inputs z range over all four pairs. KPS state these sizes are optimal ("we have also verified
# that no smaller circuits exist"); no certificate is published.
def _enc(z0, z1):
    return 2 if z0 else z1
def _rem_out(v):
    return [lambda x, v=v: 1 if v(x) == 2 else 0, lambda x, v=v: None if v(x) == 2 else v(x)]
for _k, _s in ((2, 2), (3, 5), (4, 7)):
    FUNCS[f'in{_k}'] = (_k, _rem_out(lambda x: sum(x) % 3))
    KNOWN[f'in{_k}'] = _s
FUNCS['mid3'] = (5, _rem_out(lambda x: (_enc(x[0], x[1]) + sum(x[2:])) % 3))
KNOWN['mid3'] = 9
for _r, _l, _s in ((0, 2, 5), (1, 1, 2), (2, 3, 8)):
    FUNCS[f'out{_r}_{_l}'] = (_l + 2, [lambda x, r=_r: int((_enc(x[0], x[1]) + sum(x[2:])) % 3 == r)])
    KNOWN[f'out{_r}_{_l}'] = _s


def exact_size(name, rmax=14, sym=True, rmin=1, **opts):
    """Scan r = rmin, rmin+1, ... to the first SAT. The size is certified exact only if every
    smaller r was scanned and certified UNSAT (with sym, UNSAT at r means 'not exactly r')."""
    n, fns = FUNCS[name]
    targets = [tt_of(n, f) for f in fns]
    all_unsat_ok = rmin == 1
    for r in range(rmin, rmax + 1):
        t0 = time.time()
        res = solve(n, targets, r, sym=sym, **opts)
        extra = f' proof_lines={res[2]}' if res[0] == 'UNSAT' else ''
        print(f'  {name} r={r}: {res[0]} certified={res[1]} clauses={res[-1]}{extra} [{time.time() - t0:.1f}s]', flush=True)
        if res[0] == 'SAT':
            return r, bool(res[1]) and all_unsat_ok
        all_unsat_ok = all_unsat_ok and bool(res[1])
    return None, False


def negative_controls():
    """The checkers must reject corrupted certificates."""
    n, fns = FUNCS['maj3']
    targets = [tt_of(n, f) for f in fns]
    cnf, *_ = encode(n, targets, 3)
    with Glucose4(bootstrap_with=cnf, with_proof=True) as s:
        assert not s.solve()
        proof = s.get_proof()
    adds = [i for i, l in enumerate(proof) if not l.startswith('d') and l.split()[:-1]]
    cnf4, *_ = encode(n, targets, 4)
    for nm, chk in (('drup_check', drup_check), ('drup_check_fast', drup_check_fast)):
        print(f'  [{nm}] maj3 r=3 proof: {len(proof)} lines; genuine proof accepted: {chk(cnf, proof)}')
        # corruption 1: truncate the proof to its first half (no refutation reached)
        print(f'  [{nm}] truncated proof rejected: {not chk(cnf, proof[:len(proof) // 2])}')
        # corruption 2: a proof that asserts the empty clause immediately
        print(f'  [{nm}] bare "0" proof rejected: {not chk(cnf, ["0"])}')
        # corruption 3: satisfiable formula (r=4), with a fabricated refutation
        print(f'  [{nm}] fabricated refutation of a SAT instance rejected: {not chk(cnf4, proof)}')
    # corruption 4: a correct circuit with one gate bit flipped must fail evaluation
    res = solve(n, targets, 4)
    circ, outs = res[2]
    j, k, tt = circ[-1]
    bad = circ[:-1] + [(j, k, {**tt, (1, 1): 1 - tt[1, 1]})]
    ok = matches(bad, outs, n, targets)
    print(f'  circuit with one flipped gate bit rejected: {not ok}')


# Exact sizes certified here (both directions, see README), used only by fanout_bound.
CERTIFIED = {'mod3_1_0': 0, 'mod3_1_1': 0, 'mod3_1_2': 0,        # NOT x, x, 0: no gates
             'mod3_2_0': 1, 'mod3_2_1': 1, 'mod3_2_2': 1,        # NOR, XOR, AND
             'mod3_3_0': 3, 'mod3_3_1': 4, 'mod3_3_2': 4,        # results_small.out
             'mod3_4_0': 7, 'mod3_4_1': 7, 'mod3_4_2': 6,        # results_small.out
             'mod3_5_0': 10, 'mod3_5_1': 9, 'mod3_5_2': 10}      # results_5in.out, *_r9_cubes.out


def fanout_bound(name, r):
    """An upper bound on every input's fanout in ANY r-gate circuit for mod3_n_q, or None.
    Gate elimination: set x_v = c in an r-gate circuit where x_v has fanout k. The k gates
    reading x_v (distinct: a gate reads two different nodes) each become a constant, a node
    w, or NOT w; delete each, rewiring its readers to w and folding a negation into their
    tables (or into the output's neg bit). The output cannot become a constant or a literal,
    since the restriction mod3_{n-1}_{q'} is neither. So at most r - k gates compute the
    restriction, and k <= r - size(restriction) for both c = 0 (q' = q) and c = 1
    (q' = q - 1 mod 3)."""
    if not name.startswith('mod3_'):
        return None
    _, n, q = name.split('_')
    n, q = int(n), int(q)
    rs = [CERTIFIED.get(f'mod3_{n - 1}_{q}'), CERTIFIED.get(f'mod3_{n - 1}_{(q - 1) % 3}')]
    if None in rs:
        return None
    return r - max(rs)


def elim_bounds(name, r):
    """(B0, B1) for encode's elim: r - size of the restriction at x_v = 0 and at x_v = 1."""
    if not name.startswith('mod3_'):
        return None
    _, n, q = name.split('_')
    n, q = int(n), int(q)
    rs = [CERTIFIED.get(f'mod3_{n - 1}_{q}'), CERTIFIED.get(f'mod3_{n - 1}_{(q - 1) % 3}')]
    if None in rs:
        return None
    return (r - rs[0], r - rs[1])


def elim2_bounds(name, r):
    """(B0, B1, B2) for encode's elim2: r - size of the restriction with a + b = 0, 1, 2."""
    if not name.startswith('mod3_'):
        return None
    _, n, q = name.split('_')
    n, q = int(n), int(q)
    rs = [CERTIFIED.get(f'mod3_{n - 2}_{(q - s) % 3}') for s in (0, 1, 2)]
    if None in rs:
        return None
    return tuple(r - x for x in rs)


def sem_bounds(name, r, ks=(1, 2, 3)):
    """{k: (B_0..B_k)} for encode's sem: B_s = r - size(mod3 on n - k inputs, residue q - s)."""
    _, n, q = name.split('_')
    n, q = int(n), int(q)
    out = {}
    for k in ks:
        rs = [CERTIFIED.get(f'mod3_{n - k}_{(q - s) % 3}') for s in range(k + 1)]
        if None not in rs:
            out[k] = tuple(r - x for x in rs)
    return out


def semxor_bound(name, r):
    """semxor for encode: r - size(mod3_{n-2}^{q-1}), the function left by x_u := NOT x_v."""
    _, n, q = name.split('_')
    return r - CERTIFIED[f'mod3_{int(n) - 2}_{(int(q) - 1) % 3}']


# Certified LOWER bounds on size(w2_5^q) (every smaller r UNSAT, Lean-checked), for semeq_bound.
W2_LOWER = {'w2_5_1': 10}                 # r <= 7: results_w2_5_1_scan.out; r = 8: results_w2_5_1_semrows.out; r = 9: results_w2_5_1_r9_cubes.out (w2cubes.py, symvars + sem_pairs, 2026-10-04)


def semeq_bound(name, r):
    """semeq for encode: r - (certified lower bound on size(w2_{n-1}^q)), the function left by x_u := x_v."""
    _, n, q = name.split('_')
    return r - W2_LOWER[f'w2_{int(n) - 1}_{q}']


def sem_general(name, r, ks=(1, 2)):
    """semrows for encode, any single-output target: for every S (|S| in ks) and a, the rows of S = a
    and r - size(f|S), the restricted function's exact size computed here by an upward scan
    (certified each step, cached). 2026-10-03, for w2_5^q, which is not fully symmetric."""
    n, fns = FUNCS[name]
    tt = tt_of(n, fns[0])
    out = []
    for k in ks:
        for S in itertools.combinations(range(n), k):
            rest = [v for v in range(n) if v not in S]
            for a in itertools.product((0, 1), repeat=k):
                T = [t for t in range(1 << n) if all((t >> v) & 1 == b for v, b in zip(S, a))]
                sub = tuple(tt[next(t for t in T if all(((t >> v) & 1) == ((s >> i) & 1) for i, v in enumerate(rest)))]
                            for s in range(1 << len(rest)))
                out.append((T, r - _restricted_size(len(rest), sub)))
    return out


def sem_pairs(name, r, kinds=('eq', 'neq')):
    """semrows for encode from substitutions x_v := x_u ('eq') or x_v := NOT x_u ('neq'), u < v, any
    single-output target (2026-10-04). On the rows T where the substitution holds, the circuit with
    x_v replaced by the literal of x_u (folded into readers' tables) is a circuit on the n - 1 other
    inputs computing h = f under the substitution; a gate that is +-x_v on T is +-x_u, a literal,
    so the redundancy/deletion argument of semxor/semeq applies verbatim and #redundant <= r - size(h).
    h is computed here and its exact size certified by _restricted_size."""
    n, fns = FUNCS[name]
    tt = tt_of(n, fns[0])
    out = []
    for u, v in itertools.combinations(range(n), 2):
        for kind in kinds:
            c = 0 if kind == 'eq' else 1
            T = [t for t in range(1 << n) if ((t >> u) & 1) ^ ((t >> v) & 1) == c]
            rest = [w for w in range(n) if w != v]
            def full(s):            # the row of T whose inputs other than x_v are given by s
                t = sum(((s >> i) & 1) << w for i, w in enumerate(rest))
                return t | ((((t >> u) & 1) ^ c) << v)
            h = tuple(tt[full(s)] for s in range(1 << (n - 1)))
            assert sorted(full(s) for s in range(1 << (n - 1))) == T
            out.append((T, r - _restricted_size(n - 1, h)))
    return out


_RSIZE = {}
def _restricted_size(m, tt):
    """Exact size of the m-input function tt (constants and literals: 0), certified both ways."""
    if (m, tt) not in _RSIZE:
        cols = [tuple((t >> v) & 1 for t in range(1 << m)) for v in range(m)]
        if len(set(tt)) == 1 or tt in cols or tuple(1 - x for x in tt) in cols:
            _RSIZE[m, tt] = 0
        else:
            for r in range(1, 20):
                res = solve(m, [tt], r, sym=True, order=True, allin=False, distinct=DISTINCT)
                assert res[1], f'restricted size: step r={r} not certified'
                if res[0] == 'SAT':
                    _RSIZE[m, tt] = r
                    break
    return _RSIZE[m, tt]


def best_opts(name):
    """The strongest sound option set for this target."""
    n, fns = FUNCS[name]
    return dict(order=True, allin=True, first01=fully_symmetric(n, [tt_of(n, f) for f in fns]),
                distinct=DISTINCT)


DISTINCT = True


if __name__ == '__main__':
    arg = sys.argv[1] if len(sys.argv) > 1 else 'controls'
    if arg == 'scan':      # scan <name> <r1> <r2>: each r in range, no stopping (pieces of a split scan)
        nm, r1, r2 = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        n, fns = FUNCS[nm]
        targets = [tt_of(n, f) for f in fns]
        for r in range(r1, r2 + 1):
            t0 = time.time()
            opts = best_opts(nm)
            if os.environ.get('ELIM'):
                # a negative bound means no r-gate circuit at all (allin: some gate reads x_v);
                # clamping to 0 is weaker, still sound, and lets the solver certify that
                opts['elim'] = tuple(max(b, 0) for b in elim_bounds(nm, r))
            if os.environ.get('ELIM2'):
                opts['elim2'] = tuple(max(b, 0) for b in elim2_bounds(nm, r))
            if os.environ.get('SEM'):
                opts['sem'] = sem_bounds(nm, r, tuple(int(k) for k in os.environ['SEM'].split(',')))
            if os.environ.get('SEMXOR'):
                opts['semxor'] = semxor_bound(nm, r)
            if os.environ.get('SYMIN'):
                opts['symin'] = True
            if os.environ.get('FANOUT'):
                opts['maxfan'] = fanout_bound(nm, r)
                if opts['maxfan'] < 1:           # allin needs fanout >= 1: trivially UNSAT
                    print(f'  {nm} r={r}: fanout bound {opts["maxfan"]} < 1, skipped', flush=True)
                    continue
            res = solve(n, targets, r, **opts)
            extra = f' proof={res[2]}' if res[0] == 'UNSAT' else f' circuit={res[2]}'
            print(f'  {nm} r={r}: {res[0]} certified={res[1]} clauses={res[-1]}{extra} [{time.time() - t0:.1f}s]',
                  flush=True)
        sys.exit(0)
    if arg == 'controls':
        negative_controls()
        names = ['and2', 'xor3', 'maj3', 'fulladder', 'xor4']
        # symmetry breaking must not change any exact size: compare with no constraints at all
        for nm in names + ['mod3_3_0', 'mod3_3_1', 'mod3_3_2', 'in2', 'in3', 'out1_1', 'out0_2']:
            a = exact_size(nm, sym=False)[0]
            b = exact_size(nm, sym=True, **best_opts(nm))[0]
            print(f'  plain vs {best_opts(nm)} on {nm}: {a} vs {b} -> {"same" if a == b else "DIFFERENT"}',
                  flush=True)
    else:
        names = sys.argv[1:]
    for nm in names:
        t0 = time.time()
        size, cert = exact_size(nm, **best_opts(nm))
        k = KNOWN.get(nm)
        print(f'{nm}: exact size {size} (both directions certified: {cert}); published {k}'
              f' -> {"MATCH" if size == k else ("no published value" if k is None else "MISMATCH")}'
              f'  opts={best_opts(nm)} [{time.time() - t0:.1f}s]', flush=True)
