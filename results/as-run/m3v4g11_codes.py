"""m3v4g11_codes.py (2026-10-26): how many residue codes does Kulikov's open problem m3v4g11 range over?

github.com/alexanderskulikov/circuit-synthesis, openproblems/m3v4g11.py (2018): inputs x1..x4 and a
2-bit code (r1, r2) for a residue mod 3; two outputs must code (res + x1 + .. + x4) mod 3 in the same
code; 11 gates. The code is existential: each of the 4 codewords means a residue or nothing (17), and
every residue has a codeword. Two codes give the same question when one is the other after
  - relabeling the codewords by a bit swap and/or negations, applied to input and output alike
    (input and output negation are free in B2), or
  - shifting every residue by s (a circuit for code c computes the block for code c + s too).
A residue with two codewords at Hamming distance 2 (00/11 or 01/10) is not a per-bit don't-care,
so optimal_circuit.encode cannot state it as is ("relational").
Usage: python3 m3v4g11_codes.py   (no solver; < 1 s)
"""
import itertools as it

W = [(a, b) for a in (0, 1) for b in (0, 1)]
codes = [c for c in it.product((0, 1, 2, None), repeat=4) if {0, 1, 2} <= set(c)]
G = [(lambda w, sw=sw, na=na, nb=nb: (w[sw] ^ na, w[1 - sw] ^ nb))
     for sw in (0, 1) for na in (0, 1) for nb in (0, 1)]


def img(c, g, s):
    d = [None] * 4
    for i, w in enumerate(W):
        d[W.index(g(w))] = None if c[i] is None else (c[i] + s) % 3
    return tuple(d)


def relational(c):
    return any(c[i] == c[j] is not None and W[i][0] != W[j][0] and W[i][1] != W[j][1]
               for i in range(4) for j in range(i + 1, 4))


seen, orbits = set(), []
for c in codes:
    if c not in seen:
        orb = {img(c, g, s) for g in G for s in range(3)}
        seen |= orb
        orbits.append((c, len(orb)))
assert sum(k for _, k in orbits) == len(codes)
print(f'{len(codes)} codes; {len(orbits)} classes; {sum(relational(c) for c, _ in orbits)} relational')
for c, k in orbits:
    print('  ' + ' '.join(f'{a}{b}->{"-" if v is None else v}' for (a, b), v in zip(W, c)),
          f'orbit {k}', 'relational' if relational(c) else '')
