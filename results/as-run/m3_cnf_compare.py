"""m3_cnf_compare.py (2026-10-27): the m3v4g11 CNFs generated in Lean (research/lean/Garden/M3Gen.lean, exe
m3export) against the sha256 recorded for every job of the 2026-10-27 runs (m3v4g11_results.tsv).

For each distinct job with a 64-hex sha256, m3export writes the DIMACS from the row's (class, k, shift, r,
kind, cube, elim L) and its sha256 must equal the row's. Reads only the TSV and m3export's output; imports
no Python encoder.
Usage: python3 m3_cnf_compare.py <results.tsv> <m3export binary> [workers]
"""
import hashlib, os, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

COLS = ['job', 'class', 'k', 'shift', 'r', 'kind', 'cube', 'sha256']


def jobs(path):
    out = {}
    for line in open(path):
        if line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        if len(f) < len(COLS) or len(f[7]) != 64:
            continue
        r = dict(zip(COLS, f))
        kind, _, e = r['kind'].partition('+e')
        key = (r['class'], r['k'], r['shift'], r['r'], kind, r['cube'], e.replace('-', ',') if e else '-')
        out.setdefault(key, set()).add(r['sha256'])
    return out


def lean_sha(exe, key, d):
    p = os.path.join(d, '_'.join(key).replace(',', '.').replace(':', '_') + '.cnf')
    subprocess.run([exe, *key, p], check=True)
    h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    os.remove(p)
    return h


def main():
    tsv, exe = sys.argv[1], os.path.abspath(sys.argv[2])
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    J = jobs(tsv)
    conflicting = [k for k, s in J.items() if len(s) > 1]
    with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as d:
        keys = sorted(J)
        with ThreadPoolExecutor(workers) as ex:
            hs = list(ex.map(lambda k: lean_sha(exe, k, d), keys))
    mism = [k for k, h in zip(keys, hs) if h not in J[k]]
    kinds = {}
    for k in keys:
        kinds[k[4]] = kinds.get(k[4], 0) + 1
    print(f'jobs compared: {len(keys)} {dict(sorted(kinds.items()))}; rows with two different sha256: {len(conflicting)}')
    print(f'sha256 mismatches (Lean vs recorded): {len(mism)} {mism[:5]}')
    return 1 if mism else 0


if __name__ == '__main__':
    sys.exit(main())
