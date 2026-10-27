"""m3_lean_recheck_k3.py (2026-10-27): discharge the 3-bit hypotheses of `M3Reduce.m3v4g11` a second way.

`M3Reduce.m3v4g11` adds, to `M3Sound.m3v4g11_le11`'s 453 CNFs, the 3-bit runs that the k = 4 elim bounds
rest on (`h3s0`, `h3s1`): per class c, `job3 c s r` (k = 3, shift s, symmetry options only, whole) for
s = 0 at r = 1 .. elimOf(c).1 - 1 and s = 1 at r = 1 .. elimOf(c).2 - 1. 53 CNFs. Each is handled as
m3_lean_recheck.py handles the k = 4 ones (whose functions this reuses):

  1. `m3export` (Lean) writes the DIMACS; its sha256 must equal the one recorded in m3v4g11_results.tsv for
     that job (whose proof cake_lpr verified on the Mac);
  2. CaDiCaL 2.1.2 (the Lean toolchain's, not the Mac's 3.0.1) solves it, writing a binary LRAT proof;
  3. `lratcheck` (Lean core's verified checker) must print `s VERIFIED UNSAT`. The proof is then deleted.

Runtime control first: lratcheck must reject the class-1 shift-1 r = 8 proof against the class-1 shift-0
r = 8 CNF, and that proof with one byte flipped.

Usage (from research/, after `cd lean/direct && lake build m3export lratcheck`):
    TMPDIR=/scratch/m3 python3 circuits/m3_lean_recheck_k3.py [workers] > circuits/m3_lean_recheck_k3.out
"""
import os, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m3_lean_recheck import CADICAL, CHECK, EXPORT, TSV, proc, sha256, verdict

ELIM = {1: (9, 10), 2: (10, 10), 3: (10, 10)}       # M3Sound.elimOf


def jobs():
    return [(c, s, r) for c in (1, 2, 3) for s in (0, 1) for r in range(1, ELIM[c][s])]


def recorded():
    rec = {}
    for line in open(TSV):
        f = line.rstrip('\n').split('\t')
        if line.startswith('#') or len(f) < 24 or len(f[7]) != 64:
            continue
        if f[2] == '3' and f[5] == 'whole' and f[-1] == 'UNSAT-OK':
            rec.setdefault((int(f[1]), int(f[3]), int(f[4])), set()).add(f[7])
    return rec


def run(job, rec, tmp, keep=None):
    c, s, r = job
    d = tempfile.mkdtemp(dir=tmp)
    try:
        cnf = os.path.join(d, 'f.cnf')
        subprocess.run([EXPORT, str(c), '3', str(s), str(r), 'whole', '-', '-', cnf], check=True)
        h = sha256(cnf)
        sha_ok = h in rec.get(job, set())
        proof = os.path.join(d, 'p.lrat')
        so = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof])
        size = os.path.getsize(proof) if os.path.exists(proof) else 0
        k = proc([CHECK, cnf, proof])
        ok = sha_ok and so[0] == 20 and k[0] == 0 and verdict(k[1]).startswith('s VERIFIED UNSAT')
        if keep:
            shutil.move(proof, keep + '.lrat')
            shutil.move(cnf, keep + '.cnf')
        return dict(job=job, ok=ok, sha_ok=sha_ok, sha=h, cad=so[0], solve=so[3], mb=size / 1e6,
                    check=verdict(k[1]), check_s=k[3])
    finally:
        shutil.rmtree(d, ignore_errors=True)


def line(x):
    c, s, r = x['job']
    return (f"class {c} k=3 shift={s} r={r} whole sha256 {x['sha'][:16]} {'=' if x['sha_ok'] else 'MISMATCH'} recorded; "
            f"cadical exit {x['cad']} [{x['solve']:.1f}s CPU, {x['mb']:.1f} MB]; lratcheck: {x['check']} "
            f"[{x['check_s']:.1f}s CPU]{'' if x['ok'] else '   <-- NOT OK'}")


def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    tmp = tempfile.mkdtemp(dir=os.environ.get('TMPDIR'))
    t0 = time.time()
    rec = recorded()
    try:
        print('# control (lratcheck must reject):', flush=True)
        a, b = os.path.join(tmp, 'a'), os.path.join(tmp, 'b')
        print('  ' + line(run((1, 1, 8), rec, tmp, keep=a)))
        print('  ' + line(run((1, 0, 8), rec, tmp, keep=b)))
        k1 = proc([CHECK, b + '.cnf', a + '.lrat'])
        data = bytearray(open(a + '.lrat', 'rb').read())
        data[len(data) // 2] ^= 1
        open(a + '.flip', 'wb').write(data)
        k2 = proc([CHECK, a + '.cnf', a + '.flip'])
        c1 = not verdict(k1[1]).startswith('s VERIFIED UNSAT')
        c2 = not verdict(k2[1]).startswith('s VERIFIED UNSAT')
        print(f"  class-1 shift-1 r=8 proof vs class-1 shift-0 r=8 CNF: {verdict(k1[1])} -> {'rejected' if c1 else 'NOT REJECTED'}")
        print(f"  class-1 shift-1 r=8 proof, middle byte bit 0 flipped: {verdict(k2[1])} -> {'rejected' if c2 else 'NOT REJECTED'}")
        for f in (a + '.lrat', a + '.cnf', a + '.flip', b + '.lrat', b + '.cnf'):
            os.remove(f)
        J = sorted(jobs(), key=lambda j: -j[2])          # the r = 9 jobs first: they dominate the wall time
        print(f'# {len(J)} jobs, {workers} workers', flush=True)
        with ThreadPoolExecutor(workers) as ex:
            res = list(ex.map(lambda j: run(j, rec, tmp), J))
        for x in sorted(res, key=lambda x: x['job']):
            print(line(x))
        nok = sum(x['ok'] for x in res)
        print(f"SUMMARY: {nok}/{len(res)} jobs OK; controls {'both rejected' if c1 and c2 else 'NOT AS REQUIRED'}; "
              f"solve {sum(x['solve'] for x in res):.0f}s CPU, lratcheck {sum(x['check_s'] for x in res):.0f}s CPU, "
              f"max proof {max(x['mb'] for x in res):.0f} MB; wall {time.time() - t0:.0f}s")
        return 0 if nok == len(res) and c1 and c2 else 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == '__main__':
    sys.exit(main())
