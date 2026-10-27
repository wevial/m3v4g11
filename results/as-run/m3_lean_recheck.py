"""m3_lean_recheck.py (2026-10-27): discharge the hypotheses of `M3Sound.m3v4g11_le11` a second way.

For every CNF the theorem's hypotheses name (per class c = 1, 2, 3: `job c r .whole` for r = 1..10 with
elim L = elimOf c; at r = 11 the whole CNF for classes 2 and 3, and for class 1 the cover and all 420
leaves, as the Mac's runs did):

  1. `m3export` (Lean, `Garden/M3Gen.lean`) writes the DIMACS; its sha256 must equal the one recorded in
     m3v4g11_results.tsv for that job (whose proof cake_lpr verified on the Mac);
  2. CaDiCaL (the Lean toolchain's 2.1.2, not the Mac's 3.0.1) solves it, writing a binary LRAT proof;
  3. `lratcheck` (Lean core's verified LRAT checker, `Garden/LratStream.lean`) must print `s VERIFIED UNSAT`
     for that DIMACS and proof. The proof is then deleted.

Runtime controls first: lratcheck must reject the class-2 r = 10 proof against the class-3 r = 10 CNF, and
the class-2 r = 10 proof with one byte flipped in its middle.

Usage (from research/, after `cd lean/direct && lake build m3export lratcheck`):
    TMPDIR=/scratch/m3 python3 circuits/m3_lean_recheck.py [workers] > circuits/m3_lean_recheck.out
"""
import hashlib, os, re, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, '../lean/direct/.lake/build/bin')
EXPORT = os.environ.get('M3EXPORT', os.path.join(BIN, 'm3export'))
CHECK = os.environ.get('LRATCHECK', os.path.join(BIN, 'lratcheck'))
CADICAL = os.environ.get('CADICAL', '/cache/elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical')
TSV = os.path.join(HERE, 'm3v4g11_results.tsv')
ELIM = {1: '9,10', 2: '10,10', 3: '10,10'}          # M3Sound.elimOf
FIRST_PAIRS = [(0, 1), (0, 2), (1, 2), (2, 3)]
TABLES = ['001', '010', '100', '110', '111']


def cubes(k):                                      # M3Gen.cubes, as m3v4g11_run.cube_str writes them
    n = k + 2
    return ['%d,%d:%s:%d,%d' % (a, b, t, c, d) for a, b in FIRST_PAIRS for t in TABLES
            for c in range(n + 1) for d in range(c + 1, n + 1)]


def jobs():
    out = []
    for c in (1, 2, 3):
        for r in range(1, 11):
            out.append((c, r, 'whole', '-'))
        if c == 1:
            out.append((c, 11, 'cover', '-'))
            out += [(c, 11, 'leaf', q) for q in cubes(4)]
        else:
            out.append((c, 11, 'whole', '-'))
    return out


def recorded():
    rec = {}
    for line in open(TSV):
        f = line.rstrip('\n').split('\t')
        if line.startswith('#') or len(f) < 24 or len(f[7]) != 64:
            continue
        kind, _, e = f[5].partition('+e')
        if f[2] == '4' and f[3] == '0' and e:
            rec.setdefault((int(f[1]), int(f[4]), kind, f[6], e.replace('-', ',')), set()).add(f[7])
    return rec


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''):
            h.update(b)
    return h.hexdigest()


def proc(cmd):
    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    p.stdout.close()
    return os.waitstatus_to_exitcode(status), out.strip(), time.time() - t0, ru.ru_utime + ru.ru_stime


def verdict(out):
    m = re.search(r'^s (VERIFIED UNSAT|NOT VERIFIED).*$', out, re.M)
    return m.group(0) if m else (out.splitlines()[-1] if out else '(no output)')


def export(job, d):
    c, r, kind, cube = job
    p = os.path.join(d, 'f.cnf')
    subprocess.run([EXPORT, str(c), '4', '0', str(r), kind, cube, ELIM[c], p], check=True)
    return p


def run(job, rec, tmp, keep_proof=False):
    d = tempfile.mkdtemp(dir=tmp)
    try:
        cnf = export(job, d)
        h = sha256(cnf)
        key = (job[0], job[1], job[2], job[3], ELIM[job[0]])
        sha_ok = h in rec.get(key, set())
        proof = os.path.join(d, 'p.lrat')
        s = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof])
        size = os.path.getsize(proof) if os.path.exists(proof) else 0
        k = proc([CHECK, cnf, proof])
        ok = sha_ok and s[0] == 20 and k[0] == 0 and verdict(k[1]).startswith('s VERIFIED UNSAT')
        if keep_proof:
            kept = os.path.join(tmp, 'ctl_%d_%d.lrat' % (job[0], job[1]))
            shutil.move(proof, kept)
            shutil.move(cnf, kept[:-5] + '.cnf')
        return dict(job=job, ok=ok, sha_ok=sha_ok, sha=h, cad=s[0], solve=s[3], mb=size / 1e6,
                    check=verdict(k[1]), check_s=k[3])
    finally:
        shutil.rmtree(d, ignore_errors=True)


def line(x):
    c, r, kind, cube = x['job']
    return (f"class {c} r={r:2d} {kind:5s} {cube:12s} sha256 {x['sha'][:16]} {'=' if x['sha_ok'] else 'MISMATCH'} recorded; "
            f"cadical exit {x['cad']} [{x['solve']:.1f}s CPU, {x['mb']:.1f} MB]; lratcheck: {x['check']} [{x['check_s']:.1f}s CPU]"
            f"{'' if x['ok'] else '   <-- NOT OK'}")


def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    tmp = tempfile.mkdtemp(dir=os.environ.get('TMPDIR'))
    t0 = time.time()
    rec = recorded()
    try:
        print('# controls (lratcheck must reject):')
        a = run((2, 10, 'whole', '-'), rec, tmp, keep_proof=True)
        b = run((3, 10, 'whole', '-'), rec, tmp, keep_proof=True)
        print('  ' + line(a)); print('  ' + line(b))
        pa, pb = os.path.join(tmp, 'ctl_2_10.lrat'), os.path.join(tmp, 'ctl_3_10.lrat')
        k1 = proc([CHECK, pb[:-5] + '.cnf', pa])
        data = bytearray(open(pa, 'rb').read())
        data[len(data) // 2] ^= 1
        pf = pa + '.flip'
        open(pf, 'wb').write(data)
        k2 = proc([CHECK, pa[:-5] + '.cnf', pf])
        c1 = not verdict(k1[1]).startswith('s VERIFIED UNSAT')
        c2 = not verdict(k2[1]).startswith('s VERIFIED UNSAT')
        print(f"  class-2 r=10 proof vs class-3 r=10 CNF: {verdict(k1[1])} -> {'rejected' if c1 else 'NOT REJECTED'}")
        print(f"  class-2 r=10 proof, middle byte bit 0 flipped: {verdict(k2[1])} -> {'rejected' if c2 else 'NOT REJECTED'}")
        for f in (pa, pb, pf, pa[:-5] + '.cnf', pb[:-5] + '.cnf'):
            os.remove(f)
        J = jobs()
        print(f'# {len(J)} jobs, {workers} workers')
        with ThreadPoolExecutor(workers) as ex:
            res = list(ex.map(lambda j: run(j, rec, tmp), J))
        for x in res:
            if x['job'][2] != 'leaf' or not x['ok']:
                print(line(x))
        leaves = [x for x in res if x['job'][2] == 'leaf']
        print(f"class 1 r=11 leaves: {sum(x['ok'] for x in leaves)}/{len(leaves)} OK (sha256 = recorded, exit 20, VERIFIED); "
              f"solve {sum(x['solve'] for x in leaves):.0f}s CPU, lratcheck {sum(x['check_s'] for x in leaves):.0f}s CPU, "
              f"max leaf solve {max(x['solve'] for x in leaves):.0f}s, proofs {sum(x['mb'] for x in leaves) / 1e3:.1f} GB")
        nok = sum(x['ok'] for x in res)
        print(f"SUMMARY: {nok}/{len(res)} jobs OK; controls {'both rejected' if c1 and c2 else 'NOT AS REQUIRED'}; "
              f"solve {sum(x['solve'] for x in res):.0f}s CPU, lratcheck {sum(x['check_s'] for x in res):.0f}s CPU; "
              f"wall {time.time() - t0:.0f}s")
        return 0 if nok == len(res) and c1 and c2 else 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == '__main__':
    sys.exit(main())
