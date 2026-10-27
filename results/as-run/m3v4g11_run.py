"""m3v4g11_run.py (2026-10-27): the Mac driver for m3v4g11 (Kulikov's 11-gate mod-3 block, 3 code classes).

Usage (on the Mac, in ~/work, as `garden`):
    python3 -B run/m3v4g11_run.py plan scan <classes> <r1> <r2> [k] [shift]  >> jobs.tsv   whole CNFs
    python3 -B run/m3v4g11_run.py plan cubes <class> <r> [k] [shift]         >> jobs.tsv   leaves + cover
    nohup caffeinate -i nice python3 -B run/m3v4g11_run.py run jobs.tsv <workers> &
    python3 -B run/m3v4g11_run.py status

A job is one CNF: m3v4g11.encode(class, r, k, shift) with the default options (symmetry only), plus
  - kind `whole`: nothing;
  - kind `leaf`: the cube's literals as unit clauses;
  - kind `cover`: one clause NOT(cube) per cube of the set. Its UNSAT, with every leaf's UNSAT, gives
    the whole CNF's UNSAT: a model of the whole CNF satisfies some cube (else it satisfies the cover),
    so it would be a model of that leaf. Coverage is thus checked by the same checker as the leaves.
Cubes (class, r): gate n's input pair, its three table bits, and gate n+1's input pair, enumerated over
the first-gate pairs (0,1), (0,2), (1,2), (2,3) and the 5 non-degenerate tables; whether anything was
left out is exactly what the cover job checks.

For each job: write the DIMACS, sha256 it, CaDiCaL (`--lrat=true --binary=true`, model to a file).
  exit 20: cake_lpr checks the proof against that DIMACS file; accepted only if its stdout is exactly
           `s VERIFIED UNSAT\n`. The proof's size and sha256 are recorded, then it is deleted.
  exit 10: the model is decoded and the circuit evaluated on every input by m3v4g11.check_block, which
           reads the code table directly; recorded as JSON. A SAT leaf or whole CNF at the job's r stops
           every other job of that class and r (the headline case).
Verdicts: UNSAT-OK, SAT-OK, TIMEOUT (only for jobs given a time limit), FAIL. A FAIL writes ~/work/FAILED
and stops new starts. ~/work/PAUSE stops new starts. Free disk under DISK_FLOOR, or proofs in flight
over WORK_CAP, kills the running solvers and stops (the jobs are re-run on resume); proofs in flight
over HOLD_CAP only hold new starts.
Resume: a job is skipped only if a line for it ends in UNSAT-OK with exit 20, cake's exact verdict and
a 64-hex DIMACS sha256, or in SAT-OK with check_block true (fixes the 10-25 driver's "any OK" resume).
"""
import hashlib, json, os, shutil, signal, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import m3v4g11 as M

W = os.environ.get('M3_HOME') or os.path.expanduser('~/work')
CADICAL = os.path.join(W, 'src/cadical/build/cadical')
CAKE = os.path.join(W, 'src/cake_lpr/cake_lpr')
RESULTS = os.path.join(W, 'results.tsv')
TMP = os.path.join(W, 'tmp.noindex')
PAUSE = os.environ.get('M3_PAUSE') or os.path.join(W, 'PAUSE')      # per-driver pause file (10-27 03:30)
FAILED = os.path.join(W, 'FAILED')
CAKE_ENV = dict(os.environ, CML_HEAP_SIZE='2048', CML_STACK_SIZE='4096')
DISK_FLOOR = 60 * 10**9          # 2026-10-27: stop the workers if free space drops below 60 GB
HOLD_CAP = 20 * 10**9            # proofs in flight above this: no new starts until they shrink
WORK_CAP = 28 * 10**9            # above this: kill the solvers and stop (~/work stays under 30 GB)
MAX_WORKERS = 12
COLUMNS = ['job', 'class', 'k', 'shift', 'r', 'kind', 'cube', 'sha256', 'vars', 'clauses', 'cadical',
           'solve_s', 'solve_cpu', 'solve_MiB', 'proof_MB', 'proof_sha256', 'cake', 'cake_s', 'cake_cpu',
           'cake_MiB', 'circuit', 'start', 'end', 'verdict']
FIRST_PAIRS = [(0, 1), (0, 2), (1, 2), (2, 3)]
TABLES = [(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)]     # (f01, f10, f11), non-degenerate


def utc(t=None):
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(time.time() if t is None else t))


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''):
            h.update(b)
    return h.hexdigest()


def cubes(k):
    n = k + 2
    return [(p1, t1, p2) for p1 in FIRST_PAIRS for t1 in TABLES
            for p2 in [(a, b) for a in range(n + 1) for b in range(a + 1, n + 1)]]


def cube_str(c):
    (a, b), t, (c2, d2) = c
    return '%d,%d:%d%d%d:%d,%d' % (a, b, t[0], t[1], t[2], c2, d2)


def cube_parse(s):
    p1, t, p2 = s.split(':')
    return (tuple(map(int, p1.split(','))), tuple(int(x) for x in t), tuple(map(int, p2.split(','))))


def cube_lits(c, n, sel, fbit):
    (a, b), t, (c2, d2) = c
    lits = [sel[n, a, b]]
    lits += [fbit[n, p, q] if bit else -fbit[n, p, q] for (p, q), bit in zip(((0, 1), (1, 0), (1, 1)), t)]
    lits.append(sel[n + 1, c2, d2])
    return lits


def build(job):
    """The job's clause list and the encoder's maps."""
    extra = {}
    if job.get('elimL', '-') != '-':
        assert M.restricted_ok(job['class'], job['k'], job['shift'])
        extra['elim'] = M.elim_bounds(job['r'], job['k'], tuple(map(int, job['elimL'].split(','))))
    cnf, sel, fbit, outsel, neg, n, Wt = M.encode(job['class'], job['r'], job['k'], job['shift'], **extra)
    if job['kind'] == 'leaf':
        cnf = cnf + [[l] for l in cube_lits(cube_parse(job['cube']), n, sel, fbit)]
    elif job['kind'] == 'cover':
        cnf = cnf + [[-l for l in cube_lits(c, n, sel, fbit)] for c in cubes(job['k'])]
    return cnf, (sel, fbit, outsel, neg, n)


RUNNING = {}        # job id -> (Popen or None, proof path)
LOCK = threading.Lock()
STOPPING = threading.Event()


def proc(cmd, d, jid, proof=None, env=None, timeout=None):
    err = os.path.join(d, 'stderr')
    t0 = time.time()
    with open(err, 'wb') as e:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=e, stdin=subprocess.DEVNULL, env=env)
        with LOCK:
            RUNNING[jid] = (p, proof)
        timer = threading.Timer(timeout, p.kill) if timeout else None
        if timer:
            timer.start()
        out = p.stdout.read()
        _, status, ru = os.wait4(p.pid, 0)
        if timer:
            timer.cancel()
    p.stdout.close()
    code = os.waitstatus_to_exitcode(status)
    tail = open(err, 'rb').read()[-300:].decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    rss = ru.ru_maxrss / (2**20 if sys.platform == 'darwin' else 2**10)
    return code, out, tail, time.time() - t0, ru.ru_utime + ru.ru_stime, rss


def run_job(job):
    d = tempfile.mkdtemp(dir=TMP, prefix='job-%d-' % os.getpid())
    t0 = time.time()
    try:
        cnf, (sel, fbit, outsel, neg, n) = build(job)
        path, proof, model = (os.path.join(d, x) for x in ('f.cnf', 'proof.lrat', 'model'))
        M.write_dimacs(cnf, path)
        h = sha256(path)
        nv = max(abs(l) for c in cnf for l in c)
        del cnf
        cmd = [CADICAL, '-q', '--lrat=true', '--binary=true', '-w', model, path, proof]
        c = proc(cmd, d, job['id'], proof, timeout=job['tlimit'] or None)
        psize = os.path.getsize(proof) if os.path.exists(proof) else 0
        cake, cake_t, circ, psha = 'not run', (0.0, 0.0, 0.0), '-', '-'
        if c[0] == 20:
            psha = sha256(proof)
            k = proc([CAKE, path, proof], d, job['id'], proof, env=CAKE_ENV)
            ok_cake = k[1] == b's VERIFIED UNSAT\n'
            text = k[1].decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
            cake = text if ok_cake else 'REJECTED exit %d: %s' % (k[0], (text or k[2])[:200] or '(no output)')
            cake_t = k[3:]
            verdict = 'UNSAT-OK' if ok_cake else 'FAIL'
        elif c[0] == 10:
            lits = M.read_model(model)
            if not lits:            # cadical -w writes `v` lines; fall back to stdout
                lits = [int(x) for line in c[1].decode().splitlines() if line.startswith('v ')
                        for x in line.split()[1:] if x != '0']
            circ_l, outs = M.oc.decode(lits, n, job['r'], sel, fbit, outsel, neg, 2)
            okc = M.check_block(circ_l, outs, job['class'], job['k'], job['shift'])
            circ = json.dumps({'gates': [[j, kk, [tt[0, 1], tt[1, 0], tt[1, 1]]] for j, kk, tt in circ_l],
                               'outputs': outs, 'check_block': okc}, separators=(',', ':'))
            verdict = 'SAT-OK' if okc else 'FAIL'
        elif STOPPING.is_set():
            verdict = 'KILLED'
        elif job['tlimit'] and c[3] >= job['tlimit'] - 1:
            verdict = 'TIMEOUT'
        else:
            verdict = 'FAIL'
        cad = 'exit %d' % c[0] if c[0] in (10, 20) else 'exit %d: %s' % (c[0], c[2][:200])
        kind = job['kind'] + ('' if job.get('elimL', '-') == '-' else '+e' + job['elimL'].replace(',', '-'))
        return [job['id'], job['class'], job['k'], job['shift'], job['r'], kind, job['cube'], h, nv,
                job.get('nclauses', '-'), cad, '%.1f' % c[3], '%.1f' % c[4], '%.0f' % c[5], '%.1f' % (psize / 1e6),
                psha, cake, '%.1f' % cake_t[0], '%.1f' % cake_t[1], '%.0f' % cake_t[2], circ,
                utc(t0), utc(), verdict]
    finally:
        with LOCK:
            RUNNING.pop(job['id'], None)
        shutil.rmtree(d, ignore_errors=True)


def read_jobs(path):
    out = []
    for line in open(path):
        if line.startswith('#') or not line.strip():
            continue
        f = line.rstrip('\n').split('\t')
        out.append(dict(id=f[0], **{'class': int(f[1])}, k=int(f[2]), shift=int(f[3]), r=int(f[4]),
                        kind=f[5], cube=f[6], tlimit=float(f[7]), elimL=f[8] if len(f) > 8 else '-'))
    return out


def done_ids():
    done = set()
    if not os.path.exists(RESULTS):
        return done
    for line in open(RESULTS):
        if line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        if len(f) != len(COLUMNS):
            continue
        r = dict(zip(COLUMNS, f))
        if (r['verdict'] == 'UNSAT-OK' and r['cadical'] == 'exit 20' and r['cake'] == 's VERIFIED UNSAT'
                and len(r['sha256']) == 64):
            done.add(r['job'])
        elif r['verdict'] == 'SAT-OK' and r['cadical'] == 'exit 10' and json.loads(r['circuit'])['check_block'] is True:
            done.add(r['job'])
    return done


def sat_found():
    """(class, k, shift, r, elimL) with a SAT-OK line."""
    s = set()
    if os.path.exists(RESULTS):
        for line in open(RESULTS):
            f = line.rstrip('\n').split('\t')
            if not line.startswith('#') and len(f) == len(COLUMNS) and f[-1] == 'SAT-OK':
                s.add(tuple(map(int, f[1:5])) + (f[5].partition('+e')[2].replace('-', ',') or '-',))
    return s


def append(fields):
    with open(RESULTS, 'a') as f:
        f.write('\t'.join(map(str, fields)) + '\n')
        f.flush()
        os.fsync(f.fileno())


def free_disk():
    s = os.statvfs(W)
    return s.f_bavail * s.f_frsize


def in_flight_bytes():
    tot = 0
    with LOCK:
        paths = [p for _, p in RUNNING.values() if p]
    for p in paths:
        try:
            tot += os.path.getsize(p)
        except OSError:
            pass
    return tot


def kill_all():
    STOPPING.set()
    with LOCK:
        procs = [p for p, _ in RUNNING.values() if p]
    for p in procs:
        try:
            p.send_signal(signal.SIGTERM)
        except OSError:
            pass


def run(jobfile, workers):
    assert 1 <= workers <= MAX_WORKERS
    os.makedirs(TMP, exist_ok=True)
    for d in os.listdir(TMP):          # temp dirs of dead drivers only (10-27 02:37: a second driver's
        if d.startswith('job-'):        # blanket cleanup deleted a running driver's job dirs)
            try:
                os.kill(int(d.split('-')[1]), 0)
            except (ValueError, IndexError, ProcessLookupError):
                shutil.rmtree(os.path.join(TMP, d), ignore_errors=True)
            except PermissionError:
                pass
    if os.path.exists(FAILED):
        raise SystemExit('~/work/FAILED exists: look at it before running again')
    done = done_ids()
    todo = [j for j in read_jobs(jobfile) if j['id'] not in done]
    if not os.path.exists(RESULTS):
        append(['# ' + COLUMNS[0]] + COLUMNS[1:])
    append(['# session %s pid %d jobs %s sha256 %s workers %d driver %s encoder %s: %d done, %d to do'
            % (utc(), os.getpid(), jobfile, sha256(jobfile)[:16], workers, sha256(__file__)[:16],
               sha256(M.__file__)[:16], len(done), len(todo))])
    running, stop, nfail = {}, None, 0
    sats = sat_found()
    with ThreadPoolExecutor(workers) as ex:
        while todo or running:
            for fut in [f for f in running if f.done()]:
                j = running.pop(fut)
                try:
                    f = fut.result()
                except Exception as e:
                    f = [j['id'], j['class'], j['k'], j['shift'], j['r'], j['kind'], j['cube']] + \
                        ['-'] * (len(COLUMNS) - 8) + ['FAIL: driver error %r' % e]
                append(f)
                if f[-1].startswith('FAIL'):
                    nfail += 1
                    with open(FAILED, 'a') as g:
                        g.write('\t'.join(map(str, f)) + '\n')
                if f[-1] == 'SAT-OK':
                    sats.add((j['class'], j['k'], j['shift'], j['r'], j['elimL']))
            # 10-27 04:00: the key includes elimL (a SAT without elim must not cancel the elim control)
            todo = [j for j in todo if (j['class'], j['k'], j['shift'], j['r'], j['elimL']) not in sats]
            if stop is None:
                if os.path.exists(FAILED):
                    stop = 'a job failed (see FAILED)'
                elif os.path.exists(PAUSE):
                    stop = 'PAUSE'
                elif free_disk() < DISK_FLOOR:
                    stop = 'free disk %.1f GB < floor' % (free_disk() / 1e9)
                    kill_all()
                elif in_flight_bytes() > WORK_CAP:
                    stop = 'proofs in flight %.1f GB > cap' % (in_flight_bytes() / 1e9)
                    kill_all()
            if stop is None:
                while todo and len(running) < workers and in_flight_bytes() <= HOLD_CAP:
                    j = todo.pop(0)
                    running[ex.submit(run_job, j)] = j
            elif not running:
                break
            time.sleep(1)
    why = stop or 'all done'
    append(['# end %s: %s; %d left; %d failed this session' % (utc(), why, len(todo), nfail)])
    print('%s: stopped: %s; %d left, %d failed' % (utc(), why, len(todo), nfail), flush=True)


def elim_of(c):
    """ELIM='1:9,8;3:10,9' -> the certified lower bounds (L0, L1) for class c, or '-'."""
    for part in filter(None, os.environ.get('ELIM', '').split(';')):
        cc, L = part.split(':')
        if int(cc) == c:
            return L
    return '-'


def plan(args):
    what = args[0]
    if what == 'scan':
        classes = [int(c) for c in args[1].split(',')]
        r1, r2 = int(args[2]), int(args[3])
        k = int(args[4]) if len(args) > 4 else 4
        s = int(args[5]) if len(args) > 5 else 0
        tl = float(os.environ.get('TLIMIT', 0))
        for r in range(r1, r2 + 1):
            for c in classes:
                L = elim_of(c)
                tag = '' if L == '-' else '_e' + L.replace(',', '-')
                print('c%d_k%d_s%d_r%d_whole%s\t%d\t%d\t%d\t%d\twhole\t-\t%g\t%s' % (c, k, s, r, tag, c, k, s, r, tl, L))
    elif what == 'cubes':
        c, r = int(args[1]), int(args[2])
        k = int(args[3]) if len(args) > 3 else 4
        s = int(args[4]) if len(args) > 4 else 0
        L = elim_of(c)
        tag = '' if L == '-' else '_e' + L.replace(',', '-')
        print('c%d_k%d_s%d_r%d%s_cover\t%d\t%d\t%d\t%d\tcover\t-\t0\t%s' % (c, k, s, r, tag, c, k, s, r, L))
        for q in cubes(k):
            print('c%d_k%d_s%d_r%d%s_%s\t%d\t%d\t%d\t%d\tleaf\t%s\t0\t%s' % (c, k, s, r, tag, cube_str(q), c, k, s, r, cube_str(q), L))


def status():
    from collections import Counter
    cnt, cpu = Counter(), Counter()
    for line in open(RESULTS):
        f = line.rstrip('\n').split('\t')
        if line.startswith('#') or len(f) != len(COLUMNS):
            continue
        key = (f[1], f[4], f[5], f[-1])
        cnt[key] += 1
        cpu[key] += float(f[12]) + float(f[18])
    for key in sorted(cnt):
        print('class %s r=%s %s %s: %d (%.2f CPU-h)' % (key + (cnt[key], cpu[key] / 3600)))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'plan':
        plan(sys.argv[2:])
    elif cmd == 'run':
        run(sys.argv[2], int(sys.argv[3]))
    elif cmd == 'status':
        status()
