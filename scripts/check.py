"""check.py: re-solve the 506 CNFs that `M3Codes.m3v4g11_all` takes as hypotheses, and check every proof
with two verified checkers. Python 3.9+, standard library only. reproduce.sh calls it; the paths
below are relative to the repository, and the work directory is $M3_WORK (default ./work).

    check.py audit                     check the records in results/ against the Lean job list
    check.py controls                  both checkers must reject altered proofs, explicitly
    check.py run quick [--seed S] [--sample N] [--workers N]
    check.py run full [--hardest K] [--workers N]
    check.py summary <results.tsv>

The job list is Lean's: `m3export list` prints `M3Jobs.jobs`, the list the theorem's hypothesis
quantifies over, one line per job (index, class, k, shift, r, kind, cube, elim sizes). `run full`
does all 506, hardest first (by the Mac's recorded time); `--hardest K` only the K hardest.
`run quick` does a seeded uniform sample of N jobs (default 51, 10%), drawn as
`random.Random(sha256(S)).sample(range(506), N)`.

For each job i: `m3export job i` writes the DIMACS. Its sha256 must equal the one recorded for that
job in results/m3v4g11_results.tsv (the Mac run, whose proofs cake_lpr verified; written there by
the Python encoder, which `m3_cnf_compare.out` shows is byte-identical to the Lean generator).
CaDiCaL writes a binary LRAT proof and must exit 20. Then:

* cake_lpr (CakeML, verified down to machine code, DIMACS parser included) checks the proof against
  the DIMACS file. It exits 0 on failure too, so only stdout exactly `s VERIFIED UNSAT\\n` with exit
  0 counts.
* m3direct (Lean, `Garden/M3Direct.lean`, `LratDirect.check_sound`) checks it against the CNF it
  builds in memory from `M3Jobs.jobs[i]`; only exit 0 with exactly one stdout line starting
  `s VERIFIED UNSAT (job <i>: ` counts.

A job is OK only if all four hold. The proof is then deleted. This is MOD3_6's driver
(github.com/wevial/mod3-6-circuit-size, scripts/recheck.py) with the job list, the record and the
checker invocation changed; resuming, validation, controls and resource planning are the same.
"""
import calendar, hashlib, math, os, random, re, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
W = os.path.abspath(os.environ.get('M3_WORK') or os.path.join(ROOT, 'work'))
BIN = os.path.join(ROOT, 'lean/direct/.lake/build/bin')
EXPORT, DIRECT = os.path.join(BIN, 'm3export'), os.path.join(BIN, 'm3direct')
CADICAL = os.path.join(W, 'tools/cadical/build/cadical')
CAKE = os.path.join(W, 'tools/cake_lpr/cake_lpr')
MAC_RESULTS = os.path.join(ROOT, 'results/m3v4g11_results.tsv')
RECHECKS = [os.path.join(ROOT, 'results', f) for f in ('m3_lean_recheck.out', 'm3_lean_recheck_k3.out')]
TMP = os.path.join(W, 'tmp')
# cake_lpr's RSS is its heap (CakeML's GC grows into all of it). The Mac ran every job at 2048 MB
# (peak RSS 2,051 MiB in the record).
CAKE_HEAP_MB, CAKE_STACK_MB = 2048, 4096
WORKER_PEAK_MIB = 2100           # bounds cake_lpr (its heap); a worker runs its processes one after another
OTHER_PEAK_MIB = 800             # bounds CaDiCaL (198 MiB on the Mac) and m3direct
RESERVE_MIB = 1024               # for the driver and the page cache
DISK_FLOOR = int(float(os.environ.get('M3_DISK_FLOOR_GB', '10')) * 1e9)
CAKE_ENV = dict(os.environ, CML_HEAP_SIZE=str(CAKE_HEAP_MB), CML_STACK_SIZE=str(CAKE_STACK_MB))
TOTAL = 506
MAC_COLUMNS = ['job', 'class', 'k', 'shift', 'r', 'kind', 'cube', 'sha256', 'vars', 'clauses', 'cadical', 'solve_s',
               'solve_cpu', 'solve_MiB', 'proof_MB', 'proof_sha256', 'cake', 'cake_s', 'cake_cpu', 'cake_MiB',
               'circuit', 'start', 'end', 'verdict']
COLUMNS = ['i', 'job', 'sha256', 'sha', 'cadical', 'solve_s', 'solve_cpu', 'solve_MiB', 'proof_MB', 'cake', 'cake_s',
           'cake_cpu', 'cake_MiB', 'm3direct', 'direct_s', 'direct_cpu', 'direct_MiB', 'recorded_s', 'start', 'end',
           'verdict']
CAKE_OK = 's VERIFIED UNSAT'


def est_proof_bytes(rec):
    """Upper estimate of a proof's size from the Mac's solve+check seconds (the Mac wrote 2.0-4.1 MB
    per second of solve+check on the jobs above 100 s; x86-64 proofs may be larger)."""
    return 8e6 * rec + 50e6


def utc(t):
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t))


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def proc(cmd, d, env=None):
    """Run cmd (stderr to a file in d); return (exit code, stdout bytes, stderr text (its first 2,000
    characters), wall s, cpu s, peak RSS MiB). CPU time and peak RSS come from wait4 on that process."""
    err = os.path.join(d, 'stderr')
    t0 = time.time()
    with open(err, 'wb') as e:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=e, stdin=subprocess.DEVNULL, env=env)
        out = p.stdout.read()
        _, status, ru = os.wait4(p.pid, 0)
    p.stdout.close()
    code = os.waitstatus_to_exitcode(status)
    with open(err, 'rb') as e:
        errtext = e.read(2000).decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    rss = ru.ru_maxrss / (2**20 if sys.platform == 'darwin' else 2**10)
    return code, out, errtext, time.time() - t0, ru.ru_utime + ru.ru_stime, rss


def one_line(out):
    """stdout as text if it is exactly one newline-terminated line, else None."""
    text = out.decode(errors='replace')
    return text[:-1] if text.endswith('\n') and text.count('\n') == 1 else None


def cake_verdict(code, out, err):
    """(accepted, explicitly rejected, text). Accepted: exit 0 and stdout exactly `s VERIFIED UNSAT\\n`.
    Explicit rejection: exit 0, nothing on stdout, and stderr starting `c Checking failed` (cake_lpr's
    message for a proof step that fails)."""
    ok = code == 0 and out == (CAKE_OK + '\n').encode()
    if ok:
        return True, False, CAKE_OK
    text = out.decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    rejected = code == 0 and out == b'' and err.startswith('c Checking failed')
    return False, rejected, '%s exit %d: %s' % ('REJECTED' if rejected else 'INCONCLUSIVE', code,
                                                (text or err)[:200] or '(no output)')


def direct_verdict(code, out, err, label):
    """(accepted, explicitly rejected, text). Accepted: exit 0, one line `s VERIFIED UNSAT (<label>: …`.
    Explicit rejection: exit 1, one line `s NOT VERIFIED (… <label>: …`."""
    line = one_line(out)
    ok = code == 0 and line is not None and line.startswith('s VERIFIED UNSAT (%s: ' % label)
    if ok:
        return True, False, line.replace('\t', ' ')
    rejected = code == 1 and line is not None and line.startswith('s NOT VERIFIED (') and \
        ('; %s: ' % label) in line
    text = out.decode(errors='replace').strip().replace('\n', ' | ').replace('\t', ' ')
    return False, rejected, '%s exit %d: %s' % ('REJECTED' if rejected else 'INCONCLUSIVE', code,
                                                (text or err)[:300] or '(no output)')


# ---------------------------------------------------------------- jobs

def mac_key(cls, k, shift, r, kind, cube, elim):
    """The record's key for a job: its kind carries `+eL0-L1` when the job has elim sizes."""
    return (cls, k, shift, r, kind + ('' if elim == '-' else '+e' + elim.replace(',', '-')), cube)


def mac_record():
    """key -> list of the record's rows (dicts) for it."""
    out = {}
    for line in open(MAC_RESULTS):
        if line.startswith('#'):
            continue
        t = line.rstrip('\n').split('\t')
        if len(t) != len(MAC_COLUMNS):
            continue
        r = dict(zip(MAC_COLUMNS, t))
        out.setdefault((r['class'], r['k'], r['shift'], r['r'], r['kind'], r['cube']), []).append(r)
    return out


def jobs():
    """`M3Jobs.jobs` as `m3export list` prints it, each with the sha256 its DIMACS must have (the one
    recorded with verdict UNSAT-OK) and the recorded solve+check seconds."""
    out = subprocess.run([EXPORT, 'list'], capture_output=True, text=True, check=True).stdout
    rec = mac_record()
    js = []
    for n, line in enumerate(out.splitlines()):
        i, cls, k, shift, r, kind, cube, elim = line.split('\t')
        assert int(i) == n, 'm3export list out of order'
        rows = [x for x in rec.get(mac_key(cls, k, shift, r, kind, cube, elim), []) if x['verdict'] == 'UNSAT-OK']
        name = 'c%s_k%s_s%s_r%s_%s%s%s' % (cls, k, shift, r, kind, '' if cube == '-' else '_' + cube,
                                         '' if elim == '-' else '_e' + elim.replace(',', '-'))
        js.append(dict(i=n, name=name, label='job %d' % n, cls=cls, k=k, shift=shift, r=r, kind=kind, cube=cube,
                       elim=elim, want={x['sha256'] for x in rows}, rows=rows,
                       rec=max([float(x['solve_s']) + float(x['cake_s']) for x in rows] or [0.0])))
    assert len(js) == TOTAL, 'm3export list printed %d jobs, not %d' % (len(js), TOTAL)
    return js


def write_cnf(j, path):
    subprocess.run([EXPORT, 'job', str(j['i']), path], check=True)


RUNNING = {}          # job index -> proof path, for the disk estimate


def run_job(j):
    """Export, sha256, solve, check twice; return the result line's fields."""
    d = tempfile.mkdtemp(dir=TMP, prefix='job-')
    t0 = time.time()
    try:
        cnf, proof = os.path.join(d, 'f.cnf'), os.path.join(d, 'proof.lrat')
        RUNNING[j['i']] = proof
        write_cnf(j, cnf)
        h = sha256(cnf)
        sha_ok = h in j['want']
        c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', cnf, proof], d)
        size = os.path.getsize(proof) if os.path.exists(proof) else 0
        none = (False, False, 'not run', 0.0, 0.0, 0.0)
        cake = direct = none
        if sha_ok and c[0] == 20:
            with CAKE_SLOTS:
                k = proc([CAKE, cnf, proof], d, CAKE_ENV)
            cake = cake_verdict(k[0], k[1], k[2]) + k[3:]
            x = proc([DIRECT, str(j['i']), proof], d)
            direct = direct_verdict(x[0], x[1], x[2], j['label']) + x[3:]
        ok = sha_ok and c[0] == 20 and cake[0] and direct[0]
        return [j['i'], j['name'], h, '= recorded' if sha_ok else 'MISMATCH',
                'exit %d' % c[0] if c[0] == 20 else 'exit %d: %s' % (c[0], c[2][:200]),
                '%.1f' % c[3], '%.1f' % c[4], '%.0f' % c[5], '%.1f' % (size / 1e6),
                cake[2], '%.1f' % cake[3], '%.1f' % cake[4], '%.0f' % cake[5],
                direct[2], '%.1f' % direct[3], '%.1f' % direct[4], '%.0f' % direct[5],
                '%.1f' % j['rec'], utc(t0), utc(time.time()), 'OK' if ok else 'FAIL']
    finally:
        RUNNING.pop(j['i'], None)
        shutil.rmtree(d, ignore_errors=True)


# ---------------------------------------------------------------- validation of result lines

def valid_ok_row(t, by):
    """Why a line marked OK is not a valid OK line for a job in `by` (None if it is)."""
    if len(t) != len(COLUMNS):
        return 'has %d fields, not %d' % (len(t), len(COLUMNS))
    r = dict(zip(COLUMNS, t))
    try:
        i = int(r['i'])
    except ValueError:
        return 'bad index'
    j = by.get(i)
    if j is None:
        return 'not a job of the theorem'
    if r['job'] != j['name']:
        return 'job %s, expected %s' % (r['job'], j['name'])
    if r['sha256'] not in j['want']:
        return 'sha256 is not the recorded one'
    if r['sha'] != '= recorded':
        return 'sha field %r' % r['sha']
    if r['cadical'] != 'exit 20':
        return 'CaDiCaL %r' % r['cadical']
    if r['cake'] != CAKE_OK:
        return 'cake_lpr %r' % r['cake']
    if not re.fullmatch(r's VERIFIED UNSAT \(%s: .*\)' % re.escape(j['label']), r['m3direct']):
        return 'm3direct %r' % r['m3direct']
    for c in ('solve_s', 'solve_cpu', 'solve_MiB', 'proof_MB', 'cake_s', 'cake_cpu', 'cake_MiB',
              'direct_s', 'direct_cpu', 'direct_MiB', 'recorded_s'):
        try:
            v = float(r[c])
        except ValueError:
            return '%s %r' % (c, r[c])
        if not (math.isfinite(v) and v >= 0):
            return '%s %r' % (c, r[c])
    try:
        t0, t1 = (calendar.timegm(time.strptime(r[c], '%Y-%m-%dT%H:%M:%SZ')) for c in ('start', 'end'))
    except ValueError:
        return 'start/end %r %r' % (r['start'], r['end'])
    if t1 < t0:
        return 'ends before it starts'
    return None


def read_results(path, by, pins):
    """Parse and validate a results file written by `run`. Return (ok, superseded, fails, sessions):
    ok maps each job to its valid OK line; superseded are FAIL lines followed by a valid OK line for
    the same job; fails are the other FAIL lines. Raises SystemExit unless every line is a column
    header, a session or end line, a valid OK line or a FAIL line; every result line follows a session
    header run under `pins` (the sha256 of this script, the binaries and the record); and no job has
    two OK lines."""
    ok, failed, sessions, bad, in_session, okline = {}, {}, [], [], False, {}
    for n, line in enumerate(open(path), 1):
        line = line.rstrip('\n')
        if line.startswith('# session'):
            sessions.append(line)
            m = re.search(r' pins ([0-9a-f]{64}) ', line)
            if not m or m.group(1) != pins:
                raise SystemExit('%s:%d: this session ran under other pins (a binary, the script or the record '
                                 'differs from now); use a new results file' % (path, n))
            in_session = True
            continue
        if line.startswith('# end'):
            sessions.append(line)
            continue
        if line.startswith('#') or not line:
            continue
        t = line.split('\t')
        if not in_session:
            bad.append('%s:%d: result line before any session header' % (path, n))
            continue
        if t[-1] == 'OK':
            why = valid_ok_row(t, by)
            if why:
                bad.append('%s:%d: %s' % (path, n, why))
            elif int(t[0]) in ok and not any(m > okline[int(t[0])] for m, _ in failed.get(int(t[0]), [])):
                bad.append('%s:%d: a second OK line for job %s' % (path, n, t[0]))
            else:
                ok[int(t[0])] = t
                okline[int(t[0])] = n
        elif t[-1] == 'FAIL' and len(t) == len(COLUMNS) and t[0].isdigit() and int(t[0]) in by \
                and t[1] == by[int(t[0])]['name']:
            failed.setdefault(int(t[0]), []).append((n, t))
        else:
            bad.append('%s:%d: not a result line' % (path, n))
    if bad:
        raise SystemExit('lines that do not validate:\n  ' + '\n  '.join(bad[:20]))
    # A FAIL line is superseded only by a valid OK line for the same job further down the file; a FAIL
    # after the OK line stays a failure, and so the job counts as not done.
    superseded, fails = [], []
    for k, rows in failed.items():
        for n, t in rows:
            (superseded if k in okline and okline[k] > n else fails).append(t)
        if any(not (k in okline and okline[k] > n) for n, _ in rows):
            ok.pop(k, None)
    return ok, superseded, fails, sessions


# ---------------------------------------------------------------- pins of this session

def pins_text():
    files = [CADICAL, CAKE, DIRECT, EXPORT, os.path.abspath(__file__), MAC_RESULTS]
    return ''.join('%s  %s\n' % (sha256(p), os.path.relpath(p, ROOT if p.startswith(ROOT + os.sep) else W))
                   for p in files)


# ---------------------------------------------------------------- resources

def cgroup_cpus():
    try:
        q, p = open('/sys/fs/cgroup/cpu.max').read().split()
        if q != 'max':
            return max(1, int(int(q) // int(p)))
    except (OSError, ValueError):
        pass
    try:
        return len(os.sched_getaffinity(0))
    except AttributeError:
        return os.cpu_count() or 1


def memory_mib():
    total = None
    try:
        total = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES') / 2**20
    except (ValueError, OSError, AttributeError):
        pass
    try:
        m = open('/sys/fs/cgroup/memory.max').read().strip()
        if m != 'max':
            total = min(total or float('inf'), int(m) / 2**20)
    except (OSError, ValueError):
        pass
    return total


def plan_memory(workers=None):
    """(workers, cake slots): at most `slots` cake_lpr processes run at once, so that
    slots * WORKER_PEAK_MIB + (workers - slots) * OTHER_PEAK_MIB fits in memory less RESERVE_MIB."""
    mem = memory_mib()
    budget = (mem - RESERVE_MIB) if mem else WORKER_PEAK_MIB
    slots = lambda w: int((budget - w * OTHER_PEAK_MIB) // (WORKER_PEAK_MIB - OTHER_PEAK_MIB))
    if workers is None:
        workers = max(1, cgroup_cpus())
        while workers > 1 and slots(workers) < 1:
            workers -= 1
    if slots(workers) < 1:
        raise SystemExit('not enough memory for %d workers (%.0f MiB): use --workers with a smaller number'
                         % (workers, mem or 0))
    return workers, min(slots(workers), workers)


CAKE_SLOTS = threading.Semaphore(1)


def free_disk():
    s = os.statvfs(W)
    return s.f_bavail * s.f_frsize


def disk_ok(j, running):
    pending = 0.0
    for r in running:
        p = RUNNING.get(r['i'])
        try:
            cur = os.path.getsize(p) if p else 0
        except FileNotFoundError:    # not written yet, or deleted as its job finished: reserve it all
            cur = 0
        pending += max(0.0, est_proof_bytes(r['rec']) - cur)
    return free_disk() - pending - est_proof_bytes(j['rec']) >= DISK_FLOOR


# ---------------------------------------------------------------- run

def append(path, line):
    with open(path, 'a') as f:
        f.write(line + '\n')
        f.flush()
        os.fsync(f.fileno())


def select(all_jobs, mode, seed_hex, nsample, hardest, quiet=False):
    """The jobs of a run, hardest first. quick: `random.Random(seed_hex).sample(range(506), nsample)`.
    full: every job, or with `hardest` only that many of the hardest."""
    order = lambda js: sorted(js, key=lambda j: (-j['rec'], j['i']))
    if mode == 'quick':
        pick = sorted(random.Random(seed_hex).sample(range(TOTAL), nsample))
        if not quiet:
            print('seed sha256 %s; %d jobs: %s' % (seed_hex, nsample, pick), flush=True)
        return order([all_jobs[p] for p in pick])
    return order(all_jobs)[:hardest] if hardest else order(all_jobs)


def run(mode, results, workers, seed, nsample, hardest):
    seed_hex = hashlib.sha256(seed.encode()).hexdigest() if mode == 'quick' else '0' * 64
    global CAKE_SLOTS
    workers, slots = plan_memory(workers)
    CAKE_SLOTS = threading.Semaphore(slots)
    all_jobs = jobs()
    by = {j['i']: j for j in all_jobs}
    pins = hashlib.sha256(pins_text().encode()).hexdigest()
    for d in os.listdir(TMP):                      # a killed session's temp dirs
        if d.startswith('job-'):
            shutil.rmtree(os.path.join(TMP, d), ignore_errors=True)
    done = {}
    if os.path.exists(results):
        done, _, _, sessions = read_results(results, by, pins)
        if sessions and session_selection(sessions) != (mode, seed_hex, nsample, hardest):
            raise SystemExit('%s holds a different selection of jobs; use another --results file' % results)
    want = select(all_jobs, mode, seed_hex, nsample, hardest)
    todo = [j for j in want if j['i'] not in done]
    if not os.path.exists(results):
        append(results, '# ' + '\t'.join(COLUMNS))
    append(results, '# session %s pid %d pins %s mode %s seed_sha256 %s sample %d hardest %d workers %d '
           'cake_slots %d cake_heap_MB %d (seed %r): %d of %d done, %d to do'
           % (utc(time.time()), os.getpid(), pins, mode, seed_hex, nsample, hardest, workers, slots, CAKE_HEAP_MB,
              seed, len(want) - len(todo), len(want), len(todo)))
    print('%s: %s: %d jobs, %d already done, %d to do; %d workers, at most %d cake_lpr at once (heap %d MB)'
          % (utc(time.time()), mode, len(want), len(want) - len(todo), len(todo), workers, slots, CAKE_HEAP_MB),
          flush=True)
    t_start = time.time()
    running, stop, nfail, ndone = {}, None, 0, 0
    with ThreadPoolExecutor(workers) as ex:
        while todo or running:
            for fut in [f for f in running if f.done()]:
                j = running.pop(fut)
                try:
                    f = fut.result()
                except Exception as e:             # an exception in the driver is a FAIL too
                    f = [j['i'], j['name'], '-', 'driver error: %r' % e] + ['-'] * (len(COLUMNS) - 5) + ['FAIL']
                line = '\t'.join(map(str, f))
                append(results, line)
                ndone += 1
                if f[-1] != 'OK':
                    nfail += 1
                    stop = stop or 'a CNF failed: job %s %s' % tuple(f[:2])
                    print('FAIL ' + line, flush=True)
                elif max(float(f[i]) for i in (7, 12, 16)) > WORKER_PEAK_MIB:
                    stop = stop or 'a process of job %s exceeded %d MiB' % (f[0], WORKER_PEAK_MIB)
                if ndone % 50 == 0 or not todo:
                    print('%s: %d/%d finished, %d failed' % (utc(time.time()), ndone, ndone + len(todo) + len(running),
                                                            nfail), flush=True)
            if stop is not None:
                if not running:
                    break
            else:
                while todo and len(running) < workers:
                    j = todo[0]
                    rs = list(running.values())
                    if not disk_ok(j, rs):
                        if not rs:
                            stop = 'free disk below M3_DISK_FLOOR_GB with nothing running'
                        break
                    todo.pop(0)
                    running[ex.submit(run_job, j)] = j
            time.sleep(0.5)
    why = stop or 'all done'
    append(results, '# end %s: %s; %d left; %d failed this session; %.0f s wall'
           % (utc(time.time()), why, len(todo), nfail, time.time() - t_start))
    print('%s: stopped: %s; %d left, %d failed, %.0f s wall' % (utc(time.time()), why, len(todo), nfail,
                                                               time.time() - t_start), flush=True)
    if nfail or todo or stop is not None:
        sys.exit(1)
    summary(results)


# ---------------------------------------------------------------- summary and audit

def session_selection(sessions):
    """(mode, seed's sha256, sample, hardest) of the sessions in a results file, which must all agree."""
    sel = set()
    for line in sessions:
        m = re.search(r' mode (quick|full) seed_sha256 ([0-9a-f]{64}) sample (\d+) hardest (\d+) ', line)
        if line.startswith('# session'):
            if not m:
                raise SystemExit('unreadable session line: ' + line)
            sel.add((m.group(1), m.group(2), int(m.group(3)), int(m.group(4))))
    if len(sel) != 1:
        raise SystemExit('sessions with different selections: %s' % sorted(sel))
    return sel.pop()


def summary(results):
    """Validate a results file (every line, under the current pins) and report counts, times and peak
    RSS. Every job its sessions selected must have a valid OK line; a FAIL line counts as recovered
    only if a valid OK line for the same CNF follows it."""
    all_jobs = jobs()
    by = {j['i']: j for j in all_jobs}
    pins = hashlib.sha256(pins_text().encode()).hexdigest()
    ok, superseded, fails, sessions = read_results(results, by, pins)
    mode, seed, nsample, hardest = session_selection(sessions)
    want = {j['i'] for j in select(all_jobs, mode, seed, nsample, hardest, quiet=True)}
    extra = set(ok) - want
    good = [dict(zip(COLUMNS, ok[k])) for k in want if k in ok]
    print('# summary of %s (%s): mode %s%s' % (os.path.basename(results), utc(time.time()), mode,
          (', seed sha256 %s, %d jobs' % (seed, nsample)) if mode == 'quick' else
          (', the %d hardest jobs' % hardest) if hardest else ''))
    print('%d/%d CNFs OK (sha256 = recorded, CaDiCaL exit 20, cake_lpr exit 0 and stdout exactly '
          '`s VERIFIED UNSAT`, m3direct exit 0 and one line `s VERIFIED UNSAT (job <i>: …)`)'
          % (len(want & set(ok)), len(want)))
    for cls in ('1', '2', '3'):
        w = {k for k in want if by[k]['cls'] == cls}
        print('  class %s: %d/%d' % (cls, len(w & set(ok)), len(w)))
    print('FAIL lines: %d unrecovered, %d followed by a valid OK line for the same CNF'
          % (len(fails), len(superseded)))
    for t in (fails + superseded)[:20]:
        print('  ' + '\t'.join(t))
    f = lambda c: sum(float(r[c]) for r in good)
    print('process times, hours: CaDiCaL %.2f wall / %.2f CPU; cake_lpr %.2f / %.2f; m3direct %.2f / %.2f'
          % (f('solve_s') / 3600, f('solve_cpu') / 3600, f('cake_s') / 3600, f('cake_cpu') / 3600,
             f('direct_s') / 3600, f('direct_cpu') / 3600))
    print('proofs written and deleted: %.1f GB' % (f('proof_MB') / 1e3))
    for c, name in (('solve_MiB', 'CaDiCaL'), ('cake_MiB', 'cake_lpr'), ('direct_MiB', 'm3direct')):
        if good:
            m = max(good, key=lambda r: float(r[c]))
            print('peak RSS, %s: %s MiB (job %s %s)' % (name, m[c], m['i'], m['job']))
    if good:
        m = max(good, key=lambda r: float(r['proof_MB']))
        print('largest proof: %s MB (job %s %s)' % (m['proof_MB'], m['i'], m['job']))
    print('sessions:')
    for line in sessions:
        print('  ' + line)
    missing = want - set(ok)
    if missing or fails or extra:
        print('NOT ALL OK: %d selected CNFs without a valid OK line, %d unrecovered FAIL lines, %d OK lines '
              'for CNFs not selected' % (len(missing), len(fails), len(extra)))
        sys.exit(1)
    print('ALL OK: %d/%d CNFs' % (len(want), len(want)))


def audit():
    """Check the records in results/ against the job list Lean prints:
    1. results/m3v4g11_results.tsv (the Mac run, CaDiCaL 3.0.1 + cake_lpr): every one of the 506 jobs
       has at least one line, every line for it has verdict UNSAT-OK, CaDiCaL exit 20, cake_lpr
       `s VERIFIED UNSAT`, and they all record the same sha256;
    2. results/m3_lean_recheck.out and m3_lean_recheck_k3.out (gembox, CaDiCaL 2.1.2 + Lean's
       lratcheck): every job of the list is covered, by its own line (sha256 prefix = the recorded
       one, `s VERIFIED UNSAT`) or, for the 420 class-1 leaves, by the summary line `420/420 OK`;
       both files end with all jobs OK and exit 0."""
    all_jobs = jobs()
    bad = []
    nrows = 0
    for j in all_jobs:
        if not j['rows']:
            bad.append('%s: no line in the record' % j['name'])
            continue
        if len(j['want']) != 1:
            bad.append('%s: %d different sha256 in the record' % (j['name'], len(j['want'])))
        for x in j['rows']:
            nrows += 1
            if x['cadical'] != 'exit 20' or x['cake'] != CAKE_OK:
                bad.append('%s: line %s: cadical %r, cake_lpr %r' % (j['name'], x['job'], x['cadical'], x['cake']))
    rec, retried = mac_record(), []
    for j in all_jobs:
        # Any other line for a job of the theorem must be an attempt that ended without a solver
        # verdict (the record has these: a driver error, or a solver killed when a session stopped),
        # retried later. A SAT line, or a FAIL with a CaDiCaL verdict, would contradict the hypothesis.
        for x in rec.get(mac_key(j['cls'], j['k'], j['shift'], j['r'], j['kind'], j['cube'], j['elim']), []):
            if x['verdict'] == 'UNSAT-OK':
                continue
            if x['verdict'].startswith('FAIL') and x['cadical'] in ('-', 'exit -15: ') and x['cake'] in ('-', 'not run'):
                retried.append(j['name'])
            else:
                bad.append('%s: line with verdict %r, cadical %r' % (j['name'], x['verdict'], x['cadical']))
    print('1. results/m3v4g11_results.tsv: %d jobs, %d UNSAT-OK lines for them, %d aborted attempts without a '
          'solver verdict that were retried (%s), %d problems'
          % (len(all_jobs), nrows, len(retried), ', '.join(retried) or 'none', len(bad)))
    # 2. the gembox Lean rechecks
    text = {os.path.basename(p): open(p).read() for p in RECHECKS}
    covered, bad2 = set(), []
    k4 = re.compile(r'^class (\d) r=\s*(\d+) (whole|cover|leaf) (\S+)\s+sha256 ([0-9a-f]{16}) = recorded; '
                    r'cadical exit 20 .*; lratcheck: s VERIFIED UNSAT ', re.M)
    k3 = re.compile(r'^class (\d) k=3 shift=(\d) r=(\d+) whole sha256 ([0-9a-f]{16}) = recorded; '
                    r'cadical exit 20 .*; lratcheck: s VERIFIED UNSAT ', re.M)
    by4 = {(j['cls'], j['r'], j['kind'], j['cube']): j for j in all_jobs if j['k'] == '4'}
    by3 = {(j['cls'], j['shift'], j['r']): j for j in all_jobs if j['k'] == '3'}
    body = text['m3_lean_recheck.out'].split('# 453 jobs')[-1] if '# 453 jobs' in text['m3_lean_recheck.out'] \
        else text['m3_lean_recheck.out']
    for m in k4.finditer(body):
        j = by4.get((m.group(1), m.group(2), m.group(3), m.group(4)))
        if j and any(s.startswith(m.group(5)) for s in j['want']):
            covered.add(j['i'])
        elif j:
            bad2.append('m3_lean_recheck.out: %s sha256 prefix %s differs' % (j['name'], m.group(5)))
    # The Linux driver printed no line per leaf, only a summary for the 420. So the leaves are covered
    # by that summary, not by individual evidence; the report below says so.
    by_summary = set()
    if re.search(r'^class 1 r=11 leaves: 420/420 OK \(sha256 = recorded, exit 20, VERIFIED\)', body, re.M):
        by_summary = {j['i'] for j in all_jobs if j['kind'] == 'leaf'}
        covered |= by_summary
    for m in k3.finditer(text['m3_lean_recheck_k3.out'].split('# 53 jobs')[-1]):
        j = by3.get((m.group(1), m.group(2), m.group(3)))
        if j and any(s.startswith(m.group(4)) for s in j['want']):
            covered.add(j['i'])
        elif j:
            bad2.append('m3_lean_recheck_k3.out: %s sha256 prefix %s differs' % (j['name'], m.group(4)))
    for name, n in (('m3_lean_recheck.out', 453), ('m3_lean_recheck_k3.out', 53)):
        if not re.search(r'^SUMMARY: %d/%d jobs OK; controls both rejected;[^\n]*\nexit 0\n?\Z' % (n, n), text[name], re.M):
            bad2.append('%s does not end with its summary line (%d/%d jobs OK) and `exit 0`' % (name, n, n))
        # After the controls header, every line must be a job line matched above, the leaves'
        # summary, the SUMMARY line or the exit line: anything else (a failure) is a problem.
        part = text[name].split('# %d jobs' % n, 1)[-1].split('\n', 1)[-1]
        for line in part.splitlines():
            if not (k4.match(line) or k3.match(line) or line.startswith('SUMMARY: %d/%d jobs OK; ' % (n, n))
                    or line == 'exit 0' or line.startswith('class 1 r=11 leaves: 420/420 OK ')):
                bad2.append('%s: unexpected line %r' % (name, line[:120]))
    missing = [j['name'] for j in all_jobs if j['i'] not in covered]
    print('2. results/m3_lean_recheck*.out: %d of %d jobs covered, %d by their own line (sha256 prefix = recorded, '
          'lratcheck VERIFIED) and %d (the class-1 leaves) by the summary line `420/420 OK`; %d missing; %d problems'
          % (len(covered), len(all_jobs), len(covered - by_summary), len(by_summary), len(missing), len(bad2)))
    for b in (bad + bad2)[:10]:
        print('  ' + b)
    for n in missing[:10]:
        print('  missing %s' % n)
    if bad or bad2 or missing:
        print('AUDIT FAILED')
        sys.exit(1)
    print('AUDIT OK: each of the 506 jobs has its own line in the Mac record (sha256, CaDiCaL exit 20, cake_lpr '
          'VERIFIED); in the Linux recheck, 86 have their own line and the 420 leaves are covered by its summary')


# ---------------------------------------------------------------- controls

def lrat_positions(path):
    """Byte offsets in a binary LRAT file: the first byte of the first literal of each added clause,
    of each hint, and of the empty clause's last hint."""
    data = open(path, 'rb').read()
    lits, hints, last_empty_hint, p, n = [], [], None, 0, len(data)

    def num(p):
        while data[p] & 0x80:
            p += 1
        return p + 1

    while p < n:
        kind = data[p]
        p += 1
        if kind == ord('a'):
            p = num(p)                              # clause id
            first, nlits = p, 0
            while data[p] != 0:
                if nlits == 0:
                    lits.append(first)
                p = num(p)
                nlits += 1
            p += 1
            last = None
            while data[p] != 0:
                hints.append(p)
                last = p
                p = num(p)
            p += 1
            if nlits == 0:
                last_empty_hint = last
        elif kind == ord('d'):
            while data[p] != 0:
                p = num(p)
            p += 1
        else:
            raise ValueError('not binary LRAT at byte %d' % (p - 1))
    return lits, hints, last_empty_hint, n


def flip(src, dst, pos, bit):
    data = bytearray(open(src, 'rb').read())
    data[pos] ^= 1 << bit
    with open(dst, 'wb') as f:
        f.write(data)


# (base job, the jobs its proof is then given as): the 3-bit class-1 block at r = 8 with shift 1,
# given as the same block with shift 0; and a class-1 r = 11 leaf, given as the next leaf (same
# header, another cube) and as a leaf with another second gate.
CONTROL_CASES = [(15, [7]), (28, [29, 33])]


def controls():
    """Each base proof must be accepted by both checkers; then both must reject, explicitly, the
    proof given for a different CNF and the proof with one bit flipped at four places."""
    allok = True
    by = {j['i']: j for j in jobs()}
    for ai, others in CONTROL_CASES:
        a = by[ai]
        d = tempfile.mkdtemp(dir=TMP, prefix='ctl-')
        try:
            fa, proof, g = (os.path.join(d, x) for x in ('a.cnf', 'proof.lrat', 'flip.lrat'))
            write_cnf(a, fa)
            c = proc([CADICAL, '-q', '--lrat=true', '--binary=true', fa, proof], d)
            base_cake = cake_verdict(*proc([CAKE, fa, proof], d, CAKE_ENV)[:3])
            base_direct = direct_verdict(*proc([DIRECT, str(ai), proof], d)[:3], a['label'])
            sha_a = sha256(fa) in a['want']
            ok = c[0] == 20 and base_cake[0] and base_direct[0] and sha_a
            print('base: %s %s (sha256 %s): cadical exit %d; cake_lpr %s; m3direct %s -> %s'
                  % (a['label'], a['name'], 'matches' if sha_a else 'MISMATCH', c[0], base_cake[2], base_direct[2],
                     'accepted by both' if ok else 'NOT ACCEPTED'), flush=True)
            allok &= ok
            for bi in others:
                b = by[bi]
                fb = os.path.join(d, 'b.cnf')
                write_cnf(b, fb)
                sha_b = sha256(fb) in b['want']
                k = cake_verdict(*proc([CAKE, fb, proof], d, CAKE_ENV)[:3])
                x = direct_verdict(*proc([DIRECT, str(bi), proof], d)[:3], b['label'])
                good = k[1] and x[1] and sha_b
                print('  (1) proof of %s given as %s %s: cake_lpr %s; m3direct %s -> %s'
                      % (a['label'], b['label'], b['name'], k[2], x[2],
                         'both rejected explicitly' if good else 'NOT BOTH REJECTED EXPLICITLY'), flush=True)
                allok &= good
            lits, hints, empty, n = lrat_positions(proof)
            # bit 0 of a literal's first byte is its sign; bit 1 of a hint's first byte moves it to the
            # next or previous clause id (bit 0 would make it a RAT hint, which an LPR checker may accept)
            spots = [('sign of the first literal of the added clause at 1/2 of the clauses', lits[len(lits) // 2], 0),
                     ('hint at 1/4 of the hints, id +-1', hints[len(hints) // 4], 1),
                     ('hint at 3/4 of the hints, id +-1', hints[3 * len(hints) // 4], 1),
                     ('last hint of the empty clause, id +-1', empty, 1)]
            for what, pos, bit in spots:
                flip(proof, g, pos, bit)
                k = cake_verdict(*proc([CAKE, fa, g], d, CAKE_ENV)[:3])
                x = direct_verdict(*proc([DIRECT, str(ai), g], d)[:3], a['label'])
                good = k[1] and x[1]
                print('  (2) bit %d of byte %d of %d flipped (%s): cake_lpr %s; m3direct %s -> %s'
                      % (bit, pos, n, what, k[2], x[2],
                         'both rejected explicitly' if good else 'NOT BOTH REJECTED EXPLICITLY'), flush=True)
                allok &= good
        finally:
            shutil.rmtree(d, ignore_errors=True)
    print('RUNTIME CONTROLS %s' % ('PASSED: each base proof accepted by both checkers, every altered one '
                                   'rejected explicitly by both' if allok else 'FAILED'), flush=True)
    sys.exit(0 if allok else 1)


def parse_run(a):
    """(mode, options) for `run quick|full [options]`, rejecting unknown or misplaced options and bad
    values. `reproduce.sh` calls `check.py args …` with the same arguments before it fetches or builds."""
    if len(a) < 2 or a[0] != 'run' or a[1] not in ('quick', 'full'):
        raise SystemExit(__doc__)
    mode, rest = a[1], a[2:]
    allowed = {'quick': ('--seed', '--sample', '--workers', '--results'),
               'full': ('--hardest', '--workers', '--results')}[mode]
    o = {}
    if len(rest) % 2:
        raise SystemExit('%s: options take one value each: %s' % (mode, ' '.join(rest)))
    for name, val in zip(rest[::2], rest[1::2]):
        if name not in allowed:
            raise SystemExit('%s: unknown option %s (allowed: %s)' % (mode, name, ', '.join(allowed)))
        if name in o:
            raise SystemExit('%s: %s given twice' % (mode, name))
        o[name] = val
    def num(name, lo, hi, default):
        if name not in o:
            return default
        try:
            v = int(o[name])
        except ValueError:
            raise SystemExit('%s must be an integer, not %r' % (name, o[name]))
        if not lo <= v <= hi:
            raise SystemExit('%s must be between %d and %d' % (name, lo, hi))
        return v
    return mode, dict(seed=o.get('--seed', 'm3v4g11'), nsample=num('--sample', 1, TOTAL, 51) if mode == 'quick' else 0,
                      hardest=num('--hardest', 1, TOTAL, 0) if mode == 'full' else 0,
                      workers=num('--workers', 1, 256, None), results=o.get('--results'))


def main():
    a = sys.argv[1:]
    if a[:1] == ['args']:
        parse_run(['run'] + a[1:])
        return
    os.makedirs(TMP, exist_ok=True)

    if a == ['audit']:
        audit()
    elif a == ['controls']:
        controls()
    elif a[:1] == ['run']:
        mode, o = parse_run(a)
        seed, nsample, hardest, workers = o['seed'], o['nsample'], o['hardest'], o['workers']
        name = 'quick-%s-%d' % (hashlib.sha256(seed.encode()).hexdigest()[:12], nsample) if mode == 'quick' \
            else ('full-hardest%d' % hardest if hardest else 'full')
        results = o['results'] or os.path.join(W, 'results-%s.tsv' % name)
        print('results file: %s' % os.path.relpath(results, ROOT), flush=True)
        run(mode, results, workers, seed, nsample, hardest)
    elif a[:1] == ['summary'] and len(a) == 2:
        summary(a[1])
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
