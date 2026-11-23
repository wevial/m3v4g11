# Kulikov's `m3v4g11` is unsatisfiable: no 11-gate MOD3 block over B2

## The question

A standard way to compute `MOD3(x_1, …, x_n) = [x_1 + … + x_n ≡ 0 (mod 3)]` is a chain of identical blocks. Each block reads the count so far, reduced mod 3 and stored on two wires. It adds four more input bits and passes on the new count in the same two-wire code. A block of `s` gates gives circuits of about `s·n/4` gates. The best known blocks give about `3n`.

In 2018 A. S. Kulikov asked whether such a block of **11** gates exists over B2 (any two-input gates), which would give `2.75n + O(1)`. The question is the first open problem in his repository [`alexanderskulikov/circuit-synthesis`](https://github.com/alexanderskulikov/circuit-synthesis#open-problems) ([`openproblems/m3v4g11.py`](https://github.com/alexanderskulikov/circuit-synthesis/blob/master/openproblems/m3v4g11.py)):

> The script openproblems/m3v4g11.py generates a CNF formula with 1831 variables and 642938 clauses. Most probably, it is unsatisfiable. But if it is satisfiable, then C(MOD_3) <= 2.75n+O(1).

The two-wire code is part of the question. Each of the four words `00, 01, 10, 11` may mean residue 0, 1 or 2, or nothing, as long as every residue has at least one word. That allows 60 codes.

## The answer

**No.** For each of the 60 codes, no circuit of at most 11 gates over B2 computes the block. That is a Lean 4 theorem, with one hypothesis: 506 CNF formulas generated in Lean are unsatisfiable. Each of the 506 has been solved twice, on two machines, with two CaDiCaL versions, and every proof was accepted by a formally verified checker (`cake_lpr` on one machine, Lean's own on the other). `./reproduce.sh full` re-solves all 506 and checks every proof with two verified checkers. In Docker on 4 cores, starting from an empty volume, that took 54 minutes.

## The theorem

`lean/Garden/M3Codes.lean`, as `#check` prints it:

```lean
M3Codes.m3v4g11_all : (∀ j ∈ M3Jobs.jobs, (CnfGen.toCNF (M3Gen.cnf j)).Unsat) →
  ∀ (c : M3Codes.Code),
    M3Codes.ValidCode c →
      ∀ (gs : List CircuitDual.Gate) (o0 o1 : ℕ) (n0 n1 : Bool),
        gs.length ≤ 11 → ¬M3Codes.Computes2 c 4 0 gs o0 o1 n0 n1
```

The theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only. The definitions below are the whole statement. Read them yourself; they are short.

```lean
abbrev Code := Bool × Bool → Option ℕ           -- the residue each word (w0, w1) means, or none

def ValidCode (c : Code) : Prop :=
  (∀ w : Bool × Bool, ∀ r, c w = some r → r < 3) ∧ ∀ r < 3, ∃ w : Bool × Bool, c w = some r

def BlockOK (c : Code) (shift : ℕ) (x : List Bool) (w : Bool × Bool) : Prop :=
  ∀ res, c (x.getD 0 false, x.getD 1 false) = some res →
    c w = some ((res + (x.drop 2).count true + shift) % 3)

def Computes2 (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) : Prop :=
  o0 < k + 2 + gs.length ∧ o1 < k + 2 + gs.length ∧
    ∀ x : List Bool, x.length = k + 2 → BlockOK c shift x (n0 ^^ V gs x o0, n1 ^^ V gs x o1)
```

- **The circuit** (`Garden/CircuitDual.lean`, `GateElim.V`): a list of gates `⟨a, b, op⟩`, where `op : Bool → Bool → Bool` is any truth table. The nodes, in order, are the inputs `x0 … x5` and then the gates; gate `j` is node `6 + j` and reads nodes `a` and `b`. A node not yet defined reads `false`. `V gs x i` is node `i`'s value on input `x`. The size is `gs.length`.
- **The block**: `x0 x1` is the input word, and `x2 … x5` are the four bits to add. The outputs are any two nodes, each optionally negated (`n0`, `n1`). Whenever the input word means a residue `res`, the output word must mean `res + x2 + … + x5 (mod 3)`. An input word that means nothing is a don't-care.
- **`ValidCode`**: every word means a residue mod 3 or nothing, and each of 0, 1, 2 has at least one word. `validCode_iff` and `codes60_length` show that exactly 60 tables satisfy it.

Compared with Kulikov's model, this model only adds circuits: it allows free output negation, reading an input as an output, and reading a constant `false`. Kulikov's circuits are among these, so the "no" covers them.

**The hypothesis.** `M3Jobs.jobs` (`Garden/M3Jobs.lean`, about 20 lines) lists 506 jobs. `M3Gen.cnf j` (`Garden/M3Gen.lean`) is the CNF of job `j`: "some circuit of `r` gates with this shape computes this block". `Unsat` is `Std.Sat.CNF.Unsat`, the property Lean core's verified LRAT checker concludes. Nothing in the hypothesis mentions circuits. The table groups the 506 jobs by code class (the classes are defined in the next section). All sizes `r` start at 1.

| class (representative code) | 3-bit blocks, shift 0 and 1 | 4-bit block, r = 1 … 10 | 4-bit block, r = 11 | CNFs |
|---|---|---|---|---|
| 1 (`00→0 01→1 10→2 11→2`) | r < 9 and r < 10 | whole | split into 420 cubes, plus their cover | 448 |
| 2 (`00→0 01→1 10→1 11→2`) | r < 10, r < 10 | whole | whole | 29 |
| 3 (`00→0 01→1 10→2 11 unused`) | r < 10, r < 10 | whole | whole | 29 |

A second theorem, `M3Codes.m3v4g11_all_direct`, states the same conclusion with a different hypothesis: "Lean's verified LRAT checker accepted some proof for every job, against the CNF built in memory". That hypothesis is what the `m3direct` executable reports.

## How it is proved

- **60 codes, 3 classes** (`M3Codes`). Three moves each turn a circuit for one code into a circuit of the same size for the resulting code: exchanging the code's two bits (`computes_swap`), negating its bit 0 (`computes_neg0`), and adding 1 to every residue (`computes_shift`). Using `decide` over all 256 tables, `classify` shows that one of 24 sequences of these moves takes every valid code to one of three representatives.
- **Per class** (`M3Reduce.m3v4g11`). A smallest circuit can be put into the form the CNF describes: no redundant or dead gate, sorted inputs, canonical gate order, the counted bits in symmetric order, and the gate-elimination bound. The gate-elimination bound uses the classical argument: fixing one counted bit leaves a 3-bit block, and the 3-bit CNFs bound its size. A circuit in this form satisfies the CNF (`M3Sound.adm3_sat`), and for class 1 at r = 11 the 420 cubes cover every case.
- **Controls** (`lean/controls/`). The 17 must-fail controls each apply an original proof to a slightly wrong statement, and each fails with the error its mutation causes. Examples: shifts left out of the classification, output negation not flipped, the symmetric set including a code bit, the bound one tighter, 12 gates. Three witness files build. They show two things: a real 13-gate circuit meets `Computes2` for 24 of the 60 codes (so the theorem is not vacuous), and several of the mutated claims are false.

## What is trusted

**Checked by the Lean kernel:** everything from "the 506 CNFs are unsatisfiable" to the theorem, including the reduction from 60 codes to 3 and the soundness of `m3direct`'s checking function (`LratDirect.check_sound`).

**Trusted on the formal side:** the Lean 4.33.1 toolchain, including the prebuilt core library it ships (`Init`, `Std`, `Lean`), and the definitions above, read by eye. Mathlib is compiled from source here, with no prebuilt cache, so its proofs are kernel-checked on your machine too. The proof imports only 10 Mathlib modules. With their imports that is 982 modules of Mathlib and its dependencies, compiled in about 6 minutes on 4 cores.

**Established by computation, outside the kernel:** that the 506 CNFs are unsatisfiable. There are three independent records:

1. **The original run** (2026-10-27, an Apple M4 Pro laptop). A Python encoder wrote the CNFs, and `results/m3_cnf_compare.out` shows that Lean's generator writes the same bytes (653 of 653 jobs). CaDiCaL 3.0.1 solved them. Every proof was accepted by `cake_lpr`, CakeML's LRAT checker, which is verified down to machine code, including its DIMACS parser. The record is `results/m3v4g11_results.tsv`.
2. **A Linux re-check** (2026-10-27). Lean's exporter wrote each DIMACS file, and each file's sha256 had to equal the original run's. CaDiCaL 2.1.2 solved each CNF, and Lean core's verified checker `lratcheck` accepted every proof (`results/m3_lean_recheck.out` and `results/m3_lean_recheck_k3.out`). Those files list 86 of the jobs one per line. For the 420 class-1 cubes (the leaves), the Linux re-check driver printed only a summary (`420/420 OK`), so for those jobs this record is that summary.
3. **Your run** (`./reproduce.sh full`). Lean's exporter, `m3export`, writes each DIMACS file from `M3Jobs.jobs`, and each file's sha256 must equal the one in the original run's record. CaDiCaL 3.0.1 solves each CNF. Both `cake_lpr` (against the DIMACS file) and `m3direct` (against the CNF built in memory, with no file) must accept the proof.

In run 3 you trust your machine and `scripts/check.py`. You also trust the compiled code of the exporter and the checkers: the Lean compiler and runtime for `m3export` and `m3direct`, and your `gcc` for `cake_lpr`'s verified assembly and its small C shim. CaDiCaL needs no trust, because its proofs are checked. `m3direct`'s IO loop (about ten lines in `lean/M3Direct.lean`) is read by eye.

## What is open

- **12 or 13.** The best known blocks have 13 gates (class 1: the 9-gate 3-bit block, then the 4-gate 1-bit block) and 14 gates (class 3). A one-hour search at 12 gates found nothing for any class and proved nothing.
- **Blocks whose output code is the input code shifted by a constant residue.** Such blocks would chain just as well, but they are not part of Kulikov's question and are not covered.
- **Mathlib.** The proof imports 10 Mathlib modules (`Finset`, `split_ifs`, `Nat.find` and similar). A port to Lean core alone would remove the last large dependency. That port has not been done.

## Reproduce

Use Linux on x86-64 (tested) or arm64 (untested). You need bash, curl, git, gcc/g++, make, python3 ≥ 3.9 (standard library only), zstd and tar. Allow 5 GB of disk for the tools, Mathlib and the build. The re-check driver (`scripts/check.py`) starts a CNF only if free disk would stay above 10 GB (`M3_DISK_FLOOR_GB`) after every running proof reaches its estimated size (8 MB per second the job took originally, plus 50 MB). So `full` needs at least 19 GB free to start the hardest CNF, and about 40 GB to run the four hardest at once; with less it runs them fewer at a time. 10 GB of RAM is enough with 4 workers.

```
./reproduce.sh fetch     # the only step that uses the network
./reproduce.sh quick     # (runs fetch first if needed): everything below, on a seeded sample of 51 CNFs
./reproduce.sh full      # every CNF
```

**`fetch`** downloads these, each checked against a pin at the top of `reproduce.sh`:
- the Lean 4.33.1 toolchain, by sha256;
- CaDiCaL `rel-3.0.1`, by the tarball's sha256, or else by the sha256 of its file tree;
- `cake_lpr` `a4323b20`, whose three source files are checked against the pins and against the repository's own `cake_lpr.sha256`;
- Mathlib and its 8 dependencies, as shallow git fetches of the commits in `lean/lake-manifest.json`. These are sources only.

**`quick` and `full`** then run these steps, all offline:
1. Build CaDiCaL, `cake_lpr`, and the three executables of `lean/direct/`. That package has no Mathlib.
2. `lake build` the proof, then print the main theorem and the axioms of 14 theorems (`lean/Axioms.lean`). This step fails if any theorem lists an axiom outside the standard three.
3. Run the 17 must-fail controls and the 3 witness files (`scripts/lean_controls.py`).
4. Audit the records. `m3export list` prints the 506 jobs. Each must have its own line in the original run's record, with the sha256 it is checked against later. In the Linux re-check record, 86 jobs must each have their own line, and the 420 class-1 leaves their summary line. Any failure line fails the audit.
5. Runtime controls. Both checkers (`cake_lpr` and `m3direct`) must accept two real proofs. Both must then explicitly reject each proof given for another CNF, and each proof with one bit flipped at four places.
6. Re-check. `quick` takes a uniform sample of 51 jobs; choose your own sample with `--seed <any string>`, or its size with `--sample N`. `full` takes all 506, hardest first; `--hardest K` takes only the K hardest. Results go to `work/results-*.tsv`, one line per CNF. Rerunning the same command validates every earlier line before resuming. `python3 scripts/check.py summary <file>` re-validates a results file.

**In Docker**, as tested:

```
docker build -t m3v4g11 - <<'EOF'
FROM ubuntu:24.04@sha256:68ee22004a9109b44973313b02ff7b1de250f1de0f5ecb628d73f579aaff33ac
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      build-essential ca-certificates curl git python3 zstd && rm -rf /var/lib/apt/lists/*
EOF
docker volume create m3v4g11
docker run --rm --memory 10g --memory-swap 10g --cpus 4 -v m3v4g11:/m3 -v "$PWD":/src:ro m3v4g11 \
  bash -c 'cp -a /src/. /m3/ && /m3/reproduce.sh fetch'
docker run --rm --network none --memory 10g --memory-swap 10g --cpus 4 -v m3v4g11:/m3 m3v4g11 /m3/reproduce.sh full
```

## Timings

Measured on 2026-10-27 in Docker (`--memory 10g --memory-swap 10g --cpus 4`) on an x86-64 machine (gembox, 16 cores, 27 GB). The `full` run started from an empty volume. `fetch` used the network; every later step ran with `--network none`.

**`full`** passed (`ALL CHECKS PASSED (full)`, 506/506 CNFs OK, 0 failures):

| step | wall |
|---|---|
| `fetch`: Lean toolchain, CaDiCaL, `cake_lpr`, Mathlib and 8 dependencies (sources) | 26 s |
| build CaDiCaL (21 s), `cake_lpr`, `m3export`/`m3direct`/`lratcheck` | 25 s |
| build the Lean proof: 982 Mathlib-side modules from source, then the 21 garden files | 6 min 17 s |
| axioms; Lean controls; audit | 2 s; 14 s; 1 s |
| runtime controls | 1 min 57 s |
| re-check of all 506 CNFs, 4 workers | 44 min 33 s |
| **in all** | **53 min 29 s**, plus 26 s for `fetch` |

The re-check took 2.9 CPU-hours: CaDiCaL 1.58, `m3direct` 0.96, `cake_lpr` 0.36. The re-check wrote and deleted 23.4 GB of proofs; the largest proof was 3.6 GB (job 476, class 2 at r = 11). Peak RSS was 2,051 MiB for `cake_lpr` (its heap), 385 MiB for `m3direct` and 71 MiB for CaDiCaL. Afterwards the volume held 4.7 GB.

**`quick`** (the default seed, 51 CNFs) passed on the same machine in a separate container: 15 min 22 s for the re-check, after the same build.

## Layout

- `reproduce.sh`: fetch, build and check, as above.
- `lean/`: the Lake project.
  - `Garden/`: the 21 files of the proof, which are the import closure of `M3Codes` and `M3Direct`. `CnfSpecs` and `CnfLeaves` are MOD3₆ job lists that `LratDirect` imports; they are unused here.
  - `M3Export.lean`, `M3Direct.lean` and `LratCheck.lean`: the executables.
  - `Axioms.lean`: prints the main theorem and the axioms of 14 theorems.
  - `direct/`: the Std-only package for the executables.
  - `controls/`: the must-fail controls and the witnesses.
- `scripts/check.py`: the re-check driver; `scripts/lean_controls.py`: the Lean controls.
- `results/`:
  - `m3v4g11_results.tsv`: the original run, one line per CNF solved, including SAT runs at sizes the theorem does not use. `mac_pins_m3.txt` holds the pins for the original run.
  - `m3_lean_recheck.out` and `m3_lean_recheck_k3.out`: the Linux re-check.
  - `m3_cnf_compare.out`: Lean's CNFs are byte-identical to the original ones.
  - `m3v4g11_audit.out`: the original run's audit. `m3v4g11_codes.out`: the 60 codes in 3 classes, by a Python script that came before `M3Codes`.
  - `as-run/`: the scripts behind the files in `results/`. `m3v4g11.py` and `optimal_circuit.py` are the encoder versions last pinned in `mac_pins_m3.txt`. `m3v4g11_run.py` is that version with a personal name removed from one comment.

## Credits

- The problem and its CNF are A. S. Kulikov's (`circuit-synthesis`, 2018, linked above).
- The code of class 1 is the one used by A. S. Kulikov, D. Pechenev and N. Slezkin, *SAT-based circuit local improvement*, MFCS 2022, arXiv:2102.12579. Their 9-gate 3-bit block (MID3) matches the size found here.
- Kulikov's CNF uses the SAT encoding of circuits of A. Kojevnikov, A. S. Kulikov and G. Yaroslavtsev, *Finding efficient circuits using SAT-solvers*, SAT 2009. The encoding here is of the same kind.

**Who did this.** The work was done by Claude, Anthropic's AI model, in a research repository that Ko Vial gave it for its own questions. That covers the SAT encoding and the search, the Lean formalization, the checker integration and the re-checks. This package comes from that repository. The Lean sources are unchanged, except `Axioms.lean`, which is new here. Some header comments in those files record the files' history (what was proved when). Their comments that point at `research/…` files or logs refer to that repository, which is not public.

## License

Apache License 2.0; see `LICENSE`. CaDiCaL, `cake_lpr` and Mathlib are not included in this repository; they are downloaded under their own licenses.
