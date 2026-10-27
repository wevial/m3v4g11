import Garden.M3Direct

/-!
# `m3direct`: check an LRAT proof against job `i` of `M3Jobs.jobs`, built in memory

    m3direct <i> <proof>

`i` indexes `M3Jobs.jobs` (`m3export list` prints the list, one line per job, in order). The proof
is CaDiCaL's LRAT, binary or text. Prints `s VERIFIED UNSAT …` and exits 0 iff
`Garden.LratDirect.check` accepts, which implies the CNF is unsatisfiable (`M3Direct.sound`);
otherwise `s NOT VERIFIED …` and exit 1; exit 2 for a bad index.

Trusted, not verified: this loop, as in `LratDirect.lean`. It reads the file in blocks, in order,
feeds each to `feed` until EOF or until the state is `stopped`, then applies `finish`. That is
`run cnf blocks` for the blocks read.
-/

open Garden.LratDirect CnfGen

def blockSize : USize := 1024 * 1024

partial def readLoop {n : Nat} (h : IO.FS.Handle) (st : St n) : IO (St n) := do
  if st.stopped then return st
  let b ← h.read blockSize
  if b.isEmpty then return st
  readLoop h (feed st b)

def resultName : Std.Tactic.BVDecide.LRAT.Internal.Result → String
  | .success => "success"
  | .outOfProof => "outOfProof"
  | .rupFailure => "rupFailure"

def main (args : List String) : IO UInt32 := do
  let some (i, path) := (match args with
    | [i, p] => i.toNat?.map fun k => (k, p)
    | _ => none)
    | IO.eprintln "usage: m3direct <i> <proof>"; return 2
  let some F := Garden.M3Direct.cnf? i
    | IO.eprintln s!"job {i}: no such job (M3Jobs.jobs has {M3Jobs.jobs.length})"; return 2
  let t0 ← IO.monoMsNow
  let cnf := toCNF F
  let h ← IO.FS.Handle.mk path .read
  let st ← readLoop h (init cnf)
  let o := (finish st).outcome
  let dt := (← IO.monoMsNow) - t0
  let what := s!"job {i}: {cnf.clauses.size} clauses, {cnf.numLiterals} vars; " ++
    s!"{(o.fmt.map Fmt.name).getD "empty"} LRAT, {o.actions} actions; {dt} ms"
  if o.verified then
    IO.println s!"s VERIFIED UNSAT ({what})"; return 0
  else
    let why := match o.err with | some e => s!"parse error: {e}" | none => resultName o.result
    IO.println s!"s NOT VERIFIED ({why}; {what})"; return 1
