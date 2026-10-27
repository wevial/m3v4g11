import Garden.M3Jobs

/-!
# `m3export`: write an `m3v4g11` job's Lean-generated CNF as DIMACS

    m3export <class> <k> <shift> <r> <kind> <cube> <elimL> <file>
    m3export list                  -- the 506 jobs of `M3Jobs.jobs`, one line each, in order
    m3export job <i> <file>        -- job `i` of that list

with `kind` ∈ {whole, leaf, cover}, `cube` as `m3v4g11_run.cube_str` writes it (`a,b:fff:c,d`, or `-`),
and `elimL` as `L0,L1` or `-`, the fields of a row of `research/circuits/m3v4g11_results.tsv`.
Glue, not verified: the argument parsing and the file writing.
-/

open M3Gen

def parsePair (s : String) : Option (Nat × Nat) :=
  match s.splitOn "," with
  | [a, b] => do pure (← a.toNat?, ← b.toNat?)
  | _ => none

def parseBit : Char → Option Bool
  | '0' => some false
  | '1' => some true
  | _ => none

def parseCube (s : String) : Option ((Nat × Nat) × (Bool × Bool × Bool) × (Nat × Nat)) :=
  match s.splitOn ":" with
  | [p1, t, p2] => do
    let a ← parsePair p1
    let b ← parsePair p2
    match t.toList with
    | [x, y, z] => pure (a, (← parseBit x, ← parseBit y, ← parseBit z), b)
    | _ => none
  | _ => none

def bitStr (b : Bool) : String := if b then "1" else "0"

/-- `m3v4g11_run.cube_str`: `a,b:fff:c,d`. -/
def cubeStr : (Nat × Nat) × (Bool × Bool × Bool) × (Nat × Nat) → String
  | ((a, b), (x, y, z), (c, d)) => s!"{a},{b}:{bitStr x}{bitStr y}{bitStr z}:{c},{d}"

/-- A job as the eight-argument form's first seven fields, tab-separated. -/
def jobLine (j : Job) : String :=
  let (kind, cube) := match j.kind with
    | .whole => ("whole", "-") | .cover => ("cover", "-") | .leaf q => ("leaf", cubeStr q)
  let e := match j.elimL with | some (a, b) => s!"{a},{b}" | none => "-"
  s!"{j.cls}\t{j.k}\t{j.shift}\t{j.r}\t{kind}\t{cube}\t{e}"

def write (j : Job) (path : String) : IO Unit := do
  let F := cnf j
  IO.FS.withFile path .write fun h => do
    h.putStr (CnfGen.header (CnfGen.maxVar F) F.length)
    for cl in F do h.putStr (CnfGen.clauseLine cl)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for (j, i) in M3Jobs.jobs.zipIdx do IO.println s!"{i}\t{jobLine j}"
    return 0
  | ["job", i, path] =>
    let some j := i.toNat?.bind (M3Jobs.jobs[·]?) | IO.eprintln "no such job"; return 2
    write j path
    return 0
  | [c, k, s, r, kind, cube, e, path] =>
    let some cls := c.toNat? | return 2
    let some k := k.toNat? | return 2
    let some sh := s.toNat? | return 2
    let some r := r.toNat? | return 2
    let elimL ← if e == "-" then pure none else
      match parsePair e with
      | some p => pure (some p)
      | none => do IO.eprintln "bad elimL"; return 2
    let kd ← match kind, parseCube cube with
      | "whole", _ => pure Kind.whole
      | "cover", _ => pure Kind.cover
      | "leaf", some q => pure (Kind.leaf q)
      | _, _ => do IO.eprintln "bad kind/cube"; return 2
    let F := cnf { cls, k, shift := sh, r, elimL, kind := kd }
    IO.FS.withFile path .write fun h => do
      h.putStr (CnfGen.header (CnfGen.maxVar F) F.length)
      for cl in F do h.putStr (CnfGen.clauseLine cl)
    return 0
  | _ => IO.eprintln "usage: m3export <class> <k> <shift> <r> <kind> <cube> <elimL> <file>"; return 2
