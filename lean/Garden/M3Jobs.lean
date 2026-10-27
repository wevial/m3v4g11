import Garden.M3Gen

/-!
# The 506 CNFs behind `m3v4g11`, as one list

`M3Reduce.m3v4g11` takes, per code class, the CNFs it needs as five hypotheses. This file names
them all in one list, `jobs`, so that a theorem can take the single hypothesis
`∀ j ∈ jobs, (CnfGen.toCNF (M3Gen.cnf j)).Unsat` and a script can check exactly that list
(`m3export list` prints it). Std only, like `M3Gen`, so the exporter can import it.

Per class `cls` (`M3Codes.jobs_cover` proves these are the CNFs `M3Reduce.m3v4g11` names):
* `k3 cls 0 r` for `1 ≤ r < L0` and `k3 cls 1 r` for `1 ≤ r < L1`: the 3-bit blocks, shift 0 and 1,
  symmetry options only, where `(L0, L1) = elimL cls` are the 3-bit sizes the `elim` bounds use;
* `k4 cls r .whole` for `1 ≤ r ≤ 10`: the 4-bit block with `elim`;
* at `r = 11`: for class 1 the cube cover and its 420 leaves (`M3Gen.cubes 4`), for classes 2
  and 3 the whole CNF.

That is 8 + 9 + 10 + 421 = 448 for class 1 and 9 + 9 + 10 + 1 = 29 each for classes 2 and 3.
-/

namespace M3Jobs
open M3Gen

/-- The 3-bit sizes `(L0, L1)` (shift 0, shift 1) the `elim` bounds use; `M3Sound.elimOf`. -/
def elimL : Nat → Nat × Nat
  | 1 => (9, 10)
  | _ => (10, 10)

/-- The 4-bit block, class `cls`, shift 0, `r` gates, with `elim`; `M3Sound.job`. -/
def k4 (cls r : Nat) (kind : Kind) : Job := ⟨cls, 4, 0, r, some (elimL cls), kind⟩

/-- The 3-bit block, class `cls`, shift `shift`, `r` gates, no `elim`; `M3Reduce.job3`. -/
def k3 (cls shift r : Nat) : Job := ⟨cls, 3, shift, r, none, .whole⟩

/-- The 3-bit CNFs for class `cls`: shift 0 at `1 ≤ r < L0`, shift 1 at `1 ≤ r < L1`. -/
def jobs3 (cls : Nat) : List Job :=
  (List.range' 1 ((elimL cls).1 - 1)).map (k3 cls 0) ++ (List.range' 1 ((elimL cls).2 - 1)).map (k3 cls 1)

/-- The 4-bit CNFs for class `cls` at `r = 11`: class 1's cube cover and 420 leaves, else whole. -/
def jobs11 : Nat → List Job
  | 1 => k4 1 11 .cover :: (cubes 4).map fun q => k4 1 11 (.leaf q)
  | cls => [k4 cls 11 .whole]

/-- The CNFs for class `cls`. -/
def jobsOf (cls : Nat) : List Job :=
  jobs3 cls ++ (List.range' 1 10).map (fun r => k4 cls r .whole) ++ jobs11 cls

/-- **The 506 CNFs.** -/
def jobs : List Job := [1, 2, 3].flatMap jobsOf

set_option maxRecDepth 100000 in
theorem jobs_length : jobs.length = 506 := by decide

end M3Jobs
