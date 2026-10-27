import Garden.LratDirect
import Garden.M3Jobs

/-!
# `m3direct`: check an LRAT proof against one of the 506 `m3v4g11` CNFs, built in memory

`LratDirect` for `M3Jobs.jobs`: the executable (`M3Direct.lean`) is given an index `i` and a proof
file. It builds `toCNF (M3Gen.cnf j)` for `j = M3Jobs.jobs[i]` in memory and feeds the proof
through `LratDirect.check`, so no DIMACS writer or parser stands between the hypothesis of
`M3Codes.m3v4g11_all` and the verdict. `check_sound` makes the verdict a proof of `Unsat`;
`M3Codes.m3v4g11_all_direct` states the theorem with these verdicts as hypotheses.

Std only, like `LratDirect`, so `m3direct` builds with the toolchain alone (`research/lean/direct/`).
-/

namespace Garden.M3Direct
open Garden.LratDirect CnfGen

/-- The CNF of job `i`, as DIMACS integers; `none` past the end of the list. -/
def cnf? (i : Nat) : Option (List (List Int)) := M3Jobs.jobs[i]?.map M3Gen.cnf

/-- **A verified check of job `i` proves its CNF unsatisfiable.** -/
theorem sound {i : Nat} {F : List (List Int)} (hF : cnf? i = some F) (bs : List ByteArray)
    (h : (check (toCNF F) bs).verified = true) :
    ∃ j, M3Jobs.jobs[i]? = some j ∧ (toCNF (M3Gen.cnf j)).Unsat := by
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hF
  exact ⟨j, hj, check_sound _ bs h⟩

end Garden.M3Direct
