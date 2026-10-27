import Garden.M3Codes
/-! Must-fail controls for `Garden/M3Codes.lean`. Every `C…` below must FAIL to build. Each is a
theorem of `M3Codes` with its proof copied verbatim from the source (by
`research/circuits/m3codes_controls.py`, which writes this file) onto a mutated statement.
Not part of the library; run with `lake env lean controls/2026-10-27-m3codes-must-fail.lean`.
The witnesses are in `controls/2026-10-27-m3codes-witness.lean`, which builds.

* C1, the moves without the residue shifts (relabelings only). Fails at `decide`: under relabeling alone the 60 codes do not fall into 3 classes.
* C2, the cover condition dropped from the orbit check. Fails at `decide`: the all-`none` table reaches no representative.
* C3, negating bit 0 without flipping output 0 (`n0` for `!n0`). Fails at the final `decide`.
* C4, negating bit 0 without the correction for an output that is the input node `x0`. Fails at the final `decide`; the claim is false (witness file, `neg0_no_fix_false`).
* C5, exchanging the code bits without exchanging the two outputs. Fails at the output bounds and the final `exact`.
* C6, the final theorem at ≤ 12 gates. Fails at the last `omega`.
* C7, the final theorem with the cover condition dropped from `ValidCode`. Fails where `exists_moves` needs a `ValidCode`; the claim is false (witness file, `no_cover_false`).
-/
open CircuitDual GateElim SymCanon M3Codes

namespace Ctl

-- C1
theorem C1_no_shift : ∀ a ∈ vals, ∀ b ∈ vals, ∀ d ∈ vals, ∀ e ∈ vals, covers [a, b, d, e] = true →
    (relabels.any fun os => [1, 2, 3].any fun cls => reaches os (ofTbl a b d e) cls) = true := by
  decide

-- C2
theorem C2_no_cover : ∀ a ∈ vals, ∀ b ∈ vals, ∀ d ∈ vals, ∀ e ∈ vals, (moves.any fun os => [1, 2, 3].any fun cls => reaches os (ofTbl a b d e) cls) = true := by
  decide

-- C3
theorem C3_neg0_output_not_flipped (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 c k shift gs o0 o1 n0 n1) :
    Computes2 (neg0C c) k shift (gs.map (negGate 1)) o0 o1
      (n0 ^^ decide (o0 < 1)) (n1 ^^ decide (o1 < 1)) := by
  obtain ⟨h0, h1, hx⟩ := h
  refine ⟨by rw [List.length_map]; exact h0, by rw [List.length_map]; exact h1, fun x hlen => ?_⟩
  obtain _ | ⟨a, rest⟩ := x
  · simp at hlen
  have hyl : ((!a) :: rest).length = k + 2 := by simpa using hlen
  have hrel : Rel 1 (a :: rest) ((!a) :: rest) := by
    refine ⟨by simp, by simp, fun i => ?_⟩
    rcases i with _ | i <;> simp
  have hr := (rel_run 1 gs _ _ hrel).2.2
  have v : ∀ o, V (gs.map (negGate 1)) (a :: rest) o = (decide (o < 1) ^^ V gs ((!a) :: rest) o) := by
    intro o; unfold V; rw [hr o]; by_cases ho : o < 1 <;> simp [ho]
  rw [v, v]
  have hy := hx _ hyl
  intro res hres
  have := hy res (by simpa [neg0C] using hres)
  have d : ((!a) :: rest).drop 2 = (a :: rest).drop 2 := by cases rest <;> rfl
  rw [d] at this
  simp only [neg0C]
  convert this using 2
  generalize V gs ((!a) :: rest) o0 = p; generalize V gs ((!a) :: rest) o1 = q
  generalize decide (o0 < 1) = d0; generalize decide (o1 < 1) = d1
  revert p q d0 d1; cases n0 <;> cases n1 <;> decide

-- C4
theorem C4_neg0_no_node0_fix (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 c k shift gs o0 o1 n0 n1) :
    Computes2 (neg0C c) k shift (gs.map (negGate 1)) o0 o1
      (!n0) n1 := by
  obtain ⟨h0, h1, hx⟩ := h
  refine ⟨by rw [List.length_map]; exact h0, by rw [List.length_map]; exact h1, fun x hlen => ?_⟩
  obtain _ | ⟨a, rest⟩ := x
  · simp at hlen
  have hyl : ((!a) :: rest).length = k + 2 := by simpa using hlen
  have hrel : Rel 1 (a :: rest) ((!a) :: rest) := by
    refine ⟨by simp, by simp, fun i => ?_⟩
    rcases i with _ | i <;> simp
  have hr := (rel_run 1 gs _ _ hrel).2.2
  have v : ∀ o, V (gs.map (negGate 1)) (a :: rest) o = (decide (o < 1) ^^ V gs ((!a) :: rest) o) := by
    intro o; unfold V; rw [hr o]; by_cases ho : o < 1 <;> simp [ho]
  rw [v, v]
  have hy := hx _ hyl
  intro res hres
  have := hy res (by simpa [neg0C] using hres)
  have d : ((!a) :: rest).drop 2 = (a :: rest).drop 2 := by cases rest <;> rfl
  rw [d] at this
  simp only [neg0C]
  convert this using 2
  generalize V gs ((!a) :: rest) o0 = p; generalize V gs ((!a) :: rest) o1 = q
  generalize decide (o0 < 1) = d0; generalize decide (o1 < 1) = d1
  revert p q d0 d1; cases n0 <;> cases n1 <;> decide

-- C5
theorem C5_swap_outputs_kept (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 c k shift gs o0 o1 n0 n1) :
    Computes2 (swapC c) k shift (gs.map (ren (tr 0 1))) (tr 0 1 o0) (tr 0 1 o1) n0 n1 := by
  obtain ⟨h0, h1, hx⟩ := h
  refine ⟨by rw [List.length_map]; exact tr01_lt _ _ (by omega) h1,
    by rw [List.length_map]; exact tr01_lt _ _ (by omega) h0, fun x hlen => ?_⟩
  have hR := (tr_nodes (k + 2) 0 1 (by omega) (by omega) x hlen gs).2
  have hy := hx (swapIn 0 1 x) (by rw [swapIn_length, hlen])
  have v : ∀ o, V (gs.map (ren (tr 0 1))) x (tr 0 1 o) = V gs (swapIn 0 1 x) o := by
    intro o; unfold V; rw [hR, tr_inv]
  rw [v, v]
  intro res hres
  have := hy res (by
    rw [swapIn_getD0 x (by omega), swapIn_getD1 x (by omega)]; exact hres)
  rw [swapIn_drop2] at this
  exact this

-- C6
theorem C6_twelve_gates (hU : ∀ j ∈ M3Jobs.jobs, (CnfGen.toCNF (M3Gen.cnf j)).Unsat) :
    ∀ c : Code, ValidCode c →
      ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 12 →
        ¬ Computes2 c 4 0 gs o0 o1 n0 n1 := by
  intro c hc gs o0 o1 n0 n1 hle h
  obtain ⟨os, cls, hcls, hos⟩ := exists_moves c hc
  obtain ⟨gs', p0, p1, m0, m1, hl, h'⟩ := computes_applyAll os c 4 0 gs o0 o1 n0 n1 h
  rw [hos] at h'
  obtain ⟨a, b, d, e⟩ := jobs_cover hU cls hcls
  exact M3Reduce.m3v4g11 cls hcls a b d e gs' p0 p1 m0 m1 (by omega) h'

-- C7
theorem C7_no_cover (hU : ∀ j ∈ M3Jobs.jobs, (CnfGen.toCNF (M3Gen.cnf j)).Unsat) :
    ∀ c : Code, (∀ w : Bool × Bool, ∀ r, c w = some r → r < 3) →
      ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 →
        ¬ Computes2 c 4 0 gs o0 o1 n0 n1 := by
  intro c hc gs o0 o1 n0 n1 hle h
  obtain ⟨os, cls, hcls, hos⟩ := exists_moves c hc
  obtain ⟨gs', p0, p1, m0, m1, hl, h'⟩ := computes_applyAll os c 4 0 gs o0 o1 n0 n1 h
  rw [hos] at h'
  obtain ⟨a, b, d, e⟩ := jobs_cover hU cls hcls
  exact M3Reduce.m3v4g11 cls hcls a b d e gs' p0 p1 m0 m1 (by omega) h'

end Ctl
