import Garden.M3Reduce
/-! Must-fail controls for `Garden/M3Reduce.lean`. Every `R…` below must FAIL to build, each with the
original proof verbatim on a mutated statement. Not part of the library; run with
`lake env lean controls/2026-10-27-m3reduce-must-fail.lean`. The witnesses (that `Computes2` is met
by a real 13-gate circuit, and that R1's and R2's mutated claims are false, not just unproved) are
in `controls/2026-10-27-m3reduce-witness.lean`, which builds.

* R1, dropped symmetry condition: the symmetric set includes the code bit `x1`, not only the
  counted bits `x2 … x_{k+1}`. Fails where `blockOK_swap` needs `M3Sound.S k`.
* R2, wrong code table: the decided spec facts for a class number outside 1–3 (no word has a
  residue). Fails at `decide`.
* R3, `elim` one tighter: at most `size − (L + 1)` redundant gates. Fails at the last `omega`.
* R4, fixing a counted bit without adding it to the shift. Fails: the goal the final `rw` leaves is open.
* R5, the no-dead-gate condition without its output exemption (every gate read later). Fails
  at the `obtain` that splits off the two output cases. -/
open CircuitDual GateElim SymBreak SymCanon Reduction Mod3Lower M3Reduce

namespace Ctl

-- R1 the code bit x1 counted as symmetric with the counted bits
theorem R1_symvars_with_code_bit (cls k shift : ℕ) (n0 n1 : Bool) :
    SymOnL (k + 2) (fun u => 1 ≤ u ∧ u < k + 2) (F2 cls shift n0 n1) := by
  rintro u v hu hv x hx ys ⟨a, b, rfl, h⟩
  exact ⟨a, b, rfl, blockOK_swap cls k shift u v hu hv x hx _ h⟩

-- R2 a code table with no residues (class 4)
set_option maxRecDepth 100000 in
theorem R2_no_table : NoConst 4 4 0 ∧ NoLit 4 4 0 := by
  unfold NoConst NoLit <;> decide

-- R3 elim one tighter
theorem R3_elim_plus_one (cls k shift : ℕ) (c : Bool) (hc : NoConst cls k (shift + c.toNat)) (L : ℕ)
    (hLB : ∀ gs o0 o1 n0 n1, Computes2 cls k (shift + c.toNat) gs o0 o1 n0 n1 → L ≤ gs.length)
    (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) (h : Computes2 cls (k + 1) shift gs o0 o1 n0 n1)
    (v : ℕ) (hv1 : 2 ≤ v) (hv2 : v < k + 3) :
    redCount (k + 3) gs {x | x.length = k + 3 ∧ x.getD v false = c} + (L + 1) ≤ gs.length := by
  classical
  set T : Set (List Bool) := {x | x.length = k + 3 ∧ x.getD v false = c} with hTdef
  have hT : ∀ x ∈ T, x.length = k + 3 := fun x hx => hx.1
  obtain ⟨hLt, hEv⟩ := build_inv (k + 3) gs T hT gs.length le_rfl
  have hcnt := build_count (k + 3) gs T gs.length
  set acc := (build (k + 3) gs T gs.length).1 with hacc
  set ρ := (build (k + 3) gs T gs.length).2 with hρ
  have hσ : ∀ i < k + 3, (fixσ v c i).Lt (k + 2) := by
    intro i hi; unfold fixσ; split_ifs <;> simp [Rep.Lt] <;> omega
  set acc' := acc.map (substGate (k + 3) (k + 2) (fixσ v c)) with hacc'
  have hlen' : acc'.length = acc.length := by simp [acc']
  have hin : ∀ y : List Bool, y.length = k + 2 → inRow (k + 3) (fixσ v c) y ∈ T := by
    intro y hy
    rw [inRow_fix (k + 3) v c hv2 y (by omega)]
    have hvl : (y.take v).length = v := by simp only [List.length_take]; omega
    refine ⟨by simp only [List.length_append, List.length_cons, List.length_drop, hvl]; omega, ?_⟩
    rw [List.getD_append_right _ _ _ _ (by omega), hvl, Nat.sub_self]
    rfl
  have hS : ∀ y : List Bool, y.length = k + 2 → ∀ i,
      (run (inRow (k + 3) (fixσ v c) y) acc).getD i false =
        (mv (k + 3) (k + 2) (fixσ v c) i).eval (run y acc') := by
    intro y hy
    have h0 : SRel (k + 3) (k + 2) (fixσ v c) (inRow (k + 3) (fixσ v c) y) y := by
      refine ⟨by simp [inRow], by omega, by simp [inRow]; omega, hσ, fun i => ?_⟩
      unfold mv inRow
      split_ifs with hi
      · simp [List.getD_eq_getElem?_getD, hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), Rep.eval, List.getD_eq_default _ _ (by omega)]
        rfl
    exact (srel_run _ _ _ acc _ _ h0).2.2.2.2
  have hrep : ∀ o, ∃ R : Rep, R.Lt (k + 2 + acc'.length) ∧ ∀ y : List Bool, y.length = k + 2 →
      V gs (inRow (k + 3) (fixσ v c) y) o = R.eval (run y acc') := by
    intro o
    have hLo := hLt o
    have hEo : ∀ y : List Bool, y.length = k + 2 →
        V gs (inRow (k + 3) (fixσ v c) y) o = (ρ o).eval (run (inRow (k + 3) (fixσ v c) y) acc) := by
      intro y hy
      have := hEv _ (hin y hy) o
      rw [List.take_length] at this
      exact this
    generalize hR : ρ o = R at hLo hEo
    cases R with
    | const d => exact ⟨.const d, trivial, fun y hy => hEo y hy⟩
    | lit q b =>
      refine ⟨(mv (k + 3) (k + 2) (fixσ v c) q).neg b, Rep.Lt_neg _ _ _ ?_, fun y hy => ?_⟩
      · simp only [Rep.Lt] at hLo
        unfold mv; split_ifs with hq
        · exact Rep.Lt_mono (by omega) _ (hσ q hq)
        · simp [Rep.Lt]; omega
      · rw [hEo y hy, Rep.eval, hS y hy q, Rep.eval_neg]
  obtain ⟨R0, hR0, e0⟩ := hrep o0
  obtain ⟨R1, hR1, e1⟩ := hrep o1
  obtain ⟨p0, p1, m0, m1, hc'⟩ := computes2_of_reps cls k (shift + c.toNat) hc acc' R0 R1 hR0 hR1
    n0 n1 (fun y hy => by
      rw [← e0 y hy, ← e1 y hy, ← blockOK_fix cls k shift v c hv1 hv2 y hy,
        ← inRow_fix (k + 3) v c hv2 y (by omega)]
      exact h.2.2 _ (by simp [inRow]))
  have := hLB _ _ _ _ _ hc'
  unfold redCount
  omega

-- R4 fixing x_v = c without adding c to the shift
theorem R4_fix_no_shift (cls k shift v : ℕ) (c : Bool) (hv1 : 2 ≤ v) (hv2 : v < k + 3) (y : List Bool)
    (hy : y.length = k + 2) (w : Bool × Bool) :
    BlockOK cls shift (y.take v ++ c :: y.drop v) w ↔ BlockOK cls shift y w := by
  have hvl : (y.take v).length = v := by simp only [List.length_take]; omega
  have hg : ∀ i, i < 2 → (y.take v ++ c :: y.drop v).getD i false = y.getD i false := by
    intro i hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega), List.getElem_take]
  have hcnt : ((y.take v ++ c :: y.drop v).drop 2).count true =
      (y.drop 2).count true + c.toNat := by
    have e1 : (y.take v ++ c :: y.drop v).drop 2 = (y.take v).drop 2 ++ c :: y.drop v :=
      List.drop_append_of_le_length (by omega)
    have e2 : (y.take v ++ y.drop v).drop 2 = (y.take v).drop 2 ++ y.drop v :=
      List.drop_append_of_le_length (by omega)
    rw [List.take_append_drop] at e2
    rw [e1, e2, List.count_append, List.count_append, List.count_cons]
    cases c <;> simp <;> omega
  unfold BlockOK
  rw [hg 0 (by omega), hg 1 (by omega), hcnt]
  refine forall_congr' fun res => imp_congr_right fun _ => ?_
  rw [show res + ((y.drop 2).count true + c.toNat) + shift =
    res + (y.drop 2).count true + (shift + c.toNat) by omega]


-- R5 every gate read later, outputs not exempt
theorem R5_dead_gate_no_output_exemption (cls k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 cls k shift gs o0 o1 n0 n1) (hmin : Min2 cls k shift gs) :
    ∀ j (_ : j < gs.length),
      ∃ i, ∃ hi : i < gs.length, j < i ∧ Reads gs[i] (k + 2 + j) := by
  intro j hj
  by_contra hno
  push Not at hno
  obtain ⟨h0, h1, hnone⟩ := hno
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  have hAlen : (gs.take j).length = j := by simp; omega
  have hB : ∀ g ∈ gs.drop (j + 1), ¬ Reads g (k + 2 + j) := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [List.getElem_drop]
    exact hnone (j + 1 + i) (by simp at hi; omega) (by omega)
  set gsD := gs.take j ++ (gs.drop (j + 1)).map (mapG (dl (k + 2 + j))) with hgsD
  have hDlen : gsD.length = gs.length - 1 := by simp [gsD]; omega
  have hV : ∀ x : List Bool, x.length = k + 2 → ∀ o, o ≠ k + 2 + j →
      V gsD x (dl (k + 2 + j) o) = V gs x o := by
    intro x hx o ho
    have := delete_nodes x (gs.take j) (gs.drop (j + 1)) gs[j]
      (by rw [hx, hAlen]; exact hB) (dl (k + 2 + j) o)
    rw [hx, hAlen] at this
    unfold V
    rw [this, ← hsplit, show up (k + 2 + j) (dl (k + 2 + j) o) = o by unfold up dl; split_ifs <;> omega]
  have hc' : Computes2 cls k shift gsD (dl (k + 2 + j) o0) (dl (k + 2 + j) o1) n0 n1 := by
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · have := h.1; rw [hDlen]; unfold dl; split_ifs <;> omega
    · have := h.2.1; rw [hDlen]; unfold dl; split_ifs <;> omega
    · rw [hV x hx o0 h0, hV x hx o1 h1]; exact h.2.2 x hx
  have := hmin _ _ _ _ _ hc'
  omega

end Ctl
