import Garden.M3Sound
/-! Must-fail controls for `Garden/M3Sound.lean`. Every `M…` below must FAIL to build, each with the
original proof verbatim on a mutated statement. Not part of the library; run with
`lake env lean controls/2026-10-27-m3-must-fail.lean`. The witness that `Adm3` is satisfiable, so
the theorems are not vacuous, is `controls/2026-10-27-m3-witness.lean` (builds). These show that a
reused proof no longer fits a mutated claim, which is weaker than showing the claim false. -/
open CircuitDual GateElim SymCanon Mod3Lower M3Sound

namespace Ctl
variable {cls k shift : ℕ} {elimL : Option (ℕ × ℕ)} {gs : List Gate} {o0 o1 : ℕ} {n0 n1 : Bool}

-- M1 the output clauses of the complemented projection
theorem M1_out_negated (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (o : ℕ) (ho : o < 2) :
    ∀ e ∈ M3Gen.outCls (k + 2) gs.length o (fun t => (M3Gen.proj cls k shift o t).map (!·)),
      Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  intro e he
  simp only [M3Gen.outCls, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap] at he
  rcases he with (rfl | ⟨c, hc, rfl⟩) | ⟨i, -, t, ht, he⟩
  · exact ⟨M3Gen.pos (.osel o (onode o0 o1 o)), List.mem_map.mpr
      ⟨_, (CnfSound.mem_gates _ _ _).mpr (onode_lt h o), rfl⟩, by simp [ev, M3Gen.pos]⟩
  · obtain ⟨a, b, rfl, hab⟩ := CnfSound.mem_combs2 _ _ hc
    have hlt := CnfSound.sublist_pair_lt _ (CnfSound.gates_sorted _ _) a b hab
    by_cases ha : onode o0 o1 o = a
    · refine ⟨M3Gen.ng (.osel o b), by simp [M3Gen.ng], ?_⟩
      simp [ev, M3Gen.ng]; omega
    · exact ⟨M3Gen.ng (.osel o a), by simp [M3Gen.ng], by simp [ev, M3Gen.ng, ha]⟩
  · rw [CnfSound.mem_rows] at ht
    by_cases hoi : onode o0 o1 o = i
    swap
    · split at he <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at he
      all_goals rcases he with rfl | rfl <;>
        exact ⟨M3Gen.ng (.osel o i), by simp [M3Gen.ng], by simp [ev, M3Gen.ng, hoi]⟩
    subst hoi
    have hout : ∀ b, M3Gen.proj cls k shift o t = some b →
        (oneg n0 n1 o ^^ CnfSound.nodeV (k + 2) gs t (onode o0 o1 o)) = b := by
      intro b hb
      obtain ⟨A, hA, hall⟩ := proj_spec cls k shift o t b hb
      have := hall _ (h.computes t ht A hA)
      unfold M3Gen.bit at this
      unfold oneg onode
      split_ifs at this ⊢ <;> simpa using this
    have h3 : ∀ {l1 l2 l3 : M3Gen.L}, (ev (k + 2) gs o0 o1 n0 n1 l2.1 = l2.2 ∨
        ev (k + 2) gs o0 o1 n0 n1 l3.1 = l3.2) → Good (ev (k + 2) gs o0 o1 n0 n1) (.cl [l1, l2, l3]) := by
      intro l1 l2 l3 h
      rcases h with h | h
      · exact ⟨l2, by simp, h⟩
      · exact ⟨l3, by simp, h⟩
    split at he
    · simp at he
    all_goals rename_i hp
    all_goals simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    all_goals have hv := hout _ hp
    all_goals
      rcases he with rfl | rfl <;> refine h3 ?_ <;> simp only [ev, CnfSound.ev, M3Gen.pos, M3Gen.ng] <;>
          revert hv <;> cases oneg n0 n1 o <;> cases CnfSound.nodeV (k + 2) gs t (onode o0 o1 o) <;> simp

-- M2 the word clauses of the block with output shift + 1
theorem M2_word_shift (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) :
    ∀ e ∈ M3Gen.wordCls (k + 2) gs.length (M3Gen.allowed cls k (shift + 1)),
      Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  intro e he
  simp only [M3Gen.wordCls, List.mem_flatMap] at he
  obtain ⟨t, ht, he⟩ := he
  rw [CnfSound.mem_rows] at ht
  split at he
  · simp at he
  rename_i A hA
  split_ifs at he
  · simp at he
  have hy : ∀ o, ∀ e ∈ M3Gen.yDef (k + 2) gs.length o t, Good (ev (k + 2) gs o0 o1 n0 n1) e := by
    intro o e he
    simp only [M3Gen.yDef, List.mem_cons, List.mem_flatMap] at he
    rcases he with rfl | ⟨i, -, he⟩
    · trivial
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    by_cases hoi : onode o0 o1 o = i
    · subst hoi
      rcases he with rfl | rfl | rfl | rfl <;> simp only [Good, ev, CnfSound.ev, M3Gen.pos, M3Gen.ng,
        List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] <;>
        cases oneg n0 n1 o <;> cases CnfSound.nodeV (k + 2) gs t (onode o0 o1 o) <;> simp
    · rcases he with rfl | rfl | rfl | rfl <;>
        exact ⟨M3Gen.ng (.osel o i), by simp [M3Gen.ng], by simp [ev, M3Gen.ng, hoi]⟩
  simp only [List.mem_append] at he
  rcases he with (he | he) | he
  · exact hy 0 e he
  · exact hy 1 e he
  · simp only [List.mem_map, List.mem_filter] at he
    obtain ⟨⟨w1, w2⟩, ⟨-, hw⟩, rfl⟩ := he
    have hin := h.computes t ht A hA
    have e0 : ev (k + 2) gs o0 o1 n0 n1 (.y 0 t) = (n0 ^^ CnfSound.nodeV (k + 2) gs t o0) := rfl
    have e1 : ev (k + 2) gs o0 o1 n0 n1 (.y 1 t) = (n1 ^^ CnfSound.nodeV (k + 2) gs t o1) := rfl
    by_cases h1 : (n0 ^^ CnfSound.nodeV (k + 2) gs t o0) = w1
    · by_cases h2 : (n1 ^^ CnfSound.nodeV (k + 2) gs t o1) = w2
      · exfalso
        rw [h1, h2] at hin
        exact absurd hin (by simpa using hw)
      · exact ⟨(.y 1 t, !w2), by simp, by rw [e1]; revert h2; cases w2 <;> simp⟩
    · exact ⟨(.y 0 t, !w1), by simp, by rw [e0]; revert h1; cases w1 <;> simp⟩

-- M3 elim with B_0 one smaller than the certified bound allows
theorem M3_elim_tighter (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (L : ℕ × ℕ) (hL : elimL = some L) :
    ∀ e ∈ M3Gen.elimCls (k + 2) gs.length (List.range' 2 k) (L.1 + 1, L.2), Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  refine lift_good _ _ _ _ _ _ _ (fun e he => ?_)
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.contains_iff_mem,
    List.mem_range', List.mem_append] at he
  obtain ⟨v, ⟨hvn, i, hi, rfl⟩, (he | he) | he⟩ := he
  · exact CnfSound.kCls_good (k + 2) gs o0 n0 h.normal _ e he
  · exact CnfSound.e1Cls_good (k + 2) gs o0 n0 h.shaped _ false _
      (by have := (h.elim L hL (2 + 1 * i) (by omega) (by omega)).1; omega) e he
  · exact CnfSound.e1Cls_good (k + 2) gs o0 n0 h.shaped _ true _
      (by have := (h.elim L hL (2 + 1 * i) (by omega) (by omega)).2; omega) e he

-- M4 adm3_sat without the cube condition (a leaf CNF for a circuit outside its cube)
theorem M4_no_cube (j : M3Gen.Job) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Adm3 j.cls j.k j.shift j.elimL gs o0 o1 n0 n1) (hr : j.r = gs.length)
    (hc : True) :
    ¬ (CnfGen.toCNF (M3Gen.cnf j)).Unsat := by
  obtain ⟨cls, k, shift, r, elimL, kind⟩ := j
  simp only at h hr hc
  subst hr
  have hgood : ∀ e ∈ M3Gen.events ⟨cls, k, shift, gs.length, elimL, kind⟩,
      Good (ev (k + 2) gs o0 o1 n0 n1) e := by
    unfold M3Gen.events
    simp only [List.forall_mem_append]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact coreDecls_good k gs o0 o1 n0 n1
    · exact lift_good _ _ _ _ _ _ _ (CnfSound.coreCls_good (k + 2) gs o0 n0 h.shaped h.normal)
    · exact symCls_good h
    · exact lift_good _ _ _ _ _ _ _ (CnfSound.orderCls_good (k + 2) gs o0 n0 h.order)
    · exact allinCls_good h
    · exact lift_good _ _ _ _ _ _ _ (CnfSound.distinctCls_good (k + 2) gs o0 n0 h.distinct)
    · cases hL : elimL with
      | none => simp
      | some L => exact elimCls_good h L hL
    · split_ifs with hk
      · exact lift_good _ _ _ _ _ _ _ (symvarsCls_good h hk)
      · simp
    · exact outCls_good h 0 (by omega)
    · exact outCls_good h 1 (by omega)
    · exact wordCls_good h
    · cases kind with
      | whole => simp
      | leaf c =>
        intro e he
        simp only [List.mem_map] at he
        obtain ⟨l, hl, rfl⟩ := he
        exact ⟨l, by simp, hc l hl⟩
      | cover =>
        intro e he
        simp only [List.mem_map] at he
        obtain ⟨c, hcm, rfl⟩ := he
        have hn := hc c hcm
        simp only [InCube, not_forall] at hn
        obtain ⟨l, hl, hne⟩ := hn
        exact ⟨(l.1, !l.2), List.mem_map.mpr ⟨l, hl, rfl⟩, by revert hne; cases l.2 <;> simp⟩
  intro hU
  have := number_sat _ _ hgood
  unfold M3Gen.cnf at hU
  rw [hU] at this
  exact Bool.false_ne_true this

-- M5 allin_of_computes concluding that the next input is read
theorem M5_allin_wrong_input (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (v : ℕ) (hv : v < k + 2)
    (o t : ℕ) (a b : Bool) (ho : o < 2) (ht : t < 2 ^ (k + 2))
    (ha : M3Gen.proj cls k shift o t = some a) (hb : M3Gen.proj cls k shift o (t ^^^ (1 <<< v)) = some b)
    (hab : a ≠ b) : ∃ g ∈ gs, Reads g (v + 1) := by
  by_contra hno
  push_neg at hno
  have ht' : t ^^^ (1 <<< v) < 2 ^ (k + 2) :=
    Nat.xor_lt_two_pow ht (by rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by omega) hv)
  obtain ⟨A, hA, hallA⟩ := proj_spec cls k shift o t a ha
  obtain ⟨B, hB, hallB⟩ := proj_spec cls k shift o _ b hb
  have e0 := nodeV_flip (k + 2) gs h.shaped v hno t o0 (by have := h.out0; omega) h.out0.2
  have e1 := nodeV_flip (k + 2) gs h.shaped v hno t o1 (by have := h.out1; omega) h.out1.2
  have wa := hallA _ (h.computes t ht A hA)
  have wb := hallB _ (h.computes _ ht' B hB)
  rw [e0, e1] at wb
  exact hab (wa.symm.trans wb)

end Ctl
