import Garden.M3Sound
/-! Witness that must BUILD: `M3Sound.Adm3` is not vacuous. The 5-gate class-2, k = 1 block the Mac
found (`m3v4g11_results.tsv`, job `c2_k1_s0_r5_whole`, SAT, decoded by `oc.decode`) satisfies every
field, so `adm3_sat` is about circuits that exist, and the relational word clauses (class 2) are
met by a real circuit. Gate `[j, k, [f01, f10, f11]]` is `⟨j, k, op⟩` with `op p q` = table at
`(x_j, x_k) = (p, q)`; outputs nodes 5 and 7, not negated. -/
open CircuitDual GateElim SymCanon M3Sound

def w2 : List Gate :=
  [⟨0, 1, fun p q => p != q⟩, ⟨0, 2, fun p q => p != q⟩, ⟨3, 4, fun p q => p || q⟩,
   ⟨1, 5, fun p q => !p && q⟩, ⟨4, 6, fun p q => p != q⟩]

lemma allRows {P : List Bool → Prop} :
    (∀ x, ∀ t ∈ CnfGen.rows 3, x = CnfSound.row 3 t → P x) ↔ ∀ t ∈ CnfGen.rows 3, P (CnfSound.row 3 t) :=
  ⟨fun h t ht => h _ t ht rfl, fun h _ t ht hx => hx ▸ h t ht⟩

theorem w2_adm : Adm3 2 1 0 none w2 5 7 false false := by
  have key : ∀ t < 8, (M3Gen.allowed 2 1 0 t).all (fun A =>
      decide ((false ^^ CnfSound.nodeV 3 w2 t 5, false ^^ CnfSound.nodeV 3 w2 t 7) ∈ A)) = true := by
    decide
  refine ⟨(shaped_iff 3 w2).mpr (by decide), by decide, by decide, by decide, ?_, by decide, ?_, ?_, ?_,
    fun h => absurd h (by decide), fun h => absurd h (by decide), by simp⟩
  · intro t ht A hA
    have := key t ht
    rw [hA] at this
    simpa using this
  · intro j hj
    have hj : j < 5 := hj
    interval_cases j
    · exact Or.inr (Or.inr ⟨2, by decide, by decide, Or.inl rfl⟩)
    · exact Or.inr (Or.inr ⟨2, by decide, by decide, Or.inr rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨4, by decide, by decide, Or.inr rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · intro i h
    have h4 : i < 4 := by have : i + 1 < 5 := h; omega
    interval_cases i <;> simp [w2, Reads, PairLt]
  · intro j hj
    rw [← CnfSound.rowSet_all 3]
    simp only [Redundant, CnfSound.rowSet, Set.mem_ofPred_eq, forall_exists_index, and_imp, allRows]
    have hj : j < 5 := hj
    revert j
    decide

/-- So the class-2, k = 1, r = 5 whole CNF is satisfiable, as the Mac's SAT verdict says. -/
theorem w2_cnf_sat : ¬ (CnfGen.toCNF (M3Gen.cnf ⟨2, 1, 0, 5, none, .whole⟩)).Unsat :=
  adm3_sat ⟨2, 1, 0, 5, none, .whole⟩ w2 5 7 false false w2_adm rfl trivial

#print axioms w2_adm
#print axioms w2_cnf_sat
