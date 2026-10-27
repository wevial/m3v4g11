import Garden.M3Reduce
/-! Witnesses that must BUILD, for `Garden/M3Reduce.lean`. Run with
`lake env lean controls/2026-10-27-m3reduce-witness.lean`.

* `c13_computes`: `Computes2 1 4 0` is satisfiable. The 13-gate class-1 block (the Mac's 9-gate
  3-bit block `c1_k3_s0_r9_whole`, then its 4-gate 1-bit block `c1_k1_s0_r4_whole`, composed and
  normalized by `m3v4g11_controls.compose`/`normalize`, as in `m3v4g11_elim_controls.py`) computes
  the 4-bit block. So `m3v4g11`'s conclusion (≥ 12) is about a predicate that real circuits meet.
* `code_bit_not_symmetric`: the symmetry condition matters. Swapping the code bit `x1` with a
  counted bit `x2` is not a symmetry of the class-1 block (so `canonicalL` could not be run on
  `x1 … x5`, which is why `symvars` covers only `x2 … x5`).
* `no_table_false`: the code table matters. For a class number outside 1–3, `M3Gen.code` gives no
  word a residue, every row is a don't-care, and a circuit with no gates "computes" the block:
  the conclusion of `m3v4g11` is false there (its proof fails at `spec_facts`; see the
  must-fail file, R2). -/
open CircuitDual GateElim SymCanon M3Reduce

def xorT : Bool → Bool → Bool := fun p q => p != q
def orT : Bool → Bool → Bool := fun p q => p || q
def andT : Bool → Bool → Bool := fun p q => p && q
def nAndT : Bool → Bool → Bool := fun p q => !p && q
def andNT : Bool → Bool → Bool := fun p q => p && !q

/-- Gate `⟨j, k, op⟩` reads nodes `j < k`; outputs nodes 18 and 16, not negated. -/
def c13 : List Gate :=
  [⟨1, 2, xorT⟩, ⟨0, 6, nAndT⟩, ⟨2, 3, xorT⟩, ⟨7, 8, orT⟩, ⟨0, 9, xorT⟩, ⟨3, 7, xorT⟩,
   ⟨4, 10, xorT⟩, ⟨11, 12, xorT⟩, ⟨10, 13, andT⟩, ⟨12, 14, orT⟩, ⟨5, 15, xorT⟩, ⟨14, 16, xorT⟩,
   ⟨15, 17, andNT⟩]

theorem c13_computes : Computes2 1 4 0 c13 18 16 false false := by
  have key : ∀ t < 64, (M3Gen.allowed 1 4 0 t).all (fun A =>
      decide ((false ^^ V c13 (CnfSound.row 6 t) 18, false ^^ V c13 (CnfSound.row 6 t) 16) ∈ A)) = true := by
    decide
  refine ⟨by decide, by decide, fun x hx => ?_⟩
  obtain ⟨t, ht, rfl⟩ := CnfSound.row_surj 6 x hx
  rw [CnfSound.mem_rows] at ht
  refine (blockOK_row 1 4 0 t _).mpr fun A hA => ?_
  have := key t ht
  rw [hA] at this
  simpa using this

theorem c13_length : c13.length = 13 := rfl

theorem code_bit_not_symmetric : ¬ SymOnL 6 (fun u => 1 ≤ u ∧ u < 6) (F2 1 0 false false) := by
  intro h
  -- row x = (1, 0, 1, 0, 0, 0): word 10 means 2, plus one 1, so the output word must mean 0 (00).
  -- Swapping x1, x2 gives (1, 1, 0, 0, 0, 0): word 11 means 2, plus none: 10 is correct there.
  obtain ⟨a, b, hab, hB⟩ := h 1 2 ⟨le_refl _, by omega⟩ ⟨by omega, by omega⟩
    [true, false, true, false, false, false] rfl [true, false]
    ⟨true, false, rfl, fun res hres => by
      simp only [swapIn, tr] at hres ⊢
      simp [M3Gen.code] at hres
      subst hres
      decide⟩
  simp only [List.cons.injEq, and_true] at hab
  obtain ⟨rfl, rfl⟩ := hab
  have := hB 2 (by simp [M3Gen.code])
  simp [M3Gen.code] at this

theorem no_table_false : ¬ ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 →
    ¬ Computes2 4 4 0 gs o0 o1 n0 n1 := by
  intro h
  exact h [] 0 0 false false (by simp) ⟨by simp, by simp, fun x _ res hres => by simp [M3Gen.code] at hres⟩

#print axioms c13_computes
#print axioms code_bit_not_symmetric
#print axioms no_table_false
