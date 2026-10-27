import Garden.M3Codes
/-! Witnesses that must BUILD, for `Garden/M3Codes.lean`. Run with
`lake env lean controls/2026-10-27-m3codes-witness.lean`.

* `orbit1_thirteen`, `orbit1_length`: the conclusion of `m3v4g11_all` is about a predicate real
  circuits meet, for 24 of the 60 codes. Every code the moves reach from `M3Gen.code 1` has a
  13-gate block: the class-1 circuit `c13` of `controls/2026-10-27-m3reduce-witness.lean` (copied
  here), carried over by `computes_applyAll`. Those are 24 of the 60 tables (`decide`). So for
  them the size is 12 or 13.
* `neg0_no_fix_false`: control C4's claim is false, not just unproved. For the gate-free circuit
  whose outputs are the input word itself (`k = 0`), negating bit 0 of the code without the
  node-0 correction gives a wrong output on row `00`.
* `no_cover_false`: control C7's claim is false. For the code that gives no word a residue, every
  row is a don't-care and a gate-free circuit "computes" the block. -/
open CircuitDual GateElim SymCanon M3Codes

def xorT : Bool → Bool → Bool := fun p q => p != q
def orT : Bool → Bool → Bool := fun p q => p || q
def andT : Bool → Bool → Bool := fun p q => p && q
def nAndT : Bool → Bool → Bool := fun p q => !p && q
def andNT : Bool → Bool → Bool := fun p q => p && !q

/-- `M3Reduce`'s witness circuit (`controls/2026-10-27-m3reduce-witness.lean`), verbatim. -/
def c13 : List Gate :=
  [⟨1, 2, xorT⟩, ⟨0, 6, nAndT⟩, ⟨2, 3, xorT⟩, ⟨7, 8, orT⟩, ⟨0, 9, xorT⟩, ⟨3, 7, xorT⟩,
   ⟨4, 10, xorT⟩, ⟨11, 12, xorT⟩, ⟨10, 13, andT⟩, ⟨12, 14, orT⟩, ⟨5, 15, xorT⟩, ⟨14, 16, xorT⟩,
   ⟨15, 17, andNT⟩]

theorem c13_computes : Computes2 (M3Gen.code 1) 4 0 c13 18 16 false false := by
  have key : ∀ t < 64, (M3Gen.allowed 1 4 0 t).all (fun A =>
      decide ((false ^^ V c13 (CnfSound.row 6 t) 18, false ^^ V c13 (CnfSound.row 6 t) 16) ∈ A)) = true := by
    decide
  refine ⟨by decide, by decide, fun x hx => ?_⟩
  obtain ⟨t, ht, rfl⟩ := CnfSound.row_surj 6 x hx
  rw [CnfSound.mem_rows] at ht
  refine (M3Reduce.blockOK_row 1 4 0 t _).mpr fun A hA => ?_
  have := key t ht
  rw [hA] at this
  simpa using this

/-- Every code the moves reach from class 1 has a 13-gate block. -/
theorem orbit1_thirteen (c : Code) (h : ∃ os ∈ moves, applyAll os (M3Gen.code 1) = c) :
    ∃ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length = 13 ∧ Computes2 c 4 0 gs o0 o1 n0 n1 := by
  obtain ⟨os, -, rfl⟩ := h
  obtain ⟨gs, o0, o1, n0, n1, hl, h⟩ := computes_applyAll os _ 4 0 c13 18 16 false false c13_computes
  exact ⟨gs, o0, o1, n0, n1, hl, h⟩

/-- The tables the moves reach from class 1. -/
def orbit1 : List (List (Option ℕ)) :=
  codes60.filter fun t => moves.any fun os =>
    M3Gen.words.map (applyAll os (M3Gen.code 1)) == t

set_option maxRecDepth 20000 in
/-- They are 24 of the 60. -/
theorem orbit1_length : orbit1.length = 24 := by decide

/-- Control C4's claim is false. -/
theorem neg0_no_fix_false : ¬ ∀ (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool),
    Computes2 c k shift gs o0 o1 n0 n1 → Computes2 (neg0C c) k shift (gs.map (negGate 1)) o0 o1 (!n0) n1 := by
  intro h
  have hid : Computes2 (M3Gen.code 1) 0 0 [] 0 1 false false := by
    refine ⟨by decide, by decide, fun x hx => ?_⟩
    match x, hx with
    | [a, b], _ =>
      intro res hres
      cases a <;> cases b <;> simp [V, run, M3Gen.code] at hres ⊢ <;> omega
  have := (h _ 0 0 [] 0 1 false false hid).2.2 [false, false] rfl
  exact absurd (this 2 rfl) (by decide)

/-- Control C7's claim is false. -/
theorem no_cover_false : ¬ ∀ c : Code, (∀ w : Bool × Bool, ∀ r, c w = some r → r < 3) →
    ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 → ¬ Computes2 c 4 0 gs o0 o1 n0 n1 := by
  intro h
  exact h (fun _ => none) (fun _ _ h => by cases h) [] 0 1 false false (by decide)
    ⟨by decide, by decide, fun _ _ _ h => by cases h⟩
