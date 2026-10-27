import Garden.M3Reduce
import Garden.M3Jobs
import Garden.M3Direct

/-!
# `m3v4g11` for every residue code

Kulikov's question ranges over every two-bit code for a residue mod 3: each word `(w0, w1)` means
a residue `0`, `1`, `2`, or nothing, and every residue has a word (`ValidCode`; 60 tables,
`validCode_iff`, `codes60_length`). `M3Reduce.m3v4g11` answers it for three representatives,
`M3Gen.code 1/2/3`. This file proves the rest in Lean, replacing `m3v4g11_codes.py` and the prose
that came with it:

* **Three moves keep a circuit's size** (`computes_swap`, `computes_neg0`, `computes_shift`). A
  circuit for code `c` becomes one, of the same size, for
  - `swapC c`, the code with its two bits exchanged: rename inputs `x0 ↔ x1` (`SymCanon.tr_nodes`)
    and exchange the two outputs;
  - `neg0C c`, the code with bit 0 negated: fold `¬x0` into the gates' tables
    (`CircuitDual.negGate 1`), and flip output 0's negation bit (also when the output is `x0`
    itself, where the folding does not reach);
  - `shiftC c`, every residue plus one: the same circuit.
* **Every valid code reaches a representative** (`classify`, by `decide` over all 256 tables with
  values in `{none, 0, 1, 2}`): some list of at most four bit moves and two shifts takes it to
  `M3Gen.code 1`, `2` or `3`.
* **`m3v4g11_all`**: if the 506 CNFs of `M3Jobs.jobs` are unsatisfiable, no circuit over B2 with at
  most 11 gates computes the 4-bit block for any valid code. **`m3v4g11_all_direct`**: the same,
  with "Lean's verified LRAT checker accepted some proof for each, against the CNF built in memory"
  (what `m3direct` reports, `Garden.M3Direct`) as the hypothesis.

The specification here (`BlockOK`, `Computes2`) is `M3Reduce`'s with the code table as a
parameter; on the representatives the two agree by definition (`computes2_rep`).
-/

namespace M3Codes
open CircuitDual GateElim SymCanon

/-! ### The question, for any code -/

/-- A two-bit residue code: the residue each word `(w0, w1)` means, or `none` if unused. -/
abbrev Code := Bool × Bool → Option ℕ

/-- **The codes of Kulikov's question**: every word means a residue mod 3 or nothing, and every
residue `0, 1, 2` has a word. -/
def ValidCode (c : Code) : Prop :=
  (∀ w : Bool × Bool, ∀ r, c w = some r → r < 3) ∧ ∀ r < 3, ∃ w : Bool × Bool, c w = some r

/-- **The block's specification**, for code `c`: on a row `x = (x0, x1, x2, …)`, if the word
`(x0, x1)` means a residue `res`, the output word `w` must mean `res` + (number of 1s among
`x2, x3, …`) + `shift`, mod 3. An unused input word is a don't-care. -/
def BlockOK (c : Code) (shift : ℕ) (x : List Bool) (w : Bool × Bool) : Prop :=
  ∀ res, c (x.getD 0 false, x.getD 1 false) = some res →
    c w = some ((res + (x.drop 2).count true + shift) % 3)

/-- **A circuit computing the block**, for code `c`: `gs` over B2 in `CircuitDual`'s model (gate `j`
is node `k + 2 + j`, any two-input table, any reads), outputs any two nodes `o0`, `o1`, each
optionally negated by `n0`, `n1`; `BlockOK` on every row of length `k + 2`. Size is `gs.length`. -/
def Computes2 (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) : Prop :=
  o0 < k + 2 + gs.length ∧ o1 < k + 2 + gs.length ∧
    ∀ x : List Bool, x.length = k + 2 → BlockOK c shift x (n0 ^^ V gs x o0, n1 ^^ V gs x o1)

/-- On the three representatives this is `M3Reduce.Computes2`, by definition. -/
theorem computes2_rep (cls k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) :
    Computes2 (M3Gen.code cls) k shift gs o0 o1 n0 n1 ↔ M3Reduce.Computes2 cls k shift gs o0 o1 n0 n1 :=
  Iff.rfl

/-! ### Three moves that keep a circuit's size -/

/-- The code with its two bits exchanged. -/
def swapC (c : Code) : Code := fun w => c (w.2, w.1)

/-- The code with bit 0 negated. -/
def neg0C (c : Code) : Code := fun w => c (!w.1, w.2)

/-- The code with every residue shifted by one. -/
def shiftC (c : Code) : Code := fun w => (c w).map fun r => (r + 1) % 3

lemma tr01_lt (i m : ℕ) (hm : 2 ≤ m) (hi : i < m) : tr 0 1 i < m := by
  unfold tr; split <;> [omega; split <;> omega]

lemma swapIn_getD0 (x : List Bool) (hx : 2 ≤ x.length) :
    (swapIn 0 1 x).getD 0 false = x.getD 1 false := by
  rw [swapIn_getD, if_pos (by omega)]; rfl

lemma swapIn_getD1 (x : List Bool) (hx : 2 ≤ x.length) :
    (swapIn 0 1 x).getD 1 false = x.getD 0 false := by
  rw [swapIn_getD, if_pos (by omega)]; rfl

lemma swapIn_drop2 (x : List Bool) : (swapIn 0 1 x).drop 2 = x.drop 2 := by
  apply List.ext_getElem
  · simp [swapIn_length]
  · intro i h1 h2
    have e1 := swapIn_getD 0 1 x (i + 2)
    have hi : i + 2 < x.length := by simp at h2; omega
    rw [if_pos hi, show tr 0 1 (i + 2) = i + 2 by unfold tr; split <;> [omega; split <;> omega]] at e1
    simp only [List.getElem_drop]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [swapIn_length]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at e1
    simpa [Nat.add_comm] using e1

/-- **Exchanging the code's bits**: rename the reads by `x0 ↔ x1` and exchange the outputs. -/
theorem computes_swap (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 c k shift gs o0 o1 n0 n1) :
    Computes2 (swapC c) k shift (gs.map (ren (tr 0 1))) (tr 0 1 o1) (tr 0 1 o0) n1 n0 := by
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

/-- **Negating the code's bit 0**: fold `¬x0` into the gates' tables, flip output 0's negation, and
flip an output's negation if that output is `x0` itself (node 0). -/
theorem computes_neg0 (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 c k shift gs o0 o1 n0 n1) :
    Computes2 (neg0C c) k shift (gs.map (negGate 1)) o0 o1
      (!n0 ^^ decide (o0 < 1)) (n1 ^^ decide (o1 < 1)) := by
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

/-- **Shifting every residue**: the same circuit. -/
theorem computes_shift (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 c k shift gs o0 o1 n0 n1) : Computes2 (shiftC c) k shift gs o0 o1 n0 n1 := by
  obtain ⟨h0, h1, hx⟩ := h
  refine ⟨h0, h1, fun x hlen res hres => ?_⟩
  simp only [shiftC, Option.map_eq_some_iff] at hres ⊢
  obtain ⟨r, hr, rfl⟩ := hres
  refine ⟨_, hx x hlen r hr, ?_⟩
  omega

/-! ### Sequences of moves -/

inductive Op where
  | swap
  | neg0
  | shift
  deriving DecidableEq, Repr

def Op.apply : Op → Code → Code
  | .swap => swapC
  | .neg0 => neg0C
  | .shift => shiftC

/-- Apply the moves left to right. -/
def applyAll : List Op → Code → Code
  | [], c => c
  | o :: os, c => applyAll os (o.apply c)

/-- A circuit for `c` gives one of the same size for `applyAll os c`. -/
theorem computes_applyAll (os : List Op) : ∀ (c : Code) (k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ)
    (n0 n1 : Bool), Computes2 c k shift gs o0 o1 n0 n1 →
    ∃ (gs' : List Gate) (p0 p1 : ℕ) (m0 m1 : Bool),
      gs'.length = gs.length ∧ Computes2 (applyAll os c) k shift gs' p0 p1 m0 m1 := by
  induction os with
  | nil => intro c k shift gs o0 o1 n0 n1 h; exact ⟨gs, o0, o1, n0, n1, rfl, h⟩
  | cons o os ih =>
    intro c k shift gs o0 o1 n0 n1 h
    cases o
    · obtain ⟨gs', p0, p1, m0, m1, hl, h'⟩ :=
        ih _ k shift _ _ _ _ _ (computes_swap c k shift gs o0 o1 n0 n1 h)
      exact ⟨gs', p0, p1, m0, m1, by rw [hl, List.length_map], h'⟩
    · obtain ⟨gs', p0, p1, m0, m1, hl, h'⟩ :=
        ih _ k shift _ _ _ _ _ (computes_neg0 c k shift gs o0 o1 n0 n1 h)
      exact ⟨gs', p0, p1, m0, m1, by rw [hl, List.length_map], h'⟩
    · exact ih _ k shift _ _ _ _ _ (computes_shift c k shift gs o0 o1 n0 n1 h)

/-! ### Every valid code reaches a representative (by `decide`) -/

/-- The code with table `a b d e` on the words `00, 01, 10, 11`. -/
def ofTbl (a b d e : Option ℕ) : Code
  | (false, false) => a
  | (false, true) => b
  | (true, false) => d
  | (true, true) => e

lemma eq_ofTbl (c : Code) : c = ofTbl (c (false, false)) (c (false, true)) (c (true, false)) (c (true, true)) := by
  funext w; obtain ⟨_ | _, _ | _⟩ := w <;> rfl

/-- The values a valid code takes. -/
def vals : List (Option ℕ) := [none, some 0, some 1, some 2]

/-- Every residue has a word. -/
def covers (l : List (Option ℕ)) : Bool := [0, 1, 2].all fun r => l.contains (some r)

/-- The eight relabelings of the two bits (the group generated by `swap` and `neg0`), each
followed by no shift, one, or two. -/
def relabels : List (List Op) :=
  [[], [.swap], [.neg0], [.swap, .neg0], [.neg0, .swap], [.swap, .neg0, .swap],
   [.neg0, .swap, .neg0], [.swap, .neg0, .swap, .neg0]]

def moves : List (List Op) := relabels.flatMap fun l => [l, l ++ [.shift], l ++ [.shift, .shift]]

/-- `os` takes code `c` to representative `cls`, on all four words. -/
def reaches (os : List Op) (c : Code) (cls : ℕ) : Bool :=
  M3Gen.words.all fun w => applyAll os c w == M3Gen.code cls w

set_option maxRecDepth 20000 in
/-- **The orbit check**: every table with values in `{none, 0, 1, 2}` that covers all three
residues is taken to `M3Gen.code 1`, `2` or `3` by one of the 24 `moves`. -/
theorem classify : ∀ a ∈ vals, ∀ b ∈ vals, ∀ d ∈ vals, ∀ e ∈ vals, covers [a, b, d, e] = true →
    (moves.any fun os => [1, 2, 3].any fun cls => reaches os (ofTbl a b d e) cls) = true := by
  decide

lemma mem_vals (o : Option ℕ) (h : ∀ r, o = some r → r < 3) : o ∈ vals := by
  rcases o with _ | r
  · simp [vals]
  · have := h r rfl
    rcases r with _ | _ | _ | r
    all_goals (try simp [vals]); all_goals omega

lemma words_all (p : Bool × Bool → Bool) (h : (M3Gen.words.all p) = true) : ∀ w, p w = true := by
  intro w; exact List.all_eq_true.mp h w (M3Reduce.mem_words w)

/-- A valid code is taken to a representative by some list of moves. -/
theorem exists_moves (c : Code) (hc : ValidCode c) :
    ∃ os : List Op, ∃ cls, (cls = 1 ∨ cls = 2 ∨ cls = 3) ∧ applyAll os c = M3Gen.code cls := by
  obtain ⟨hv, hcov⟩ := hc
  have hcv : covers [c (false, false), c (false, true), c (true, false), c (true, true)] = true := by
    simp only [covers, List.all_eq_true, List.contains_iff_mem]
    intro r hr
    have hr3 : r < 3 := by simp at hr; omega
    obtain ⟨w, hw⟩ := hcov r hr3
    obtain ⟨_ | _, _ | _⟩ := w <;> simp [← hw]
  have := classify _ (mem_vals _ (hv _)) _ (mem_vals _ (hv _)) _ (mem_vals _ (hv _)) _
    (mem_vals _ (hv _)) hcv
  rw [← eq_ofTbl] at this
  obtain ⟨os, -, hos⟩ := List.any_eq_true.mp this
  obtain ⟨cls, hcls, hr⟩ := List.any_eq_true.mp hos
  refine ⟨os, cls, by simpa [or_assoc] using hcls, funext fun w => ?_⟩
  simpa using words_all _ hr w

/-! ### The 60 codes -/

/-- All tables with values in `vals` that cover the three residues. -/
def codes60 : List (List (Option ℕ)) :=
  vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun d => vals.filterMap fun e =>
    if covers [a, b, d, e] then some [a, b, d, e] else none

theorem codes60_length : codes60.length = 60 := by decide

/-- `ValidCode` is exactly membership of the code's table in `codes60`. -/
theorem validCode_iff (c : Code) :
    ValidCode c ↔ [c (false, false), c (false, true), c (true, false), c (true, true)] ∈ codes60 := by
  constructor
  · intro ⟨hv, hcov⟩
    have hcv : covers [c (false, false), c (false, true), c (true, false), c (true, true)] = true := by
      simp only [covers, List.all_eq_true, List.contains_iff_mem]
      intro r hr
      have hr3 : r < 3 := by simp at hr; omega
      obtain ⟨w, hw⟩ := hcov r hr3
      obtain ⟨_ | _, _ | _⟩ := w <;> simp [← hw]
    simp only [codes60, List.mem_flatMap, List.mem_filterMap]
    exact ⟨_, mem_vals _ (hv _), _, mem_vals _ (hv _), _, mem_vals _ (hv _), _, mem_vals _ (hv _),
      by rw [if_pos hcv]⟩
  · intro h
    simp only [codes60, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨a, ha, b, hb, d, hd, e, he, hif⟩ := h
    split at hif
    · rename_i hcv
      simp only [Option.some.injEq, List.cons.injEq, and_true] at hif
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hif
      refine ⟨fun w r hw => ?_, fun r hr => ?_⟩
      · have hm : ∀ o ∈ vals, o = some r → r < 3 := by
          intro o ho hor; subst hor; simp [vals] at ho; omega
        obtain ⟨_ | _, _ | _⟩ := w
        exacts [hm _ ha hw, hm _ hb hw, hm _ hd hw, hm _ he hw]
      · simp only [covers, List.all_eq_true, List.contains_iff_mem] at hcv
        have := hcv r (by simp; omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with h | h | h | h
        exacts [⟨(false, false), h.symm⟩, ⟨(false, true), h.symm⟩, ⟨(true, false), h.symm⟩,
          ⟨(true, true), h.symm⟩]
    · cases hif

/-! ### The hypotheses: the 506 CNFs of `M3Jobs.jobs` -/

/-- `M3Jobs.jobs` contains every CNF `M3Reduce.m3v4g11` names, for each class. -/
theorem jobs_cover (hU : ∀ j ∈ M3Jobs.jobs, (CnfGen.toCNF (M3Gen.cnf j)).Unsat) (cls : ℕ)
    (hcls : cls = 1 ∨ cls = 2 ∨ cls = 3) :
    (∀ r, 1 ≤ r → r < (M3Sound.elimOf cls).1 → (CnfGen.toCNF (M3Gen.cnf (M3Reduce.job3 cls 0 r))).Unsat) ∧
    (∀ r, 1 ≤ r → r < (M3Sound.elimOf cls).2 → (CnfGen.toCNF (M3Gen.cnf (M3Reduce.job3 cls 1 r))).Unsat) ∧
    (∀ r, 1 ≤ r → r ≤ 10 → (CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls r .whole))).Unsat) ∧
    ((CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls 11 .whole))).Unsat ∨
      ((CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls 11 .cover))).Unsat ∧
        ∀ c ∈ M3Gen.cubes 4, (CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls 11 (.leaf c)))).Unsat)) := by
  have hm : ∀ j ∈ M3Jobs.jobsOf cls, (CnfGen.toCNF (M3Gen.cnf j)).Unsat := fun j hj =>
    hU j (List.mem_flatMap.mpr ⟨cls, by rcases hcls with rfl | rfl | rfl <;> simp, hj⟩)
  have e : M3Sound.elimOf cls = M3Jobs.elimL cls := by rcases hcls with rfl | rfl | rfl <;> rfl
  have h3 : ∀ j ∈ M3Jobs.jobs3 cls, (CnfGen.toCNF (M3Gen.cnf j)).Unsat := fun j hj =>
    hm j (List.mem_append_left _ (List.mem_append_left _ hj))
  have h11 : ∀ j ∈ M3Jobs.jobs11 cls, (CnfGen.toCNF (M3Gen.cnf j)).Unsat := fun j hj =>
    hm j (List.mem_append_right _ hj)
  refine ⟨fun r h1 h2 => h3 _ (List.mem_append_left _ (List.mem_map.mpr ⟨r, ?_, rfl⟩)),
    fun r h1 h2 => h3 _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, ?_, rfl⟩)),
    fun r h1 h2 => hm _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, ?_, rfl⟩))),
    ?_⟩
  · rw [List.mem_range'_1]; rw [e] at h2; omega
  · rw [List.mem_range'_1]; rw [e] at h2; omega
  · rw [List.mem_range'_1]; omega
  · have ej : ∀ r kind, M3Sound.job cls r kind = M3Jobs.k4 cls r kind := by
      intro r kind; unfold M3Sound.job M3Jobs.k4; rw [e]
    simp only [ej]
    rcases hcls with rfl | rfl | rfl
    · exact Or.inr ⟨h11 _ (List.mem_cons_self ..),
        fun c hc => h11 _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩))⟩
    · exact Or.inl (h11 _ (List.mem_cons_self ..))
    · exact Or.inl (h11 _ (List.mem_cons_self ..))

/-! ### The theorem -/

/-- **Kulikov's `m3v4g11`, for every code: no circuit over B2 with at most 11 gates computes the
4-bit block.** For every code table `c` in which each word means a residue mod 3 or nothing and
every residue has a word (`ValidCode`, 60 tables), no circuit of `≤ 11` gates (`Computes2`: any
two-input gates, outputs any two nodes, each optionally negated) adds four bits to a residue
coded by `c` and outputs the result in the same code. The hypothesis: the 506 CNFs of
`M3Jobs.jobs`, each generated in Lean (`M3Gen.cnf`), are unsatisfiable. -/
theorem m3v4g11_all (hU : ∀ j ∈ M3Jobs.jobs, (CnfGen.toCNF (M3Gen.cnf j)).Unsat) :
    ∀ c : Code, ValidCode c →
      ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 →
        ¬ Computes2 c 4 0 gs o0 o1 n0 n1 := by
  intro c hc gs o0 o1 n0 n1 hle h
  obtain ⟨os, cls, hcls, hos⟩ := exists_moves c hc
  obtain ⟨gs', p0, p1, m0, m1, hl, h'⟩ := computes_applyAll os c 4 0 gs o0 o1 n0 n1 h
  rw [hos] at h'
  obtain ⟨a, b, d, e⟩ := jobs_cover hU cls hcls
  exact M3Reduce.m3v4g11 cls hcls a b d e gs' p0 p1 m0 m1 (by omega) h'

/-- **`m3v4g11_all` with checker verdicts as hypotheses**: for each of the 506 jobs, some byte
blocks were accepted by `LratDirect.check` against the job's CNF, which is what `m3direct i`
reports for `M3Jobs.jobs[i]`. -/
theorem m3v4g11_all_direct
    (hV : ∀ j ∈ M3Jobs.jobs, ∃ bs, (Garden.LratDirect.check (CnfGen.toCNF (M3Gen.cnf j)) bs).verified = true) :
    ∀ c : Code, ValidCode c →
      ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 →
        ¬ Computes2 c 4 0 gs o0 o1 n0 n1 :=
  m3v4g11_all fun j hj =>
    let ⟨bs, hb⟩ := hV j hj
    Garden.LratDirect.check_sound _ bs hb

end M3Codes
