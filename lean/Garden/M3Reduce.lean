import Garden.M3Sound

/-!
# `m3v4g11`: no circuit over B2 with ≤ 11 gates computes the 4-bit block, from Lean CNFs

`M3Sound.m3v4g11_le11` says: if the run's CNFs are unsatisfiable, no circuit satisfying `Adm3`
(the list of what the CNF asserts) has ≤ 11 gates. This file closes the gap to arbitrary
circuits: a minimum circuit for the block can always be put in `Adm3`'s form. The statement:

* `BlockOK cls shift x w`: the specification, from the code table `M3Gen.code cls` alone.
* `Computes2 cls k shift gs o0 o1 n0 n1`: a circuit over B2 (`CircuitDual`'s model: any
  two-input tables, any reads) computes the block, outputs any two nodes, optionally negated.
* **`m3v4g11 cls`**: for `cls ∈ {1, 2, 3}`, if 453 + 53 named Lean-generated CNFs are `Unsat`, no
  circuit of ≤ 11 gates satisfies `Computes2 cls 4 0`. The 453 are `m3v4g11_le11`'s; the 53 are
  the 3-bit runs (`job3`) behind the `elim` bounds.

The chain, for any (class, k, shift) whose outputs can be neither constants nor literals
(`NoConst`, `NoLit`, decided per instance in `spec_facts`):
* `no_redundant`: in a minimum circuit no gate is redundant (`GateElim.build` deletes them all,
  and reads each output off a representative, `computes2_of_reps`).
* `normalize`: so it has the CNF's shape (`Reduction.reads_ok`, `sortG`, `normL`); the
  negations pushed forward land in the output bits.
* `outs_gates`: both outputs are gates. `canonicalL` (`SymCanon`, generalized on 2026-10-27 from
  one output to any list of outputs and a relational spec) gives `order`, `symvars` and the table
  clause, since the block is symmetric in the counted bits (`blockOK_swap`).
* `used_of_min`: no dead gate, with two outputs exempt (`Reduction.delete_nodes`).
* `elim_bound`: in any circuit for the (k + 1)-bit block, at most `size − L` gates are redundant at
  `x_v = c`, if every circuit for the k-bit block with shift `+ c` has ≥ `L` gates: delete them,
  substitute `x_v := c` (`GateElim.srel_run`), and the rest computes the smaller block
  (`blockOK_fix`). `Mod3Lower.elimCount_le` turns that into the CNF's syntactic counts.
* `exists_adm3`: hence a minimum circuit yields an `Adm3` one of the same size; `lower3`: so runs
  refuting every `r < s` give `size ≥ s`. `lb3` applies this at k = 3 (no `elim`), and `m3v4g11`
  at k = 4 with `elim` from `lb3`.

Axioms: the standard three. Controls: `controls/2026-10-27-m3reduce-must-fail.lean` (R1–R5) and
`controls/2026-10-27-m3reduce-witness.lean` (a 13-gate block satisfies `Computes2 1 4 0`; R1's and
R2's mutated claims are false).

Not here: the unsatisfiability of the CNFs (LRAT, outside the kernel: `cake_lpr` on the Mac for
all 506, Lean's `lratcheck` for all 506 on gembox). That the 60 codes fall into these 3 classes,
and that relabeling and shifting keep a circuit's size, is `M3Codes` (2026-10-27 19:08), which
states the theorem for every code.
-/

namespace M3Reduce
open CircuitDual GateElim SymBreak SymCanon Reduction Mod3Lower

/-! ### The question, stated plainly -/

/-- **The block's specification.** On a row `x = (x0, x1, x2, …)`, the word `(x0, x1)` codes the
count so far (`M3Gen.code cls`, the class's code table) and `x2, x3, …` are the bits to add. An
output word `w` is correct if, whenever the input word means a residue `res`, `w` means `res` +
(number of 1s among `x2, x3, …`) + `shift`, mod 3. An unused input word is a don't-care. -/
def BlockOK (cls shift : ℕ) (x : List Bool) (w : Bool × Bool) : Prop :=
  ∀ res, M3Gen.code cls (x.getD 0 false, x.getD 1 false) = some res →
    M3Gen.code cls w = some ((res + (x.drop 2).count true + shift) % 3)

/-- **A circuit computing the block.** `gs` is a circuit over B2 in `CircuitDual`'s model: gate
`j` is node `k + 2 + j`, applies any two-input table to any two nodes (`run`), and the outputs are
any two nodes `o0`, `o1`, each optionally negated by `n0`, `n1`. Size is `gs.length`. -/
def Computes2 (cls k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) : Prop :=
  o0 < k + 2 + gs.length ∧ o1 < k + 2 + gs.length ∧
    ∀ x : List Bool, x.length = k + 2 → BlockOK cls shift x (n0 ^^ V gs x o0, n1 ^^ V gs x o1)


/-! ### The specification on a row index, as `M3Gen.allowed` states it -/

open CnfSound (row row_getD row_length) in
lemma drop_row (k t : ℕ) : (row (k + 2) t).drop 2 = (List.range' 2 k).map t.testBit := by
  apply List.ext_getElem
  · simp [row]
  · intro i h1 h2
    simp only [row, List.getElem_drop, List.getElem_map, List.getElem_range, List.getElem_range']
    congr 1; omega

lemma count_map (l : List ℕ) (p : ℕ → Bool) : (l.map p).count true = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [List.filter_cons, h, ih]

lemma mem_words (w : Bool × Bool) : w ∈ M3Gen.words := by
  obtain ⟨a, b⟩ := w; cases a <;> cases b <;> decide

open CnfSound (row row_getD) in
/-- On row `t`, `BlockOK` is membership in the CNF's allowed set (`M3Gen.allowed`). -/
lemma blockOK_row (cls k shift t : ℕ) (w : Bool × Bool) :
    BlockOK cls shift (row (k + 2) t) w ↔ ∀ A, M3Gen.allowed cls k shift t = some A → w ∈ A := by
  unfold BlockOK M3Gen.allowed
  rw [row_getD _ _ _ (by omega), row_getD _ _ _ (by omega), drop_row, count_map]
  cases M3Gen.code cls (t.testBit 0, t.testBit 1) with
  | none => simp
  | some res =>
    simp only [Option.some.injEq, forall_eq', List.mem_filter, beq_iff_eq]
    exact ⟨fun h => ⟨mem_words w, h⟩, fun h => h.2⟩

/-! ### The facts about the specification the reduction uses (checked by `decide`) -/

/-- Output `o` is wrong on row `t` whatever the circuit does, if its bit is `p`. -/
def excl (cls k shift o t : ℕ) (p : Bool) : Bool :=
  match M3Gen.allowed cls k shift t with
  | some A => A.all (M3Gen.bit o · != p)
  | none => false

/-- Neither output can be a constant. -/
def NoConst (cls k shift : ℕ) : Prop :=
  ∀ o < 2, ∀ c : Bool, ∃ t < 2 ^ (k + 2), excl cls k shift o t c = true

/-- Neither output can be an input literal `±x_u`. -/
def NoLit (cls k shift : ℕ) : Prop :=
  ∀ o < 2, ∀ u < k + 2, ∀ b : Bool, ∃ t < 2 ^ (k + 2), excl cls k shift o t (b ^^ t.testBit u) = true

set_option maxRecDepth 100000 in
/-- For every class, at each (k, shift) the runs use: the 4-bit block, and the 3-bit blocks with
shift 0 and 1. -/
theorem spec_facts (cls k shift : ℕ) (hcls : cls = 1 ∨ cls = 2 ∨ cls = 3)
    (hks : (k = 4 ∧ shift = 0) ∨ (k = 3 ∧ shift = 0) ∨ (k = 3 ∧ shift = 1)) :
    NoConst cls k shift ∧ NoLit cls k shift := by
  rcases hks with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hcls with rfl | rfl | rfl <;>
    unfold NoConst NoLit <;> decide

open CnfSound (row row_length) in
lemma excl_spec (cls k shift o t : ℕ) (p : Bool) (h : excl cls k shift o t p = true) (w : Bool × Bool)
    (hw : BlockOK cls shift (row (k + 2) t) w) : M3Gen.bit o w ≠ p := by
  unfold excl at h
  rw [blockOK_row] at hw
  revert h hw
  cases M3Gen.allowed cls k shift t with
  | none => simp
  | some A =>
    intro h hw
    have := List.all_eq_true.mp h w (hw A rfl)
    simpa using this

lemma bit_fst (w : Bool × Bool) : M3Gen.bit 0 w = w.1 := rfl
lemma bit_snd (w : Bool × Bool) : M3Gen.bit 1 w = w.2 := rfl

open CnfSound (row row_length) in
/-- If the outputs on every row are given by `F0 x`, `F1 x`, neither is constant. -/
lemma not_const (cls k shift : ℕ) (hc : NoConst cls k shift) (F0 F1 : List Bool → Bool)
    (h : ∀ x : List Bool, x.length = k + 2 → BlockOK cls shift x (F0 x, F1 x)) :
    (¬ ∃ c, ∀ x : List Bool, x.length = k + 2 → F0 x = c) ∧
      (¬ ∃ c, ∀ x : List Bool, x.length = k + 2 → F1 x = c) := by
  refine ⟨fun ⟨c, hc0⟩ => ?_, fun ⟨c, hc1⟩ => ?_⟩
  · obtain ⟨t, -, ht⟩ := hc 0 (by omega) c
    exact excl_spec _ _ _ _ _ _ ht _ (h _ (row_length _ _)) (by rw [bit_fst, hc0 _ (row_length _ _)])
  · obtain ⟨t, -, ht⟩ := hc 1 (by omega) c
    exact excl_spec _ _ _ _ _ _ ht _ (h _ (row_length _ _)) (by rw [bit_snd, hc1 _ (row_length _ _)])

open CnfSound (row row_length row_getD) in
/-- … and neither is an input literal. -/
lemma not_lit (cls k shift : ℕ) (hl : NoLit cls k shift) (F0 F1 : List Bool → Bool)
    (h : ∀ x : List Bool, x.length = k + 2 → BlockOK cls shift x (F0 x, F1 x)) (u : ℕ)
    (hu : u < k + 2) (b : Bool) :
    (¬ ∀ x : List Bool, x.length = k + 2 → F0 x = (b ^^ x.getD u false)) ∧
      (¬ ∀ x : List Bool, x.length = k + 2 → F1 x = (b ^^ x.getD u false)) := by
  refine ⟨fun hc0 => ?_, fun hc1 => ?_⟩
  · obtain ⟨t, -, ht⟩ := hl 0 (by omega) u hu b
    exact excl_spec _ _ _ _ _ _ ht _ (h _ (row_length _ _))
      (by rw [bit_fst, hc0 _ (row_length _ _), row_getD _ _ _ hu])
  · obtain ⟨t, -, ht⟩ := hl 1 (by omega) u hu b
    exact excl_spec _ _ _ _ _ _ ht _ (h _ (row_length _ _))
      (by rw [bit_snd, hc1 _ (row_length _ _), row_getD _ _ _ hu])

/-! ### Minimum circuits -/

/-- No circuit computing the block is smaller than `gs`. -/
def Min2 (cls k shift : ℕ) (gs : List Gate) : Prop :=
  ∀ gs' o0 o1 n0 n1, Computes2 cls k shift gs' o0 o1 n0 n1 → gs.length ≤ gs'.length

/-- Outputs read off representatives (`GateElim.Rep`: a constant, or `±` a node) over a circuit
give outputs of that circuit, since neither output can be a constant. -/
lemma computes2_of_reps (cls k shift : ℕ) (hc : NoConst cls k shift) (gs : List Gate) (R0 R1 : Rep)
    (h0 : R0.Lt (k + 2 + gs.length)) (h1 : R1.Lt (k + 2 + gs.length)) (n0 n1 : Bool)
    (h : ∀ x : List Bool, x.length = k + 2 →
      BlockOK cls shift x (n0 ^^ R0.eval (run x gs), n1 ^^ R1.eval (run x gs))) :
    ∃ o0 o1 m0 m1, Computes2 cls k shift gs o0 o1 m0 m1 := by
  have hnc := not_const cls k shift hc (fun x => n0 ^^ R0.eval (run x gs))
    (fun x => n1 ^^ R1.eval (run x gs)) h
  cases R0 with
  | const c => exact absurd ⟨n0 ^^ c, fun x _ => rfl⟩ hnc.1
  | lit q0 b0 =>
    cases R1 with
    | const c => exact absurd ⟨n1 ^^ c, fun x _ => rfl⟩ hnc.2
    | lit q1 b1 =>
      refine ⟨q0, q1, n0 ^^ b0, n1 ^^ b1, h0, h1, fun x hx => ?_⟩
      have := h x hx
      simp only [Rep.eval] at this
      unfold V; simpa [Bool.xor_assoc] using this

/-- **In a minimum circuit no gate is redundant** (a constant, `±x_u`, or `±` an earlier gate, on
all rows): deleting the redundant gates (`GateElim.build`) would leave a smaller one. -/
theorem no_redundant (cls k shift : ℕ) (hc : NoConst cls k shift) (gs : List Gate) (o0 o1 : ℕ)
    (n0 n1 : Bool) (h : Computes2 cls k shift gs o0 o1 n0 n1) (hmin : Min2 cls k shift gs) :
    ∀ j < gs.length, ¬ Redundant (k + 2) gs {x | x.length = k + 2} j := by
  classical
  intro j hj hred
  have hT : ∀ x ∈ ({x | x.length = k + 2} : Set (List Bool)), x.length = k + 2 := fun x hx => hx
  obtain ⟨hLt, hEv⟩ := build_inv (k + 2) gs _ hT gs.length le_rfl
  have hcnt := build_count (k + 2) gs {x | x.length = k + 2} gs.length
  have hpos : 0 < ((Finset.range gs.length).filter
      (fun h => Redundant (k + 2) gs {x | x.length = k + 2} h)).card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hred⟩⟩
  obtain ⟨o0', o1', m0, m1, hc'⟩ := computes2_of_reps cls k shift hc _ _ _ (hLt o0) (hLt o1) n0 n1
    (fun x hx => by
      have e0 := hEv x hx o0; have e1 := hEv x hx o1
      rw [List.take_length] at e0 e1
      rw [← e0, ← e1]; exact h.2.2 x hx)
  have := hmin _ _ _ _ _ hc'
  omega

/-- **A minimum circuit in the CNF's shape**: sorted reads of earlier nodes, tables `0` on `00`
(negations pushed forward, into the output bits). -/
theorem normalize (cls k shift : ℕ) (hc : NoConst cls k shift) (gs : List Gate) (o0 o1 : ℕ)
    (n0 n1 : Bool) (h : Computes2 cls k shift gs o0 o1 n0 n1) (hmin : Min2 cls k shift gs) :
    ∃ gs1 m0 m1, gs1.length = gs.length ∧ Shaped (k + 2) gs1 ∧ Normal gs1 ∧
      Computes2 cls k shift gs1 o0 o1 m0 m1 := by
  have hnr := no_redundant cls k shift hc gs o0 o1 n0 n1 h hmin
  set gsS := gs.map sortG with hgsS
  set N := normL (List.replicate (k + 2) false) gsS with hN
  have hlenS : gsS.length = gs.length := by simp [gsS]
  have hlenN : N.1.length = gs.length := by rw [hN, normL_length, hlenS]
  refine ⟨N.1, n0 ^^ N.2.getD o0 false, n1 ^^ N.2.getD o1 false, hlenN, ?_, normL_normal gsS _, ?_⟩
  · rw [shaped_iff]
    intro i hi
    obtain ⟨ea, eb⟩ := normL_getElem gsS _ i hi
    have hi' : i < gs.length := by omega
    obtain ⟨ha, hb, hne⟩ := reads_ok (k + 2) gs i hi' (hnr i hi')
    rw [ea, eb]
    simp only [gsS, List.getElem_map, sortG]
    split_ifs <;> (try dsimp only at *) <;> omega
  · refine ⟨by have := h.1; omega, by have := h.2.1; omega, fun x hx => ?_⟩
    have hR := nrel_run gsS (List.replicate (k + 2) false) x x
      ⟨rfl, by simp [hx], fun i => by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> simp⟩
    have e : ∀ o, V N.1 x o = (V gs x o ^^ N.2.getD o false) := by
      intro o; unfold V; rw [hR.2.2, hgsS, run_map_sortG x gs]
    have key : ∀ a b d : Bool, ((a ^^ d) ^^ (b ^^ d)) = (a ^^ b) := by decide
    rw [e, e, key, key]
    exact h.2.2 x hx

/-- Neither output is an input, since neither can be an input literal. -/
lemma outs_gates (cls k shift : ℕ) (hl : NoLit cls k shift) (gs : List Gate) (o0 o1 : ℕ)
    (n0 n1 : Bool) (h : Computes2 cls k shift gs o0 o1 n0 n1) : k + 2 ≤ o0 ∧ k + 2 ≤ o1 := by
  have hnl := not_lit cls k shift hl (fun x => n0 ^^ V gs x o0) (fun x => n1 ^^ V gs x o1) h.2.2
  constructor
  · by_contra hlt; push Not at hlt
    exact (hnl o0 hlt n0).1 (fun x hx => by unfold V; rw [run_getD_input _ _ _ (by omega)])
  · by_contra hlt; push Not at hlt
    exact (hnl o1 hlt n1).2 (fun x hx => by unfold V; rw [run_getD_input _ _ _ (by omega)])

/-- **`sym`'s no-dead-gate half, for two outputs**: in a minimum circuit every gate is an output
or is read by a later gate; otherwise deleting it (`Reduction.delete_nodes`) leaves a smaller one. -/
theorem used_of_min (cls k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Computes2 cls k shift gs o0 o1 n0 n1) (hmin : Min2 cls k shift gs) :
    ∀ j (_ : j < gs.length), o0 = k + 2 + j ∨ o1 = k + 2 + j ∨
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

/-! ### The canonical form: the block is symmetric in the counted bits -/

lemma filter_length_comp (τ : ℕ → ℕ) (hτ : ∀ i, τ (τ i) = i) (l : List ℕ) (hl : l.Nodup)
    (hmem : ∀ i ∈ l, τ i ∈ l) (p : ℕ → Bool) :
    (l.filter (p ∘ τ)).length = (l.filter p).length := by
  have hinj : Function.Injective τ := fun a b e => by rw [← hτ a, e, hτ]
  have hperm : (l.map τ).Perm l := by
    rw [List.perm_ext_iff_of_nodup (hl.map hinj) hl]
    intro a
    simp only [List.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hmem b hb
    · intro ha; exact ⟨τ a, hmem a ha, hτ a⟩
  have := (hperm.filter p).length_eq
  rw [List.filter_map, List.length_map] at this
  exact this

lemma drop_count (k : ℕ) (x : List Bool) (hx : x.length = k + 2) :
    (x.drop 2).count true = ((List.range' 2 k).filter (x.getD · false)).length := by
  have : x.drop 2 = (List.range' 2 k).map (x.getD · false) := by
    apply List.ext_getElem
    · simp [hx]
    · intro i h1 h2
      simp only [List.getElem_drop, List.getElem_map, List.getElem_range']
      rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]
      congr 1; omega
  rw [this, count_map]

/-- Swapping two counted bits changes nothing the block asks. -/
lemma blockOK_swap (cls k shift u v : ℕ) (hu : M3Sound.S k u) (hv : M3Sound.S k v) (x : List Bool)
    (hx : x.length = k + 2) (w : Bool × Bool) (h : BlockOK cls shift (swapIn u v x) w) :
    BlockOK cls shift x w := by
  unfold M3Sound.S at hu hv
  have hg : ∀ i, i < 2 → (swapIn u v x).getD i false = x.getD i false := by
    intro i hi
    rw [swapIn_getD, if_pos (by omega)]
    congr 1; unfold tr; split_ifs <;> omega
  have hcnt : ((swapIn u v x).drop 2).count true = (x.drop 2).count true := by
    rw [drop_count k _ (by rw [swapIn_length, hx]), drop_count k x hx]
    have e : ((List.range' 2 k).filter ((swapIn u v x).getD · false)) =
        (List.range' 2 k).filter ((x.getD · false) ∘ tr u v) := by
      apply List.filter_congr
      intro i hi
      rw [List.mem_range'_1] at hi
      simp only [Function.comp, swapIn_getD, if_pos (show i < x.length by omega)]
    rw [e]
    apply filter_length_comp _ (tr_inv u v) _ List.nodup_range'
    intro i hi
    rw [List.mem_range'_1] at hi ⊢
    unfold tr; split_ifs <;> omega
  intro res hres
  have := h res (by rw [hg 0 (by omega), hg 1 (by omega)]; exact hres)
  rw [hcnt] at this
  exact this

/-- The spec `canonicalL` canonicalizes: two outputs, negated by `n0`, `n1`, meet `BlockOK`. -/
def F2 (cls shift : ℕ) (n0 n1 : Bool) (x : List Bool) (ys : List Bool) : Prop :=
  ∃ a b, ys = [a, b] ∧ BlockOK cls shift x (n0 ^^ a, n1 ^^ b)

lemma symOnL_F2 (cls k shift : ℕ) (n0 n1 : Bool) :
    SymOnL (k + 2) (M3Sound.S k) (F2 cls shift n0 n1) := by
  rintro u v hu hv x hx ys ⟨a, b, rfl, h⟩
  exact ⟨a, b, rfl, blockOK_swap cls k shift u v hu hv x hx _ h⟩

lemma computesL_F2 (cls k shift : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) :
    ComputesL (k + 2) (F2 cls shift n0 n1) gs [o0, o1] ↔
      ∀ x : List Bool, x.length = k + 2 → BlockOK cls shift x (n0 ^^ V gs x o0, n1 ^^ V gs x o1) := by
  unfold ComputesL F2 V
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨a, b, hab, hB⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hab
    rw [hab.1, hab.2]; exact hB
  · intro hB; exact ⟨_, _, rfl, hB⟩

/-! ### Gate elimination, for two outputs -/

/-- The substitution `x_v := c`: old input `i` is new input `i` below `v` and `i − 1` above. -/
def fixσ (v : ℕ) (c : Bool) : ℕ → Rep :=
  fun i => if i < v then .lit i false else if i = v then .const c else .lit (i - 1) false

lemma inRow_fix (n v : ℕ) (c : Bool) (hv : v < n) (y : List Bool) (hy : y.length + 1 = n) :
    inRow n (fixσ v c) y = y.take v ++ c :: y.drop v := by
  apply List.ext_getElem
  · simp [inRow]; omega
  · intro i h1 h2
    have hvl : (y.take v).length = v := by simp only [List.length_take]; omega
    simp only [inRow, List.length_map, List.length_range] at h1
    simp only [inRow, List.getElem_map, List.getElem_range, fixσ]
    rw [List.getElem_append]
    by_cases h3 : i < v
    · rw [if_pos h3, dif_pos (by rw [hvl]; exact h3)]
      simp only [Rep.eval, Bool.false_xor, List.getElem_take]
      exact List.getD_eq_getElem _ _ (by omega)
    · by_cases h5 : i = v
      · subst h5
        rw [if_neg (lt_irrefl _), if_pos rfl, dif_neg (by omega)]
        simp [hvl, Rep.eval]
      · rw [if_neg h3, if_neg h5, dif_neg (by omega), List.getElem_cons, dif_neg (by omega)]
        simp only [Rep.eval, Bool.false_xor, List.getElem_drop]
        rw [List.getD_eq_getElem _ _ (by omega)]
        congr 1; omega

/-- Fixing a counted bit to `c` leaves the block on the other bits, with `c` added to the shift. -/
lemma blockOK_fix (cls k shift v : ℕ) (c : Bool) (hv1 : 2 ≤ v) (hv2 : v < k + 3) (y : List Bool)
    (hy : y.length = k + 2) (w : Bool × Bool) :
    BlockOK cls shift (y.take v ++ c :: y.drop v) w ↔ BlockOK cls (shift + c.toNat) y w := by
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

/-- **The bound behind `elim`, for two outputs.** If every circuit for the `k`-bit block with
shift `shift + c` has at least `L` gates, then in any circuit for the `(k + 1)`-bit block at
most `size − L` gates are redundant on the rows with a counted bit `x_v = c`. (Delete them
(`GateElim.build`); substitute `x_v := c` (`GateElim.srel_run`); what is left computes the
smaller block, and neither of its outputs is a constant.) -/
theorem elim_bound (cls k shift : ℕ) (c : Bool) (hc : NoConst cls k (shift + c.toNat)) (L : ℕ)
    (hLB : ∀ gs o0 o1 n0 n1, Computes2 cls k (shift + c.toNat) gs o0 o1 n0 n1 → L ≤ gs.length)
    (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) (h : Computes2 cls (k + 1) shift gs o0 o1 n0 n1)
    (v : ℕ) (hv1 : 2 ≤ v) (hv2 : v < k + 3) :
    redCount (k + 3) gs {x | x.length = k + 3 ∧ x.getD v false = c} + L ≤ gs.length := by
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

/-! ### Assembly: a minimum circuit satisfies `Adm3` -/

/-- The `elim` bounds `(L0, L1)` are sound for the block: in every circuit for it, at most
`size − L_c` gates are redundant on the rows with a counted bit `x_v = c`. -/
def ElimSound (cls k shift : ℕ) (elimL : Option (ℕ × ℕ)) : Prop :=
  ∀ L, elimL = some L → ∀ gs o0 o1 n0 n1, Computes2 cls k shift gs o0 o1 n0 n1 →
    ∀ v, 2 ≤ v → v < k + 2 → ∀ c : Bool,
      redCount (k + 2) gs {x | x.length = k + 2 ∧ x.getD v false = c} + (if c then L.2 else L.1) ≤
        gs.length

open CnfSound (row row_length) in
/-- **A minimum circuit for the block, in the form the CNF asserts.** For a block whose outputs
can be neither constants nor input literals, and `elim` bounds that are sound for it, a minimum
circuit yields one of the same size satisfying `M3Sound.Adm3`: shaped, normal, outputs at gates,
computing the block, no degenerate or dead gate, `order`, `distinct`, `symvars` with its table
clause on the counted bits, and the `elim` bounds. -/
theorem exists_adm3 (cls k shift : ℕ) (elimL : Option (ℕ × ℕ)) (hc : NoConst cls k shift)
    (hl : NoLit cls k shift) (helim : ElimSound cls k shift elimL) (g0 : List Gate) (o0 o1 : ℕ)
    (n0 n1 : Bool) (h0 : Computes2 cls k shift g0 o0 o1 n0 n1) (hmin : Min2 cls k shift g0) :
    ∃ gs p0 p1 m0 m1, gs.length = g0.length ∧ M3Sound.Adm3 cls k shift elimL gs p0 p1 m0 m1 := by
  obtain ⟨gs1, m0, m1, hl1, hs1, hn1, hc1⟩ := normalize cls k shift hc g0 o0 o1 n0 n1 h0 hmin
  have hg1 := outs_gates cls k shift hl gs1 o0 o1 m0 m1 hc1
  obtain ⟨gs, os, hl2, hlo, hs, hn, ho, hcL, hO, hI, hT⟩ :=
    canonicalL (k + 2) (M3Sound.S k) (fun u hu => hu.2) _ (symOnL_F2 cls k shift m0 m1) gs1 [o0, o1]
      hs1 hn1 (by
        intro o h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact ⟨hg1.1, hc1.1⟩
        · exact ⟨hg1.2, hc1.2.1⟩)
      ((computesL_F2 cls k shift gs1 o0 o1 m0 m1).mpr hc1.2.2)
  obtain ⟨p0, p1, rfl⟩ : ∃ p0 p1, os = [p0, p1] := by
    match os, hlo with
    | [p0, p1], _ => exact ⟨p0, p1, rfl⟩
  have hp0 := ho p0 (by simp)
  have hp1 := ho p1 (by simp)
  have hcc : Computes2 cls k shift gs p0 p1 m0 m1 :=
    ⟨hp0.2, hp1.2, (computesL_F2 cls k shift gs p0 p1 m0 m1).mp hcL⟩
  have hmin' : Min2 cls k shift gs := fun gs' a b c d h => by
    rw [hl2, hl1]; exact hmin gs' a b c d h
  have hNR := no_redundant cls k shift hc gs p0 p1 m0 m1 hcc hmin'
  have hshape := (shaped_iff (k + 2) gs).mp hs
  refine ⟨gs, p0, p1, m0, m1, by rw [hl2, hl1],
    { shaped := hs, normal := hn, out0 := hp0, out1 := hp1,
      computes := fun t _ A hA =>
        (blockOK_row cls k shift t _).mp (hcc.2.2 (row (k + 2) t) (row_length _ _)) A hA,
      nondegenerate := ?_, used := used_of_min cls k shift gs p0 p1 m0 m1 hcc hmin',
      order := hO, distinct := hNR, symin := fun _ => hI, table := fun _ => hT,
      elim := fun L hL v hv1 hv2 => ?_ }⟩
  · -- `sym` (i): a degenerate table makes the gate `0`, `x_a` or `x_b`, which is redundant
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hsj := hshape j hj
    have hnorm := hn _ hg
    have hT' : ∀ x ∈ ({x | x.length = k + 2} : Set (List Bool)), x.length = k + 2 := fun x hx => hx
    have red : ∀ φ : Bool → Bool → Bool, (∀ p q, gs[j].op p q = φ p q) →
        ((∀ p q, φ p q = false) ∨ (∀ p q, φ p q = p) ∨ (∀ p q, φ p q = q)) →
        Redundant (k + 2) gs {x | x.length = k + 2} j := by
      intro φ hφ hcase
      rcases hcase with h | h | h
      · exact Or.inl ⟨false, fun x hx => by
          rw [V_gate (k + 2) x hx gs j hj (by omega) (by omega), hφ, h]⟩
      · exact redundant_of_fun (k + 2) gs _ hT' j gs[j].a (by omega) id (fun x hx => by
          rw [V_gate (k + 2) x hx gs j hj (by omega) (by omega), hφ, h]; rfl)
      · exact redundant_of_fun (k + 2) gs _ hT' j gs[j].b (by omega) id (fun x hx => by
          rw [V_gate (k + 2) x hx gs j hj (by omega) (by omega), hφ, h]; rfl)
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h1, h2, h3⟩
      refine hNR j hj (red gs[j].op (fun _ _ => rfl) (Or.inl fun p q => ?_))
      cases p <;> cases q <;> first | exact hnorm | exact h1 | exact h2 | exact h3
    · rintro ⟨h1, h2, h3⟩
      refine hNR j hj (red gs[j].op (fun _ _ => rfl) (Or.inr (Or.inl fun p q => ?_)))
      cases p <;> cases q <;> first | exact hnorm | exact h1 | exact h2 | exact h3
    · rintro ⟨h1, h2, h3⟩
      refine hNR j hj (red gs[j].op (fun _ _ => rfl) (Or.inr (Or.inr fun p q => ?_)))
      cases p <;> cases q <;> first | exact hnorm | exact h1 | exact h2 | exact h3
  · -- `elim`: each count is at most the gates redundant at `x_v = c` (`Mod3Lower.elimCount_le`)
    have b0 := elimCount_le (k + 2) gs hs v hv2 false
    have b1 := elimCount_le (k + 2) gs hs v hv2 true
    have e0 := helim L hL gs p0 p1 m0 m1 hcc v hv1 hv2 false
    have e1 := helim L hL gs p0 p1 m0 m1 hcc v hv1 hv2 true
    simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
    exact ⟨by omega, by omega⟩

/-- **A lower bound from runs.** If for every `r` with `1 ≤ r < s` no circuit of `r` gates satisfies
`Adm3`, then every circuit computing the block has at least `s` gates. -/
theorem lower3 (cls k shift : ℕ) (elimL : Option (ℕ × ℕ)) (hc : NoConst cls k shift)
    (hl : NoLit cls k shift) (helim : ElimSound cls k shift elimL) (s : ℕ)
    (hno : ∀ r, 1 ≤ r → r < s → ∀ gs p0 p1 m0 m1, gs.length = r →
      ¬ M3Sound.Adm3 cls k shift elimL gs p0 p1 m0 m1) :
    ∀ gs o0 o1 n0 n1, Computes2 cls k shift gs o0 o1 n0 n1 → s ≤ gs.length := by
  classical
  intro gs o0 o1 n0 n1 h
  by_contra hlt
  have hex : ∃ m, ∃ gs : List Gate, ∃ o0 o1 n0 n1, Computes2 cls k shift gs o0 o1 n0 n1 ∧
      gs.length = m := ⟨_, gs, o0, o1, n0, n1, h, rfl⟩
  obtain ⟨g0, q0, q1, b0, b1, hg0, hlen0⟩ := Nat.find_spec hex
  have hmin : Min2 cls k shift g0 := fun gs' a b c d h' =>
    hlen0 ▸ Nat.find_min' hex ⟨gs', a, b, c, d, h', rfl⟩
  have hle := hmin gs o0 o1 n0 n1 h
  obtain ⟨gs', p0, p1, m0, m1, hl', hadm⟩ := exists_adm3 cls k shift elimL hc hl helim g0 q0 q1 b0 b1
    hg0 hmin
  have hpos : 1 ≤ gs'.length := by have := hadm.out0; omega
  exact hno gs'.length hpos (by omega) gs' p0 p1 m0 m1 rfl hadm

/-! ### The runs -/

/-- The `k = 3` symmetry-only job the elim bounds rest on: class `cls`, shift `shift`, `r` gates. -/
def job3 (cls shift r : ℕ) : M3Gen.Job := ⟨cls, 3, shift, r, none, .whole⟩

/-- **The 3-bit blocks' sizes, from their runs.** If the `k = 3` CNFs with shift `c` are
unsatisfiable for `r = 1 … L − 1`, every circuit for the 3-bit block with shift `c` has at least
`L` gates. -/
theorem lb3 (cls : ℕ) (hcls : cls = 1 ∨ cls = 2 ∨ cls = 3) (c : Bool) (L : ℕ)
    (hU : ∀ r, 1 ≤ r → r < L → (CnfGen.toCNF (M3Gen.cnf (job3 cls c.toNat r))).Unsat) :
    ∀ gs o0 o1 n0 n1, Computes2 cls 3 c.toNat gs o0 o1 n0 n1 → L ≤ gs.length := by
  have hf := spec_facts cls 3 c.toNat hcls (by cases c <;> simp)
  exact lower3 cls 3 c.toNat none hf.1 hf.2 (fun L h => by cases h) L
    (fun r h1 h2 gs p0 p1 m0 m1 hr => M3Sound.no_adm3_whole cls 3 c.toNat r none (hU r h1 h2) gs p0 p1 m0 m1 hr)

/-- **Kulikov's `m3v4g11`, per code class: no circuit over B2 with at most 11 gates computes the
4-bit block.** For `cls ∈ {1, 2, 3}` (the three classes of two-bit residue codes, `M3Gen.code`),
no circuit of `≤ 11` gates (`Computes2`: any two-input gates, outputs any two nodes, each
optionally negated) computes `BlockOK cls 0`, from these hypotheses, each that a CNF generated in
Lean (`M3Gen.cnf`) is unsatisfiable:
* `h3s0`, `h3s1`: the 3-bit blocks (shift 0 and 1, symmetry options only) at every `r` below the
  sizes the `k = 4` runs' `elim` used (`M3Sound.elimOf cls`);
* `hwhole`, `h11`: the hypotheses of `M3Sound.m3v4g11_le11` (`k = 4`, shift 0, with `elim`). -/
theorem m3v4g11 (cls : ℕ) (hcls : cls = 1 ∨ cls = 2 ∨ cls = 3)
    (h3s0 : ∀ r, 1 ≤ r → r < (M3Sound.elimOf cls).1 → (CnfGen.toCNF (M3Gen.cnf (job3 cls 0 r))).Unsat)
    (h3s1 : ∀ r, 1 ≤ r → r < (M3Sound.elimOf cls).2 → (CnfGen.toCNF (M3Gen.cnf (job3 cls 1 r))).Unsat)
    (hwhole : ∀ r, 1 ≤ r → r ≤ 10 → (CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls r .whole))).Unsat)
    (h11 : (CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls 11 .whole))).Unsat ∨
      ((CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls 11 .cover))).Unsat ∧
        ∀ c ∈ M3Gen.cubes 4, (CnfGen.toCNF (M3Gen.cnf (M3Sound.job cls 11 (.leaf c)))).Unsat)) :
    ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 →
      ¬ Computes2 cls 4 0 gs o0 o1 n0 n1 := by
  have hf := spec_facts cls 4 0 hcls (by simp)
  have helim : ElimSound cls 4 0 (some (M3Sound.elimOf cls)) := by
    intro L hL gs o0 o1 n0 n1 h v hv1 hv2 c
    cases hL
    have hc3 := (spec_facts cls 3 c.toNat hcls (by cases c <;> simp)).1
    have hLB := lb3 cls hcls c (if c then (M3Sound.elimOf cls).2 else (M3Sound.elimOf cls).1)
      (by cases c
          · simpa using h3s0
          · simpa using h3s1)
    have := elim_bound cls 3 0 c (by simpa using hc3) _ (by simpa using hLB) gs o0 o1 n0 n1 h v hv1 hv2
    simpa using this
  intro gs o0 o1 n0 n1 hle h
  have := lower3 cls 4 0 _ hf.1 hf.2 helim 12
    (fun r h1 h2 gs' p0 p1 m0 m1 hr hadm =>
      M3Sound.m3v4g11_le11 cls hwhole h11 gs' p0 p1 m0 m1 (by omega) hadm) gs o0 o1 n0 n1 h
  omega

end M3Reduce
