import Garden.M3Gen
import Garden.CnfSound

/-!
# Every admissible two-output circuit satisfies its `m3v4g11` job's CNF

`M3Gen.cnf j` is the Lean transcription of the CNF the 2026-10-27 runs solved for job `j` (byte
for byte: `research/circuits/m3_cnf_compare.py`). Here a circuit `gs` with outputs `o0`, `o1`
(negated by `n0`, `n1`) gives each meaning a value (`ev`), and:

* `number_sat`: the numbering only renames (as `CnfSound.number_sat`, for `M3Gen.N`).
* **`adm3_sat`**: if `gs` satisfies `Adm3` (it computes the block of the job's class, `k` and shift,
  on every row whose input word has a residue, and meets the clause families the job's options
  add) and lies in the job's cube (for a leaf) or in none of them (for the cover), then the job's
  CNF is satisfiable.
* **`no_adm3_whole`, `no_adm3_split`**: so an `Unsat` whole CNF, or an `Unsat` cover with every
  leaf `Unsat`, leaves no `Adm3` circuit of `r` gates.

`Adm3` is a list of what the CNF *asserts*. That a minimum circuit for the block can be chosen to
satisfy it (the symmetry breaks for two outputs, and the gate-elimination bounds from the 3-bit
blocks' runs) is proved in `M3Reduce.lean` (`exists_adm3`, `m3v4g11`).
The families that do not mention the outputs reuse `CnfSound`'s lemmas through `M3Gen.lift`.
-/

namespace M3Sound
open CircuitDual GateElim SymCanon Mod3Lower

/-! ### Numbering (as in `CnfSound`, over `M3Gen.N`) -/

section Numbering
open M3Gen

def Good (ev : N → Bool) : Ev → Prop
  | .decl _ => True
  | .cl c => ∃ l ∈ c, ev l.1 = l.2

def LitTrue (ev : N → Bool) (D : Array N) (l : Int) : Prop :=
  l.natAbs ≠ 0 ∧ l.natAbs ≤ D.size ∧ ev (D[l.natAbs - 1]?.getD (.neg 0)) = decide (0 < l)

structure Inv (ev : N → Bool) (s : NS) : Prop where
  map_ok : ∀ m k, s.map[m]? = some k → k ≠ 0 ∧ k ≤ s.decls.size ∧ s.decls[k - 1]? = some m
  out_ok : ∀ c ∈ s.out, ∃ l ∈ c, LitTrue ev s.decls l

def Ext (D D' : Array N) : Prop := D.size ≤ D'.size ∧ ∀ i < D.size, D'[i]? = D[i]?

lemma ext_refl (D : Array N) : Ext D D := ⟨le_refl _, fun _ _ => rfl⟩

lemma ext_trans {D D' D'' : Array N} (h1 : Ext D D') (h2 : Ext D' D'') : Ext D D'' :=
  ⟨le_trans h1.1 h2.1, fun i hi => by rw [h2.2 i (by have := h1.1; omega), h1.2 i hi]⟩

lemma ext_push (D : Array N) (m : N) : Ext D (D.push m) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [Array.getElem?_push, if_neg (by omega)]

lemma litTrue_ext {ev : N → Bool} {D D' : Array N} (h : Ext D D') {l : Int} (hl : LitTrue ev D l) :
    LitTrue ev D' l := by
  obtain ⟨h1, h2, h3⟩ := hl
  exact ⟨h1, le_trans h2 h.1, by rw [h.2 _ (by omega)]; exact h3⟩

lemma inv_declare (ev : N → Bool) (s : NS) (m : N) (h : Inv ev s) : Inv ev (s.declare m) := by
  constructor
  · intro m' k hk
    simp only [NS.declare, Std.HashMap.getElem?_insert] at hk ⊢
    split_ifs at hk with hm
    · cases hk
      have : m = m' := by simpa using hm
      subst this
      refine ⟨by omega, by simp, ?_⟩
      simp
    · obtain ⟨h1, h2, h3⟩ := h.map_ok m' k hk
      refine ⟨h1, by simp; omega, ?_⟩
      rw [(ext_push s.decls m).2 _ (by omega), h3]
  · intro c hc
    obtain ⟨l, hl, hl'⟩ := h.out_ok c hc
    exact ⟨l, hl, litTrue_ext (ext_push _ _) hl'⟩

lemma lit_spec (ev : N → Bool) (s : NS) (l : L) (h : Inv ev s) :
    Inv ev (s.lit l).1 ∧ Ext s.decls (s.lit l).1.decls ∧ (s.lit l).1.out = s.out ∧
      (ev l.1 = l.2 → LitTrue ev (s.lit l).1.decls (s.lit l).2) := by
  obtain ⟨m, b⟩ := l
  unfold NS.lit
  split
  · rename_i k hk
    obtain ⟨h1, h2, h3⟩ := h.map_ok m k hk
    refine ⟨h, ext_refl _, rfl, fun he => ?_⟩
    simp only at he ⊢
    refine ⟨by rw [CnfSound.mkLit_natAbs]; exact h1, by rw [CnfSound.mkLit_natAbs]; exact h2, ?_⟩
    rw [CnfSound.mkLit_natAbs, h3, CnfSound.mkLit_pos k h1]; exact he
  · refine ⟨inv_declare ev s m h, ext_push _ _, rfl, fun he => ?_⟩
    simp only at he ⊢
    refine ⟨by rw [CnfSound.mkLit_natAbs]; omega, by rw [CnfSound.mkLit_natAbs]; simp [NS.declare], ?_⟩
    rw [CnfSound.mkLit_natAbs, CnfSound.mkLit_pos _ (by omega)]
    simp [NS.declare, he]

lemma lits_spec (ev : N → Bool) : ∀ (c : List L) (s : NS), Inv ev s →
    Inv ev (s.lits c).1 ∧ Ext s.decls (s.lits c).1.decls ∧ (s.lits c).1.out = s.out ∧
      ((∃ l ∈ c, ev l.1 = l.2) → ∃ i ∈ (s.lits c).2, LitTrue ev (s.lits c).1.decls i)
  | [], s, h => ⟨h, ext_refl _, rfl, fun ⟨_, hl, _⟩ => by simp at hl⟩
  | l :: ls, s, h => by
    obtain ⟨h1, e1, o1, t1⟩ := lit_spec ev s l h
    obtain ⟨h2, e2, o2, t2⟩ := lits_spec ev ls _ h1
    have hl : s.lits (l :: ls) =
        (((s.lit l).1.lits ls).1, (s.lit l).2 :: ((s.lit l).1.lits ls).2) := rfl
    rw [hl]
    refine ⟨h2, ext_trans e1 e2, by rw [o2, o1], ?_⟩
    rintro ⟨l', hl', he⟩
    simp only [List.mem_cons] at hl' ⊢
    rcases hl' with rfl | hl'
    · exact ⟨_, Or.inl rfl, litTrue_ext e2 (t1 he)⟩
    · obtain ⟨i, hi, hi'⟩ := t2 ⟨l', hl', he⟩
      exact ⟨i, Or.inr hi, hi'⟩

lemma inv_step (ev : N → Bool) (s : NS) (e : Ev) (h : Inv ev s) (he : Good ev e) :
    Inv ev (s.step e) := by
  cases e with
  | decl m => exact inv_declare ev s m h
  | cl c =>
    obtain ⟨h1, -, -, t1⟩ := lits_spec ev c s h
    have hc' : s.step (.cl c) = { (s.lits c).1 with out := (s.lits c).1.out.push (s.lits c).2 } := rfl
    rw [hc']
    constructor
    · exact h1.map_ok
    · intro c' hc'
      simp only [Array.mem_push] at hc'
      rcases hc' with hc' | rfl
      · exact h1.out_ok c' hc'
      · exact t1 he

lemma inv_number (ev : N → Bool) (evs : List Ev) (h : ∀ e ∈ evs, Good ev e) :
    Inv ev (number evs) := by
  have : ∀ (evs : List Ev) (s : NS), Inv ev s → (∀ e ∈ evs, Good ev e) →
      Inv ev (evs.foldl NS.step s) := by
    intro evs
    induction evs with
    | nil => intro s h _; exact h
    | cons e es ih =>
      intro s h he
      exact ih _ (inv_step ev s e h (he e (by simp))) (fun e' he' => he e' (by simp [he']))
  apply this evs {} _ h
  constructor
  · intro m k hk; simp at hk
  · intro c hc; simp at hc

def assign (ev : N → Bool) (evs : List Ev) (k : ℕ) : Bool := ev ((number evs).decls[k]?.getD (.neg 0))

theorem number_sat (ev : N → Bool) (evs : List Ev) (h : ∀ e ∈ evs, Good ev e) :
    (CnfGen.toCNF (number evs).out.toList).eval (assign ev evs) = true := by
  have hI := inv_number ev evs h
  simp only [CnfGen.toCNF, Std.Sat.CNF.eval, List.all_toArray, List.all_map, List.all_eq_true,
    Array.mem_toList_iff]
  intro c hc
  obtain ⟨l, hl, h1, h2, h3⟩ := hI.out_ok c hc
  simp only [Function.comp, Std.Sat.CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨l, hl, by simp [CnfGen.litOf, assign, h3]⟩

end Numbering

/-! ### What each variable means for a two-output circuit -/

section Meaning
variable (n : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)

def onode (o : ℕ) : ℕ := if o = 0 then o0 else o1
def oneg (o : ℕ) : Bool := if o = 0 then n0 else n1

open Classical in
/-- The circuit's value for each meaning; `CnfGen` meanings as in `CnfSound.ev` (whose output
arguments the lifted families never read). -/
noncomputable def ev : M3Gen.N → Bool
  | .b m => CnfSound.ev n gs o0 n0 m
  | .osel o i => decide (onode o0 o1 o = i)
  | .neg o => oneg n0 n1 o
  | .y o t => oneg n0 n1 o ^^ CnfSound.nodeV n gs t (onode o0 o1 o)

lemma lift_good (es : List CnfGen.Ev) (h : ∀ e ∈ es, CnfSound.Good (CnfSound.ev n gs o0 n0) e) :
    ∀ e ∈ M3Gen.lift es, Good (ev n gs o0 o1 n0 n1) e := by
  intro e he
  simp only [M3Gen.lift, List.mem_flatMap] at he
  obtain ⟨e', he', he⟩ := he
  have hg := h e' he'
  cases e' with
  | decl m => simp [M3Gen.lift1] at he; subst he; trivial
  | cl c =>
    simp only [M3Gen.lift1, List.mem_singleton] at he
    subst he
    obtain ⟨l, hl, hv⟩ := hg
    exact ⟨(.b l.1, l.2), List.mem_map.mpr ⟨l, hl, rfl⟩, hv⟩
  | lazy m d => simp [M3Gen.lift1] at he

end Meaning

/-! ### The specification -/

/-- The inputs `symvars` ranges over: the counted bits `x2 .. x_{k+1}`. -/
def S (k u : ℕ) : Prop := 2 ≤ u ∧ u < k + 2

/-- The options record `CnfSound`'s chain and table lemmas read (only `S` matters to them). -/
def R3 (k : ℕ) : Tower.Opts :=
  { S := S k, symin := true, table := true, first01 := false, allin := false, elim := none,
    elim2 := none, sem := fun _ _ => False }

lemma proj_spec (cls k shift o t : ℕ) (b : Bool) (h : M3Gen.proj cls k shift o t = some b) :
    ∃ A, M3Gen.allowed cls k shift t = some A ∧ ∀ w ∈ A, M3Gen.bit o w = b := by
  unfold M3Gen.proj at h
  split at h
  · cases h
  · rename_i A hA
    refine ⟨A, hA, ?_⟩
    split at h
    · cases h
    · rename_i w ws
      split_ifs at h with hall
      cases h
      intro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · rfl
      · have := List.all_eq_true.mp hall w' hw'
        simpa using this

/-- **What a job's CNF asserts about `gs`** (`n = k + 2`, `r = gs.length`): outputs `o0`, `o1`
xor `n0`, `n1` give an allowed word on every row whose input word has a residue, and the clause
families of `m3v4g11.encode`'s options hold. `allin` is not a field: every circuit that computes
the block satisfies it (`allin_of_computes`). -/
structure Adm3 (cls k shift : ℕ) (elimL : Option (ℕ × ℕ)) (gs : List Gate) (o0 o1 : ℕ)
    (n0 n1 : Bool) : Prop where
  shaped : Shaped (k + 2) gs
  normal : Normal gs
  out0 : k + 2 ≤ o0 ∧ o0 < k + 2 + gs.length
  out1 : k + 2 ≤ o1 ∧ o1 < k + 2 + gs.length
  computes : ∀ t < 2 ^ (k + 2), ∀ A, M3Gen.allowed cls k shift t = some A →
    (n0 ^^ CnfSound.nodeV (k + 2) gs t o0, n1 ^^ CnfSound.nodeV (k + 2) gs t o1) ∈ A
  nondegenerate : ∀ g ∈ gs,
    ¬ (g.op false true = false ∧ g.op true false = false ∧ g.op true true = false) ∧
    ¬ (g.op false true = false ∧ g.op true false = true ∧ g.op true true = true) ∧
    ¬ (g.op false true = true ∧ g.op true false = false ∧ g.op true true = true)
  used : ∀ j (_ : j < gs.length), o0 = k + 2 + j ∨ o1 = k + 2 + j ∨
    ∃ i, ∃ hi : i < gs.length, j < i ∧ Reads gs[i] (k + 2 + j)
  order : Order (k + 2) gs
  distinct : ∀ j < gs.length, ¬ Redundant (k + 2) gs {x | x.length = k + 2} j
  symin : 2 ≤ k → SymInOrd (S k) gs
  table : 2 ≤ k → TableOK (S k) gs
  elim : ∀ L, elimL = some L → ∀ v, 2 ≤ v → v < k + 2 →
    elimCount (k + 2) v false gs + L.1 ≤ gs.length ∧ elimCount (k + 2) v true gs + L.2 ≤ gs.length

/-! ### Each family -/

section Fam
variable (cls k shift : ℕ) (elimL : Option (ℕ × ℕ)) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)

lemma coreDecls_good : ∀ e ∈ M3Gen.coreDecls (k + 2) gs.length 2, Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  intro e he
  simp only [M3Gen.coreDecls, List.mem_append, List.mem_flatMap, List.mem_map] at he
  rcases he with (⟨i, -, he⟩ | ⟨o, -, i, -, rfl⟩) | ⟨o, -, rfl⟩
  · refine lift_good _ _ _ _ _ _ _ (fun e' he' => ?_) e he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at he'
    rcases he' with ((⟨_, -, rfl⟩ | rfl | rfl | rfl) | ⟨_, -, rfl⟩) <;> trivial
  · trivial
  · trivial

variable {cls k shift elimL gs o0 o1 n0 n1}

lemma onode_lt (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (o : ℕ) :
    k + 2 ≤ onode o0 o1 o ∧ onode o0 o1 o < k + 2 + gs.length := by
  unfold onode; split_ifs
  · exact h.out0
  · exact h.out1

lemma symCls_good (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) :
    ∀ e ∈ M3Gen.symCls (k + 2) gs.length 2, Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  intro e he
  simp only [M3Gen.symCls, List.mem_flatMap, List.mem_append, List.mem_singleton] at he
  obtain ⟨i, hi, he | rfl⟩ := he
  · refine lift_good _ _ _ _ _ _ _ (fun e' he' => ?_) e he
    -- the three table clauses are `CnfGen.symCls`'s first three for gate `i`
    have hsub : e' ∈ CnfGen.symCls (k + 2) gs.length := by
      simp only [CnfGen.symCls, List.mem_flatMap]
      refine ⟨i, hi, ?_⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he' ⊢
      rcases he' with rfl | rfl | rfl <;> simp
    -- `CnfSound.symCls_good` needs a whole `Adm`; the table clauses only use `nondegenerate`
    rw [CnfSound.mem_gates] at hi
    obtain ⟨n1', n2', n3'⟩ := h.nondegenerate _ (CnfSound.gt_mem (k + 2) gs i hi.1 hi.2)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he'
    clear hsub
    have three : ∀ (b1 b2 b3 : Bool) (c : List CnfGen.L),
        (.fbit i false true, b1) ∈ c → (.fbit i true false, b2) ∈ c → (.fbit i true true, b3) ∈ c →
        ¬ ((CnfSound.gt (k + 2) gs i).op false true = !b1 ∧ (CnfSound.gt (k + 2) gs i).op true false = !b2 ∧
          (CnfSound.gt (k + 2) gs i).op true true = !b3) →
        CnfSound.Good (CnfSound.ev (k + 2) gs o0 n0) (.cl c) := by
      intro b1 b2 b3 c h1 h2 h3 hn
      by_cases a : (CnfSound.gt (k + 2) gs i).op false true = b1
      · exact CnfSound.good_cl _ h1 a
      by_cases b : (CnfSound.gt (k + 2) gs i).op true false = b2
      · exact CnfSound.good_cl _ h2 b
      by_cases d : (CnfSound.gt (k + 2) gs i).op true true = b3
      · exact CnfSound.good_cl _ h3 d
      refine absurd ⟨?_, ?_, ?_⟩ hn
      · revert a; cases (CnfSound.gt (k + 2) gs i).op false true <;> cases b1 <;> simp
      · revert b; cases (CnfSound.gt (k + 2) gs i).op true false <;> cases b2 <;> simp
      · revert d; cases (CnfSound.gt (k + 2) gs i).op true true <;> cases b3 <;> simp
    rcases he' with rfl | rfl | rfl
    · exact three true true true _ (by simp [CnfGen.pos]) (by simp [CnfGen.pos]) (by simp [CnfGen.pos])
        (by simpa using n1')
    · exact three true false false _ (by simp [CnfGen.pos]) (by simp [CnfGen.ng]) (by simp [CnfGen.ng])
        (by simpa using n2')
    · exact three false true false _ (by simp [CnfGen.ng]) (by simp [CnfGen.pos]) (by simp [CnfGen.ng])
        (by simpa using n3')
  · rw [CnfSound.mem_gates] at hi
    rcases h.used (i - (k + 2)) (by omega) with ho | ho | ⟨j, hj, hij, hr⟩
    · refine ⟨M3Gen.pos (.osel 0 i), by simp [M3Gen.pos], ?_⟩
      show decide (o0 = i) = true
      simp only [decide_eq_true_eq]; omega
    · refine ⟨M3Gen.pos (.osel 1 i), by simp [M3Gen.pos], ?_⟩
      show decide (o1 = i) = true
      simp only [decide_eq_true_eq]; omega
    · have hm := CnfSound.sel_mem (k + 2) gs h.shaped (k + 2 + j) (by omega) (by omega)
      rw [CnfSound.gt_add (k + 2) gs j hj] at hm
      refine ⟨M3Gen.pos (.b (.sel (k + 2 + j) gs[j].a gs[j].b)), List.mem_append_right _
        (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩), ?_⟩
      · simp only [decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rcases hr with hr | hr <;> [left; right] <;> omega
      · have := CnfSound.ev_sel_self (k + 2) gs o0 n0 (k + 2 + j)
        rw [CnfSound.gt_add (k + 2) gs j hj] at this
        exact this

/-- If no gate reads `x_v`, flipping `x_v` changes no other node. -/
lemma nodeV_flip (n : ℕ) (gs : List Gate) (hs : Shaped n gs) (v : ℕ) (hv : ∀ g ∈ gs, ¬ Reads g v)
    (t : ℕ) : ∀ i, i ≠ v → i < n + gs.length →
      CnfSound.nodeV n gs (t ^^^ (1 <<< v)) i = CnfSound.nodeV n gs t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiv hi
    by_cases hin : i < n
    · rw [CnfSound.nodeV_input n gs _ i hin, CnfSound.nodeV_input n gs _ i hin, Nat.testBit_xor,
        Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp [Ne.symm hiv]
    · obtain ⟨hab, hbi, he⟩ := CnfSound.nodeV_gate n gs hs i (by omega) hi t
      obtain ⟨-, -, he'⟩ := CnfSound.nodeV_gate n gs hs i (by omega) hi (t ^^^ (1 <<< v))
      rw [he, he']
      have hr := hv _ (CnfSound.gt_mem n gs i (by omega) hi)
      unfold Reads at hr
      push_neg at hr
      rw [ih _ (by omega) hr.1 (by omega), ih _ hbi hr.2 (by omega)]

/-- **`allin` holds in every circuit that computes the block**: an input on which some output's
defined bit changes is read by some gate. -/
lemma allin_of_computes (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (v : ℕ) (hv : v < k + 2)
    (o t : ℕ) (a b : Bool) (ho : o < 2) (ht : t < 2 ^ (k + 2))
    (ha : M3Gen.proj cls k shift o t = some a) (hb : M3Gen.proj cls k shift o (t ^^^ (1 <<< v)) = some b)
    (hab : a ≠ b) : ∃ g ∈ gs, Reads g v := by
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

lemma allinCls_good (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) :
    ∀ e ∈ M3Gen.allinCls (k + 2) gs.length [M3Gen.proj cls k shift 0, M3Gen.proj cls k shift 1],
      Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  intro e he
  simp only [M3Gen.allinCls, List.mem_map] at he
  obtain ⟨v, hv, rfl⟩ := he
  simp only [M3Gen.essential, List.mem_filter, List.mem_range, List.any_eq_true, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hv
  obtain ⟨hvn, tt, htt, t, htr, hne⟩ := hv
  rw [CnfSound.mem_rows] at htr
  have hex : ∃ g ∈ gs, Reads g v := by
    rcases htt with rfl | rfl
    · revert hne; split <;> intro hne
      · rename_i a b ha hb
        exact allin_of_computes h v hvn 0 t a b (by omega) htr ha hb (by simpa using hne)
      · simp at hne
    · revert hne; split <;> intro hne
      · rename_i a b ha hb
        exact allin_of_computes h v hvn 1 t a b (by omega) htr ha hb (by simpa using hne)
      · simp at hne
  obtain ⟨g, hg, hr⟩ := hex
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  have hm := CnfSound.sel_mem (k + 2) gs h.shaped (k + 2 + j) (by omega) (by omega)
  rw [CnfSound.gt_add (k + 2) gs j hj] at hm
  refine ⟨M3Gen.pos (.b (.sel (k + 2 + j) gs[j].a gs[j].b)), List.mem_map.mpr
    ⟨_, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩, ?_⟩
  · simp only [decide_eq_true_eq]; exact hr
  · have := CnfSound.ev_sel_self (k + 2) gs o0 n0 (k + 2 + j)
    rw [CnfSound.gt_add (k + 2) gs j hj] at this
    exact this

lemma elimCls_good (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (L : ℕ × ℕ) (hL : elimL = some L) :
    ∀ e ∈ M3Gen.elimCls (k + 2) gs.length (List.range' 2 k) L, Good (ev (k + 2) gs o0 o1 n0 n1) e := by
  refine lift_good _ _ _ _ _ _ _ (fun e he => ?_)
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, List.contains_iff_mem,
    List.mem_range', List.mem_append] at he
  obtain ⟨v, ⟨hvn, i, hi, rfl⟩, (he | he) | he⟩ := he
  · exact CnfSound.kCls_good (k + 2) gs o0 n0 h.normal _ e he
  · exact CnfSound.e1Cls_good (k + 2) gs o0 n0 h.shaped _ false _
      (by have := (h.elim L hL (2 + 1 * i) (by omega) (by omega)).1; omega) e he
  · exact CnfSound.e1Cls_good (k + 2) gs o0 n0 h.shaped _ true _
      (by have := (h.elim L hL (2 + 1 * i) (by omega) (by omega)).2; omega) e he

lemma outCls_good (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (o : ℕ) (ho : o < 2) :
    ∀ e ∈ M3Gen.outCls (k + 2) gs.length o (M3Gen.proj cls k shift o),
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

lemma wordCls_good (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) :
    ∀ e ∈ M3Gen.wordCls (k + 2) gs.length (M3Gen.allowed cls k shift),
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

lemma symvarsCls_good (h : Adm3 cls k shift elimL gs o0 o1 n0 n1) (hk : 2 ≤ k) :
    ∀ e ∈ CnfGen.symvarsCls (k + 2) gs.length (List.range' 2 k),
      CnfSound.Good (CnfSound.ev (k + 2) gs o0 n0) e := by
  have hpos : 0 < gs.length := by have := h.out0; omega
  have hall : ∀ u ∈ List.range' 2 k, S k u := by
    intro u hu
    rw [List.mem_range'_1] at hu
    exact ⟨by omega, by omega⟩
  have hch : ∀ p ∈ (List.range' 2 k).zip (List.range' 2 k).tail, p.1 < p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    simp [List.getElem_zip, List.getElem_tail, List.getElem_range']
  intro x hx
  simp only [CnfGen.symvarsCls, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨p, hp, hx⟩ | ⟨c, hc, hx⟩
  · have hp1 : p.1 ∈ List.range' 2 k := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ List.range' 2 k := List.mem_of_mem_tail (List.of_mem_zip hp).2
    exact CnfSound.chainCls_good (k + 2) (R3 k) gs o0 n0 h.shaped (h.symin hk) p.1 p.2 (hall _ hp1)
      (hall _ hp2) (hch p hp) x hx
  · obtain ⟨a, b, rfl, hsub⟩ := CnfSound.mem_combs2 _ c hc
    simp only [List.mem_singleton] at hx
    subst hx
    refine CnfSound.good_sel (k + 2) gs o0 n0 (k + 2) a b (by simp [CnfGen.tableCl]) fun hsl => ?_
    exact CnfSound.table_good (k + 2) (R3 k) gs o0 n0 hpos (h.table hk) _ (by simp [CnfGen.tableCl])
      (by simp [CnfGen.tableCl]) (by simp [CnfGen.tableCl])
      ⟨hsl.1 ▸ hall a (hsub.subset (by simp)), hsl.2 ▸ hall b (hsub.subset (by simp))⟩

end Fam

/-! ### The whole job -/

/-- The circuit lies in cube `c` (`m3v4g11_run.cube_lits`). -/
def InCube (k : ℕ) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (c : (ℕ × ℕ) × (Bool × Bool × Bool) × (ℕ × ℕ)) : Prop :=
  ∀ l ∈ M3Gen.cubeLits (k + 2) c, ev (k + 2) gs o0 o1 n0 n1 l.1 = l.2

/-- What the job's cube part asks of the circuit. -/
def CubeOK (j : M3Gen.Job) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool) : Prop :=
  match j.kind with
  | .whole => True
  | .leaf c => InCube j.k gs o0 o1 n0 n1 c
  | .cover => ∀ c ∈ M3Gen.cubes j.k, ¬ InCube j.k gs o0 o1 n0 n1 c

/-- **An `Adm3` circuit of `r` gates satisfies the job's CNF** (in its cube, for a leaf; in
none, for the cover). -/
theorem adm3_sat (j : M3Gen.Job) (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool)
    (h : Adm3 j.cls j.k j.shift j.elimL gs o0 o1 n0 n1) (hr : j.r = gs.length)
    (hc : CubeOK j gs o0 o1 n0 n1) :
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

/-- **A whole run**: an `Unsat` CNF leaves no `Adm3` circuit of `r` gates. -/
theorem no_adm3_whole (cls k shift r : ℕ) (elimL : Option (ℕ × ℕ))
    (hU : (CnfGen.toCNF (M3Gen.cnf ⟨cls, k, shift, r, elimL, .whole⟩)).Unsat) :
    ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length = r →
      ¬ Adm3 cls k shift elimL gs o0 o1 n0 n1 :=
  fun gs o0 o1 n0 n1 hr h => adm3_sat ⟨cls, k, shift, r, elimL, .whole⟩ gs o0 o1 n0 n1 h hr.symm trivial hU

/-- **A split run**: an `Unsat` cover and every leaf `Unsat` leave no `Adm3` circuit of `r` gates. -/
theorem no_adm3_split (cls k shift r : ℕ) (elimL : Option (ℕ × ℕ))
    (hcover : (CnfGen.toCNF (M3Gen.cnf ⟨cls, k, shift, r, elimL, .cover⟩)).Unsat)
    (hleaf : ∀ c ∈ M3Gen.cubes k, (CnfGen.toCNF (M3Gen.cnf ⟨cls, k, shift, r, elimL, .leaf c⟩)).Unsat) :
    ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length = r →
      ¬ Adm3 cls k shift elimL gs o0 o1 n0 n1 := by
  intro gs o0 o1 n0 n1 hr h
  by_cases hin : ∃ c ∈ M3Gen.cubes k, InCube k gs o0 o1 n0 n1 c
  · obtain ⟨c, hcm, hc⟩ := hin
    exact adm3_sat ⟨cls, k, shift, r, elimL, .leaf c⟩ gs o0 o1 n0 n1 h hr.symm hc (hleaf c hcm)
  · push_neg at hin
    exact adm3_sat ⟨cls, k, shift, r, elimL, .cover⟩ gs o0 o1 n0 n1 h hr.symm hin hcover

/-! ### The runs -/

/-- The elim sizes `(L0, L1)` the 2026-10-27 runs used at `k = 4`, shift 0: the certified sizes of
the 3-bit block with shift 0 and 1 (`m3v4g11_audit.out`, items 3 and 4). -/
def elimOf : ℕ → ℕ × ℕ
  | 1 => (9, 10)
  | _ => (10, 10)

/-- The run's job for class `cls` at `r` gates. -/
def job (cls r : ℕ) (kind : M3Gen.Kind) : M3Gen.Job := ⟨cls, 4, 0, r, some (elimOf cls), kind⟩

/-- **`m3v4g11`, per class, from its runs**: if the whole CNFs for `r = 1 … 10` are unsatisfiable,
and at `r = 11` either the whole CNF is or the cover and all 420 leaves are, then no `Adm3`
circuit for the 4-bit block of class `cls` has at most 11 gates. -/
theorem m3v4g11_le11 (cls : ℕ)
    (hwhole : ∀ r, 1 ≤ r → r ≤ 10 → (CnfGen.toCNF (M3Gen.cnf (job cls r .whole))).Unsat)
    (h11 : (CnfGen.toCNF (M3Gen.cnf (job cls 11 .whole))).Unsat ∨
      ((CnfGen.toCNF (M3Gen.cnf (job cls 11 .cover))).Unsat ∧
        ∀ c ∈ M3Gen.cubes 4, (CnfGen.toCNF (M3Gen.cnf (job cls 11 (.leaf c)))).Unsat)) :
    ∀ (gs : List Gate) (o0 o1 : ℕ) (n0 n1 : Bool), gs.length ≤ 11 →
      ¬ Adm3 cls 4 0 (some (elimOf cls)) gs o0 o1 n0 n1 := by
  intro gs o0 o1 n0 n1 hle h
  have hpos : 1 ≤ gs.length := by have := h.out0; omega
  by_cases h10 : gs.length ≤ 10
  · exact no_adm3_whole cls 4 0 gs.length _ (hwhole _ hpos h10) gs o0 o1 n0 n1 rfl h
  · have h11' : gs.length = 11 := by omega
    rcases h11 with hw | ⟨hc, hl⟩
    · exact no_adm3_whole cls 4 0 11 _ hw gs o0 o1 n0 n1 h11' h
    · exact no_adm3_split cls 4 0 11 _ hc hl gs o0 o1 n0 n1 h11' h

end M3Sound
