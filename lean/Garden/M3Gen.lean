import Garden.CnfGen

/-!
# Kulikov's `m3v4g11` CNFs, generated in Lean

A transcription of `research/circuits/m3v4g11.encode` (which calls `optimal_circuit.encode` with two
outputs, don't-cares, `order`, `allin`, `distinct`, `symvars` and optionally `elim` as a dict on the
counted bits) and of `m3v4g11_run.build`'s cube clauses. Like `CnfGen` it reproduces Python's
variable numbering, clause order and DIMACS writer, so each CNF can be compared byte for byte with
the sha256 recorded for the 2026-10-27 runs (`research/circuits/m3_cnf_compare.py`).

Every clause builder of `CnfGen` that does not mention outputs (`coreCls`, `orderCls`,
`distinctCls`, `kCls`, `e1Cls`, `symvarsCls`) is reused through `lift`; what is new is the
two-output core (`osel o i`, `neg o`), the targets with don't-cares, and the relational variables
`y o t` (output `o`'s value on row `t`) with one clause per forbidden word on rows whose allowed
words are not a product set (class 2, residue 1).

Only the CNF is here; this file replaces "the Python encoder" by "a Lean function with the same
bytes". What the clauses mean for a circuit is proved in `M3Sound` (`adm3_sat`, 2026-10-27 10:20).
-/

namespace M3Gen

open CnfGen (combs gates rows pairs selItems)

/-- What a CNF variable means: a `CnfGen` meaning, or the two-output additions. -/
inductive N where
  | b (m : CnfGen.M)
  | osel (o i : Nat)
  | neg (o : Nat)
  | y (o t : Nat)
  deriving DecidableEq, Hashable, Repr

abbrev L := N × Bool

@[inline] def pos (m : N) : L := (m, true)
@[inline] def ng (m : N) : L := (m, false)

inductive Ev where
  | decl (m : N)
  | cl (c : List L)

/-- A `CnfGen` event over meanings `.b m` (no `lazy` event occurs in the builders used here). -/
def lift1 : CnfGen.Ev → List Ev
  | .decl m => [.decl (.b m)]
  | .cl c => [.cl (c.map fun l => (.b l.1, l.2))]
  | .lazy _ _ => []

def lift (es : List CnfGen.Ev) : List Ev := es.flatMap lift1

/-! ### The specification (`m3v4g11.spec`, `projection`, `is_product`) -/

/-- `WORDS`: `(w[0], w[1])`; output `o` carries `w[o]`. -/
def words : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

/-- `CODES[cls][w]`: the residue a word means, `none` if unused. -/
def code : Nat → Bool × Bool → Option Nat
  | 1, (false, false) => some 0 | 1, (false, true) => some 1 | 1, (true, false) => some 2 | 1, (true, true) => some 2
  | 2, (false, false) => some 0 | 2, (false, true) => some 1 | 2, (true, false) => some 1 | 2, (true, true) => some 2
  | 3, (false, false) => some 0 | 3, (false, true) => some 1 | 3, (true, false) => some 2 | 3, (true, true) => none
  | _, _ => none

/-- `spec(cls, k, shift)[t]`: the allowed output words on row `t` (in `WORDS` order), or `none`
if the input word `(x0, x1)` is unused. -/
def allowed (cls k shift t : Nat) : Option (List (Bool × Bool)) :=
  match code cls (t.testBit 0, t.testBit 1) with
  | none => none
  | some res =>
    let want := (res + ((List.range' 2 k).filter (t.testBit ·)).length + shift) % 3
    some (words.filter fun w => code cls w == some want)

def bit (o : Nat) (w : Bool × Bool) : Bool := if o = 0 then w.1 else w.2

/-- `projection(W)[o][t]`: defined iff every allowed word agrees on bit `o`. -/
def proj (cls k shift o t : Nat) : Option Bool :=
  match allowed cls k shift t with
  | none => none
  | some A => match A with
    | [] => none
    | w :: ws => if ws.all (bit o · == bit o w) then some (bit o w) else none

/-- `is_product(A)`: `A` equals the product of its two bit projections. -/
def isProduct (A : List (Bool × Bool)) : Bool :=
  words.all fun w => !(A.any (·.1 == w.1) && A.any (·.2 == w.2)) || A.contains w

/-! ### `optimal_circuit.encode` with two outputs -/

/-- The declarations before the first clause: per gate `sel`, `fbit`, `val`; then `outsel`
(output-major), then `neg`. -/
def coreDecls (n r m : Nat) : List Ev :=
  ((gates n r).flatMap fun i =>
    lift ((pairs i).map (fun p => .decl (.sel i p.1 p.2)) ++
      [.decl (.fbit i false true), .decl (.fbit i true false), .decl (.fbit i true true)] ++
      (rows n).map fun t => .decl (.val i t))) ++
  ((List.range m).flatMap fun o => (gates n r).map fun i => .decl (.osel o i)) ++
  (List.range m).map fun o => .decl (.neg o)

def symCls (n r m : Nat) : List Ev :=
  (gates n r).flatMap fun i =>
    lift [.cl [CnfGen.pos (.fbit i false true), CnfGen.pos (.fbit i true false), CnfGen.pos (.fbit i true true)],
      .cl [CnfGen.pos (.fbit i false true), CnfGen.ng (.fbit i true false), CnfGen.ng (.fbit i true true)],
      .cl [CnfGen.ng (.fbit i false true), CnfGen.pos (.fbit i true false), CnfGen.ng (.fbit i true true)]] ++
    [.cl ((List.range m).map (fun o => pos (.osel o i)) ++
      ((selItems n r).filter fun x => i < x.1 ∧ (x.2.1 = i ∨ x.2.2 = i)).map
        fun x => pos (.b (.sel x.1 x.2.1 x.2.2)))]

/-- `essential_inputs(n, targets)` with don't-cares. -/
def essential (n : Nat) (tts : List (Nat → Option Bool)) : List Nat :=
  (List.range n).filter fun v => tts.any fun tt => (rows n).any fun t =>
    match tt t, tt (t ^^^ (1 <<< v)) with
    | some a, some b => a != b
    | _, _ => false

def allinCls (n r : Nat) (tts : List (Nat → Option Bool)) : List Ev :=
  (essential n tts).map fun v =>
    .cl (((selItems n r).filter fun x => x.2.1 = v ∨ x.2.2 = v).map fun x => pos (.b (.sel x.1 x.2.1 x.2.2)))

/-- `elim` as a dict `{v: (B0, B1)}` over `vs` in increasing order, the bounds given as sizes
`(L0, L1)` with `B_c = max(r − L_c, 0)` (`m3v4g11.elim_bounds`). -/
def elimCls (n r : Nat) (vs : List Nat) (Ls : Nat × Nat) : List Ev :=
  lift (((List.range n).filter (vs.contains ·)).flatMap fun v =>
    CnfGen.kCls n r v ++ CnfGen.e1Cls n r v false (r - Ls.1) ++ CnfGen.e1Cls n r v true (r - Ls.2))

def outCls (n r o : Nat) (tt : Nat → Option Bool) : List Ev :=
  (.cl ((gates n r).map fun i => pos (.osel o i)) ::
    (combs 2 (gates n r)).map fun c => .cl (c.map fun i => ng (.osel o i))) ++
  (gates n r).flatMap fun i => (rows n).flatMap fun t =>
    match tt t with
    | none => []
    | some true => [.cl [ng (.osel o i), pos (.b (.val i t)), pos (.neg o)],
                    .cl [ng (.osel o i), ng (.b (.val i t)), ng (.neg o)]]
    | some false => [.cl [ng (.osel o i), pos (.b (.val i t)), ng (.neg o)],
                     .cl [ng (.osel o i), ng (.b (.val i t)), pos (.neg o)]]

/-! ### `m3v4g11.encode`'s word clauses -/

def yDef (n r o t : Nat) : List Ev :=
  .decl (.y o t) :: (gates n r).flatMap fun i =>
    let g := N.osel o i; let v := N.b (.val i t); let y := N.y o t; let nb := N.neg o
    [.cl [ng g, ng y, pos v, pos nb], .cl [ng g, ng y, ng v, ng nb],
     .cl [ng g, pos y, ng v, pos nb], .cl [ng g, pos y, pos v, ng nb]]

def wordCls (n r : Nat) (W : Nat → Option (List (Bool × Bool))) : List Ev :=
  (rows n).flatMap fun t =>
    match W t with
    | none => []
    | some A =>
      if isProduct A then [] else
      yDef n r 0 t ++ yDef n r 1 t ++
      (words.filter fun w => !A.contains w).map fun w =>
        .cl [(.y 0 t, !w.1), (.y 1 t, !w.2)]

/-! ### A job -/

/-- `m3v4g11_run.build`'s job: class, `k`, shift, `r`, optional elim sizes, and the cube part. -/
inductive Kind where
  | whole
  | leaf (c : (Nat × Nat) × (Bool × Bool × Bool) × (Nat × Nat))
  | cover

structure Job where
  cls : Nat
  k : Nat
  shift : Nat
  r : Nat
  elimL : Option (Nat × Nat) := none
  kind : Kind := .whole

/-- `FIRST_PAIRS`, `TABLES`, and `cubes(k)`. -/
def firstPairs : List (Nat × Nat) := [(0, 1), (0, 2), (1, 2), (2, 3)]
def tables : List (Bool × Bool × Bool) :=
  [(false, false, true), (false, true, false), (true, false, false), (true, true, false), (true, true, true)]

def cubes (k : Nat) : List ((Nat × Nat) × (Bool × Bool × Bool) × (Nat × Nat)) :=
  firstPairs.flatMap fun p1 => tables.flatMap fun t1 => (pairs (k + 3)).map fun p2 => (p1, t1, p2)

/-- `cube_lits`: `sel[n, a, b]`, the three table bits, `sel[n + 1, c, d]`. -/
def cubeLits (n : Nat) (c : (Nat × Nat) × (Bool × Bool × Bool) × (Nat × Nat)) : List L :=
  let ((a, b), (f01, f10, f11), (c2, d2)) := c
  [pos (.b (.sel n a b)), (.b (.fbit n false true), f01), (.b (.fbit n true false), f10),
   (.b (.fbit n true true), f11), pos (.b (.sel (n + 1) c2 d2))]

/-- **`build(job)`**, as events. -/
def events (j : Job) : List Ev :=
  let n := j.k + 2
  let r := j.r
  let tts : List (Nat → Option Bool) := [proj j.cls j.k j.shift 0, proj j.cls j.k j.shift 1]
  coreDecls n r 2 ++ lift (CnfGen.coreCls n r) ++ symCls n r 2 ++
  lift (CnfGen.orderCls n r) ++ allinCls n r tts ++ lift (CnfGen.distinctCls n r) ++
  (match j.elimL with | some Ls => elimCls n r (List.range' 2 j.k) Ls | none => []) ++
  (if 2 ≤ j.k then lift (CnfGen.symvarsCls n r (List.range' 2 j.k)) else []) ++
  outCls n r 0 tts[0]! ++ outCls n r 1 tts[1]! ++
  wordCls n r (allowed j.cls j.k j.shift) ++
  match j.kind with
  | .whole => []
  | .leaf c => (cubeLits n c).map fun l => .cl [l]
  | .cover => (cubes j.k).map fun c => .cl ((cubeLits n c).map fun l => (l.1, !l.2))

/-! ### Numbering (as `CnfGen.number`, over `N`) -/

structure NS where
  map : Std.HashMap N Nat := {}
  decls : Array N := #[]
  out : Array (List Int) := #[]

def NS.declare (s : NS) (m : N) : NS :=
  { s with map := s.map.insert m (s.decls.size + 1), decls := s.decls.push m }

def NS.lit (s : NS) (l : L) : NS × Int :=
  match s.map[l.1]? with
  | some k => (s, CnfGen.mkLit k l.2)
  | none => (s.declare l.1, CnfGen.mkLit (s.decls.size + 1) l.2)

def NS.lits : NS → List L → NS × List Int
  | s, [] => (s, [])
  | s, l :: ls =>
    let (s1, i) := s.lit l
    let (s2, is) := s1.lits ls
    (s2, i :: is)

def NS.step (s : NS) : Ev → NS
  | .decl m => s.declare m
  | .cl c => let (s1, is) := s.lits c; { s1 with out := s1.out.push is }

def number (evs : List Ev) : NS := evs.foldl NS.step {}

def cnf (j : Job) : List (List Int) := (number (events j)).out.toList

end M3Gen
