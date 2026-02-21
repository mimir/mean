import LambdaGraph.Nest

/--
A mapping from old labels to new labels assigned for substitution.

There is also a mapping that maps the newly assigned labels back to their
original labels.
-/
structure LabelMap (p : Program) where
  fwd : Vector Nat p.size
  inv : Array (Fin p.size)

open Classical in -- TODO: Remove this by implementing Decidable.
/-- Returns a label map to use for substitution of the variable `n`. -/
noncomputable def Program.labelMap (p : Program) (n : Nat) : LabelMap p :=
  aux 0 (Vector.ofFn Fin.val) #[]
where
  aux i map inv :=
    if h : i < p.size then
      if n ≻[p] i then
        aux (i + 1) (map.set i (p.size + inv.size)) (inv.push ⟨i, h⟩)
      else
        aux (i + 1) map inv
    else
      ⟨map, inv⟩

/--
Substitutes a value for a variable in an expression.

The expression may include references to functions nested inside the function
corresponding to the substitution variable. For these functions, new versions
need to be added to the program, with their bodies substituted in the same way.
This function does not perform this change to the program, but takes a label map
mapping function labels to the labels assigned to their substituted versions.
-/
noncomputable def Expr.subst {p : Program} (e : Expr) (map : LabelMap p)
    (n : Nat) (v : Expr) : Expr :=
  match e with
  | var m => if n = m then v else var (map.fwd[m]?.getD m)
  | fn m => fn (map.fwd[m]?.getD m)
  | app f e => (f.subst map n v).app (e.subst map n v)
  | bool b => bool b
  | cond c et ef => (c.subst map n v).cond (et.subst map n v) (ef.subst map n v)

/--
A map specifying how variables should be substituted.

Variables that should remain untouched are simply mapped to themselves.
-/
abbrev VarMap (n : Nat) := Vector Expr n

/-- Updates the map to map a given variable to a variable with a fresh label. -/
abbrev VarMap.update {n : Nat} (vm : VarMap n) (m : Nat)
    (h : m < n := by get_elem_tactic) : VarMap (n + 1) :=
  vm.set m (.var n) |>.push (.var n)

/-- Extends the map with identity mappings for programs of a larger size. -/
def VarMap.extend {n n' : Nat} (v : VarMap n) : VarMap n' :=
  Vector.ofFn (fun m => if _ : ↑m < n then v[↑m] else .var ↑m)

/--
The typing predicate for variable maps.

For a variable map to be well-typed, each expression substituted for a variable
must have the variable's declared type.
-/
def VarMap.Types (p : Program) (vm : VarMap p.size) : Prop :=
  ∀ i (_ : i < p.size), p ⊢ vm[i] : p.ty[i]

/--
A map specifying how function references should be substituted.

Function labels for which no new mapping exists yet are mapped to none, while
functions introduced during substitution are mapped to themselves. This
distinction is necessary to support the termination proof for substitution.
-/
abbrev FunMap (n : Nat) := Vector (Option Nat) n

/-- Updates the map to map a given function to a function with a fresh label. -/
abbrev FunMap.update {n : Nat} (fm : FunMap n) (m : Nat)
    (h : m < n := by get_elem_tactic) : FunMap (n + 1) :=
  fm.set m (some n) |>.push (some n)

/-- Counts the number of function labels that might still be remapped. -/
def FunMap.unmapped {n : Nat} (fm : FunMap n) : Nat :=
  fm.countP (· = none)

/--
The typing predicate for function maps.

For a function map to be well-typed, replacement functions must have the same
type as their original.
-/
def FunMap.Types (p : Program) (fm : FunMap p.size) : Prop :=
  ∀ i (_ : i < p.size) m, fm[i] = some m → ∃ (_ : m < p.size), p.ty[i] = p.ty[m]

/-- The result of a substitution. -/
structure SubstResult (p : Program) (fm : FunMap p.size) : Type where
  program : Program
  expr : Expr
  funMap : FunMap program.size
  size_ge : p.size ≤ program.size
  unmapped_le : funMap.unmapped ≤ fm.unmapped

open Classical in
/--
Makes substitutions in an expression according to the given maps.

The expression may include references to functions in which a substitution
variable occurs free. For these functions, new versions need to be added to the
program, with their bodies substituted in the same way. In addition to the new
program and expression, this function returns a new function map to allow
reusing the newly created functions across subexpressions.
-/
noncomputable def Expr.subst' (p : Program) (e : Expr) (vm : VarMap p.size)
    (fm : FunMap p.size) : SubstResult p fm :=
  if ∀ n (_ : n < p.size), e.Free p n → vm[n] = .var n then
    ⟨p, e, fm, Nat.le_refl _, Nat.le_refl _⟩
  else
    match e with
    | var m => ⟨p, vm[m]?.getD (var m), fm, Nat.le_refl _, Nat.le_refl _⟩
    | fn m =>
      if _ : m < p.size then
        match _ : fm[m] with
        | none =>
          let m' := p.size
          let vm₁ := vm.update m
          let fm₁ := fm.update m
          let dummy := (fn m').app (var m') -- temporary body that is always well-typed
          let p₁ := p.push dummy p.ty[m]
          have hsize₁ : p.size ≤ p₁.size := by simp [p₁]
          have hum₁ : fm₁.unmapped < fm.unmapped := by
            simp only [FunMap.unmapped, FunMap.update, reduceCtorEq,
              decide_false, Bool.false_eq_true, not_false_eq_true,
              Vector.countP_push_of_neg, Vector.countP_set, decide_true,
              ↓reduceIte, Nat.add_zero, fm₁, *]
            have : 0 < Vector.countP (fun x => decide (x = none)) fm :=
              Vector.countP_pos_iff.mpr ⟨none, Vector.mem_of_getElem ‹fm[m] = none›, rfl⟩
            omega
          let ⟨p₂, f', fm₂, hsize₂, hum₂⟩ := p.fn[m].subst' p₁ vm₁ fm₁
          let p₃ := p₂.setBody m' f'
          let e' := fn m'
          have hsize : p.size ≤ p₂.size := by omega
          have hum : fm₂.unmapped ≤ fm.unmapped := by omega
          ⟨p₃, e', fm₂, hsize, hum⟩
        | some m' =>
          ⟨p, fn m', fm, Nat.le_refl _, Nat.le_refl _⟩
      else
        ⟨p, fn m, fm, Nat.le_refl _, Nat.le_refl _⟩
    | app f e =>
      let ⟨p₁, f', fm₁, hsize₁, hum₁⟩ := f.subst' p vm fm
      let ⟨p₂, e', fm₂, hsize₂, hum₂⟩ := e.subst' p₁ vm.extend fm₁
      ⟨p₂, f'.app e', fm₂, by omega, by omega⟩
    | bool b => ⟨p, bool b, fm, Nat.le_refl _, Nat.le_refl _⟩
    | cond c et ef =>
      let ⟨p₁, c', fm₁, hsize₁, hum₁⟩ := c.subst' p vm fm
      let vm₁ := vm.extend
      let ⟨p₂, et', fm₂, hsize₂, hum₂⟩ := et.subst' p₁ vm₁ fm₁
      let ⟨p₃, ef', fm₃, hsize₃, hum₃⟩ := ef.subst' p₂ vm₁.extend fm₂
      ⟨p₃, c'.cond et' ef', fm₃, by omega, by omega⟩
termination_by (fm.unmapped, e)
decreasing_by
  · exact Prod.Lex.left p.fn[m] (fn m) hum₁
  · refine Prod.Lex.right fm.unmapped ?_
    simp_wf
    omega
  · apply Prod.Lex.right'
    · assumption
    · simp_wf
      omega
  · refine Prod.Lex.right fm.unmapped ?_
    simp_wf
    omega
  · apply Prod.Lex.right'
    · assumption
    · simp_wf
      omega
  · apply Prod.Lex.right'
    · apply Nat.le_trans <;> assumption
    · simp_wf
      omega

/--
Substitutes a value for a variable in a program.

This creates a new version of each function that depends on `n`, as specified by
the passed label map.
-/
noncomputable def Program.subst (p : Program) (map : LabelMap p) (n : Nat)
    (v : Expr) : Program :=
  let fnExt : Vector Expr map.inv.size :=
    ⟨map.inv.map (p.fn[·].subst map n v), by simp⟩
  let tyExt : Vector Ty map.inv.size :=
    ⟨map.inv.map (p.ty[·]), by simp⟩
  { size := _, fn := p.fn ++ fnExt, ty := p.ty ++ tyExt }

/--
Substitutes a value for a variable in a computation.

This computes the map for translating old labels into new ones and applies the
substitution to the program and the expression.
-/
noncomputable def Computation.subst (p : Computation) (n : Nat) (v : Expr) :
    Computation :=
  let map := p.labelMap n
  ⟨p.toProgram.subst map n v, p.expr.subst map n v⟩

/-- Substitutes a value for a variable in a computation. -/
noncomputable def Computation.subst' (p : Computation) (n : Nat) (v : Expr) :
    Computation :=
  let vm := (Vector.ofFn fun i => .var ↑i).setIfInBounds n v
  let fm := Vector.ofFn fun i => ↑i
  let ⟨p', e', _, _, _⟩ := p.expr.subst' p.toProgram vm fm
  ⟨p', e'⟩

theorem program_subst_size_le {p : Program} {v : Expr} {n : Nat}
    {map : LabelMap p} : p.size ≤ (p.subst map n v).size := by
  simp [Program.subst]

theorem lt_subst_size {p : Program} (v : Expr) {m n : Nat} (map : LabelMap p)
    (hm : m < p.size) : m < (p.subst map n v).size :=
  Nat.lt_of_lt_of_le hm program_subst_size_le

theorem subst_fn_eq_of_lt {p : Program} (v : Expr) {m n : Nat}
    (map : LabelMap p) (hm : m < p.size) :
    (p.subst map n v).fn[m]'(lt_subst_size v map hm) = p.fn[m] := by
  simp [hm, Program.subst]

theorem subst_fn_eq_of_ge {p : Program} (v : Expr) {m n : Nat}
    (map : LabelMap p) (hm : p.size ≤ m) (hm' : m < p.size + map.inv.size) :
    (p.subst map n v).fn[m] = p.fn[map.inv[m - p.size]].subst map n v := by
  simp [hm, Program.subst]

theorem subst_ty_eq {p : Program} (v : Expr) {m n : Nat} (map : LabelMap p)
    (hm : m < p.size) :
    (p.subst map n v).ty[m]'(lt_subst_size v map hm) = p.ty[m] := by
  simp [hm, Program.subst]

theorem expr_types_in_subst {p : Program} {e : Expr} (v : Expr) {t : Ty}
    (n : Nat) (map : LabelMap p) (ht : p ⊢ e : t) :
    p.subst map n v ⊢ e : t := by
  induction ht with try constructor <;> assumption
  | var m hm =>
    rw [← subst_ty_eq v map hm]
    constructor
  | fn m hm =>
    rw [← subst_ty_eq v map hm]
    constructor

structure LabelMap.ValidNew {p : Program} (map : LabelMap p) {i : Nat}
    (h : i < p.size) : Prop where
  fwd_ge : p.size ≤ map.fwd[i]
  fwd_lt : map.fwd[i] < p.size + map.inv.size
  inv_fwd_sub : map.inv[map.fwd[i] - p.size] = i

structure LabelMap.Valid {p : Program} (map : LabelMap p) (n : Nat) : Prop where
  lt : n < p.size
  not_nests : ∀ {i} (h : i < p.size), n ⊁[p] i → map.fwd[i] = i
  nests : ∀ {i} (h : i < p.size), n ≻[p] i → map.ValidNew h
  fwd_inv : ∀ {k} (h : k < map.inv.size), map.fwd[map.inv[k]] = p.size + k

theorem LabelMap.Valid.eq_or_new {p : Program} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i : Nat} (hi : i < p.size) :
    map.fwd[i] = i ∨ map.ValidNew hi := by
  by_cases h : n ≻[p] i
  · right
    exact hmap.nests hi h
  · left
    exact hmap.not_nests hi h

theorem LabelMap.Valid.fwd_lt {p : Program} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i : Nat} (hi : i < p.size) :
    map.fwd[i] < p.size + map.inv.size := by
  rcases hmap.eq_or_new hi with h | h
  · rw [h]
    omega
  · exact h.fwd_lt

theorem LabelMap.Valid.fwd_inj {p : Program} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i j : Nat} (hi : i < p.size) (hj : j < p.size)
    (h : map.fwd[i] = map.fwd[j]) : i = j := by
  by_cases hni : n ≻[p] i
  · obtain ⟨hi', hi'', hinvi⟩ := hmap.nests hi hni
    by_cases hnj : n ≻[p] j
    · obtain ⟨hj', hj'', hinvj⟩ := hmap.nests hj hnj
      simp only [h] at hinvi
      rw [← hinvj, hinvi]
    · have hj' := hmap.not_nests hj hnj
      omega
  · have hi' := hmap.not_nests hi hni
    by_cases hnj : n ≻[p] j
    · obtain ⟨hj', hj'', hinvj⟩ := hmap.nests hj hnj
      omega
    · have hj' := hmap.not_nests hj hnj
      rw [← hi', h, hj']

theorem LabelMap.Valid.eq_map_of_ge {p : Program} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {m : Nat} (hm : p.size ≤ m)
    (hm' : m < p.size + map.inv.size) : ∃ i : Fin p.size, m = map.fwd[i] := by
  exists map.inv[m - p.size]
  rw [hmap.fwd_inv]
  omega

theorem labelMap_valid (p : Program) {n : Nat} (hn : n < p.size) :
    (p.labelMap n).Valid n where
  lt := hn
  not_nests := by
    intro i hi h
    unfold Program.labelMap
    simp [aux_le_not_nests hi (Nat.zero_le i) h]
  nests := by
    intro i hi h
    unfold Program.labelMap
    exact aux_le_nests hi (Nat.zero_le i) h
  fwd_inv := by
    intro i hi
    unfold Program.labelMap
    apply aux_fwd_inv
    simp
where
  aux_gt_map {i j fwd inv} (hi : i < p.size) (hj : i < j) :
      (Program.labelMap.aux p n j fwd inv).fwd[i] = fwd[i] := by
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      split
      · split
        · have : fwd[i] = (fwd.set j (p.size + inv.size) ‹j < p.size›)[i] := by
            simp [show j ≠ i by omega]
          rw [this]
          apply ih <;> omega
        · apply ih <;> omega
      · simp
  aux_inv_size_ge {j fwd inv} :
      inv.size ≤ (Program.labelMap.aux p n j fwd inv).inv.size := by
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      have hj : j < p.size := by omega
      simp only [hj, ↓reduceDIte, ge_iff_le]
      split
      · have hle : inv.size ≤ (inv.push ⟨j, hj⟩).size := by simp
        apply Nat.le_trans hle
        apply ih
        omega
      · apply ih
        omega
  aux_gt_inv {j k fwd inv} (hk : k < inv.size)
      (hk' : k < (Program.labelMap.aux p n j fwd inv).inv.size) :
      (Program.labelMap.aux p n j fwd inv).inv[k] = inv[k] := by
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      have hj : j < p.size := by omega
      simp [hj]
      split
      · have : inv[k] = (inv.push ⟨j, hj⟩)[k]'(by rw [Array.size_push]; omega) :=
          Eq.symm (Array.getElem_push_lt hk)
        rw [this]
        apply ih
        omega
      · apply ih
        omega
  aux_le_not_nests {i j fwd inv} (hi : i < p.size) (hj : j ≤ i) (h : n ⊁[p] i) :
      (Program.labelMap.aux p n j fwd inv).fwd[i] = fwd[i] := by
    have (eq := hd) d := i - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero =>
      simp only [*, show j = i by omega]
      apply aux_gt_map
      simp
    | succ d ih =>
      have hj' := Nat.lt_of_le_of_lt hj hi
      simp only [hj', ↓reduceDIte]
      split
      · have : fwd[i] = (fwd.set j (p.size + inv.size) hj')[i] := by
          simp [show j ≠ i by omega]
        rw [this]
        apply ih <;> omega
      · apply ih <;> omega
  aux_le_nests {i j fwd inv} (hi : i < p.size) (hj : j ≤ i) (h : n ≻[p] i) :
      (Program.labelMap.aux p n j fwd inv).ValidNew hi := by
    have (eq := hd) d := i - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero =>
      simp [*, show j = i by omega]
      refine ⟨?_, ?_, ?_⟩
      · simp [aux_gt_map]
      · have hlt : inv.size < (inv.push ⟨i, hi⟩).size := by simp
        simp only [Nat.lt_add_one, aux_gt_map, Vector.getElem_set_self,
          Nat.add_lt_add_iff_left]
        apply Nat.lt_of_lt_of_le hlt
        simp only [aux_inv_size_ge]
      · simp only [Nat.lt_add_one, aux_gt_map, Vector.getElem_set_self,
          Nat.add_sub_cancel_left]
        have : i = (inv.push ⟨i, hi⟩)[inv.size] := by simp
        conv => rhs; rw [this]
        rw [aux_gt_inv]
    | succ d ih =>
      have hj' : j < p.size := by omega
      simp [hj']
      split <;> apply ih <;> omega
  aux_fwd_inv {j fwd inv}
      (h : ∀ k (_ : k < inv.size), ↑inv[k] < j ∧ fwd[inv[k]] = p.size + k) :
      let ⟨fwd', inv'⟩ := Program.labelMap.aux p n j fwd inv
      ∀ k (_ : k < inv'.size), fwd'[inv'[k]] = p.size + k := by
    intro k hk
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero => simp [*, show ¬j < p.size by omega]
    | succ d ih =>
      simp only [show j < p.size by omega, ↓reduceDIte, Fin.getElem_fin]
      split
      · apply ih
        · intro k' hk'
          simp only [Array.size_push] at hk'
          by_cases k' = inv.size
          · simp [*]
          · have : k' < inv.size := by omega
            obtain ⟨hlt, heq⟩ := h k' this
            simp only [Fin.getElem_fin] at heq
            have hne : j ≠ ↑inv[k'] := Ne.symm (Nat.ne_of_lt hlt)
            simp [*, Array.getElem_push_lt, Nat.lt_succ_of_lt]
        · omega
      · apply ih
        · intro k' hk'
          obtain ⟨hlt, heq⟩ := h k' hk'
          simp [*, Nat.lt_succ_of_lt]
        · omega

theorem subst_ty_map_eq {p : Program} {v : Expr} {m n : Nat} {map : LabelMap p}
    (hm : m < p.size) (hmap : map.Valid n) :
    (p.subst map n v).ty[map.fwd[m]]'(hmap.fwd_lt hm) = p.ty[m] := by
  rcases hmap.eq_or_new hm with h | ⟨hle, hlt, hinv⟩
  · simp [h, hm, Program.subst]
  · simp [*, Program.subst]

theorem expr_subst_types {p : Program} {e v : Expr} {t : Ty} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (ht : p ⊢ e : t)
    (htv : p ⊢ v : p.ty[n]'hmap.lt) :
    p.subst map n v ⊢ e.subst map n v : t := by
  induction ht with try constructor <;> assumption
  | var m hm =>
    by_cases hnm : n = m
    · subst m
      simp [Expr.subst]
      exact expr_types_in_subst _ _ _ htv
    · have hm' : m < map.fwd.size := hm
      simp [hnm, hm', Expr.subst]
      rw [← subst_ty_map_eq hm hmap]
      constructor
  | fn m hm =>
    simp only [Expr.subst, hm, getElem?_pos, Option.getD_some]
    rw [← subst_ty_map_eq hm hmap]
    constructor

theorem subst_types {p : Program} {e v : Expr} {t : Ty} {n : Nat}
    (hn : n < p.size) (ht : ⊢ ⟨p, e⟩ : t) (htv : p ⊢ v : p.ty[n]) :
    ⊢ Computation.subst ⟨p, e⟩ n v : t := by
  obtain ⟨htp, ht⟩ := ht
  dsimp only at *
  constructor
  · intro m hm
    simp [Program.subst, Computation.subst]
    by_cases hm' : m < p.size
    · simp [hm']
      exact expr_types_in_subst _ _ _ (htp _)
    · simp at hm'
      simp [hm']
      exact expr_subst_types (labelMap_valid _ hn) (htp _) htv
  · exact expr_subst_types (labelMap_valid _ hn) ht htv

theorem validRefs_in_subst {p : Program} {e v : Expr} {n : Nat}
    {map : LabelMap p} (he : e.ValidRefs p) :
    e.ValidRefs (p.subst map n v) :=
  Expr.validRefs_of_size_ge program_subst_size_le he

theorem expr_subst_validRefs {p : Program} {e v : Expr} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (he : e.ValidRefs p)
    (hv : v.ValidRefs p) : (e.subst map n v).ValidRefs (p.subst map n v) := by
  induction e with
    try solve | simp_all [Expr.subst]
  | var m =>
    by_cases h : n = m
    · simp only [Expr.subst, ↓reduceIte, h]
      exact validRefs_in_subst hv
    · simp only [Expr.validRefs_var_iff] at he
      simp [*, Expr.subst, ↓reduceIte, getElem?_pos, Option.getD_some]
      exact hmap.fwd_lt he
  | fn m =>
    simp only [Expr.validRefs_fn_iff] at he
    simp only [Expr.subst, getElem?_pos, Option.getD_some, Expr.validRefs_fn_iff, he]
    exact hmap.fwd_lt he

theorem subst_validRefs {p : Program} {v : Expr} {n : Nat} {map : LabelMap p}
    (hmap : map.Valid n) (hp : p.ValidRefs) (hv : v.ValidRefs p) :
    (p.subst map n v).ValidRefs := by
  intro i hi'
  by_cases hi : i < p.size
  · simp [*, subst_fn_eq_of_lt]
    apply_rules [validRefs_in_subst]
  · simp only [Nat.not_lt] at hi
    rw [subst_fn_eq_of_ge _ _ hi]
    apply expr_subst_validRefs <;> apply_rules

theorem subst_eq_var {p : Program} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (he : e.ValidRefs p) (hv : v.Value)
    (h : e.subst map n v = .var m) :
    ∃ i : Fin p.size, m = map.fwd[i] ∧ e = .var i := by
  cases e with simp only [Expr.subst] at h <;> try contradiction
  | var k =>
    simp only [Expr.validRefs_var_iff] at he
    by_cases hnk : n = k
    · simp only [hnk, ↓reduceIte] at h
      subst v
      nomatch hv
    · exists ⟨k, he⟩
      simpa [hnk, he, eq_comm] using h

theorem subst_ne_subst_var {p : Program} {e v : Expr} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hv : v.Value) :
    e.subst map n v ≠ .var n := by
  cases e with simp only [Expr.subst] <;> try intro; contradiction
  | var m =>
    split
    · intro rfl
      nomatch hv
    · by_cases hm : m < p.size
      · rcases hmap.eq_or_new hm with hm | ⟨hle, hlt, hinv⟩
        · simp [*, Ne.symm]
        · simp [hm]
          intro h
          rw [h] at hle
          have := hmap.lt
          omega
      · simp [*, Ne.symm]

theorem subst_eq_fn {p : Program} {e v : Expr} {m n : Nat} {map : LabelMap p}
    (he : e.ValidRefs p) (h : e.subst map n v = .fn m) :
    e = .var n ∨ ∃ i : Fin p.size, m = map.fwd[i] ∧ e = .fn i := by
  cases e with simp only [Expr.subst] at h <;> try contradiction
  | var k =>
    split at h
    · simp [*]
    · simp at h
  | fn k =>
    right
    simp only [Expr.validRefs_fn_iff] at he
    exists ⟨k, he⟩
    simpa [he, eq_comm] using h

theorem subst_eq_app {p : Program} {e e₁ e₂ v : Expr} {n : Nat}
    {map : LabelMap p} (hv : v.Value) (h : e.subst map n v = e₁.app e₂) :
    ∃ e₁' e₂' : Expr, e = e₁'.app e₂' := by
  cases e with try solve | simp [Expr.subst] at h
  | var m =>
    by_cases hnm : n = m
    · simp only [Expr.subst, hnm, ↓reduceIte] at h
      subst v
      nomatch hv
    · simp [hnm, Expr.subst] at h
  | app e₁' e₂' =>
    simp only [Expr.subst, Expr.app.injEq] at h
    exists e₁', e₂'

theorem subst_eq_cond {p : Program} {e c et ef v : Expr} {n : Nat}
    {map : LabelMap p} (hv : v.Value) (h : e.subst map n v = c.cond et ef) :
    ∃ c' et' ef' : Expr, e = c'.cond et' ef' := by
  cases e with try solve | simp [Expr.subst] at h
  | var m =>
    by_cases hnm : n = m
    · simp only [Expr.subst, hnm, ↓reduceIte] at h
      subst v
      nomatch hv
    · simp [hnm, Expr.subst] at h
  | cond c' et' ef' =>
    simp only [Expr.subst, Expr.cond.injEq] at h
    exists c', et', ef'

theorem free_of_free_in_subst {p : Program} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (hp : p.ValidRefs) (he : e.ValidRefs p)
    (hf : e.Free (p.subst map n v) m) : e.Free p m := by
  generalize hp' : p.subst map n v = p' at hf
  open Expr.Free in
  induction hf with
    try solve | grind [var, appL, appR, condC, condT, condF]
  | fn k hk' hne hf ih =>
    simp only [Expr.validRefs_fn_iff] at he
    constructor
    · exact hne
    · subst p'
      rw [subst_fn_eq_of_lt _ _ he] at ih
      exact ih (hp he)

theorem not_free_in_subst {p : Program} {e v : Expr} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hv : v.ValidRefs p) (hc : v.Closed p) (hvv : v.Value)
    : ¬(e.subst map n v).Free (p.subst map n v) n := by
  intro hf
  generalize hp' : p.subst map n v = p', he' : e.subst map n v = e' at hf
  induction hf generalizing e with
  | var => exact subst_ne_subst_var hmap hvv he'
  | fn m hm' hne hf ih =>
    subst p'
    rcases subst_eq_fn he he' with rfl | ⟨⟨i, hi⟩, rfl, rfl⟩
    · simp only [Expr.subst, ↓reduceIte] at he'
      subst v
      simp only [Expr.validRefs_fn_iff] at hv
      rw [subst_fn_eq_of_lt _ _ hv] at hf
      replace hf := free_of_free_in_subst hp (hp hv) hf
      exact hc n (.fn _ _ hne hf)
    · by_cases hd : n ≻[p] i
      · obtain ⟨hle, hlt, hinv⟩ := hmap.nests hi hd
        exact ih (hp hi) (by simp [*, Program.subst])
      · have hi' := hmap.not_nests hi hd
        simp only [Fin.getElem_fin, hi', subst_fn_eq_of_lt _ _ hi] at hf
        simp only [Fin.getElem_fin, hi', ne_eq] at hne
        replace hf := free_of_free_in_subst hp (hp hi) hf
        exact hd (.free _ _ hne hf)
  | appL => grind [Expr.subst, subst_eq_app]
  | appR => grind [Expr.subst, subst_eq_app]
  | condC => grind [Expr.subst, subst_eq_cond]
  | condT => grind [Expr.subst, subst_eq_cond]
  | condF => grind [Expr.subst, subst_eq_cond]

theorem free_or_eq_map_of_free_in_subst {p : Program} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hv : v.ValidRefs p) (hvv : v.Value)
    (hf : (e.subst map n v).Free (p.subst map n v) m) :
    v.Free p m ∨ ∃ i : Fin p.size, m = map.fwd[i] ∧ e.Free p i := by
  generalize hp' : p.subst map n v = p', he' : e.subst map n v = e' at hf
  induction hf generalizing e with
  | var =>
    right
    obtain ⟨⟨i, hi⟩, rfl, rfl⟩ := subst_eq_var he hvv he'
    exists ⟨i, hi⟩
    simp [Expr.Free.var]
  | fn k hk' hne hf ih =>
    subst p'
    rcases subst_eq_fn he he' with rfl | ⟨⟨i, hi⟩, rfl, rfl⟩
    · simp only [Expr.subst, ↓reduceIte] at he'
      subst v
      simp only [Expr.validRefs_fn_iff] at hv
      rw [subst_fn_eq_of_lt _ _ hv] at hf
      replace hf := free_of_free_in_subst hp (hp hv) hf
      solve_by_elim
    · by_cases hd : n ≻[p] i
      · obtain ⟨hle, hlt, hinv⟩ := hmap.nests hi hd
        obtain hf' | ⟨j, rfl, hj⟩ := ih (hp hi) (by simp [*, Program.subst])
        · exact Or.inl hf'
        · have hij : j ≠ i := by
            intro rfl
            contradiction
          exact Or.inr ⟨j, rfl, .fn _ hi hij hj⟩
      · obtain hi' := hmap.not_nests hi hd
        simp only [Fin.getElem_fin, hi', subst_fn_eq_of_lt v map hi] at hf
        replace hf := free_of_free_in_subst hp (hp hi) hf
        simp [hi'] at hne
        have hm : n ⊁[p] m := fun h => hd (.step _ _ hi hne hf h)
        have hlt := lt_size_of_free hp (hp hi) hf
        have hm' := hmap.not_nests hlt hm
        refine Or.inr ⟨⟨m, hlt⟩, by simp [hm'], .fn _ hi hne hf⟩
  | appL => grind [Expr.subst, Expr.Free.appL, subst_eq_app]
  | appR => grind [Expr.subst, Expr.Free.appR, subst_eq_app]
  | condC => grind [Expr.subst, Expr.Free.condC, subst_eq_cond]
  | condT => grind [Expr.subst, Expr.Free.condT, subst_eq_cond]
  | condF => grind [Expr.subst, Expr.Free.condF, subst_eq_cond]

theorem eq_map_of_free_in_subst_of_closed {p : Program} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hv : v.ValidRefs p) (hc : v.Closed p)
    (hvv : v.Value) (hf : (e.subst map n v).Free (p.subst map n v) m) :
    ∃ i : Fin p.size, m = map.fwd[i] ∧ e.Free p i :=
  (free_or_eq_map_of_free_in_subst hmap hp he hv hvv hf).resolve_left (hc m)

theorem nests_of_nests_in_subst {p : Program} {m n k : Nat} {v : Expr}
    {map : LabelMap p} (hk : k < p.size) (hp : p.ValidRefs)
    (h : m ≻[p.subst map n v] k) : m < p.size ∧ m ≻[p] k := by
  generalize hp' : p.subst map n v = p' at h
  induction h with
  | free k hk' hne hf' =>
    have hf : p.fn[k].Free p m := by
      apply free_of_free_in_subst hp (hp hk)
      subst p'
      simpa [subst_fn_eq_of_lt _ _ hk] using hf'
    constructor
    · exact lt_size_of_free hp (hp hk) hf
    · apply Nests.free _ hk hne
      exact hf
  | step l k hk' hne hf' h ih =>
    have hf : p.fn[k].Free p l := by
      apply free_of_free_in_subst hp (hp hk)
      subst p'
      simpa [subst_fn_eq_of_lt _ _ hk] using hf'
    obtain ⟨hm, ih⟩ := ih (lt_size_of_free hp (hp hk) hf)
    constructor
    · exact hm
    · refine Nests.step _ _ hk hne ?_ ih
      exact hf

theorem nestsEq_or_nests_of_nests_map_in_subst {p : Program} {m n k : Nat}
    {v : Expr} {map : LabelMap p} (hk : k < p.size) (hmap : map.Valid n)
    (hp : p.ValidRefs) (hv : v.ValidRefs p) (hvv : v.Value)
    (h : m ≻[p.subst map n v] map.fwd[k]) :
    (∃ l, v.Free p l ∧ m ≽[p] l) ∨
      ∃ i : Fin p.size, m = map.fwd[i] ∧ i ≻[p] k := by
  generalize hp' : p.subst map n v = p', hleq : map.fwd[k] = l at h
  induction h generalizing k with
  | free k' hk' hne hf' =>
    by_cases hnk : n ≻[p] k
    · subst p' k'
      obtain ⟨hle, hlt, hinv⟩ := hmap.nests hk hnk
      simp only [subst_fn_eq_of_ge, Fin.getElem_fin, hle, hinv] at hf'
      obtain hf | ⟨i, heq, hf⟩ :=
        free_or_eq_map_of_free_in_subst hmap hp (hp _) hv hvv hf'
      · exact Or.inl ⟨m, hf, .refl (lt_size_of_free hp hv hf)⟩
      · refine Or.inr ⟨i, heq, ?_⟩
        have : i ≠ k := by
          intro h
          subst k
          contradiction
        constructor <;> assumption
    · subst p' k'
      simp only [hmap.not_nests hk hnk] at *
      simp only [subst_fn_eq_of_lt, hk] at hf'
      have hf := free_of_free_in_subst hp (hp hk) hf'
      have hm := lt_size_of_free hp (hp hk) hf
      have hnm : n ⊁[p] m := fun h => hnk (Nests.step _ _ _ hne hf h)
      refine Or.inr ⟨⟨m, hm⟩, (hmap.not_nests hm hnm).symm, ?_⟩
      constructor <;> assumption
  | step l' k' hk' hne hf' h' ih =>
    by_cases hnk : n ≻[p] k
    · subst p' k'
      obtain ⟨hle, hlt, hinv⟩ := hmap.nests hk hnk
      simp only [subst_fn_eq_of_ge, Fin.getElem_fin, hle, hinv] at hf'
      obtain hf | ⟨l, heq, hf⟩ :=
        free_or_eq_map_of_free_in_subst hmap hp (hp _) hv hvv hf'
      · have hl' := lt_size_of_free hp hv hf
        have ⟨hm, h⟩ := nests_of_nests_in_subst hl' hp h'
        exact Or.inl ⟨l', hf, .nests _ h⟩
      · obtain hf'' | ⟨i, heq', hil⟩ := ih _ heq.symm
        · exact Or.inl hf''
        · refine Or.inr ⟨i, heq', ?_⟩
          have : l ≠ k := by
            intro h
            subst k
            contradiction
          apply Nests.step <;> assumption
    · subst p' k'
      simp only [hmap.not_nests hk hnk] at *
      simp only [subst_fn_eq_of_lt, hk] at hf'
      have hf := free_of_free_in_subst hp (hp hk) hf'
      have hl := lt_size_of_free hp (hp hk) hf
      obtain ⟨hm, hml⟩ := nests_of_nests_in_subst hl hp h'
      have hlk : l' ≻[p] k := by constructor <;> assumption
      have hnl : n ⊁[p] l' := fun h => hnk (nests_trans h hlk)
      have hnm : n ⊁[p] m := fun h => hnl (nests_trans h hml)
      exact Or.inr ⟨⟨m, hm⟩, (hmap.not_nests hm hnm).symm, nests_trans hml hlk⟩

theorem subst_wf  {p : Program} {n : Nat} {v : Expr} {map : LabelMap p}
    (hmap : map.Valid n) (hp : p.ValidRefs) (hv : v.ValidRefs p) (hvv : v.Value)
    (hwf : p.WF) : (p.subst map n v).WF := by
  intro m h
  by_cases hm : m < p.size
  · obtain ⟨-, h'⟩ := nests_of_nests_in_subst hm hp h
    exact hwf m h'
  · simp only [Nat.not_lt] at hm
    have hp' : (p.subst map n v).ValidRefs := subst_validRefs hmap hp hv
    have hm' := lt_size_left_of_nests hp' h
    obtain ⟨⟨i, hi⟩, heq⟩ := hmap.eq_map_of_ge hm hm'
    rw [heq] at h
    obtain ⟨l, hf, hl⟩ | ⟨⟨j, hj⟩, heq, h'⟩ :=
      nestsEq_or_nests_of_nests_map_in_subst hi hmap hp hv hvv h
    · have := lt_size_left_of_nestsEq hp hl
      omega
    · simp only [hmap.fwd_inj hi hj heq] at h'
      exact hwf j h'

theorem Program.subst_ty_eq {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, fm', hsize, _⟩ := e.subst' p vm fm
    p'.ty[n] = p.ty[n] := by
  fun_induction Expr.subst' <;> dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ dummy p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
    subst p₂
    grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    have hp₁ : p₁ = (f.subst' p vm fm).program := by grind
    have hp₂ : p₂ = (e.subst' p₁ vm.extend fm₁).program := by grind
    subst p₁ p₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    have hp₁ : p₁ = (c.subst' p vm fm).program := by grind
    have hp₂ : p₂ = (et.subst' p₁ vm.extend fm₁).program := by grind
    have hp₃ : p₃ = (ef.subst' p₂ vm₁.extend fm₂).program := by grind
    subst p₁ p₂ p₃
    grind

theorem Program.subst_fn_eq_of_lt {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, _, hsize, _⟩ := (e.subst' p vm fm)
    p'.fn[n] = p.fn[n] := by
  fun_induction Expr.subst' <;>
    first | grind
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ dummy p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
    subst p₂
    grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    have hp₁ : p₁ = (f.subst' p vm fm).program := by grind
    have hp₂ : p₂ = (e.subst' p₁ vm.extend fm₁).program := by grind
    subst p₁ p₂
    grind
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    have hp₁ : p₁ = (c.subst' p vm fm).program := by grind
    have hp₂ : p₂ = (et.subst' p₁ vm.extend fm₁).program := by grind
    have hp₃ : p₃ = (ef.subst' p₂ vm₁.extend fm₂).program := by grind
    subst p₁ p₂ p₃
    grind

theorem Expr.types_in_subst_of_types {p : Program} {e₁ e₂ : Expr} {t : Ty}
    {vm : VarMap p.size} {fm : FunMap p.size} (ht : p ⊢ e₁ : t) :
    (e₂.subst' p vm fm).program ⊢ e₁ : t := by
  induction ht with
    first | constructor <;> assumption
          | rw [← Program.subst_ty_eq]; constructor

namespace VarMap

theorem update_types {p : Program} {vm : VarMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : vm.Types p) :
    (vm.update m hm).Types (p.push b p.ty[m]) := by
  intro i hi
  by_cases i = p.size
  · simp only [Vector.getElem_push_eq, *]
    have : p.ty[m] = (p.push b p.ty[m]).ty[p.size] := by simp
    conv => arg 3; rw [this]
    constructor
  · replace hi : i < p.size := by lia
    simp only [Vector.getElem_push_lt, hi]
    by_cases m = i
    · subst i
      simp only [Vector.getElem_set_self]
      have : p.ty[m] = (p.push b p.ty[m]).ty[p.size] := by simp
      conv => arg 3; rw [this]
      constructor
    · rw [Vector.getElem_set_ne _ _ ‹m ≠ i›]
      simpa [*] using Expr.types_in_push_of_types (h i hi)

theorem extend_types {p : Program} (e : Expr) {vm : VarMap p.size}
    (fm : FunMap p.size) (hvm : vm.Types p) :
    vm.extend.Types (e.subst' p vm fm).program := by
  intro i hi
  simp only [VarMap.extend, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · apply Expr.types_in_subst_of_types
    rw [Program.subst_ty_eq]
    apply hvm
    assumption
  · constructor

end VarMap

namespace FunMap

@[simp]
theorem getElem_update_size {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n) :
    (fm.update m hm)[n] = some n := by simp

@[simp]
theorem getElem_update_eq {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n) :
    (fm.update m)[m] = some n := by grind

@[simp]
theorem getElem_update_ne {n : Nat} {fm : FunMap n} {m i : Nat} (hm : m < n)
    (hi : i < n) (hne : i ≠ m) : (fm.update m hm)[i] = fm[i] := by grind

theorem update_types {p : Program} {fm : FunMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : fm.Types p) :
    (fm.update m hm).Types (p.push b p.ty[m]) := by
  intro i hi m' heq
  by_cases i = p.size
  · grind
  · replace hi : i < p.size := by lia
    simp [*]
    by_cases i = m
    · grind [getElem_update_eq]
    · simp only [ne_eq, not_false_eq_true, getElem_update_ne, *] at heq
      obtain ⟨_, _⟩ := h i hi _ heq
      grind

theorem subst_types {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hfm : fm.Types p) :
    let ⟨p', _, fm', _, _⟩ := e.subst' p vm fm
    fm'.Types p' := by
  dsimp only
  fun_induction Expr.subst' <;>
    first | grind
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ dummy p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
    subst p₂
    have hfm₂ : fm₂ = (p.fn[m].subst' p₁ vm₁ fm₁).funMap := by grind
    subst fm₂
    apply ih
    intro i hi k hk
    simp [p₁]
    by_cases i = p.size
    · subst i
      simp only [update, fm₁] at hk
      grind
    · simp only [p₁] at hi
      replace hi : i < p.size := by lia
      by_cases i = m
      · grind [getElem_update_eq]
      · simp [fm₁, *] at hk
        rw [getElem_update_ne _ hi ‹i ≠ m›] at hk
        obtain ⟨_, _⟩ := hfm i hi _ hk
        grind

end FunMap

namespace Expr

theorem subst_types {p : Program} {e : Expr} {t : Ty} {vm : VarMap p.size}
    {fm : FunMap p.size} (ht : p ⊢ e : t) (hvm : vm.Types p) (hfm : fm.Types p) :
    let ⟨p', e', _, _, _⟩ := e.subst' p vm fm
    p' ⊢ e' : t := by
  fun_induction subst' generalizing t <;> dsimp only at *
  next => exact ht
  next p vm fm m h =>
    by_cases hm : m < p.size
    · simp only [hm, getElem?_pos, Option.getD_some]
      have .var _ _ := ht
      apply hvm
    · simp [hm, ht]
  next p vm fm m hm f m' vm₁ fm₁ dummy p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have .fn _ _ := ht
    have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
    subst hp₂
    have : p.ty[m] = p₃.ty[p.size] := by grind [Program.subst_ty_eq]
    rw [this]
    constructor
  next p vm fm m hm m' hm' h =>
    have .fn _ _ := ht
    obtain ⟨_, heq⟩ := hfm _ ‹m < p.size› m' hm'
    rw [heq]
    constructor
  next => exact ht
  next =>
    have .app _ _ t' htf hte := ht
    apply Types.app _ _ t' <;>
      grind [types_in_subst_of_types, VarMap.extend_types, FunMap.subst_types]
  next => exact ht
  next =>
    have .cond _ _ _ _ htc htet htef := ht
    constructor <;>
      grind [types_in_subst_of_types, VarMap.extend_types, FunMap.subst_types]

end Expr

namespace Program

theorem subst_types {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (ht : ⊢ p) (hvm : vm.Types p) (hfm : fm.Types p) :
    ⊢ (e.subst' p vm fm).program := by
  fun_induction Expr.subst' <;>
    first | grind [VarMap.extend_types, FunMap.subst_types]
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ dummy p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    have ht₁ : ⊢ p₁ := by
      apply types_push ht
      constructor
      · constructor
        lia
      · constructor
    have hvm₁ : vm₁.Types p₁ := VarMap.update_types hm hvm
    have hfm₁ : fm₁.Types p₁ := FunMap.update_types hm hfm
    have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
    subst p₂
    have ht₂ : ⊢ _ := ih ht₁ hvm₁ hfm₁
    intro i hi
    simp only [p₃]
    by_cases m' = i
    · subst i
      have hf' : f' = (p.fn[m].subst' p₁ vm₁ fm₁).expr := by grind
      subst f'
      apply Expr.types_in_setBody_of_types
      simp only [Vector.getElem_set_self]
      apply Expr.subst_types
      · exact Expr.types_in_push_of_types (ht hm)
      · exact hvm₁
      · exact hfm₁
    · rw [Vector.getElem_set_ne _ _ ‹m' ≠ i›]
      exact Expr.types_in_setBody_of_types _ (ht₂ hi)

end Program

namespace Computation

theorem subst_types {c : Computation} {t : Ty} {n : Nat} {v : Expr}
    (hn : n < c.size) (ht : ⊢ c : t) (hv : c.toProgram ⊢ v : c.ty[n]) :
    ⊢ c.subst' n v : t := by
  refine ⟨Program.subst_types ht.program_types ?hvm ?hfm,
          Expr.subst_types ht.expr_types ?hvm ?hfm⟩
  · intro i hi
    by_cases n = i
    · simp_all
    · rw [Vector.getElem_setIfInBounds_ne _ ‹n ≠ i›, Vector.getElem_ofFn]
      constructor
  · intro i hi m heq
    grind

end Computation
