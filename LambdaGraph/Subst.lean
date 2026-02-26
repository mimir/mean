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

/-- Creates a new variable map of size `n` for substituting `m` with `v`. -/
@[grind unfold]
def VarMap.mk (n m : Nat) (v : Expr) : VarMap n :=
  (Vector.ofFn (.var ↑·)).setIfInBounds m v

/-- Updates the map to map a given variable to a variable with a fresh label. -/
def VarMap.update {n : Nat} (vm : VarMap n) (m : Nat)
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

/-- Creates a new function map of size `n`. -/
@[grind unfold]
def FunMap.mk (n : Nat) : FunMap n := Vector.ofFn (↑·)

/-- Updates the map to map a given function to a function with a fresh label. -/
def FunMap.update {n : Nat} (fm : FunMap n) (m : Nat)
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
          let p₁ := p.push (recurse m') p.ty[m] -- temporary body that is always well-typed
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
  let ⟨p', e', _, _, _⟩ := p.expr.subst' p.toProgram (.mk _ n v) (.mk _)
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
    exact hwf h'
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
      exact hwf h'

theorem Program.subst_ty_eq {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hn : n < p.size) :
    let ⟨p', _, fm', hsize, _⟩ := e.subst' p vm fm
    p'.ty[n] = p.ty[n] := by
  fun_induction Expr.subst' <;> dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
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
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
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

@[simp]
theorem getElem_update_size {n : Nat} {vm : VarMap n} {m : Nat} (hm : m < n) :
    (vm.update m hm)[n] = .var n := by simp [update]

@[simp]
theorem getElem_update_eq {n : Nat} {vm : VarMap n} {m : Nat} (hm : m < n) :
    (vm.update m hm)[m] = .var n := by simp [update, *]

@[simp]
theorem getElem_update_ne {n : Nat} {vm : VarMap n} {m i : Nat} (hm : m < n)
    (hi : i < n) (hne : m ≠ i) : (vm.update m hm)[i] = vm[i] := by simp [update, *]

@[grind =]
theorem getElem_update {n : Nat} {vm : VarMap n} {m i : Nat} (hm : m < n)
    (hi : i ≤ n) :
    (vm.update m hm)[i] = if _ : n = i ∨ m = i then .var n else vm[i] := by
  split
  next h =>
    cases h
    · simp [← ‹n = i›]
    · simp [*]
  next h =>
    replace hi : i < n := by lia
    have : m ≠ i := by simp_all
    simp_all

@[simp]
theorem getElem_extend_lt {n n' : Nat} {vm : VarMap n} {i : Nat} (hi : i < n)
    (hi' : i < n') : (vm.extend (n' := n'))[i] = vm[i] := by
  simp [VarMap.extend, hi]

@[simp]
theorem getElem_extend_ge {n n' : Nat} {vm : VarMap n} {i : Nat} (hi : n ≤ i)
    (hi' : i < n') : (vm.extend (n' := n'))[i] = .var i := by
  replace hi : ¬i < n := by lia
  simp [extend, hi]

@[grind =]
theorem getElem_extend {n n' : Nat} {vm : VarMap n} {i : Nat} (hi' : i < n') :
    (vm.extend (n' := n'))[i] = if _ : i < n then vm[i] else .var i := by
  split <;> simp_all

@[simp]
theorem extend_eq {n : Nat} {vm : VarMap n} : vm.extend (n' := n) = vm := by
  ext i hi
  simp [extend]

theorem extend_extend {m n k : Nat} {vm : VarMap m} (h : m ≤ n) :
    (vm.extend (n' := n) |>.extend (n' := k)) = vm.extend := by
  ext i hi
  by_cases i < n
  · simp [extend, *]
  · have : ¬i < m := by lia
    simp [extend, *]

theorem mk_types {p : Program} {n : Nat} {v : Expr} (hn : n < p.size)
    (h : p ⊢ v : p.ty[n]) : (mk _ n v).Types p := by
  intro m hm
  by_cases n = m
  · simpa [mk, *] using h
  · simpa [mk, *] using (.var m hm)

theorem update_types {p : Program} {vm : VarMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : vm.Types p) :
    (vm.update m hm).Types (p.push b p.ty[m]) := by
  intro i hi
  by_cases i = p.size
  · simp only [getElem_update_size, Vector.getElem_push_eq, *]
    have : p.ty[m] = (p.push b p.ty[m]).ty[p.size] := by simp
    conv => arg 3; rw [this]
    constructor
  · replace hi : i < p.size := by lia
    simp only [Vector.getElem_push_lt, hi]
    by_cases m = i
    · subst i
      simp only [getElem_update_eq]
      have : p.ty[m] = (p.push b p.ty[m]).ty[p.size] := by simp
      conv => arg 3; rw [this]
      constructor
    · simpa [*] using Expr.types_in_push_of_types (h i hi)

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
    (fm.update m hm)[n] = some n := by simp [update]

@[simp]
theorem getElem_update_eq {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n) :
    (fm.update m hm)[m] = some n := by simp [update, *]

@[simp]
theorem getElem_update_ne {n : Nat} {fm : FunMap n} {m i : Nat} (hm : m < n)
    (hi : i < n) (hne : m ≠ i) : (fm.update m hm)[i] = fm[i] := by simp [update, *]

@[grind =]
theorem getElem_update {n : Nat} {fm : FunMap n} {m i : Nat} (hm : m < n)
    (hi : i ≤ n) :
    (fm.update m hm)[i] = if _ : n = i ∨ m = i then some n else fm[i] := by
  split
  next h =>
    cases h
    · simp [← ‹n = i›]
    · simp [*]
  next h =>
    replace hi : i < n := by lia
    have : m ≠ i := by simp_all
    simp_all

theorem mk_types {p : Program} : (mk _).Types p := by
  intro m hm n heq
  simp only [mk, Vector.getElem_ofFn, Option.some.injEq] at heq
  simpa [heq] using hm

theorem update_types {p : Program} {fm : FunMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : fm.Types p) :
    (fm.update m hm).Types (p.push b p.ty[m]) := by
  intro i hi m' heq
  by_cases i = p.size
  · grind [update]
  · replace hi : i < p.size := by lia
    simp [*]
    by_cases m = i
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
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
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
      grind
    · simp only [p₁] at hi
      replace hi : i < p.size := by lia
      by_cases m = i
      · grind [getElem_update_eq]
      · simp only [fm₁] at hk
        rw [getElem_update_ne _ hi ‹m ≠ i›] at hk
        obtain ⟨_, _⟩ := hfm i hi _ hk
        grind

end FunMap

theorem Expr.subst_types {p : Program} {e : Expr} {t : Ty} {vm : VarMap p.size}
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
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
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

theorem Program.subst_types {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (ht : ⊢ p) (hvm : vm.Types p) (hfm : fm.Types p) :
    ⊢ (e.subst' p vm fm).program := by
  fun_induction Expr.subst' <;>
    first | grind [VarMap.extend_types, FunMap.subst_types]
          | dsimp only at *
  next p vm fm m hm f m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
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

structure FunMap.Extends {n' n : Nat} (fm' : FunMap n') (fm : FunMap n) : Prop where
  le : n ≤ n'
  eq : ∀ {m} (_ : m < n), fm[m].getD m ≠ m → fm'[m].getD m = fm[m].getD m
  eq_none : ∀ {m} (_ : m < n'), fm'[m] = none → ∃ (_ : m < n), fm[m] = none
  eq_of_lt : ∀ {m} (_ : m < n'), fm'[m].getD m < n →
    ∃ (_ : m < n), fm'[m].getD m = fm[m].getD m

grind_pattern FunMap.Extends.eq =>
  fm'.Extends fm, fm[m].getD m, fm'[m].getD m

@[grind →]
theorem FunMap.extends_trans {n₀ n₁ n₂ : Nat} {fm₀ : FunMap n₀}
    {fm₁ : FunMap n₁} {fm₂ : FunMap n₂} (h : fm₁.Extends fm₀)
    (h' : fm₂.Extends fm₁) : fm₂.Extends fm₀ := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  obtain ⟨h₀', h₁', h₂', h₃'⟩ := h'
  constructor
  · grind
  · intro m hm heq₂
    replace ⟨hm, heq₁⟩ := h₂' hm heq₂
    exact h₂ hm heq₁
  · grind
  · grind

theorem FunMap.extends_update {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n)
    (h : fm[m] = none) : (fm.update m hm).Extends fm := by
  constructor <;> grind

@[grind! .]
theorem FunMap.extends_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} : (e.subst' p vm fm).funMap.Extends fm := by
  fun_induction Expr.subst' <;>
    try solve | constructor <;> simp_all
              | grind [extends_update]

def Expr.NoSubst {n : Nat} (e : Expr) (fm : FunMap n) : Prop :=
  ∀ ⦃m r⦄ (_ : m < n), e.Local (fm[m].getD m) r → fm[m].getD m = m

theorem Expr.noSubst_mk {n : Nat} {e : Expr} : e.NoSubst (.mk n) := by
  grind [Expr.NoSubst]

theorem Expr.noSubst_app_iff {n : Nat} {f e : Expr} {fm : FunMap n} :
    (f.app e).NoSubst fm ↔ f.NoSubst fm ∧ e.NoSubst fm := by
  constructor
  · intro h
    and_intros
    · intro m r hm hl
      exact h hm (.appL _ _ _ hl)
    · intro m r hm hl
      exact h hm (.appR _ _ _ hl)
  · intro ⟨hf, he⟩
    intro m r hm hl
    obtain hl | hl := local_app_iff.mp hl
    · exact hf hm hl
    · exact he hm hl

theorem Expr.noSubst_cond_iff {n : Nat} {c et ef : Expr} {fm : FunMap n} :
    (c.cond et ef).NoSubst fm ↔ c.NoSubst fm ∧ et.NoSubst fm ∧ ef.NoSubst fm := by
  constructor
  · intro h
    and_intros
    · intro m r hm hl
      exact h hm (.condC _ _ _ _ hl)
    · intro m r hm hl
      exact h hm (.condT _ _ _ _ hl)
    · intro m r hm hl
      exact h hm (.condF _ _ _ _ hl)
  · intro ⟨hc, het, hef⟩
    intro m r hm hl
    obtain hl | hl | hl := local_cond_iff.mp hl
    · exact hc hm hl
    · exact het hm hl
    · exact hef hm hl

theorem Expr.noSubst_of_extends_of_noSubst {n n' : Nat} {e : Expr}
    {fm : FunMap n} {fm' : FunMap n'} (he : ∀ {m r}, e.Local m r → m < n)
    (hext : fm'.Extends fm) (h : e.NoSubst fm) :
    e.NoSubst fm' := by
  intro m r hm hl
  replace ⟨hm, heq⟩ := hext.eq_of_lt hm (he hl)
  rw [heq] at hl ⊢
  exact h hm hl

def FunMap.LocalProvenance {n : Nat} (fm : FunMap n) (e e' : Expr) (k : Option Nat) :
    Prop :=
  ∀ ⦃m r⦄ (_ : m < n),
    fm[m].getD m ≠ m → e'.Local (fm[m].getD m) r → m = k ∨ e.Local m r

structure Program.ValidSubst (p : Program) (vm : VarMap p.size) (fm : FunMap p.size) where
  validRefs : p.ValidRefs
  vm_validRefs : ∀ {m} (_ : m < p.size), vm[m].ValidRefs p
  vm_localProvenance : ∀ {m} (_ : m < p.size),
    fm[m].getD m ≠ m → fm.LocalProvenance (.var m) vm[m] none
  vm_noSubst : ∀ {m} (_ : m < p.size),
    fm[m].getD m = m → vm[m] ≠ .var m → vm[m].NoSubst fm
  fm_lt : ∀ {m} (_ : m < p.size), fm[m].getD m < p.size
  fm_inj : ∀ {m n} (_ : m < p.size) (_ : n < p.size),
    fm[m].getD m ≠ m → fm[n].getD n ≠ n → fm[m].getD m = fm[n].getD n → m = n
  fm_idem : ∀ {m} (_ : m < p.size),
    (fm[fm[m].getD m]'(fm_lt _)).getD (fm[m].getD m) = fm[m].getD m
  fm_eq_none : ∀ {m n} (_ : m < p.size) (_ : n < p.size),
    fm[m] = none → fm[n].getD n ≠ m
  fn_localProvenance : ∀ {m} (_ : m < p.size),
    fm[m].getD m ≠ m → fm.LocalProvenance p.fn[m] (p.fn[fm[m].getD m]'(fm_lt _)) m
  fn_noSubst : ∀ {m} (_ : m < p.size), fm[m] = none → p.fn[m].NoSubst fm
--  all_free_of_map_free : ∀ {m n} (_ : m < p.size) (_ : n < p.size) (_ : fm[m].getD m ≠ fm[n].getD n),
--    (p.fn[fm[m].getD m]'(all_lt _)).Free p (fm[n].getD n) →
--    p.fn[m].Free p n

attribute [grind →] Program.ValidSubst.validRefs

grind_pattern Program.ValidSubst.vm_validRefs =>
  p.ValidSubst vm fm, m < p.size, vm[m]

grind_pattern Program.ValidSubst.fm_lt =>
  p.ValidSubst vm fm, m < p.size, fm[m].getD m
  where m =/= Option.getD _ _

theorem Program.validSubst_mk {p : Program} {n : Nat} {v : Expr}
    (hp : p.ValidRefs) (hv : v.ValidRefs p) :
    p.ValidSubst (.mk _ n v) (.mk _) := by
  constructor <;> grind [Expr.NoSubst]

theorem Program.validSubst_push_recurse {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {i : Nat} (hi : i < p.size) (hfm : fm[i] = none)
    (h : p.ValidSubst vm fm) :
    (p.push (Expr.recurse p.size) p.ty[i]).ValidSubst (vm.update i hi) (fm.update i hi) := by
  constructor
  case validRefs =>
    exact validRefs_push h.validRefs (by simp)
  case vm_validRefs =>
    intro k hk
    by_cases k = p.size
    · simp [*]
    · by_cases i = k
      · subst k
        simp [*]
      · replace hk : k < p.size := by lia
        simpa [*] using Expr.validRefs_in_push (h.vm_validRefs hk)
  case vm_localProvenance =>
    intro m hm hmm' n r hn hnn' hl
    have : m ≠ p.size := by
      intro rfl
      simp at hmm'
    replace hm : m < p.size := by lia
    have : n ≠ p.size := by
      intro rfl
      simp at hnn'
    replace hn : n < p.size := by lia
    by_cases i = m
    · grind
    · have : i ≠ n := by grind
      apply h.vm_localProvenance <;> simp_all
  case vm_noSubst =>
    intro m hm hmm' hne
    have : i ≠ m := by grind
    have : m ≠ p.size := by
      intro rfl
      simp at hne
    replace hm : m < p.size := by lia
    simp only [ne_eq, not_false_eq_true, VarMap.getElem_update_ne, *]
    intro n r hn hl
    by_cases n = p.size
    · simp [*]
    · have : i ≠ n := by grind
      replace hn : n < p.size := by lia
      simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, *] at hl ⊢
      refine h.vm_noSubst hm ?_ ?_ hn hl <;> simp_all
  case fm_lt =>
    intro k hk
    by_cases k = p.size
    · simp [*]
    · replace hk : k < p.size := by lia
      grind
  case fm_inj =>
    intro m n hm hn hmm' hnn' heq
    replace hm : m < p.size := by grind
    replace hn : n < p.size := by grind
    have := h.fm_inj hm hn
    grind
  case fm_idem =>
    intro m hm
    by_cases m = p.size
    · simp [*]
    · replace hm : m < p.size := by lia
      have := h.fm_idem hm
      have := h.fm_eq_none hi hm hfm
      grind
  case fm_eq_none =>
    intro m n hm hn heq
    replace hm : m < p.size := by grind
    have him : i ≠ m := by grind
    simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, hm, him] at heq
    by_cases n = p.size
    · grind
    · replace hn : n < p.size := by lia
      have := h.fm_eq_none hm hn heq
      grind
  case fn_localProvenance =>
    intro m hm hmm' n r hn hnn' hl
    by_cases hnm : n = m
    · simp [*]
    · right
      have : m ≠ p.size := by
        rintro rfl
        simp at hmm'
      have : n ≠ p.size := by
        rintro rfl
        simp at hnn'
      replace hm : m < p.size := by lia
      replace hn : n < p.size := by lia
      have hm' := h.fm_lt hm
      have hn' := h.fm_lt hn
      have him : i ≠ m := by grind
      have hin : i ≠ n := by grind
      simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, Vector.getElem_push_lt, hm,
        him, hn, hin, hm'] at hmm' hnn' hl
      have := h.fn_localProvenance hm hmm' hn hnn' hl
      simp_all
  case fn_noSubst =>
    intro m hm heq n r hn hl
    have : m ≠ p.size := by
      intro rfl
      simp at heq
    replace hm : m < p.size := by lia
    have : i ≠ m := by
      intro rfl
      simp at heq
    simp only [Vector.getElem_push_lt, hm] at hl
    simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, hm, this] at heq
    by_cases n = p.size
    · simp [*]
    · replace hn : n < p.size := by lia
      have hin : i ≠ n := by grind
      simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, *] at hl ⊢
      exact h.fn_noSubst hm heq hn hl

theorem Program.validSubst_and_validRefs_and_localProvenance_subst {p : Program}
    {e : Expr} {vm : VarMap p.size} {fm : FunMap p.size}
    (hvalid : p.ValidSubst vm fm) (he : e.ValidRefs p) (hns : e.NoSubst fm) :
    let ⟨p', e', fm', _, _⟩ := e.subst' p vm fm
    p'.ValidSubst vm.extend fm' ∧ e'.ValidRefs p' ∧ fm'.LocalProvenance e e' none := by
  fun_induction Expr.subst'
  next p e vm fm h =>
    simp only [VarMap.extend_eq, true_and, hvalid, he]
    intro n r hn hnn' hl
    right
    simpa [hns hn hl] using hl
  next p vm fm m h =>
    simp only [VarMap.extend_eq, true_and, hvalid]
    and_intros
    · simp_all [hvalid.vm_validRefs]
    · intro n r hn hnn' hl
      simp only [Expr.validRefs_var_iff] at he
      simp only [he, getElem?_pos, Option.getD_some] at hl
      by_cases hmm' : fm[m].getD m = m
      · simp only [Classical.not_forall] at h
        obtain ⟨k, hk, hf, hne⟩ := h
        have .var := hf
        have := hvalid.vm_noSubst he hmm' hne hn hl
        contradiction
      · exact hvalid.vm_localProvenance he hmm' hn hnn' hl
  next p vm fm m hm hfm m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at ih
    have h₁ : p₁.ValidSubst vm₁ fm₁ := validSubst_push_recurse hm hfm hvalid
    have hns : p.fn[m].NoSubst fm₁ := by
      intro n r hn hl
      by_cases n = p.size
      · simp [fm₁, *]
      · replace hn : n < p.size := by lia
        have hmn : m ≠ n := by grind
        simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, fm₁, *] at hl ⊢
        exact hvalid.fn_noSubst hm hfm hn hl
    have ⟨h₂, hf', hprov⟩ :=
      ih h₁ (Expr.validRefs_in_push (hvalid.validRefs hm)) hns
    have hext₁ := FunMap.extends_update hm hfm
    have hext₂ : fm₂.Extends fm₁ := by grind
    have hext := FunMap.extends_trans hext₁ hext₂
    and_intros
    · constructor
      case validRefs =>
        exact validRefs_setBody hsize₂ h₂.validRefs hf'
      case vm_validRefs =>
        intro k hk
        by_cases hk : k < p.size
        · simp [*]
          exact Expr.validRefs_of_size_ge (by lia) (hvalid.vm_validRefs hk)
        · simp_all
      case vm_localProvenance =>
        intro k hk hkk' l r hl hll' hlc
        by_cases k < p.size
        · simp only [VarMap.getElem_extend_lt, *] at hlc
          by_cases m = k
          · subst k
            have hl' : fm₂[l].getD l < p.size := hvalid.vm_validRefs _ hlc
            obtain ⟨hl, heq⟩ := hext.eq_of_lt hl hl'
            rw [heq] at hlc
            by_cases hvmm : vm[m] = .var m
            · grind [h₂.fm_idem]
            · have := hvalid.vm_noSubst hm (by simp [*]) hvmm hl hlc
              grind
          · exact h₂.vm_localProvenance hk hkk' hl hll' (by grind)
        · exact h₂.vm_localProvenance hk hkk' hl hll' (by grind)
      case vm_noSubst =>
        intro k hk hkk' hne
        by_cases hk : k < p.size
        · have hkk' : fm[k].getD k = k := by grind
          simp only [VarMap.getElem_extend_lt, *] at hne ⊢
          intro l r hl hlc
          by_cases hll'₂ : fm₂[l].getD l = l
          · exact hll'₂
          · have hl' : fm₂[l].getD l < p.size := hvalid.vm_validRefs _ hlc
            obtain ⟨hl, heq⟩ := hext.eq_of_lt hl hl'
            rw [heq] at hlc
            have := hvalid.vm_noSubst hk hkk' hne hl hlc
            grind
        · simp_all
      case fm_lt => exact h₂.fm_lt
      case fm_inj => exact h₂.fm_inj
      case fm_idem => exact h₂.fm_idem
      case fm_eq_none => exact h₂.fm_eq_none
      case fn_localProvenance =>
        intro n hn hnn' k r hk hkk' hl
        have hfmm : fm₂[m].getD m = m' := by grind [hext₂.eq]
        by_cases hnm : m = n
        · subst n
          simp only [Vector.getElem_set_self, p₃, hfmm] at hl
          replace hl := hprov hk hkk' hl
          simp only [reduceCtorEq, false_or] at hl
          rw [hfmm] at hnn'
          have heq : p₂.fn[m] = p.fn[m] := by
            have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
            subst p₂
            rw [subst_fn_eq_of_lt (by lia)]
            simp [p₁, hm]
          simp [p₃, *]
        · have hnm' : fm₂[n].getD n ≠ m' := by
            intro heq
            rw [← heq] at hfmm
            have := h₂.fm_inj (by lia) hn (by lia) hnn' hfmm
            contradiction
          simp only [ne_eq, not_false_eq_true, Ne.symm, Vector.getElem_set_ne, p₃, hnm'] at hl
          have hne : m' ≠ n := by grind [h₂.fm_idem]
          cases h₂.fn_localProvenance hn hnn' hk hkk' hl <;> simp [p₃, *]
      case fn_noSubst =>
        intro n hn hfm' k r hk hl
        replace ⟨hn, hfm'⟩ := hext.eq_none hn hfm'
        have hnm' : m' ≠ n := by grind [h₂.fm_idem]
        have heq : p₃.fn[n] = p.fn[n] := by
          simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, p₃, hnm']
          have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
          subst p₂
          rw [subst_fn_eq_of_lt (by lia)]
          simp [p₁, *]
        rw [heq] at hl
        have hk' := hvalid.validRefs hn hl
        obtain ⟨hk, heq⟩ := hext.eq_of_lt hk hk'
        rw [heq] at hl ⊢
        exact hvalid.fn_noSubst hn hfm' hk hl
    · grind
    · intro n r hn hnn' hl
      subst f''
      right
      simp only [Expr.local_fn_iff] at hl
      obtain ⟨hr, hmn'⟩ := hl
      have : fm₂[m].getD m = m' := by
        rw [hext₂.eq (by lia) (by grind)]
        simp [fm₁, m']
      rw [← this] at hmn'
      have : m = n := h₂.fm_inj (by lia) hn (by grind) hnn' hmn'
      simp [*]
  next p vm fm m hm m' hfm h =>
    simp only [VarMap.extend_eq, Expr.validRefs_fn_iff, true_and, hvalid]
    have hfmm : fm[m].getD m = m' := by simp [*]
    and_intros
    · grind
    · intro n r hn hnn' hl
      have hm' := hvalid.fm_lt hm
      by_cases hmm' : m = m'
      · have := hns hn (hmm' ▸ hl)
        contradiction
      · grind [hvalid.fm_inj]
  next => grind
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    dsimp only at *
    obtain ⟨hvf, hve⟩ := Expr.validRefs_app_iff.mp he
    obtain ⟨hnsf, hnse⟩ := Expr.noSubst_app_iff.mp hns
    obtain ⟨h₁, hvf', hf'⟩ := ihf hvalid hvf hnsf
    obtain ⟨h₂, hve', he'⟩ :=
      ihe h₁ (Expr.validRefs_of_size_ge hsize₁ hve)
        (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnse)
    and_intros
    · grind [VarMap.extend_extend]
    · grind [Expr.validRefs_of_size_ge]
    · intro n r hn hnn' hl
      have hext₁ : fm₂.Extends fm₁ := by grind
      simp only [reduceCtorEq, Expr.local_app_iff, false_or]
      obtain hl | hl := Expr.local_app_iff.mp hl
      · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hn (hvf' hl)
        rw [heq] at hl
        have := hf' hn (by grind) hl
        grind
      · have := he' hn hnn' hl
        grind
  next p vm fm b h =>
    and_intros
    · exact VarMap.extend_eq ▸ hvalid
    · exact Expr.validRefs_bool
    · intro n r hn hnn' hl
      simp at hl
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    obtain ⟨hvc, hvet, hvef⟩ := Expr.validRefs_cond_iff.mp he
    obtain ⟨hnsc, hnset, hnsef⟩ := Expr.noSubst_cond_iff.mp hns
    obtain ⟨h₁, hvc', hc'⟩ := ihc hvalid hvc hnsc
    obtain ⟨h₂, hvet', het'⟩ :=
      ihet h₁ (Expr.validRefs_of_size_ge hsize₁ hvet)
        (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnset)
    obtain ⟨h₃, hvef', hef'⟩ :=
      ihef h₂ (Expr.validRefs_of_size_ge (by lia) hvef)
        (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnsef)
    and_intros
    · grind [VarMap.extend_extend]
    · grind [Expr.validRefs_of_size_ge]
    · intro n r hn hnn' hl
      have hext₁ : fm₃.Extends fm₁ := by grind
      have hext₂ : fm₃.Extends fm₂ := by grind
      simp only [reduceCtorEq, Expr.local_cond_iff, false_or]
      obtain hl | hl | hl := Expr.local_cond_iff.mp hl
      · replace ⟨hn, heq⟩ := hext₁.eq_of_lt hn (hvc' hl)
        rw [heq] at hl
        have := hc' hn (by grind) hl
        grind
      · replace ⟨hn, heq⟩ := hext₂.eq_of_lt hn (hvet' hl)
        rw [heq] at hl
        have := het' hn (by grind) hl
        grind
      · have := hef' hn hnn' hl
        grind

theorem Program.validSubst_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvalid : p.ValidSubst vm fm) (he : e.ValidRefs p)
    (hns : e.NoSubst fm) :
    let ⟨p', _, fm', _, _⟩ := e.subst' p vm fm
    p'.ValidSubst vm.extend fm' :=
  Program.validSubst_and_validRefs_and_localProvenance_subst hvalid he hns |>.1

theorem Expr.validRefs_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvalid : p.ValidSubst vm fm) (he : e.ValidRefs p)
    (hns : e.NoSubst fm) :
    let ⟨p', e', _, _, _⟩ := e.subst' p vm fm
    e'.ValidRefs p' :=
  Program.validSubst_and_validRefs_and_localProvenance_subst hvalid he hns |>.2.1

theorem Expr.localProvenance_subst {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} (hvalid : p.ValidSubst vm fm) (he : e.ValidRefs p)
    (hns : e.NoSubst fm) :
    let ⟨_, e', fm', _, _⟩ := e.subst' p vm fm
    fm'.LocalProvenance e e' none :=
  Program.validSubst_and_validRefs_and_localProvenance_subst hvalid he hns |>.2.2

theorem Program.exists_of_ge_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _, _⟩ := e.subst' p vm fm
    n' < p'.size → ∃ (n : Nat) (_ : n < p.size), n' = fm'[n].getD n := by
  intro hlt
  fun_induction Expr.subst' generalizing n' <;> try grind
  next p vm fm m hm hfm m' vm₁ fm₁ p₁ hsize₁ hum₁ p₂ f' fm₂ hsize₂ hum₂ hs₂
      p₃ f'' hsize hum h ih =>
    rw [hs₂] at ih
    dsimp only at *
    have hext : fm₂.Extends fm₁ := by grind
    have hfm' : fm₂[m].getD m = p.size := by
      rw [hext.eq (by lia) (by grind)]
      simp [fm₁]
    have h₁ : p₁.ValidSubst vm₁ fm₁ := validSubst_push_recurse hm hfm h
    have hns : p.fn[m].NoSubst fm₁ := by
      intro n r hn hl
      by_cases n = p.size
      · simp [fm₁, *]
      · replace hn : n < p.size := by lia
        have hmn : m ≠ n := by grind
        simp only [ne_eq, not_false_eq_true, FunMap.getElem_update_ne, fm₁, *] at hl ⊢
        exact h.fn_noSubst hm hfm hn hl
    have h₂ : p₂.ValidSubst vm₁.extend fm₂ := by
      have hp₂ : p₂ = (p.fn[m].subst' p₁ vm₁ fm₁).program := by grind
      subst p₂
      have hfm₂ : fm₂ = (p.fn[m].subst' p₁ vm₁ fm₁).funMap := by grind
      subst fm₂
      exact validSubst_subst h₁ (Expr.validRefs_in_push (h.validRefs hm)) hns
    by_cases n' = p.size
    · refine ⟨m, hm, ?_⟩
      rwa [hfm']
    · obtain ⟨n, hn, heq⟩ :=
        ih (validSubst_push_recurse hm hfm h)
          (Expr.validRefs_in_push (h.validRefs hm)) hns (by lia) hlt
      have : n ≠ p.size := by grind [h₂.fm_idem]
      exact ⟨n, by lia, heq⟩
  next p vm fm f e p₁ f' fm₁ hsize₁ hum₁ hs₁ p₂ e' fm₂ hsize₂ hum₂ hs₂ h ihf ihe =>
    rw [hs₁] at ihf
    rw [hs₂] at ihe
    dsimp only at *
    obtain ⟨hvf, hve⟩ := Expr.validRefs_app_iff.mp he
    obtain ⟨hnsf, hnse⟩ := Expr.noSubst_app_iff.mp hns
    have h₁ : p₁.ValidSubst vm.extend fm₁ := by
      grind [validSubst_subst]
    have h₂ : p₂.ValidSubst vm.extend fm₂ := by
      grind [validSubst_subst, VarMap.extend_extend, Expr.validRefs_of_size_ge,
        Expr.noSubst_of_extends_of_noSubst]
    have hext₁ : fm₂.Extends fm₁ := by grind
    by_cases n' < p₁.size
    · grind
    · replace hn' : p₁.size ≤ n' := by lia
      obtain ⟨n, hlt, heq⟩ := ihe h₁ (Expr.validRefs_of_size_ge hsize₁ hve)
        (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnse) hn' hlt
      by_cases hn : n < p.size
      · exact ⟨n, hn, heq⟩
      · grind [h₂.fm_idem]
  next p vm fm c et ef p₁ c' fm₁ hsize₁ hum₁ hs₁ vm₁ p₂ et' fm₂ hsize₂ hum₂ hs₂
      p₃ ef' fm₃ hsize₃ hum₃ hs₃ h ihc ihet ihef =>
    rw [hs₁] at ihc
    rw [hs₂] at ihet
    rw [hs₃] at ihef
    dsimp only at *
    obtain ⟨hvc, hvet, hvef⟩ := Expr.validRefs_cond_iff.mp he
    obtain ⟨hnsc, hnset, hnsef⟩ := Expr.noSubst_cond_iff.mp hns
    have h₁ : p₁.ValidSubst vm₁ fm₁ := by
      grind [validSubst_subst]
    have h₂ : p₂.ValidSubst vm₁.extend fm₂ := by
      grind [validSubst_subst, VarMap.extend_extend, Expr.validRefs_of_size_ge,
        Expr.noSubst_of_extends_of_noSubst]
    have h₃ : p₃.ValidSubst vm₁.extend fm₃ := by
      grind [validSubst_subst, VarMap.extend_extend, Expr.validRefs_of_size_ge,
        Expr.noSubst_of_extends_of_noSubst]
    have hext₁₂ : fm₂.Extends fm₁ := by grind
    have hext₁₃ : fm₃.Extends fm₁ := by grind
    have hext₂₃ : fm₃.Extends fm₂ := by grind
    by_cases n' < p₁.size
    · obtain ⟨n, hlt, heq⟩ := ihc h hvc hnsc hn' ‹_›
      grind
    · replace hn' : p₁.size ≤ n' := by lia
      by_cases n' < p₂.size
      · obtain ⟨n, hlt, heq⟩ := ihet h₁ (Expr.validRefs_of_size_ge hsize₁ hvet)
          (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnset) hn' ‹_›
        by_cases hn : n < p.size
        · grind
        · replace hn : p.size ≤ n := by lia
          obtain ⟨m, hlt', heq'⟩ := ihc h hvc hnsc hn hlt
          have := hext₁₂.eq (show m < p₁.size by lia) (by lia)
          grind [h₂.fm_idem]
      · replace hn' : p₂.size ≤ n' := by lia
        obtain ⟨n, hlt, heq⟩ := ihef h₂ (Expr.validRefs_of_size_ge (by lia) hvef)
          (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnsef) hn' hlt
        by_cases hn : n < p.size
        · exact ⟨n, hn, heq⟩
        · replace hn : p.size ≤ n := by lia
          by_cases n < p₁.size
          · obtain ⟨m, hlt', heq'⟩ := ihc h hvc hnsc hn ‹_›
            have := hext₁₂.eq (show m < p₁.size by lia) (by lia)
            grind [h₃.fm_idem]
          · replace hn : p₁.size ≤ n := by lia
            obtain ⟨m, hlt', heq'⟩ := ihet h₁ (Expr.validRefs_of_size_ge hsize₁ hvet)
              (Expr.noSubst_of_extends_of_noSubst (by grind) (by grind) hnset) hn ‹_›
            have := hext₂₃.eq (show m < p₂.size by lia) (by lia)
            grind [h₃.fm_idem]

theorem Program.lt_size_of_pathWithout_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hp : p.ValidRefs) {m n k : Nat}
    (hm : m < p.size) (hp : m ⟶[(e.subst' p vm fm).program, n]* k) :
    k < p.size := by
  induction hp with
  | refl m hm => exact hm
  | step m l k hne hs hp ih =>
    obtain ⟨_, hlf⟩ := hs
    rw [subst_fn_eq_of_lt hm] at hlf
    grind

theorem Program.pathWithout_of_pathWithout_in_subst {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' m' k' : Nat} (hn' : p.size ≤ n')
    (hm' : p.size ≤ m') (hk' : p.size ≤ k') :
    let ⟨p', _, fm', _, _⟩ := e.subst' p vm fm
    n' < p'.size → m' < p'.size → k' < p'.size → m' ⟶[p', n']* k' →
      ∃ (n m k : Nat) (hn : n < p.size) (hm : m < p.size) (hk : k < p.size),
        n' = fm'[n].getD n ∧ m' = fm'[m].getD m ∧ k' = fm'[k].getD k ∧ m ⟶[p, n]* k := by
  intro hnlt hmlt hklt hp'
  let p' := (e.subst' p vm fm).program
  let e' := (e.subst' p vm fm).expr
  let fm' := (e.subst' p vm fm).funMap
  have hsize := (e.subst' p vm fm).size_ge
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst h he hns
  induction hp' with
  | refl m' hne' =>
    obtain ⟨n, hn, hfmn⟩ := exists_of_ge_in_subst h he hns hn' hnlt
    obtain ⟨k, hk, hfmk⟩ := exists_of_ge_in_subst h he hns hk' hklt
    obtain ⟨m, hm, hfmm⟩ := exists_of_ge_in_subst h he hns hm' hmlt
    have hne : n ≠ m := by grind
    exact ⟨n, m, m, hn, hm, hm, hfmn, hfmm, hfmm, .refl _ hne⟩
  | step m' l' k' hne' hs' hp' ih =>
    obtain ⟨m, hm, hfmm⟩ := exists_of_ge_in_subst h he hns hm' hmlt
    have hl' : p.size ≤ l' := by
      false_or_by_contra
      rename_i hl'
      have := lt_size_of_pathWithout_of_lt h.validRefs (by simpa using hl') hp'
      lia
    obtain ⟨_, hlf'⟩ := hs'
    have hllt : l' < p'.size := by grind
    have ⟨n, l, k, hn, hl, hk, hfmn, hfml, hfmk, hp⟩ := ih hl' hk' hllt hklt
    have hne : n ≠ m := by grind
    have hlf := h'.fn_localProvenance
      (show m < p'.size by lia) (by lia) (show l < p'.size by lia) (by lia)
      (by simpa [*] using hlf')
    simp only [Option.some.injEq, Program.subst_fn_eq_of_lt hm, p'] at hlf
    obtain heq | hlf := hlf
    · grind
    · refine ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, .step _ _ _ hne ⟨hm, hlf⟩ hp⟩

theorem Program.free_in_fn_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' m' : Nat} (hn' : p.size ≤ n')
    (hm' : p.size ≤ m') (hne' : n' ≠ m') :
    let ⟨p', _, fm', _, _⟩ := e.subst' p vm fm
    ∀ (_ : m' < p'.size), p'.fn[m'].Free p' n' →
      ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
        n' = fm'[n].getD n ∧ m' = fm'[m].getD m ∧ p.fn[m].Free p n := by
  intro hmlt hf'
  let p' := (e.subst' p vm fm).program
  let e' := (e.subst' p vm fm).expr
  let fm' := (e.subst' p vm fm).funMap
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst h he hns
  obtain ⟨k', hklt, hlv', hp'⟩ := (free_in_fn_iff hmlt hne').mp hf'
  have hk' : p.size ≤ k' := by grind [subst_fn_eq_of_lt]
  have hnlt : n' < p'.size := by grind
  obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
    pathWithout_of_pathWithout_in_subst h he hns hn' hm' hk' hnlt hmlt hklt hp'
  have hne : n ≠ m := by grind
  have hlv := h'.fn_localProvenance
    (show k < p'.size by lia) (by lia) (show n < p'.size by lia) (by lia)
    (by simpa [hfmn, hfmk] using hlv')
  rw [subst_fn_eq_of_lt hk] at hlv
  simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
  exact ⟨n, m, hn, hm, hfmn, hfmm, (free_in_fn_iff hm hne).mpr ⟨k, hk, hlv, hp⟩⟩

theorem Expr.free_of_free_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', e', fm', _, _⟩ := e.subst' p vm fm
    e'.Free p' n' → ∃ (n : Nat) (_ : n < p.size),
      n' = fm'[n].getD n ∧ e.Free p n := by
  intro hf
  let p' := (e.subst' p vm fm).program
  let e' := (e.subst' p vm fm).expr
  let fm' := (e.subst' p vm fm).funMap
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst h he hns
  have hlt : n' < p'.size :=
    lt_size_of_free h'.validRefs (validRefs_subst h he hns) hf
  obtain ⟨n, hn, heq⟩ := Program.exists_of_ge_in_subst h he hns hn' hlt
  obtain hlv' | ⟨m', k', hk', hlf', hp', hlv'⟩ := free_iff.mp hf
  · refine ⟨n, hn, heq, free_of_localVar ?_⟩
    simpa using localProvenance_subst h he hns (by lia) (by lia) (heq ▸ hlv')
  · by_cases hm' : m' < p.size
    · replace hk' := Program.lt_size_of_pathWithout_of_lt h.validRefs ‹_› hp'
      grind [Program.subst_fn_eq_of_lt]
    · simp only [Nat.not_lt] at hm'
      have hk' : p.size ≤ k' := by grind [Program.subst_fn_eq_of_lt]
      obtain ⟨n, m, k, hn, hm, hk, hfmn, hfmm, hfmk, hp⟩ :=
        Program.pathWithout_of_pathWithout_in_subst h he hns hn' hm' hk'
          ‹_› (validRefs_subst h he hns hlf') ‹_› hp'
      have hlf := localProvenance_subst h he hns
        (show m < p'.size by lia) (by lia) (by simpa [*] using hlf')
      simp only [reduceCtorEq, false_or] at hlf
      have hlv := h'.fn_localProvenance
        (show k < p'.size by lia) (by lia) (show n < p'.size by lia) (by lia)
        (by simpa [hfmn, hfmk] using hlv')
      rw [Program.subst_fn_eq_of_lt hk] at hlv
      simp only [Option.some.injEq, hp.ne_end, false_or] at hlv
      exact ⟨n, hn, hfmn, free_iff.mpr <| Or.inr ⟨m, k, hk, hlf, hp, hlv⟩⟩

theorem Program.lt_size_of_free_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidRefs)
    {n m : Nat} (hm : m < p.size) (hne : n ≠ m) :
    let ⟨p', _, _, _, _⟩ := e.subst' p vm fm
    p'.fn[m].Free p' n → n < p.size := by
  intro hf
  obtain ⟨k, hk, hlv, hp⟩ := (free_in_fn_iff (by lia) hne).mp hf
  have hk := lt_size_of_pathWithout_of_lt h hm hp
  rw [subst_fn_eq_of_lt hk] at hlv
  exact h hk hlv

theorem Program.lt_size_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidRefs) {n m : Nat}
    (hm : m < p.size) (hnests : n ≻[(e.subst' p vm fm).program] m) :
    n < p.size := by
  induction hnests with
  | free m hm' hne hf =>
    exact lt_size_of_free_in_subst_of_lt h hm hne hf
  | step k m hm hne hf hnests ih =>
    exact ih <| lt_size_of_free_in_subst_of_lt h hm hne hf

theorem Expr.validRefs_in_subst {p : Program} {e₁ e₂ : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (he₁ : e₁.ValidRefs p) :
    e₁.ValidRefs (e₂.subst' p vm fm).program :=
  let ⟨_, _, _, hsize, _⟩ := (e₂.subst' p vm fm)
  validRefs_of_size_ge hsize he₁

theorem Expr.free_of_free_in_subst {p : Program} {e₁ e₂ : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {n : Nat} (hp : p.ValidRefs)
    (he₁ : e₁.ValidRefs p) (hf : e₁.Free (e₂.subst' p vm fm).program n) :
    e₁.Free p n := by
  generalize hp' : (e₂.subst' p vm fm).program = p' at hf
  induction hf with
    try grind [Free.var, Free.appL, Free.appR, Free.condC, Free.condT, Free.condF]
  | fn k hk' hne hf ih =>
    simp only [validRefs_fn_iff] at he₁
    constructor
    · exact hne
    · subst p'
      rw [Program.subst_fn_eq_of_lt he₁] at ih
      exact ih (hp he₁)

theorem Program.nests_of_nests_in_subst_of_lt {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {m n : Nat} (hn : n < p.size)
    (hp : p.ValidRefs) (h : m ≻[(e.subst' p vm fm).program] n) :
    m ≻[p] n := by
  generalize hp' : (e.subst' p vm fm).program = p' at h
  induction h with
  | free n hn' hne hf' =>
    subst p'
    have hf : p.fn[n].Free p m := by
      apply Expr.free_of_free_in_subst hp (hp hn)
      simpa [subst_fn_eq_of_lt hn] using hf'
    exact Nests.free _ hn hne hf
  | step k n hn' hne hf' h ih =>
    subst p'
    have hf : p.fn[n].Free p k := by
      apply Expr.free_of_free_in_subst hp (hp hn)
      simpa [subst_fn_eq_of_lt hn] using hf'
    exact Nests.step _ _ hn hne hf (ih (lt_size_of_free hp (hp hn) hf))

theorem Program.nests_of_nests_in_subst_of_ge {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (h : p.ValidSubst vm fm)
    (he : e.ValidRefs p) (hns : e.NoSubst fm) {n' m' : Nat} (hn' : p.size ≤ n') :
    let ⟨p', _, fm', _, _⟩ := e.subst' p vm fm
    n' ≻[p'] m' → ∃ (n m : Nat) (hn : n < p.size) (hm : m < p.size),
      n' = fm'[n].getD n ∧ m' = fm'[m].getD m ∧ n ≻[p] m := by
  intro hnests'
  let p' := (e.subst' p vm fm).program
  let e' := (e.subst' p vm fm).expr
  let fm' := (e.subst' p vm fm).funMap
  have h' : p'.ValidSubst vm.extend fm' := Program.validSubst_subst h he hns
  induction hnests' with
  | free m' hltm hne' hf' =>
    have hm' : p.size ≤ m' := by
      false_or_by_contra
      rename_i hm'
      simp only [Nat.not_le] at hm'
      have := lt_size_of_free_in_subst_of_lt h.validRefs hm' hne' hf'
      lia
    obtain ⟨n, m, hn, hm, hfmn, hfmm, hf⟩ :=
      Program.free_in_fn_of_free_in_subst_of_ge h he hns hn' hm' hne' hltm hf'
    have hne : n ≠ m := by grind
    exact ⟨n, m, hn, hm, hfmn, hfmm, .free _ hm hne hf⟩
  | step k' m' hmlt hne' hf' hnests' ih =>
    obtain ⟨n, k, hn, hk, hfmn, hfmk, hnests⟩ := ih
    have hk' : p.size ≤ k' := by
      false_or_by_contra
      rename_i hk'
      have := lt_size_of_nests_in_subst_of_lt h.validRefs (by simpa using hk') hnests'
      lia
    have hm' : p.size ≤ m' := by
      false_or_by_contra
      rename_i hm'
      have := lt_size_of_free_in_subst_of_lt h.validRefs (by simpa using hm') hne' hf'
      lia
    obtain ⟨l, m, hl, hm, hfml, hfmm, hf⟩ :=
      free_in_fn_of_free_in_subst_of_ge h he hns hk' hm' hne' hmlt hf'
    obtain rfl : k = l := h'.fm_inj (by lia) (by lia) (by lia) (by lia) (hfmk ▸ hfml)
    have hne : k ≠ m := by grind
    exact ⟨n, m, hn, hm, hfmn, hfmm, .step _ _ hm hne hf hnests⟩

namespace Computation

theorem subst_types {c : Computation} {t : Ty} {n : Nat} {v : Expr}
    (hn : n < c.size) (ht : ⊢ c : t) (hv : c.toProgram ⊢ v : c.ty[n]) :
    ⊢ c.subst' n v : t := by
  refine ⟨Program.subst_types ht.program_types ?hvm ?hfm,
          Expr.subst_types ht.expr_types ?hvm ?hfm⟩
  · exact VarMap.mk_types hn hv
  · exact FunMap.mk_types

theorem subst_wf {c : Computation} {n : Nat} {v : Expr} (hp : c.ValidRefs)
    (he : c.expr.ValidRefs c.toProgram) (hv : v.ValidRefs c.toProgram)
    (h : c.WF) : (c.subst' n v).WF := by
  let ⟨p, e⟩ := c
  dsimp only [subst'] at *
  intro m hnests
  by_cases hm : m < p.size
  · exact h <| Program.nests_of_nests_in_subst_of_lt hm hp hnests
  · simp only [Nat.not_lt] at hm
    have hvalid := Program.validSubst_mk (n := n) hp hv
    have hvalid' := Program.validSubst_subst hvalid he Expr.noSubst_mk
    replace ⟨k, l, hk, hl, hfmk, hfml, hnests⟩ :=
      Program.nests_of_nests_in_subst_of_ge hvalid he Expr.noSubst_mk hm hnests
    obtain rfl : k = l := hvalid'.fm_inj (by lia) (by lia) (by lia) (by lia) (hfmk ▸ hfml)
    exact h hnests

end Computation
