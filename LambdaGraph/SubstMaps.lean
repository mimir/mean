module

public import LambdaGraph.Basic

public section

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

/-- A predicate representing the domain of a variable map. -/
def VarMap.Dom {n : Nat} (vm : VarMap n) (m : Nat) : Prop :=
  ∃ hm, vm[m]'hm ≠ .var m

/--
The typing predicate for variable maps.

For a variable map to be well-typed, each expression substituted for a variable
must have the variable's declared type.
-/
def VarMap.Types (p : Program) (vm : VarMap p.size) : Prop :=
  ∀ i (_ : i < p.size), p ⊢ vm[i] : p.ty[i]

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

@[simp, grind =]
theorem extend_eq {n : Nat} {vm : VarMap n} : vm.extend (n' := n) = vm := by
  ext i hi
  simp [extend]

@[grind =]
theorem extend_extend {m n k : Nat} {vm : VarMap m} (h : m ≤ n) :
    (vm.extend (n' := n) |>.extend (n' := k)) = vm.extend := by
  ext i hi
  by_cases i < n
  · simp [extend, *]
  · have : ¬i < m := by lia
    simp [extend, *]

@[grind →]
theorem Dom.lt {n : Nat} {vm : VarMap n} {m : Nat} (h : vm.Dom m) : m < n := h.1

@[grind →]
theorem eq_of_dom_mk {n m : Nat} {v : Expr} {k : Nat} (h : (mk n m v).Dom k) :
    m = k := by
  grind [Dom]

@[grind =]
theorem dom_update_iff {n : Nat} {vm : VarMap n} {m k : Nat} (hm : m < n) :
    (vm.update m hm).Dom k ↔ vm.Dom k ∨ m = k := by
  grind [Dom]

@[grind =]
theorem dom_extend_iff {n n' : Nat} {vm : VarMap n} {m : Nat} (hle : n ≤ n') :
    (vm.extend (n' := n')).Dom m ↔ vm.Dom m := by
  grind [Dom]

theorem mk_types {p : Program} {n : Nat} {v : Expr} (hn : n < p.size)
    (h : p ⊢ v : p.ty[n]) : (mk _ n v).Types p := by
  intro m hm
  by_cases n = m
  · simpa [mk, *] using h
  · simpa [mk, *] using (.var m hm)

theorem update_types {p : Program} {vm : VarMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : vm.Types p) :
    (vm.update m hm).Types (p.push b p.ty[m] p.ret[m]) := by
  intro i hi
  by_cases i = p.size
  · simp only [getElem_update_size, Vector.getElem_push_eq, *]
    have : p.ty[m] = (p.push b p.ty[m] p.ret[m]).ty[p.size] := by simp
    conv => arg 3; rw [this]
    constructor
  · replace hi : i < p.size := by lia
    simp only [Vector.getElem_push_lt, hi]
    by_cases m = i
    · subst i
      simp only [getElem_update_eq]
      have : p.ty[m] = (p.push b p.ty[m] p.ret[m]).ty[p.size] := by simp
      conv => arg 3; rw [this]
      constructor
    · simpa [*] using Expr.types_in_push_of_types (h i hi)

theorem extend_types {p p' : Program} {vm : VarMap p.size} (hpre : p.Prefix p')
    (h : vm.Types p) : vm.extend.Types p' := by
  grind [Types, Expr.Types.var]

end VarMap

/--
A map specifying how function references should be substituted.

Function labels for which no new mapping exists yet are mapped to none, while
functions introduced during substitution are mapped to themselves. This
distinction is necessary to support the termination proof for substitution.
-/
abbrev FunMap (n : Nat) := Vector Nat n

/-- Creates a new function map of size `n`. -/
@[grind unfold]
def FunMap.mk (n : Nat) : FunMap n := Vector.ofFn (·)

/--
Updates the map to map a given function to a function with a fresh label.

The fresh label is mapped to itself, indicating that the new function should not
be substituted in turn. This is required for the termination proof. This is
correct if all labels appearing in the program and expression are in bounds, as
this means no reference to the function can appear in the expressions to be
substituted.
-/
def FunMap.update {n : Nat} (fm : FunMap n) (m : Nat)
    (h : m < n := by get_elem_tactic) : FunMap (n + 1) :=
  fm.set m n |>.push n

/-- A predicate representing the domain of a function map. -/
def FunMap.Dom {n : Nat} (fm : FunMap n) (m : Nat) : Prop :=
  ∃ hm, fm[m]'hm ≠ m

/--
The typing predicate for function maps.

For a function map to be well-typed, replacement functions must have the same
type as their original.
-/
def FunMap.Types (p : Program) (fm : FunMap p.size) : Prop :=
  ∀ i (_ : i < p.size),
    ∃ (_ : fm[i] < p.size), p.ty[i] = p.ty[fm[i]] ∧ p.ret[i] = p.ret[fm[i]]

namespace FunMap

@[simp]
theorem getElem_update_size {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n) :
    (fm.update m hm)[n] = n := by simp [update]

@[simp]
theorem getElem_update_eq {n : Nat} {fm : FunMap n} {m : Nat} (hm : m < n) :
    (fm.update m hm)[m] = n := by simp [update, *]

@[simp]
theorem getElem_update_ne {n : Nat} {fm : FunMap n} {m i : Nat} (hm : m < n)
    (hi : i < n) (hne : m ≠ i) : (fm.update m hm)[i] = fm[i] := by simp [update, *]

@[grind =]
theorem getElem_update {n : Nat} {fm : FunMap n} {m i : Nat} (hm : m < n)
    (hi : i ≤ n) :
    (fm.update m hm)[i] = if _ : n = i ∨ m = i then n else fm[i] := by
  split
  next h =>
    cases h
    · simp [← ‹n = i›]
    · simp [*]
  next h =>
    replace hi : i < n := by lia
    have : m ≠ i := by simp_all
    simp_all

@[grind →]
theorem Dom.lt {n : Nat} {fm : FunMap n} {m : Nat} (h : fm.Dom m) : m < n := h.1

@[grind .]
theorem not_dom_mk {n m : Nat} : ¬(mk n).Dom m := by
  grind [Dom]

@[grind =]
theorem dom_update_iff {n : Nat} {fm : FunMap n} {m k : Nat} (hm : m < n) :
    (fm.update m hm).Dom k ↔ fm.Dom k ∨ m = k := by
  grind [Dom]

theorem mk_types {p : Program} : (mk _).Types p := by
  intro m hm
  simpa [mk]

theorem update_types {p : Program} {fm : FunMap p.size} {b : Expr} {m : Nat}
    (hm : m < p.size) (h : fm.Types p) :
    (fm.update m hm).Types (p.push b p.ty[m] p.ret[m]) := by
  intro i hi
  grind [update, Types]

end FunMap

end

def Program.UsesFn (p : Program) (m : Nat) : Prop :=
  ∃ (i : Nat) (_ : i < p.size), p.fn[i].LocalFn m

def VarMap.UsesFn {n : Nat} (vm : VarMap n) (m : Nat) : Prop :=
  ∃ (i : Nat) (_ : i < n), vm[i].LocalFn m

def FunMap.Contains {n : Nat} (fm : FunMap n) (m : Nat) : Prop :=
  ∃ (i : Nat) (_ : i < n), fm[i] = m

@[grind →]
theorem Program.usesFn_push {p : Program} {b : Expr} {t₁ t₂ : Ty} {m : Nat}
    (h : (p.push b t₁ t₂).UsesFn m) :
    p.UsesFn m ∨ b.LocalFn m := by
  grind [UsesFn]

@[grind →]
theorem Program.usesFn_setBody {p : Program} {i : Nat} {b : Expr} {m : Nat}
    (hi : i < p.size) (h : (p.setBody i b hi).UsesFn m) :
    p.UsesFn m ∨ b.LocalFn m := by
  grind [UsesFn]

@[grind →]
theorem VarMap.usesFn_update {n : Nat} {vm : VarMap n} {m k : Nat} (hm : m < n)
    (h : (vm.update m hm).UsesFn k) : vm.UsesFn k := by
  grind [UsesFn]

@[grind →]
theorem VarMap.usesFn_extend {n n' : Nat} {vm : VarMap n} {m : Nat}
    (h : (vm.extend (n' := n')).UsesFn m) : vm.UsesFn m := by
  grind [UsesFn]

@[grind →]
theorem FunMap.contains_update {n : Nat} {fm : FunMap n} {m k : Nat}
    (hm : m < n) (h : (fm.update m hm).Contains k) : fm.Contains k ∨ n = k := by
  grind [Contains]

namespace Termination

inductive Occurs (p : Program) (vm : VarMap p.size) (fm : FunMap p.size)
    (n : Nat) : Prop where
  | program (_ : p.UsesFn n)
  | varMap (_ : vm.UsesFn n)
  | funMap (_ : fm.Contains n)

def OccursProvenance (p p' : Program) (vm : VarMap p.size)
    (vm' : VarMap p'.size) (fm : FunMap p.size) (fm' : FunMap p'.size) : Prop :=
  ∀ ⦃n⦄, Occurs p' vm' fm' n → Occurs p vm fm n ∨ n < p'.size

@[grind →]
theorem OccursProvenance.apply  {p p' : Program} {vm : VarMap p.size}
    {vm' : VarMap p'.size} {fm : FunMap p.size} {fm' : FunMap p'.size} {n : Nat}
    (hp : OccursProvenance p p' vm vm' fm fm') (h : Occurs p' vm' fm' n) :
    Occurs p vm fm n ∨ n < p'.size := hp h

@[scoped grind →]
theorem occursProvenance_program {p p' : Program} {vm : VarMap p.size}
    {vm' : VarMap p'.size} {fm : FunMap p.size} {fm' : FunMap p'.size} {n : Nat}
    (hp : OccursProvenance p p' vm vm' fm fm') (h : p'.UsesFn n) :
    Occurs p vm fm n ∨ n < p'.size := hp (.program h)

@[scoped grind →]
theorem occursProvenance_varMap {p p' : Program} {vm : VarMap p.size}
    {vm' : VarMap p'.size} {fm : FunMap p.size} {fm' : FunMap p'.size} {n : Nat}
    (hp : OccursProvenance p p' vm vm' fm fm') (h : vm'.UsesFn n) :
    Occurs p vm fm n ∨ n < p'.size := hp (.varMap h)

@[scoped grind →]
theorem occursProvenance_funMap {p p' : Program} {vm : VarMap p.size}
    {vm' : VarMap p'.size} {fm : FunMap p.size} {fm' : FunMap p'.size} {n : Nat}
    (hp : OccursProvenance p p' vm vm' fm fm') (h : fm'.Contains n) :
    Occurs p vm fm n ∨ n < p'.size := hp (.funMap h)

@[simp, scoped grind .]
theorem occursProvenance_refl {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} : OccursProvenance p p vm vm fm fm :=
  fun _ h => .inl h

@[scoped grind →]
theorem occursProvenance_trans {p p' p'' : Program}
    {vm : VarMap p.size} {vm' : VarMap p'.size} {vm'' : VarMap p''.size}
    {fm : FunMap p.size} {fm' : FunMap p'.size} {fm'' : FunMap p''.size}
    (hpre : p'.Prefix p'') (hp : OccursProvenance p p' vm vm' fm fm')
    (hp' : OccursProvenance p' p'' vm' vm'' fm' fm'') :
    OccursProvenance p p'' vm vm'' fm fm'' := by
  intro n h
  grind [Occurs]

theorem occursProvenance_push {p : Program} {vm : VarMap p.size}
    {fm : FunMap p.size} {b : Expr} {t₁ t₂ : Ty} {m : Nat} (hm : m < p.size)
    (hb : b.Bounded (p.size + 1)) :
    OccursProvenance p (p.push b t₁ t₂) vm (vm.update m hm) fm (fm.update m hm) := by
  intro n h
  grind [Occurs]

def ExprProvenance (p p' : Program) (e e' : Expr) (vm : VarMap p.size)
    (fm : FunMap p.size) : Prop :=
  ∀ ⦃n⦄, e'.LocalFn n → e.LocalFn n ∨ Occurs p vm fm n ∨ n < p'.size

@[grind →]
theorem ExprProvenance.apply {p p' : Program} {e e' : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {n : Nat} (hp : ExprProvenance p p' e e' vm fm)
    (h : e'.LocalFn n) : e.LocalFn n ∨ Occurs p vm fm n ∨ n < p'.size := hp h

@[simp, grind .]
theorem exprProvenance_refl {p p' : Program} (e : Expr) {vm : VarMap p.size}
    {fm : FunMap p.size} : ExprProvenance p p' e e vm fm := fun _ => Or.inl

@[scoped grind →]
theorem exprProvenance_of_prefix {p p' p'' : Program} {e e' : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} (hpre : p'.Prefix p'')
    (h : ExprProvenance p p' e e' vm fm) : ExprProvenance p p'' e e' vm fm := by
  grind [ExprProvenance]

@[scoped grind →]
theorem exprProvenance_of_occursProvenance_of_exprProvenance {p p' p'' : Program}
    {e e' : Expr} {vm : VarMap p.size} {vm' : VarMap p'.size}
    {fm : FunMap p.size} {fm' : FunMap p'.size}
    (hpre : p'.Prefix p'') (ho : OccursProvenance p p' vm vm' fm fm')
    (he : ExprProvenance p' p'' e e' vm' fm') : ExprProvenance p p'' e e' vm fm := by
  intro n h
  grind

@[scoped grind .]
theorem exprProvenance_var {p p' : Program} {m : Nat} {vm : VarMap p.size}
    {fm : FunMap p.size} (h : vm.Dom m) :
    ExprProvenance p p' (.var m) (vm[m]'h.1) vm fm := by
  intro n h
  grind [Occurs, VarMap.UsesFn]

@[scoped grind .]
theorem exprProvenance_fn {p p' : Program} {m : Nat} {vm : VarMap p.size}
    {fm : FunMap p.size} (h : m < p.size) :
    ExprProvenance p p' (.fn m) (.fn fm[m]) vm fm := by
  intro n h
  grind [Occurs, FunMap.Contains]

@[scoped grind .]
theorem exprProvenance_bin {p p' : Program} {k : BinKind} {e₁ e₁' e₂ e₂' : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size}
    (h₁ : ExprProvenance p p' e₁ e₁' vm fm)
    (h₂ : ExprProvenance p p' e₂ e₂' vm fm) :
    ExprProvenance p p' (e₁.bin k e₂) (e₁'.bin k e₂') vm fm := by
  intro n h
  grind

@[scoped grind .]
theorem exprProvenance_cond {p p' : Program} {c c' et et' ef ef' : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size}
    (hc : ExprProvenance p p' c c' vm fm)
    (het : ExprProvenance p p' et et' vm fm)
    (hef : ExprProvenance p p' ef ef' vm fm) :
    ExprProvenance p p' (c.cond et ef) (c'.cond et' ef') vm fm := by
  intro n h
  grind

@[scoped grind .]
theorem exprProvenance_proj {p p' : Program} {e e' : Expr} {i : Fin 2}
    {vm : VarMap p.size} {fm : FunMap p.size}
    (hp : ExprProvenance p p' e e' vm fm) :
    ExprProvenance p p' (e.proj i) (e'.proj i) vm fm := by
  intro n h
  grind

end Termination

inductive Expr.Reachable (p : Program) (n : Nat) : Expr → Prop where
  | here (e : Expr) : e.LocalFn n → e.Reachable p n
  | there (e : Expr) (m : Nat) (_ : m < p.size) :
    e.LocalFn m → p.fn[m].Reachable p n → e.Reachable p n

@[grind →]
theorem Expr.lt_of_reachable {p : Program} {e : Expr} {n : Nat}
    (hp : p.ValidRefs) (he : e.ValidRefs p) (h : e.Reachable p n) :
    n < p.size := by
  induction h with grind

@[simp, grind .]
theorem Expr.not_reachable_var {p : Program} {m n : Nat} :
    ¬(var m).Reachable p n := nofun

@[simp, grind =]
theorem Expr.reachable_fn_iff {p : Program} {m n : Nat} :
    (fn m).Reachable p n ↔ m = n ∨ ∃ (hm : m < p.size), p.fn[m].Reachable p n := by
  grind [Reachable]

@[simp, grind .]
theorem Expr.not_reachable_const {p : Program} {c : Const} {n : Nat} :
    ¬(const c).Reachable p n := nofun

@[simp, grind =]
theorem Expr.reachable_bin_iff {p : Program} {k : BinKind} {e₁ e₂ : Expr} {n : Nat} :
    (e₁.bin k e₂).Reachable p n ↔ e₁.Reachable p n ∨ e₂.Reachable p n := by
  grind [Reachable]

@[simp, grind =]
theorem Expr.reachable_cond_iff {p : Program} {c et ef : Expr} {n : Nat} :
    (c.cond et ef).Reachable p n ↔ c.Reachable p n ∨ et.Reachable p n ∨ ef.Reachable p n := by
  grind [Reachable]

@[simp, grind =]
theorem Expr.reachable_proj_iff {p : Program} {e : Expr} {i : Fin 2} {n : Nat} :
    (e.proj i).Reachable p n ↔ e.Reachable p n := by
  grind [Reachable]

def Expr.DeepValidFns (e : Expr) (p : Program) : Prop :=
  ∀ ⦃n⦄, e.Reachable p n → n < p.size

theorem Expr.reachable_in_prefix_iff {p p' : Program} {e : Expr} {n : Nat}
    (he : e.DeepValidFns p) (h : p.Prefix p') :
    e.Reachable p' n ↔ e.Reachable p n := by
  constructor <;> intro hr
  · induction hr with
    | here e hl => exact .here _ hl
    | there e m hm hl hr ih =>
      replace hm := he (.here _ hl)
      rw [h.fn_eq hm] at ih
      refine .there _ _ hm hl (ih ?_)
      intro k hrk
      exact he (.there _ _ hm hl hrk)
  · induction hr with
    | here e hl => exact .here _ hl
    | there e m hm hl hr ih =>
      rw [← h.fn_eq hm] at ih
      refine .there _ _ (by grind) hl (ih ?_)
      intro k hrk
      rw [h.fn_eq hm] at hrk
      exact he (.there _ _ hm hl hrk)

grind_pattern Expr.reachable_in_prefix_iff => p.Prefix p', e.Reachable p n
grind_pattern Expr.reachable_in_prefix_iff => p.Prefix p', e.Reachable p' n

theorem Expr.reachable_mono {p : Program} {e e' : Expr} {n : Nat}
    (h : ∀ m, e.LocalFn m → e'.LocalFn m) : e.Reachable p n → e'.Reachable p n
  | .here _ hl => .here _ (h _ hl)
  | .there _ _ hm hl hr => .there _ _ hm (h _ hl) hr

theorem Termination.localFn_or_occurs_of_reachable {p : Program} {e : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} {n : Nat} (h : e.Reachable p n) :
    e.LocalFn n ∨ Termination.Occurs p vm fm n := by
  induction h with grind [Termination.Occurs, Program.UsesFn]

theorem Expr.exists_of_new_reachable {p p' : Program} {e : Expr} {n : Nat}
    (hpre : p.Prefix p') (hp : ¬e.Reachable p n) (hp' : e.Reachable p' n) :
    ∃ m, p.size ≤ m ∧ m < p'.size ∧ (e.LocalFn m ∨ p.UsesFn m) := by
  induction hp' with
  | here e hl =>
    exfalso
    exact hp (.here _ hl)
  | there e m hm' hl hr ih =>
    by_cases hm : m < p.size
    · rw [hpre.fn_eq hm] at ih
      obtain ⟨k, hk, hk', h⟩ := ih (hp <| .there _ _ hm hl ·)
      refine ⟨k, hk, hk', ?_⟩
      obtain h | ⟨i, hi, h⟩ := h
      · exact Or.inr ⟨m, hm, h⟩
      · exact Or.inr ⟨i, hi, h⟩
    · exact ⟨m, by simpa using hm, hm', Or.inl hl⟩

structure Finset : Type where
  mem : Nat → Prop
  bound : Nat
  not_mem_of_ge_bound : ∀ m ≥ bound, ¬mem m

instance : Membership Nat Finset := ⟨Finset.mem⟩

instance : HasSubset Finset where
  Subset s₁ s₂ := ∀ n ∈ s₁, n ∈ s₂

instance : HasSSubset Finset where
  SSubset s₁ s₂ := s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁

instance : EmptyCollection Finset := ⟨fun _ => False, 0, by simp⟩

instance : Singleton Nat Finset where
  singleton n := ⟨fun m => m = n, n + 1, by lia⟩

def Finset.insert (s : Finset) (n : Nat) : Finset where
  mem := fun m => m = n ∨ s.mem m
  bound := (n + 1).max s.bound
  not_mem_of_ge_bound := by grind [not_mem_of_ge_bound]

instance : Insert Nat Finset where
  insert n s := s.insert n

protected def Finset.union (s₁ s₂ : Finset) : Finset where
  mem := fun n => s₁.mem n ∨ s₂.mem n
  bound := s₁.bound.max s₂.bound
  not_mem_of_ge_bound := by grind [not_mem_of_ge_bound]

instance : Union Finset := ⟨Finset.union⟩

def Finset.filter (s : Finset) (p : Nat → Prop) : Finset where
  mem := fun n => s.mem n ∧ p n
  bound := s.bound
  not_mem_of_ge_bound := by grind [not_mem_of_ge_bound]

open Classical in
noncomputable def Finset.size (s : Finset) : Nat := aux s.bound (Nat.le_refl _)
  where
    aux (i : Nat) (h : i ≤ s.bound) : Nat :=
      match i with
      | 0 => 0
      | i + 1 => aux i (by lia) + if i ∈ s then 1 else 0

def Finset.withBound (s : Finset) (b : Nat) (h : ∀ n ≥ b, n ∉ s) : Finset where
  mem := s.mem
  bound := b
  not_mem_of_ge_bound := by simpa [Membership.mem] using h

@[grind →]
theorem Finset.notMem_of_ge_bound {s : Finset} {n : Nat} (h : s.bound ≤ n) :
    n ∉ s := s.not_mem_of_ge_bound n h

@[grind →]
theorem Finset.mem_of_subset {s₁ s₂ : Finset} {n : Nat} (h : s₁ ⊆ s₂)
    (hn : n ∈ s₁) : n ∈ s₂ := h _ hn

@[simp, grind .]
theorem Finset.notMem_emptyCollection {n : Nat} : n ∉ (∅ : Finset) := by
  simp [Membership.mem, EmptyCollection.emptyCollection]

@[simp, grind =]
theorem Finset.singleton_eq_insert {n : Nat} : {n} = Insert.insert n (∅ : Finset) := by
  simp [EmptyCollection.emptyCollection, Singleton.singleton, Insert.insert, Finset.insert]

@[simp, grind =]
theorem Finset.mem_insert_iff {s : Finset} {m n : Nat} :
    n ∈ Insert.insert m s ↔ n = m ∨ n ∈ s := by
  simp [Membership.mem, Insert.insert, Finset.insert]

@[simp, grind =]
theorem Finset.mem_union_iff {s₁ s₂ : Finset} {n : Nat} :
    n ∈ s₁ ∪ s₂ ↔ n ∈ s₁ ∨ n ∈ s₂ := by
  simp [Membership.mem, Union.union, Finset.union]

@[simp, grind =]
theorem Finset.mem_filter_iff {s : Finset} {p : Nat → Prop} {n : Nat} :
    n ∈ s.filter p ↔ n ∈ s ∧ p n := by
  simp [Membership.mem, Finset.filter]

@[simp, grind =]
theorem Finset.mem_withBound_iff {s : Finset} {b n : Nat} (h : ∀ m ≥ b, m ∉ s) :
    n ∈ s.withBound b h ↔ n ∈ s := by
  simp [Membership.mem, withBound]

@[grind →]
theorem Finset.ssubset_of_subset {s₁ s₂ : Finset} {n : Nat} (h : s₁ ⊆ s₂)
    (h₁ : n ∉ s₁) (h₂ : n ∈ s₂) : s₁ ⊂ s₂ := ⟨h, fun h => h₁ (h _ h₂)⟩

theorem Finset.size_withBound {s : Finset} {b : Nat} (h : ∀ n ≥ b, n ∉ s) :
    (s.withBound b h).size = s.size := by
  have h₁ : ∀ i (hi : i ≤ s.bound.min b),
      size.aux (s.withBound b h) i (by grind [withBound]) = size.aux s i (by grind) := by
    intro i hi
    fun_induction size.aux s i (by grind) with grind [size.aux]
  have h₂ : ∀ i hile (higt : s.bound.min b < i),
      size.aux s i hile = size.aux s (s.bound.min b) (by lia) := by
    intro i hile higt
    fun_induction size.aux s i hile with grind
  have h₃ : ∀ i hile (hige : s.bound.min b < i),
      size.aux (s.withBound b h) i hile = size.aux (s.withBound b h) (s.bound.min b) (by lia) := by
    intro i hile higt
    fun_induction size.aux _ i hile with grind
  grind [size]

theorem Finset.size_insert {s : Finset} {n : Nat} (h : n ∉ s) :
    (Insert.insert n s).size = s.size + 1 := by
  let b := (n + 1).max s.bound
  have hb : ∀ m ≥ b, m ∉ s := by grind [notMem_of_ge_bound]
  rw [← size_withBound hb]
  suffices ∀ i hi,
      size.aux (Insert.insert n s) i hi =
        size.aux (s.withBound b hb) i hi + if n < i then 1 else 0 by
    have := this b (Nat.le_refl _)
    simpa [show n < b by grind]
  intro i hi
  fun_induction size.aux (Insert.insert n s) i hi with grind [size.aux]

@[grind →]
theorem Finset.size_le_size {s₁ s₂ : Finset} (h : s₁ ⊆ s₂) :
    s₁.size ≤ s₂.size := by
  have hb : ∀ n ≥ s₂.bound, n ∉ s₁ := by grind [notMem_of_ge_bound]
  rw [← size_withBound hb]
  suffices ∀ i (hi : i ≤ s₂.bound),
      size.aux (s₁.withBound s₂.bound hb) i hi ≤ size.aux s₂ i hi from
    this _ _
  intro i hi
  fun_induction size.aux s₂ i hi with grind [size.aux]

@[grind →]
theorem Finset.size_lt_size {s₁ s₂ : Finset} (h : s₁ ⊂ s₂) :
    s₁.size < s₂.size := by
  obtain ⟨hsub, hex⟩ := h
  simp only [Subset, Classical.not_forall] at hex
  obtain ⟨n, h₂, h₁⟩ := hex
  calc s₁.size
    _ < (Insert.insert n s₁).size := by
      rw [size_insert h₁]
      exact Nat.lt_succ_self _
    _ ≤ s₂.size := by
      apply size_le_size
      intro m h
      simp only [mem_insert_iff] at h
      obtain rfl | h := h
      · exact h₂
      · exact hsub _ h

def Expr.localFns : Expr → Finset
  | var _ | const _ => ∅
  | fn m => {m}
  | bin _ e₁ e₂ => e₁.localFns ∪ e₂.localFns
  | cond c et ef => c.localFns ∪ et.localFns ∪ ef.localFns
  | proj e _ => e.localFns

def Program.usedFns (p : Program) : Finset :=
  aux p.size (Nat.le_refl _)
  where
    aux (i : Nat) (hn : i ≤ p.size) :=
      match i with
      | 0 => ∅
      | i + 1 => aux i (by lia) ∪ p.fn[i].localFns

def VarMap.usedFns {n : Nat} (vm : VarMap n) : Finset :=
  aux n (Nat.le_refl _)
  where
    aux (i : Nat) (hn : i ≤ n) :=
      match i with
      | 0 => ∅
      | i + 1 => aux i (by lia) ∪ vm[i].localFns

def FunMap.range {n : Nat} (fm : FunMap n) : Finset :=
  aux n (Nat.le_refl _)
  where
    aux (i : Nat) (hn : i ≤ n) :=
      match i with
      | 0 => ∅
      | i + 1 => insert fm[i] (aux i (by lia))

theorem Expr.localFns_correct {e : Expr} {m : Nat} :
    m ∈ e.localFns ↔ e.LocalFn m := by
  fun_induction localFns with grind

theorem Program.usedFns_correct {p : Program} {m : Nat} :
    m ∈ p.usedFns ↔ p.UsesFn m := by
  suffices ∀ i hi, m ∈ usedFns.aux p i hi ↔
      ∃ (j : Nat) (_ : j < i), p.fn[j].LocalFn m by
    simpa [UsesFn, usedFns] using this p.size (Nat.le_refl _)
  intro i hi
  fun_induction usedFns.aux with grind [Expr.localFns_correct]

theorem VarMap.usedFns_correct {n : Nat} {vm : VarMap n} {m : Nat} :
    m ∈ vm.usedFns ↔ vm.UsesFn m := by
  suffices ∀ i hi, m ∈ usedFns.aux vm i hi ↔
      ∃ (j : Nat) (_ : j < i), vm[j].LocalFn m by
    simpa [UsesFn, usedFns] using this n (Nat.le_refl _)
  intro i hi
  fun_induction usedFns.aux with grind [Expr.localFns_correct]

theorem FunMap.range_correct {n : Nat} {fm : FunMap n} {m : Nat} :
    m ∈ fm.range ↔ fm.Contains m := by
  suffices ∀ i hi, m ∈ range.aux fm i hi ↔
      ∃ (j : Nat) (_ : j < i), fm[j] = m by
    simpa [Contains, range] using this n (Nat.le_refl _)
  intro i hi
  fun_induction range.aux with grind

namespace Termination

open Classical in
noncomputable def reachableUnmapped (p : Program) (e : Expr)
    (fm : FunMap p.size) : Finset := aux p.size (Nat.le_refl _)
  where
    aux (i : Nat) (h : i ≤ p.size) : Finset :=
      match i with
      | 0 => ∅
      | i + 1 =>
        let rest := aux i (by lia)
        if e.Reachable p i ∧ fm[i] = i then insert i rest else rest

@[grind =]
theorem reachableUnmapped_correct {p : Program} {e : Expr} {fm : FunMap p.size}
    {m : Nat} :
    m ∈ reachableUnmapped p e fm ↔ e.Reachable p m ∧ ∃ hm, fm[m] = m := by
  suffices ∀ i (hi : i ≤ p.size),
      m ∈ reachableUnmapped.aux p e fm i hi ↔ e.Reachable p m ∧ ∃ hm, fm[m] = m ∧ m < i by
    simp_all [reachableUnmapped]
  intro i hi
  fun_induction reachableUnmapped.aux with grind

@[grind! .]
theorem subset_reachableUnmapped_bin_left {p : Program} {k : BinKind}
    {e₁ e₂ : Expr} {fm : FunMap p.size} :
    reachableUnmapped p e₁ fm ⊆ reachableUnmapped p (e₁.bin k e₂) fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_reachableUnmapped_bin_right {p : Program} {k : BinKind}
    {e₁ e₂ : Expr} {fm : FunMap p.size} :
    reachableUnmapped p e₂ fm ⊆ reachableUnmapped p (e₁.bin k e₂) fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_reachableUnmapped_cond_cond {p : Program} {c et ef : Expr}
    {fm : FunMap p.size} :
    reachableUnmapped p c fm ⊆ reachableUnmapped p (c.cond et ef) fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_reachableUnmapped_cond_true {p : Program} {c et ef : Expr}
    {fm : FunMap p.size} :
    reachableUnmapped p et fm ⊆ reachableUnmapped p (c.cond et ef) fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_reachableUnmapped_cond_false {p : Program} {c et ef : Expr}
    {fm : FunMap p.size} :
    reachableUnmapped p ef fm ⊆ reachableUnmapped p (c.cond et ef) fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_reachableUnmapped_proj {p : Program} {e : Expr} {i : Fin 2}
    {fm : FunMap p.size} :
    reachableUnmapped p e fm ⊆ reachableUnmapped p (e.proj i) fm := by
  intro n hn
  grind

def invalidFns (p : Program) (e : Expr) (vm : VarMap p.size)
    (fm : FunMap p.size) : Finset :=
  (e.localFns ∪ p.usedFns ∪ vm.usedFns ∪ fm.range).filter (p.size ≤ ·)

@[grind =]
theorem invalidFns_correct {p : Program} {e : Expr} {vm : VarMap p.size}
    {fm : FunMap p.size} {m : Nat} :
    m ∈ invalidFns p e vm fm ↔ (e.LocalFn m ∨ Termination.Occurs p vm fm m) ∧ p.size ≤ m := by
  grind [Termination.Occurs, invalidFns, Expr.localFns_correct,
    Program.usedFns_correct, VarMap.usedFns_correct, FunMap.range_correct]

@[grind! .]
theorem subset_invalidFns_bin_left {p : Program} {k : BinKind} {e₁ e₂ : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    invalidFns p e₁ vm fm ⊆ invalidFns p (e₁.bin k e₂) vm fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_invalidFns_bin_right {p : Program} {k : BinKind} {e₁ e₂ : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    invalidFns p e₂ vm fm ⊆ invalidFns p (e₁.bin k e₂) vm fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_invalidFns_cond_cond {p : Program} {c et ef : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    invalidFns p c vm fm ⊆ invalidFns p (c.cond et ef) vm fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_invalidFns_cond_true {p : Program} {c et ef : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    invalidFns p et vm fm ⊆ invalidFns p (c.cond et ef) vm fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_invalidFns_cond_false {p : Program} {c et ef : Expr}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    invalidFns p ef vm fm ⊆ invalidFns p (c.cond et ef) vm fm := by
  intro n hn
  grind

@[grind! .]
theorem subset_invalidFns_proj {p : Program} {e : Expr} {i : Fin 2}
    {vm : VarMap p.size} {fm : FunMap p.size} :
    invalidFns p e vm fm ⊆ invalidFns p (e.proj i) vm fm := by
  intro n hn
  grind

@[grind! ⇒]
theorem invalidFns_subset_of_occursProvenance {p p' : Program} {e : Expr}
    {vm : VarMap p.size} {vm' : VarMap p'.size} {fm : FunMap p.size}
    {fm' : FunMap p'.size} (hpre : p.Prefix p')
    (h : Termination.OccursProvenance p p' vm vm' fm fm') :
    invalidFns p' e vm' fm' ⊆ invalidFns p e vm fm := by
  intro n hn
  grind

@[grind! ⇒]
theorem invalidFns_ssubset_or_reachableUnmapped_subset {p p' : Program}
    {e : Expr} {vm : VarMap p.size} {vm' : VarMap p'.size}
    {fm : FunMap p.size} {fm' : FunMap p'.size} (hpre : p.Prefix p')
    (hext : ∀ (m : Nat) hm, fm[m] ≠ m → fm'[m]'(by grind) = fm[m])
    (hprov : OccursProvenance p p' vm vm' fm fm') :
    invalidFns p' e vm' fm' ⊂ invalidFns p e vm fm ∨
      reachableUnmapped p' e fm' ⊆ reachableUnmapped p e fm := by
  by_cases h : reachableUnmapped p' e fm' ⊆ reachableUnmapped p e fm
  · simp [h]
  · obtain ⟨m, h⟩ := Classical.not_forall.mp h
    simp only [reachableUnmapped_correct, not_imp] at h
    obtain ⟨⟨hr', hm', hmm⟩, h⟩ := h
    simp only [not_and, not_exists] at h
    have hsub := invalidFns_subset_of_occursProvenance (e := e) hpre hprov
    by_cases hr : e.Reachable p m
    · specialize h hr
      have hm : p.size ≤ m := by grind
      refine Or.inl <| Finset.ssubset_of_subset (n := m) ?_ ?_ ?_
      · exact hsub
      · grind
      · simp only [invalidFns_correct]
        exact ⟨Termination.localFn_or_occurs_of_reachable hr, hm⟩
    · obtain ⟨k, hk, hk', hl⟩ := Expr.exists_of_new_reachable hpre hr hr'
      refine Or.inl <| Finset.ssubset_of_subset (n := k) ?_ ?_ ?_
      · exact hsub
      · grind
      · obtain hl | hp := hl
        · exact invalidFns_correct.mpr ⟨Or.inl hl, hk⟩
        · exact invalidFns_correct.mpr ⟨Or.inr (.program hp), hk⟩

end Termination
